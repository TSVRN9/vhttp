//! ct-driver (TRUSTED, unverified): the constant-time checker's front end. It runs as
//! `RUSTC_WORKSPACE_WRAPPER`. Crates named in `CT_CRATES` compile in-process under rustc_public
//! and are analysed; every other invocation passes through to rustc unchanged.
//!
//! Environment: `CT_CRATES` (comma-separated crate names), `CT_MANIFEST` (colon-separated manifest
//! paths), `CT_OUT` (report dir, created if missing), `CT_MODE` = `check` (default) | `census`.
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
#[macro_use]
extern crate rustc_public;

mod manifest;

use manifest::Manifest;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Body, TerminatorKind};
use rustc_public::{CompilerError, CrateDef, DefId, ItemKind};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::PathBuf;
use std::process::{exit, Command};

/// The one key used by census lines, manifest matching and report lines: the resolved instance's
/// name with every `::<…>` generic-argument list removed. `::<impl …>` segments stay, so
/// `std::array::<impl [u8; 16]>::as_slice` keeps its N and `core::num::<impl u32>` its width.
pub fn ct_key(inst: &Instance) -> String {
    strip_generic_args(&inst.name())
}

/// `s` with every `::<…>` generic-argument list removed; `::<impl …>` segments are kept. The `>`
/// of `->` does not close a list. An unbalanced list is kept verbatim.
pub fn strip_generic_args(s: &str) -> String {
    let b = s.as_bytes();
    let (mut out, mut i, mut kept) = (String::new(), 0, 0);
    while i < b.len() {
        if b[i..].starts_with(b"::<") && !b[i..].starts_with(b"::<impl ") {
            let (mut depth, mut j, mut end) = (0usize, i + 2, None);
            while j < b.len() {
                match b[j] {
                    b'<' => depth += 1,
                    b'>' if b[j - 1] != b'-' => {
                        depth -= 1;
                        if depth == 0 {
                            end = Some(j);
                            break;
                        }
                    }
                    _ => {}
                }
                j += 1;
            }
            let Some(e) = end else { break };
            out.push_str(&s[kept..i]);
            i = e + 1;
            kept = i;
        } else {
            i += 1;
        }
    }
    out.push_str(&s[kept..]);
    out
}

enum Mode {
    Check,
    Census,
}

fn env_list(var: &str, sep: char) -> Vec<String> {
    std::env::var(var).unwrap_or_default().split(sep).filter(|s| !s.is_empty()).map(String::from).collect()
}

fn die(msg: &str) -> ! {
    eprintln!("ct-driver: {msg}");
    exit(1)
}

fn main() {
    // argv[1] is the real rustc (RUSTC_WORKSPACE_WRAPPER protocol), the rest its arguments.
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        die("usage: ct-driver <rustc> <args..> (run as RUSTC_WORKSPACE_WRAPPER)");
    }
    let krate = args.iter().position(|a| a == "--crate-name").and_then(|i| args.get(i + 1)).cloned();
    let Some(krate) = krate.filter(|k| env_list("CT_CRATES", ',').contains(k)) else {
        let st = Command::new(&args[0]).args(&args[1..]).status().unwrap_or_else(|e| die(&format!("{}: {e}", args[0])));
        exit(st.code().unwrap_or(1));
    };
    let mode = match std::env::var("CT_MODE").as_deref() {
        Err(_) | Ok("check") => Mode::Check,
        Ok("census") => Mode::Census,
        Ok(other) => die(&format!("unknown CT_MODE {other:?} (check | census)")),
    };
    let paths: Vec<PathBuf> = env_list("CT_MANIFEST", ':').into_iter().map(PathBuf::from).collect();
    if paths.is_empty() {
        die("CT_MANIFEST is not set or empty");
    }
    let m = manifest::load(&paths).unwrap_or_else(|e| die(&e));
    let out = PathBuf::from(std::env::var("CT_OUT").unwrap_or_else(|_| die("CT_OUT is not set")));
    std::fs::create_dir_all(&out).unwrap_or_else(|e| die(&format!("{}: {e}", out.display())));
    for f in ["-Zinline-mir=no", "--cfg", "ct_check", "-Zcrate-attr=feature(register_tool)", "-Zcrate-attr=register_tool(ct)"] {
        args.push(f.to_string());
    }
    let res = run!(&args, || {
        let r = roots(&krate, &m).and_then(|roots| match mode {
            Mode::Census => census(&krate, &m, &roots, &out),
            Mode::Check => Err("check mode is not implemented yet (Task 7b)".to_string()),
        });
        match r {
            Ok(()) => ControlFlow::Continue(()),
            Err(e) => ControlFlow::Break(e),
        }
    });
    match res {
        Ok(()) => {}
        Err(CompilerError::Skipped) => die(&format!("rustc ran no analysis for crate {krate}")),
        Err(CompilerError::Interrupted(e)) => die(&e),
        Err(CompilerError::Failed) => exit(1),
    }
}

/// The manifest roots of crate `krate`, as instances of its local fn items. Errors: no root for
/// this crate, a root matching no local fn, a root whose key names more than one local fn (generic
/// items count, keyed by their def name, since `ct_key` strips generic args), or a generic match.
/// Roots of other crates are skipped (they are checked when their crate compiles).
fn roots(krate: &str, m: &Manifest) -> Result<Vec<Instance>, String> {
    let prefix = format!("{krate}::");
    let want: Vec<&String> = m.roots.iter().filter(|r| r.starts_with(&prefix)).collect();
    if want.is_empty() {
        return Err(format!("no manifest root for analysed crate {krate}"));
    }
    let mut items = Vec::new();
    for item in rustc_public::all_local_items() {
        if item.kind() != ItemKind::Fn {
            continue;
        }
        items.push(match Instance::try_from(item) {
            Ok(inst) => (ct_key(&inst), Some(inst)),
            Err(_) => (strip_generic_args(&item.name()), None), // generic: never a root
        });
    }
    pick_roots(krate, &want, &items)
}

/// Each wanted key must name exactly one of `items`, and that one must be monomorphic (`Some`).
pub fn pick_roots<T: Copy>(krate: &str, want: &[&String], items: &[(String, Option<T>)]) -> Result<Vec<T>, String> {
    let mut out = Vec::new();
    for r in want {
        let hits: Vec<Option<T>> = items.iter().filter(|(k, _)| k == *r).map(|(_, v)| *v).collect();
        match hits[..] {
            [Some(v)] => out.push(v),
            [] | [None] => return Err(format!("root {r} matches no monomorphic fn in crate {krate}")),
            _ => return Err(format!("root {r} is ambiguous: {} fns of crate {krate} share its key", hits.len())),
        }
    }
    Ok(out)
}

/// Records that `key` names `v`. A key that already names a different value is ambiguous: `ct_key`
/// strips generic args, so distinct fns can share one (`W::<u32>::f`, `W::<u64>::f`), and a
/// manifest line or report line for it could not say which one it means.
pub fn bind_key<T: Copy + Eq>(by_key: &mut HashMap<String, T>, key: &str, v: T) -> Result<(), T> {
    match by_key.get(key) {
        Some(prev) if *prev != v => Err(*prev),
        Some(_) => Ok(()),
        None => {
            by_key.insert(key.to_string(), v);
            Ok(())
        }
    }
}

/// Blocks reachable from block 0 along normal (non-unwind) edges.
pub fn normal_blocks(body: &Body) -> Vec<usize> {
    let mut seen = vec![false; body.blocks.len()];
    let (mut stack, mut out) = (vec![0], Vec::new());
    while let Some(b) = stack.pop() {
        if b >= seen.len() || seen[b] {
            continue;
        }
        seen[b] = true;
        out.push(b);
        match &body.blocks[b].terminator.kind {
            TerminatorKind::Goto { target } | TerminatorKind::Drop { target, .. } | TerminatorKind::Assert { target, .. } => {
                stack.push(*target)
            }
            TerminatorKind::Call { target, .. } => stack.extend(*target),
            TerminatorKind::InlineAsm { destination, .. } => stack.extend(*destination),
            TerminatorKind::SwitchInt { targets, .. } => stack.extend(targets.all_targets()),
            TerminatorKind::Resume | TerminatorKind::Abort | TerminatorKind::Return | TerminatorKind::Unreachable => {}
        }
    }
    out
}

/// The callee lookup order of the spec: an `intr` line wins; otherwise a callee with a body in
/// the crate being compiled or a `translate-crate` is internal (entered); otherwise it is a leaf.
pub fn is_internal(krate: &str, m: &Manifest, callee: &Instance) -> bool {
    let key = ct_key(callee);
    let c = callee.def.krate().name;
    !m.intr.iter().any(|(p, _)| *p == key) && callee.has_body() && (c == krate || m.translate_crates.contains(&c))
}

/// What a key must denote uniquely: the def for a leaf (an `intr` line or `Unresolved` speaks
/// about the generic def, so `Ghost::<Seq<u8>>` and `Ghost::<int>` are one claim), and the instance
/// for an internal fn or a root (each instance is its own translated body).
type KeyId = (DefId, Option<Instance>);

fn key_id(krate: &str, m: &Manifest, inst: &Instance) -> KeyId {
    (inst.def.def_id(), is_internal(krate, m, inst).then_some(*inst))
}

/// Census: from the roots, follow `Call`s through internal callees; write one line per reached
/// callee to `census-<krate>.txt`, sorted and unique. A call whose callee is not a resolvable
/// fn item (a fn-pointer or closure call), and a key reached as more than one distinct instance
/// (roots included), are reported and fail the build after the file is written.
fn census(krate: &str, m: &Manifest, roots: &[Instance], out: &std::path::Path) -> Result<(), String> {
    let mut seen: HashSet<Instance> = roots.iter().copied().collect();
    let mut by_key: HashMap<String, KeyId> = HashMap::new();
    for r in roots {
        let _ = bind_key(&mut by_key, &ct_key(r), key_id(krate, m, r)); // distinct roots have distinct keys (pick_roots)
    }
    let mut work = roots.to_vec();
    let (mut lines, mut errs) = (BTreeSet::new(), BTreeSet::new());
    while let Some(inst) = work.pop() {
        let Some(body) = inst.body() else {
            errs.insert(format!("{}: no body", ct_key(&inst)));
            continue;
        };
        for b in normal_blocks(&body) {
            let TerminatorKind::Call { func, .. } = &body.blocks[b].terminator.kind else { continue };
            let kind = func.ty(body.locals()).map(|t| t.kind());
            let def = kind.as_ref().ok().and_then(|k| k.fn_def());
            let Some(callee) = def.and_then(|(d, a)| Instance::resolve(d, a).ok()) else {
                errs.insert(format!("{}: call to an unresolvable callee {func:?}", ct_key(&inst)));
                continue;
            };
            let key = ct_key(&callee);
            if let Err((def, prev)) = bind_key(&mut by_key, &key, key_id(krate, m, &callee)) {
                let prev = prev.map_or_else(|| def.name(), |p| p.name());
                errs.insert(format!("ambiguous key {key}: reached as {prev} and {}", callee.name()));
            }
            let yn = if callee.has_body() { "yes" } else { "no" };
            lines.insert(format!("callee {key} crate={} body={yn}\n", callee.def.krate().name));
            if is_internal(krate, m, &callee) && seen.insert(callee) {
                work.push(callee);
            }
        }
    }
    let file = out.join(format!("census-{krate}.txt"));
    std::fs::write(&file, lines.into_iter().collect::<String>()).map_err(|e| format!("{}: {e}", file.display()))?;
    if errs.is_empty() {
        return Ok(());
    }
    Err(format!("census: {}", errs.into_iter().collect::<Vec<_>>().join("; ")))
}

#[cfg(test)]
mod tests {
    use super::strip_generic_args as k;
    use super::{bind_key, pick_roots};
    use std::collections::HashMap;

    #[test]
    fn ambiguous_root_key_is_an_error() {
        let key = "kc::W::f".to_string();
        let want = [&key];
        // `impl W<u32> { fn f }` and `impl W<u64> { fn f }` both key to `kc::W::f`.
        let two = [(key.clone(), Some(1)), (key.clone(), Some(2))];
        assert!(pick_roots("kc", &want, &two).unwrap_err().contains("ambiguous"));
        let mono_and_generic = [(key.clone(), Some(1)), (key.clone(), None)];
        assert!(pick_roots("kc", &want, &mono_and_generic).unwrap_err().contains("ambiguous"));
        assert!(pick_roots::<u8>("kc", &want, &[(key.clone(), None)]).unwrap_err().contains("no monomorphic"));
        assert!(pick_roots("kc", &want, &[("kc::g".to_string(), Some(1))]).unwrap_err().contains("no monomorphic"));
        assert_eq!(pick_roots("kc", &want, &[(key.clone(), Some(7)), ("kc::g".to_string(), Some(8))]).unwrap(), [7]);
    }

    #[test]
    fn ambiguous_callee_key_is_an_error() {
        let mut m = HashMap::new();
        assert_eq!(bind_key(&mut m, "kc::W::f", 1), Ok(()));
        assert_eq!(bind_key(&mut m, "kc::W::f", 1), Ok(())); // same instance again: fine
        assert_eq!(bind_key(&mut m, "kc::W::f", 2), Err(1)); // a second instance: ambiguous
        assert_eq!(bind_key(&mut m, "kc::g", 2), Ok(()));
    }

    #[test]
    fn ct_key_strips_generic_args_only() {
        assert_eq!(k("std::vec::Vec::<u8>::push"), "std::vec::Vec::push");
        assert_eq!(k("std::vec::Vec::<u8, std::alloc::Global>::with_capacity"), "std::vec::Vec::with_capacity");
        assert_eq!(k("vstd::prelude::Ghost::<vstd::seq::Seq<u8>>::assume_new_fallback"), "vstd::prelude::Ghost::assume_new_fallback");
        assert_eq!(k("vstd::slice::slice_subrange::<u8>"), "vstd::slice::slice_subrange");
        assert_eq!(k("core::num::<impl u32>::wrapping_add"), "core::num::<impl u32>::wrapping_add");
        assert_eq!(k("std::array::<impl [u8; 16]>::as_slice"), "std::array::<impl [u8; 16]>::as_slice");
        assert_eq!(k("<std::vec::Vec<u8> as vstd::pervasive::VecAdditionalExecFns<u8>>::set"),
                   "<std::vec::Vec<u8> as vstd::pervasive::VecAdditionalExecFns<u8>>::set");
        assert_eq!(k("a::f::<fn() -> u8, u8>::g"), "a::f::g");
        assert_eq!(k("crypto::aes::encrypt_rk::{closure#0}"), "crypto::aes::encrypt_rk::{closure#0}");
        assert_eq!(k("crypto::é::<u8>"), "crypto::é");
    }

    #[test]
    fn ct_key_keeps_unbalanced_input() {
        assert_eq!(k("a::<b"), "a::<b");
        assert_eq!(k("a::<b<c>"), "a::<b<c>");
        assert_eq!(k("a::<"), "a::<");
    }
}
