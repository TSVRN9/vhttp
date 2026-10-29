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
use rustc_public::{CompilerError, CrateDef, ItemKind};
use std::collections::{BTreeSet, HashSet};
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
        Ok(()) | Err(CompilerError::Skipped) => {}
        Err(CompilerError::Interrupted(e)) => die(&e),
        Err(CompilerError::Failed) => exit(1),
    }
}

/// The manifest roots of crate `krate`, as instances of its local fn items. A root with this
/// crate's prefix that matches no item is an error; roots of other crates are skipped.
fn roots(krate: &str, m: &Manifest) -> Result<Vec<Instance>, String> {
    let prefix = format!("{krate}::");
    let mut want: Vec<&String> = m.roots.iter().filter(|r| r.starts_with(&prefix)).collect();
    let mut found = Vec::new();
    for item in rustc_public::all_local_items() {
        if item.kind() != ItemKind::Fn {
            continue;
        }
        let Ok(inst) = Instance::try_from(item) else { continue }; // generic: not a root
        let key = ct_key(&inst);
        if let Some(i) = want.iter().position(|r| **r == key) {
            want.remove(i);
            found.push(inst);
        }
    }
    match want.first() {
        Some(r) => Err(format!("root {r} matches no monomorphic fn in crate {krate}")),
        None => Ok(found),
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

/// Census: from the roots, follow `Call`s through internal callees; write one line per reached
/// callee to `census-<krate>.txt`, sorted and unique. A call whose callee is not a resolvable
/// fn item (a fn-pointer or closure call) is reported and fails the build after the file is written.
fn census(krate: &str, m: &Manifest, roots: &[Instance], out: &std::path::Path) -> Result<(), String> {
    let mut seen: HashSet<Instance> = roots.iter().copied().collect();
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
            let yn = if callee.has_body() { "yes" } else { "no" };
            lines.insert(format!("callee {} crate={} body={yn}\n", ct_key(&callee), callee.def.krate().name));
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
