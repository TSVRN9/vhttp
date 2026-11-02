//! ct-driver (TRUSTED, unverified): the constant-time checker's front end. It runs as
//! `RUSTC_WORKSPACE_WRAPPER`. Crates named in `CT_CRATES` compile in-process under rustc_public
//! and are analysed; every other invocation passes through to rustc unchanged.
//!
//! Environment: `CT_CRATES` (comma-separated crate names), `CT_MANIFEST` (colon-separated manifest
//! paths), `CT_OUT` (report dir, created if missing), `CT_MODE` = `check` (default) | `census` |
//! `selftest` (with `CT_SELFTEST` = the vector file, see `selftest`) | `cost` (see `cost`).
//!
//! Check mode writes `$CT_OUT/report-<crate>.txt` with one verdict per manifest root of the crate
//! (`root <path> ok`, or one `reject <path> <Kind> <site> ..` line per kind and site), and for ok
//! roots the `checked` and `declassify` lines. Rejections are verdicts, not build errors; only a
//! failure to produce the report (manifest, I/O, no root for the crate) fails the build.
//! Only `secret(..)` labels are enforced; `public(..)` is a declaration (see `translate.rs`).
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
#[macro_use]
extern crate rustc_public;
extern crate rustc_public_bridge;

mod interp;
mod manifest;
mod translate;

use manifest::Manifest;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{Body, TerminatorKind};
use rustc_public::{CompilerError, CrateDef, DefId, ItemKind};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
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
    Selftest,
    Cost,
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
        Ok("selftest") => Mode::Selftest,
        Ok("cost") => Mode::Cost,
        Ok(other) => die(&format!("unknown CT_MODE {other:?} (check | census | selftest | cost)")),
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
    if encode_mir(&m, &krate) {
        args.push("-Zalways-encode-mir".into());
    }
    let res = run!(&args, || {
        let r = match mode {
            Mode::Census => roots(&krate, &m).and_then(|roots| census(&krate, &m, &roots, &out)),
            Mode::Check => check(&krate, &m, &out),
            Mode::Selftest => selftest(&krate, &m, &out),
            Mode::Cost => cost(&krate, &m, &out),
        };
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

/// Whether an analysed crate's compile adds `-Zalways-encode-mir`: a `translate-crate` line names
/// it, so the crates analysed after it may translate its bodies, which rustc otherwise leaves out
/// of the metadata unless they are generic or small enough to inline (`body=no`). The flag changes
/// which MIR is available, never what it is. No `translate-crate` line names crypto, so its builds
/// are unchanged. A dependency outside `CT_CRATES` (vest_lib) is compiled as is: a body it did not
/// encode is a leaf, since `is_internal` requires `has_body()`, and fails translation as
/// `Unresolved`.
fn encode_mir(m: &Manifest, krate: &str) -> bool {
    m.translate_crates.iter().any(|c| c == krate)
}

/// The manifest roots of crate `krate`, as instances of its local fn items. Errors: no root for
/// this crate, a root matching no local fn, a root whose key names more than one local fn (generic
/// items count, keyed by their def name, since `ct_key` strips generic args), or a generic match.
/// Roots of other crates are skipped (they are checked when their crate compiles).
fn roots(krate: &str, m: &Manifest) -> Result<Vec<Instance>, String> {
    pick_roots(krate, &crate_roots(krate, m)?, &local_fns())
}

/// The manifest roots whose crate prefix is `krate`; none is an error.
fn crate_roots<'m>(krate: &str, m: &'m Manifest) -> Result<Vec<&'m String>, String> {
    let prefix = format!("{krate}::");
    let want: Vec<&String> = m.roots.iter().filter(|r| r.starts_with(&prefix)).collect();
    if want.is_empty() {
        return Err(format!("no manifest root for analysed crate {krate}"));
    }
    Ok(want)
}

/// The manifest cost roots whose crate prefix is `krate`; none is fine (an empty cost file).
fn crate_cost_roots<'m>(krate: &str, m: &'m Manifest) -> Vec<&'m String> {
    let prefix = format!("{krate}::");
    m.cost_roots.iter().filter(|r| r.starts_with(&prefix)).collect()
}

/// The local fn items by key: `Some` instance when monomorphic; generic items (never roots) are
/// keyed by their def name, so they still make a shared key ambiguous.
pub fn local_fns() -> Vec<(String, Option<Instance>)> {
    let mut items = Vec::new();
    for item in rustc_public::all_local_items() {
        if item.kind() != ItemKind::Fn {
            continue;
        }
        items.push(match Instance::try_from(item) {
            Ok(inst) => (ct_key(&inst), Some(inst)),
            Err(_) => (strip_generic_args(&item.name()), None),
        });
    }
    items
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

/// The callee lookup order of the spec: an `intr` line wins; otherwise a plain fn item (not a
/// shim, virtual or compiler intrinsic) with a body in the crate being compiled or a
/// `translate-crate` is internal (entered); otherwise it is a leaf.
pub fn is_internal(krate: &str, m: &Manifest, callee: &Instance) -> bool {
    let key = ct_key(callee);
    let c = callee.def.krate().name;
    !m.intr.iter().any(|(p, _)| *p == key)
        && callee.kind == InstanceKind::Item
        && callee.has_body()
        && (c == krate || m.translate_crates.contains(&c))
}

/// What a key must denote uniquely: the def for a leaf (an `intr` line or `Unresolved` speaks
/// about the generic def, so `Ghost::<Seq<u8>>` and `Ghost::<int>` are one claim), and the instance
/// for an internal fn or a root (each instance is its own translated body).
pub type KeyId = (DefId, Option<Instance>);

pub fn key_id(krate: &str, m: &Manifest, inst: &Instance) -> KeyId {
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

/// Check mode: per root of `krate`, its own closure, its own `Program` and `check_program` call,
/// its own verdict; then the report, sorted.
fn check(krate: &str, m: &Manifest, out: &std::path::Path) -> Result<(), String> {
    let (mut lines, mut declass) = (BTreeSet::new(), BTreeMap::<String, BTreeSet<String>>::new());
    let mut by_key = HashMap::new();
    for r in crate_roots(krate, m)? {
        match verdict(m, r, &mut by_key) {
            Ok((infos, ls)) => {
                lines.insert(format!("root {r} ok\n"));
                for (i, l) in infos.iter().zip(&ls) {
                    let sec: Vec<String> = (0..i.param_names.len())
                        .filter(|&j| l.locals.get(1 + j) == Some(&true))
                        .map(|j| if i.param_names[j].is_empty() { format!("#{}", j + 1) } else { i.param_names[j].clone() })
                        .collect();
                    let ret = if l.locals.first() == Some(&true) { 's' } else { 'p' };
                    lines.insert(format!("checked {} secret={} ret={ret}\n", i.path, sec.join(",")));
                    declass.entry(i.path.clone()).or_default().extend(i.declassify_sites.iter().cloned());
                }
            }
            Err(rejects) => {
                // one line per (root, kind, site): the first two words of a reject text
                let mut seen = HashSet::new();
                for x in rejects {
                    if seen.insert(x.split_whitespace().take(2).collect::<Vec<_>>().join(" ")) {
                        lines.insert(format!("reject {r} {x}\n"));
                    }
                }
            }
        }
    }
    for (f, sites) in declass {
        lines.extend(sites.iter().enumerate().map(|(k, s)| format!("declassify {f}#{} {s}\n", k + 1)));
    }
    let file = out.join(format!("report-{krate}.txt"));
    std::fs::write(&file, lines.into_iter().collect::<String>()).map_err(|e| format!("{}: {e}", file.display()))
}

/// Selftest (translation validation by vectors; the interpreter is not in the TCB): for each
/// line `<path> <arg>... => <ret> <mut-out>...` of `$CT_SELFTEST` whose path is in `krate`,
/// translate that fn's closure (`translate_closure`, no label rule), run it in `interp`, and
/// compare the return value and every `&mut` param's final pointee exactly. Writes
/// `selftest-<krate>.txt`, one line per vector in file order: `pass <path> steps=<n>` or
/// `fail <path> <why>`. A malformed line, or no vector for `krate`, fails the build.
fn selftest(krate: &str, m: &Manifest, out: &std::path::Path) -> Result<(), String> {
    let file = std::env::var("CT_SELFTEST").map_err(|_| "CT_SELFTEST is not set".to_string())?;
    let text = std::fs::read_to_string(&file).map_err(|e| format!("{file}: {e}"))?;
    let prefix = format!("{krate}::");
    let mut lines = String::new();
    let mut by_key = HashMap::new();
    for (n, line) in text.lines().enumerate() {
        // a comment starts at a `#` token other than a `#k(..)` enum value
        let comment = |t: &&str| t.starts_with('#') && !t[1..].starts_with(|ch: char| ch.is_ascii_digit());
        let toks: Vec<&str> = line.split_whitespace().take_while(|t| !comment(t)).collect();
        let Some((&path, rest)) = toks.split_first() else { continue };
        if !path.starts_with(&prefix) {
            continue;
        }
        let v = interp::parse_vector(rest).map_err(|e| format!("{file}:{}: {e}", n + 1))?;
        let r = match translate::translate_closure(m, path, &mut by_key) {
            Ok((p, _)) => interp::check_vector(&p, &v),
            Err(es) => Err(format!("translation failed: {} error(s), first: {}", es.len(), tr_text(&es[0]))),
        };
        lines += &match r {
            Ok(steps) => format!("pass {path} steps={steps}\n"),
            Err(e) => format!("fail {path} {e}\n"),
        };
    }
    if lines.is_empty() {
        return Err(format!("{file}: no selftest vector for analysed crate {krate}"));
    }
    let f = out.join(format!("selftest-{krate}.txt"));
    std::fs::write(&f, lines).map_err(|e| format!("{}: {e}", f.display()))
}

/// Cost mode: per `cost-root` of `krate`, its own closure and `Program`, and one line of
/// `cost-<krate>.txt`, sorted (empty for a crate with no cost root):
/// `bounded <path> deg=<d> steps <= <poly>`, or `none <path> <why>`. `bounded` means
/// `ctcore::cost::theorem_cost`'s statement applied to the program; no code calls that theorem.
fn cost(krate: &str, m: &Manifest, out: &std::path::Path) -> Result<(), String> {
    let mut lines = BTreeSet::new();
    // ponytail: one map across roots, so an ambiguous key in one root's closure can change another
    // root's verdict (a `none` or a hard error, never a bound); a fresh map per root removes that.
    let mut by_key = HashMap::new();
    for r in crate_cost_roots(krate, m) {
        lines.insert(format!("{}\n", cost_verdict(m, r, &mut by_key)?));
    }
    let file = out.join(format!("cost-{krate}.txt"));
    std::fs::write(&file, lines.into_iter().collect::<String>()).map_err(|e| format!("{}: {e}", file.display()))
}

/// One cost root's line. `check_program` gates `analyze`: `check_cert`'s `true` says nothing about
/// an ill-typed program, and `Ok` is what supplies `theorem_cost`'s `ok_prog`. No secrets are
/// declared, so all labels are public. `Err` is a hard error: no fn for the root, or an ambiguous key.
fn cost_verdict(m: &Manifest, r: &str, by_key: &mut HashMap<String, KeyId>) -> Result<String, String> {
    use ctcore::loops::CostWhy;
    use translate::TrErr;
    let (p, infos) = match translate::translate_closure(m, r, by_key) {
        Ok(x) => x,
        Err(es) => {
            if let Some(e) = es.iter().find(|e| matches!(e, TrErr::Root { .. })) {
                return Err(tr_text(e));
            }
            return Ok(format!("none {r} {}", tr_text(&es[0]).replace('\n', " ")));
        }
    };
    if let Err(rs) = ctcore::check_program(&p, &vec![None; p.fns.len()]) {
        let recursion = rs.iter().any(|rj| matches!(rj.kind, ctcore::RejectKind::Recursion));
        return Ok(format!("none {r} {}", if recursion { "Recursion" } else { "NotTyped" }));
    }
    let (sums, _, whys) = ctcore::analyze(&p);
    if let Some(Some(poly)) = sums.first() {
        let names = &infos[0].param_names;
        let deg = poly.monos.iter().filter(|x| x.coef != 0).map(|x| x.atoms.len()).max().unwrap_or(0);
        return Ok(format!("bounded {r} deg={deg} steps <= {}", poly_text(poly, names)));
    }
    let why = match whys.first() {
        Some(CostWhy::NotCounted(h)) => format!("NotCounted({h})"),
        Some(CostWhy::CalleeNone(g)) => format!("CalleeNone({g})"),
        Some(CostWhy::Validator(b)) => format!("Validator({b})"),
        Some(CostWhy::Unresolved) => "Unresolved".into(),
        Some(CostWhy::Recursion) => "Recursion".into(),
        Some(CostWhy::DegreeCap) => "DegreeCap".into(),
        Some(CostWhy::Overflow) => "Overflow".into(),
        Some(CostWhy::NotWf) => "NotWf".into(),
        Some(CostWhy::NotTyped) => "NotTyped".into(),
        Some(CostWhy::Bounded) | None => return Err(format!("{r}: analyze gave no summary and no reason")),
    };
    Ok(format!("none {r} {why}"))
}

/// A summary in the root's source parameter names: `13*len(s)*len(s) + 40*len(s) + 33`.
fn poly_text(poly: &ctcore::cost::Poly, names: &[String]) -> String {
    let monos: Vec<String> = poly
        .monos
        .iter()
        .filter(|x| x.coef != 0)
        .map(|x| {
            let atoms = x.atoms.iter().map(|a| atom_text(a, names));
            if x.coef == 1 && !x.atoms.is_empty() {
                atoms.collect::<Vec<_>>().join("*")
            } else {
                std::iter::once(x.coef.to_string()).chain(atoms).collect::<Vec<_>>().join("*")
            }
        })
        .collect();
    if monos.is_empty() {
        "0".into()
    } else {
        monos.join(" + ")
    }
}

/// `Val` is the parameter's name, `Len` is `len(name)`, `Gap` is `sat(a - b)`, the saturating
/// difference. Local `x` is parameter `x - 1`; `#x` is an unnamed one, `_x` is not a parameter.
fn atom_text(a: &ctcore::cost::Atom, names: &[String]) -> String {
    use ctcore::cost::Atom;
    let local = |x: usize| match x.checked_sub(1).and_then(|j| names.get(j)) {
        Some(n) if !n.is_empty() => n.clone(),
        Some(_) => format!("#{x}"),
        None => format!("_{x}"),
    };
    match a {
        Atom::Const(c) => c.to_string(),
        Atom::Val(x, _) => local(*x),
        Atom::Len(x) => format!("len({})", local(*x)),
        Atom::Gap(x, y) => format!("sat({} - {})", atom_text(x, names), atom_text(y, names)),
    }
}

fn tr_text(e: &translate::TrErr) -> String {
    use translate::TrErr;
    match e {
        TrErr::Unsupported { path, what, span } => format!("Unsupported {span} {path}: {what}"),
        TrErr::Unresolved { path, callee, span } => format!("Unresolved {span} {path} calls {callee}"),
        TrErr::Attr { path, msg } => format!("Attr {path}: {msg}"),
        TrErr::Root { path, msg } => format!("Root {path}: {msg}"),
    }
}

/// One root's verdict: its fns and checked labels, or its reject texts (`<Kind> <rest>`): the
/// translation errors, then the attribute rules, then `check_program`'s rejection sites.
fn verdict(
    m: &Manifest,
    root: &str,
    by_key: &mut HashMap<String, KeyId>,
) -> Result<(Vec<translate::FnInfo>, Vec<ctcore::ct::FnLab>), Vec<String>> {
    use translate::TrErr;
    let (p, infos) = translate::translate_closure(m, root, by_key).map_err(|es| es.iter().map(tr_text).collect::<Vec<_>>())?;
    let mut errs = Vec::new();
    for i in &infos {
        if let Some(msg) = &i.attr_err {
            errs.push(TrErr::Attr { path: i.path.clone(), msg: msg.clone() });
        } else if i.is_root && i.decl.is_none() {
            errs.push(TrErr::Root { path: i.path.clone(), msg: "a root needs a ct:: attribute".into() });
        }
    }
    if !errs.is_empty() {
        return Err(errs.iter().map(tr_text).collect());
    }
    let decl: Vec<Option<Vec<bool>>> = infos.iter().map(|i| i.decl.clone()).collect();
    match ctcore::check_program(&p, &decl) {
        Ok(ls) => Ok((infos, ls)),
        Err(rs) => Err(rs.iter().map(|rj| reject_text(&p, &infos, rj)).collect()),
    }
}

/// `<Kind> <file>:<line> <fn>`; at a call, also the callee, and for `ArgLabel(j)` its param name
/// (the label of a `Mut` param must equal the caller buffer's, so this names the param to fix).
fn reject_text(p: &ctcore::Program, infos: &[translate::FnInfo], rj: &ctcore::Reject) -> String {
    use ctcore::RejectKind as K;
    let Some(i) = infos.get(rj.f) else { return format!("NotWf fn #{} out of range", rj.f) };
    let site = match rj.stmt {
        Some(s) => i.stmt_spans.get(rj.block).and_then(|v| v.get(s)),
        None => i.block_spans.get(rj.block),
    };
    let site = site.map_or("?", |s| s.as_str());
    let term = (rj.stmt.is_none()).then(|| p.fns.get(rj.f).and_then(|b| b.blocks.get(rj.block)).map(|b| &b.term)).flatten();
    let callee = match term {
        Some(ctcore::Term::Call(ctcore::Callee::Fn(g), ..)) => infos.get(*g),
        _ => None,
    };
    let kind = match &rj.kind {
        K::SecretSwitch => "SecretSwitch",
        K::SecretAssert => "SecretAssert",
        K::SecretIndex => "SecretIndex",
        K::SecretDivOperand => "SecretDivOperand",
        K::SecretShift => "SecretShift",
        K::SecretAlloc => "SecretAlloc",
        K::SecretRange => "SecretRange",
        K::ArgLabel(_) => "ArgLabel",
        K::RetLabel => "RetLabel",
        K::MutLabel => "MutLabel",
        K::NotWf => "NotWf",
        K::Recursion => "Recursion",
        K::InferFailed => "InferFailed",
    };
    let mut s = format!("{kind} {site} in {}", i.path);
    if let Some(g) = callee {
        s += &format!(" calling {}", g.path);
        if let K::ArgLabel(j) = rj.kind {
            let name = g.param_names.get(j).map_or("", |n| n.as_str());
            s += &format!(" param #{} {name}", j + 1);
        }
    }
    s
}

#[cfg(test)]
mod tests {
    use super::strip_generic_args as k;
    use super::{bind_key, pick_roots, poly_text};
    use ctcore::cost::{Atom, Mono, Poly};
    use ctcore::IntTy;
    use std::collections::HashMap;

    #[test]
    fn poly_text_names_parameters() {
        let val = |x| Atom::Val(x, IntTy::Usize);
        let mono = |coef, atoms| Mono { coef, atoms };
        let gap = Atom::Gap(Box::new(Atom::Len(1)), Box::new(val(2)));
        let poly = Poly {
            monos: vec![
                mono(1, vec![Atom::Len(1)]),
                mono(13, vec![val(2), gap]),
                mono(0, vec![val(2)]),
                mono(3, vec![val(3)]),
                mono(2, vec![val(9), val(0)]),
                mono(7, vec![]),
            ],
        };
        let names = ["s".to_string(), "n".to_string(), String::new()];
        assert_eq!(poly_text(&poly, &names), "len(s) + 13*n*sat(len(s) - n) + 3*#3 + 2*_9*_0 + 7");
        assert_eq!(poly_text(&Poly { monos: vec![] }, &names), "0");
    }

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
