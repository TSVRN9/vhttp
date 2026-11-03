use ctmir::json::parse;
use ctmir::lower::{lower, FnInfo, Reject};
use ctmir::mir::*;
use ctmir::policy::Policy;
use ctmir::schema::decode;

#[path = "../../../tools/ct-driver/src/pprint.rs"]
mod pprint;

const TINY: &[u8] = include_bytes!("data/tiny.json");

fn dec(b: &[u8]) -> MirCrate { decode(parse(b).expect("parse")).expect("decode") }

fn s(b: &[u8]) -> String { String::from_utf8_lossy(b).into_owned() }

fn v(x: &str) -> Vec<u8> { x.as_bytes().to_vec() }

fn pol0() -> Policy {
    Policy {
        roots: vec![], cost_roots: vec![], labels: vec![], internal_crates: vec![], translate_crates: vec![],
        declassify: vec![], ghost_unit: vec![],
    }
}

fn reject_line(r: &Reject) -> String {
    match r {
        Reject::Unsupported { path, what, site } => format!("reject Unsupported {} {} # {}\n", s(site), s(path), s(what)),
        Reject::Unresolved { path, callee, site } => format!("reject Unresolved {} {} # {}\n", s(site), s(path), s(callee)),
        Reject::Attr { path, msg } => format!("reject Attr {} # {}\n", s(path), s(msg)),
        Reject::Root { path, msg } => format!("reject Root {} # {}\n", s(path), s(msg)),
    }
}

fn text(m: &MirCrate, pol: &Policy, root: &str) -> String {
    match lower(m, pol, root.as_bytes()) {
        Ok((p, infos)) => pprint::program_text(&p, &infos.iter().map(|i: &FnInfo| s(&i.path)).collect::<Vec<_>>()),
        Err(es) => {
            let mut lines: Vec<String> = es.iter().map(reject_line).collect();
            lines.sort();
            lines.dedup();
            lines.concat()
        }
    }
}

/// The manifests of one comparison run, read the way the old `manifest.rs` reads them, as a
/// `Policy` for crate `krate`: `intr .. Declassify` is a `declassify` line, `intr .. GhostUnit` a
/// `ghost` line unless the std model has the key, other `intr` lines are the std model's; vest_lib's
/// `Ghost::assume_new_fallback` is a `ghost` line (8c ruling).
fn policy(files: &[std::path::PathBuf], krate: &str) -> Policy {
    let mut p = pol0();
    p.internal_crates.push(v(krate));
    p.ghost_unit.push(v("vest_lib::prelude::Ghost::assume_new_fallback"));
    for f in files {
        for line in std::fs::read_to_string(f).unwrap().lines() {
            let line = line.split(" #").next().unwrap().trim();
            let w: Vec<&str> = line.split_whitespace().collect();
            match w.first().copied() {
                Some("root") => p.roots.push(v(w[1])),
                Some("cost-root") => p.cost_roots.push(v(w[1])),
                Some("translate-crate") => p.translate_crates.push(v(w[1])),
                Some("intr") => {
                    let k = w[1..w.len() - 1].join(" ");
                    let kind = *w.last().unwrap();
                    let (k, kind) = if ["Wrapping"].contains(&w[w.len() - 3]) { (w[1..w.len() - 3].join(" "), "Wrapping") } else { (k, kind) };
                    match kind {
                        "Declassify" => p.declassify.push(v(&k)),
                        "GhostUnit" if k != "vstd::prelude::Ghost::assume_new_fallback" => p.ghost_unit.push(v(&k)),
                        _ => {}
                    }
                }
                _ => {}
            }
        }
    }
    p
}

/// Step 3 of Task 5: for every run under `$CT_T5_OUT` (written by the evidence `runs.sh`: a dump and
/// the old translator's `program-<crate>.txt` per run), lower every root and cost root of each
/// dumped crate and write `new-program-<crate>.txt` beside the old one, in the same format.
/// `CT_T5_OUT=<dir> cargo test -p ctmir --release --test lower -- --ignored --nocapture`.
#[test]
#[ignore]
fn compare_runs() {
    let out = std::path::PathBuf::from(std::env::var("CT_T5_OUT").expect("CT_T5_OUT"));
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let ct = root.join("tools/ct-driver");
    let fx = root.join("tools/ct-fixtures");
    let runs: Vec<(&str, Vec<std::path::PathBuf>)> = vec![
        ("crypto", vec![ct.join("manifest.txt")]),
        ("fixtures", vec![fx.join("manifest.txt"), fx.join("cost-manifest.txt")]),
        ("negative", vec![ct.join("manifest.txt"), ct.join("manifest-negative.txt")]),
        ("parsers", vec![ct.join("manifest.txt"), ct.join("manifest-parsers.txt"), ct.join("cost-targets.txt")]),
    ];
    for (run, files) in runs {
        for e in std::fs::read_dir(out.join(run)).unwrap() {
            let path = e.unwrap().path();
            let file = path.file_name().unwrap().to_string_lossy().into_owned();
            let Some(krate) = file.strip_prefix("mir-").and_then(|f| f.strip_suffix(".json")) else { continue };
            let t = std::time::Instant::now();
            let m = dec(&std::fs::read(&path).unwrap());
            let pol = policy(&files, krate);
            let prefix = format!("{krate}::");
            let mut txt = String::new();
            for (list, roots) in [("root", &pol.roots), ("cost-root", &pol.cost_roots)] {
                for r in roots.iter().map(|r| s(r)).filter(|r| r.starts_with(&prefix)) {
                    txt += &format!("=== {list} {r}\n");
                    txt += &text(&m, &pol, &r);
                }
            }
            std::fs::write(out.join(run).join(format!("new-program-{krate}.txt")), txt).unwrap();
            eprintln!("{run}/{krate}: {:?}", t.elapsed());
        }
    }
}

/// `b` with its only occurrence of `from` replaced by `to`.
fn edit(b: &[u8], from: &str, to: &str) -> Vec<u8> {
    let s = std::str::from_utf8(b).unwrap();
    assert_eq!(s.matches(from).count(), 1, "{from}");
    s.replacen(from, to, 1).into_bytes()
}

fn kinds(m: &MirCrate, root: &str) -> Vec<String> {
    match lower(m, &pol0(), root.as_bytes()) {
        Ok(_) => vec![],
        Err(es) => es.iter().map(|r| reject_line(r).split_whitespace().nth(1).unwrap().to_string()).collect(),
    }
}

#[test]
fn tiny_lowers() {
    let m = dec(TINY);
    // `a[i & 3] ^ x[1]`: the bounds check, then the read (rustc folded `x[1]` to `2`).
    assert_eq!(text(&m, &pol0(), "tiny::tiny"), "fn tiny::tiny\n  nargs=2 locals=[u8, &[u8; 4], usize, [u8; 3], u8, usize, bool]\n\
        \x20 bb0: _3 = Array(1_u8, 2_u8, 3_u8); _5 = BitAnd.usize(_2, 3_usize); _6 = Lt.usize(_5, 4_usize); -> assert _6 == true -> bb1\n\
        \x20 bb1: _4 = (*_1)[_5]; _0 = BitXor.u8(_4, 2_u8); -> return\n");
    let (p, infos) = lower(&m, &pol0(), b"tiny::call").ok().unwrap();
    assert_eq!((p.fns.len(), s(&infos[0].path), s(&infos[1].path), infos[1].inst), (2, "tiny::call".into(), "tiny::tiny".into(), 2));
    // `Some(3)` and `None` are ADT constants: one temp each, read by the assignment.
    let opt = text(&m, &pol0(), "tiny::opt");
    assert!(opt.contains("bb1: _2 = Adt1(3_u8); _0 = _2; -> goto bb3") && opt.contains("bb2: _3 = Adt0(); _0 = _3; -> goto bb3"), "{opt}");
}

/// Review Focus 1: a missing table entry is a reject, never acceptance.
#[test]
fn missing_rows_reject() {
    let mut m = dec(TINY);
    m.calls.clear();
    assert_eq!(kinds(&m, "tiny::call"), ["Unresolved"]);
    let mut m = dec(TINY);
    m.adts.clear();
    assert!(!kinds(&m, "tiny::opt").is_empty());
    assert!(kinds(&m, "tiny::opt").iter().all(|k| k == "Unsupported"));
}

/// Review Focus 4: an uninitialized byte or a pointer in an integer constant.
#[test]
fn bad_constant_bytes_reject() {
    let m = dec(&edit(TINY, "\"bytes\":[2,0,0,0,0,0,0,0]", "\"bytes\":[null,0,0,0,0,0,0,0]"));
    assert_eq!(kinds(&m, "tiny::call"), ["Unsupported"]);
    let m = dec(&edit(TINY, "\"bytes\":[2,0,0,0,0,0,0,0],\"provenance\":{\"ptrs\":[]}", "\"bytes\":[2,0,0,0,0,0,0,0],\"provenance\":{\"ptrs\":[[0,0]]}"));
    assert_eq!(kinds(&m, "tiny::call"), ["Unsupported"]);
    assert_eq!(kinds(&dec(TINY), "tiny::call"), Vec::<String>::new());
}

/// Two instances under one key: the root (or a callee) is ambiguous.
#[test]
fn shared_key_rejects() {
    let mut m = dec(TINY);
    m.insts[1].key = v("tiny::tiny");
    match lower(&m, &pol0(), b"tiny::tiny") {
        Err(es) => match &es[..] { [Reject::Root { msg, .. }] => assert!(s(msg).contains("ambiguous")), _ => panic!() },
        Ok(_) => panic!("accepted"),
    }
}
