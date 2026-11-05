use ctmir::eval::*;
use ctmir::eval_const::e_const_val;
use ctmir::eval_tab::*;
use ctmir::interp_val::{CFrame, CVal};
use ctmir::json::parse;
use ctmir::mir::*;
use ctmir::schema::decode;

const TINY: &[u8] = include_bytes!("data/tiny.json");

fn dec(b: &[u8]) -> MirCrate { decode(parse(b).expect("parse")).expect("decode") }

/// `b` with its only occurrence of `from` replaced by `to` (as in tests/lower.rs).
fn edit(b: &[u8], from: &str, to: &str) -> Vec<u8> {
    let s = std::str::from_utf8(b).unwrap();
    assert_eq!(s.matches(from).count(), 1, "{from}");
    s.replacen(from, to, 1).into_bytes()
}

fn show(v: &CVal) -> String {
    let all = |vs: &Vec<CVal>| vs.iter().map(show).collect::<Vec<_>>().join(",");
    match v {
        CVal::Int(n) => format!("{n}"),
        CVal::Unit => "()".into(),
        CVal::Tup(vs) => format!("({})", all(vs)),
        CVal::Adt(k, vs) => format!("Adt{k}[{}]", all(vs)),
        CVal::Arr(vs) => format!("[{}]", all(vs)),
        CVal::Shr(b) => format!("&{}", show(b)),
        CVal::Mut(_) => "&mut".into(),
    }
}

fn inst(m: &MirCrate, name: &str) -> usize { m.insts.iter().position(|i| i.name == name.as_bytes()).expect(name) }

fn bytes(xs: &[u128]) -> CVal { CVal::Arr(xs.iter().map(|x| CVal::Int(*x)).collect()) }

fn tiny_args(a: CVal) -> Vec<CVal> { vec![a, CVal::Int(5)] }

fn entry(m: &MirCrate, tb: &Tabs) -> CFrame {
    let a = CVal::Shr(Box::new(bytes(&[0x0a, 0x0b, 0x0c, 0x0d])));
    match e_mir_entry(m, tb, inst(m, "tiny::tiny"), tiny_args(a), vec![CVal::Unit, CVal::Unit]) {
        Ok(fr) => fr,
        Err(_) => panic!("entry"),
    }
}

/// Review Focus 1: a duplicate id resolves to its first row; an id past the cap is `None`.
#[test]
fn tabs_first_match_and_cap() {
    let m = dec(&edit(TINY, r#"],"adts""#, r#",{"id":2,"kind":{"RigidTy":"Bool"}}],"adts""#));
    let tb = tabs(&m).expect("tabs");
    assert!(matches!(t_rigid(&m, &tb, 2), Some(RigidTy::Uint(UintTy::U8))));
    let u8row = r#"{"id":2,"kind":{"RigidTy":{"Uint":"U8"}}}"#;
    assert!(tabs(&dec(&edit(TINY, u8row, r#"{"id":16777216,"kind":{"RigidTy":{"Uint":"U8"}}}"#))).is_none());
    assert!(tabs(&dec(&edit(TINY, u8row, r#"{"id":16777215,"kind":{"RigidTy":{"Uint":"U8"}}}"#))).is_some());
}

#[test]
fn entry_frame_tiny() {
    let m = dec(TINY);
    let tb = tabs(&m).unwrap();
    let fr = entry(&m, &tb);
    let ls: Vec<String> = fr.locals.iter().map(show).collect();
    // tiny's locals: no unit-like type holding an array, so every non-parameter local is `Unit`
    assert_eq!(ls, ["()", "&[10,11,12,13]", "5", "()", "()", "()", "()"]);
    let i = inst(&m, "tiny::tiny");
    let a = CVal::Shr(Box::new(bytes(&[0x0a, 0x0b, 0x0c, 0x0d])));
    assert!(x_wt_args(&m, &tb, i, &tiny_args(a), &vec![CVal::Unit, CVal::Unit]));
    assert!(!x_wt_args(&m, &tb, i, &tiny_args(CVal::Int(5)), &vec![CVal::Unit, CVal::Unit]));
}

#[test]
fn stmts_tiny() {
    let m = dec(TINY);
    let tb = tabs(&m).unwrap();
    let mut fr = entry(&m, &tb);
    let b = m.insts[inst(&m, "tiny::tiny")].body.as_ref().unwrap();
    // three assignments of uncharged constants: one step each
    assert!(matches!(e_exec_stmts(&m, &tb, b, &mut fr, &b.blocks[0].statements), Ok(3)));
    assert_eq!(show(&fr.locals[5]), "1"); // 5 & 3
    assert_eq!(show(&fr.locals[3]), "[1,2,3]");
    assert_eq!(show(&fr.locals[6]), "1"); // 1 < 4
}

/// An out-of-bounds `Index` is a panic (`proj_step`'s bound), not a read.
#[test]
fn index_oob_panics() {
    let m = dec(TINY);
    let tb = tabs(&m).unwrap();
    let mut fr = entry(&m, &tb);
    let b = m.insts[inst(&m, "tiny::tiny")].body.as_ref().unwrap();
    let Some(Statement { kind: StatementKind::Assign(_, Rvalue::Use(Operand::Copy(p), _)), .. }) = b.blocks[1].statements.first() else { panic!("bb1") };
    fr.locals[5] = CVal::Int(3);
    assert!(matches!(e_read_place(&fr, p), Ok(CVal::Int(0x0d))));
    fr.locals[5] = CVal::Int(4);
    assert!(matches!(e_read_place(&fr, p), Err(Halt::Panic)));
}

#[test]
fn const_opt() {
    let m = dec(TINY);
    let tb = tabs(&m).unwrap();
    let b = m.insts[inst(&m, "tiny::opt")].body.as_ref().unwrap();
    let Some(Statement { kind: StatementKind::Assign(_, Rvalue::Use(Operand::Constant(c), _)), .. }) = b.blocks[1].statements.first() else { panic!("bb1") };
    let ConstantKind::Allocated(a) = &c.const_.kind else { panic!("kind") };
    assert_eq!(a.bytes, [Some(1), Some(3)]);
    match e_const_val(&m, &tb, c) {
        Ok((v, k)) => assert_eq!((show(&v), k), ("Adt1[3]".to_string(), 1)),
        Err(_) => panic!("const"),
    }
}

// ------------------------------------------------------------------ Task 2: runs

use ctmir::eval_run::{mir_eval, Ev};
use ctmir::lower_fn::lower;
use ctmir::policy::Policy;
use ctmir::vectors::FUEL;

fn pol0() -> Policy {
    Policy {
        roots: vec![], cost_roots: vec![], labels: vec![], internal_crates: vec![], translate_crates: vec![],
        declassify: vec![], ghost_unit: vec![],
    }
}

/// `mir_eval` of `root` (which must lower, so it is in the subset) with `Unit` slots.
fn run(m: &MirCrate, root: &str, args: Vec<CVal>, fuel: u64) -> Ev {
    assert!(lower(m, &pol0(), root.as_bytes(), &mut Vec::new()).is_ok(), "{root} does not lower");
    let tb = tabs(m).unwrap();
    let slots: Vec<CVal> = args.iter().map(|_| CVal::Unit).collect();
    mir_eval(m, &tb, &pol0(), inst(m, root), &args, &slots, fuel)
}

fn done(e: Ev) -> (String, u64) {
    match e {
        Ev::Done(fr, n) => (show(&fr.locals[0]), n),
        Ev::Panic => ("panic".into(), 0),
        Ev::Fuel => ("fuel".into(), 0),
        Ev::GaveUp => ("gave up".into(), 0),
    }
}

fn abcd() -> CVal { CVal::Shr(Box::new(bytes(&[0x0a, 0x0b, 0x0c, 0x0d]))) }

/// The step counts are the core interpreter's `steps=` for the same vectors (selftest at 0b0061c's
/// core path, vt-8d-evidence/t2/core-steps.txt).
#[test]
fn eval_tiny() {
    let m = dec(TINY);
    assert_eq!(done(run(&m, "tiny::tiny", tiny_args(abcd()), FUEL)), ("9".into(), 7));
    assert_eq!(done(run(&m, "tiny::opt", vec![CVal::Int(1)], FUEL)), ("Adt1[3]".into(), 5));
    assert_eq!(done(run(&m, "tiny::opt", vec![CVal::Int(0)], FUEL)), ("Adt0[]".into(), 5));
    assert_eq!(done(run(&m, "tiny::call", vec![abcd()], FUEL)), ("14".into(), 9));
}

#[test]
fn eval_fuel() {
    let m = dec(TINY);
    assert!(matches!(run(&m, "tiny::call", vec![abcd()], 1), Ev::Fuel));
}

#[test]
fn eval_panic() {
    let m = dec(&edit(TINY, r#""expected":true"#, r#""expected":false"#));
    assert!(matches!(run(&m, "tiny::tiny", tiny_args(abcd()), FUEL), Ev::Panic));
}

/// The timing probe (Task 3's 150 s bound): `CT_DUMP_DIR` is a ct-check output dir; `CT_PROBE_EXTRA`
/// optionally names a file of more crypto vectors (the RSA spike vector). Each vector runs on
/// `mir_eval` and, for comparison, on the core interpreter (`check_vector`). Arguments are shaped
/// by hand: a non-`Shr` value at a `&` parameter is wrapped in `Shr`.
#[test]
#[ignore]
fn eval_probe() {
    let dir = std::env::var("CT_DUMP_DIR").expect("CT_DUMP_DIR");
    let m = dec(&std::fs::read(format!("{dir}/crypto/mir-crypto.json")).unwrap());
    let pol = ctmir::policy::parse_manifests(&vec![std::fs::read("../../tools/ct-driver/manifest.txt").unwrap()]).unwrap();
    let tb = tabs(&m).unwrap();
    let st = std::fs::read_to_string("../../tools/ct-driver/selftest.txt").unwrap();
    let mut lines: Vec<String> = vec![
        st.lines().find(|l| l.starts_with("crypto::sha256::sha256 616263 ")).unwrap().into(),
        st.lines().find(|l| l.starts_with("crypto::p256::p256_public_key 0000000000000000000000000000000000000000000000000000000000000003 ")).unwrap().into(),
    ];
    if let Ok(p) = std::env::var("CT_PROBE_EXTRA") {
        lines.extend(std::fs::read_to_string(p).unwrap().lines().filter(|l| !l.trim().is_empty() && !l.starts_with('#')).map(String::from));
    }
    for line in &lines {
        let ws: Vec<Vec<u8>> = line.split_whitespace().map(|w| w.as_bytes().to_vec()).collect();
        let path = std::str::from_utf8(&ws[0]).unwrap();
        let v = ctmir::vectors::parse_vector(&ws[1..]).ok().expect("vector");
        let i = ctmir::lower_fn::root_inst(&m, path.as_bytes()).ok().expect("root");
        let (p, _) = lower(&m, &pol, path.as_bytes(), &mut Vec::new()).ok().expect("lower");
        let b = m.insts[i].body.as_ref().unwrap();
        let args: Vec<CVal> = v.args.iter().enumerate().map(|(j, (_, x))| {
            let shr = matches!(t_rigid(&m, &tb, b.locals[j + 1].ty), Some(RigidTy::Ref(_, _, Mutability::Not)));
            if shr && !matches!(x, CVal::Shr(_)) { CVal::Shr(Box::new(clone(x))) } else { clone(x) }
        }).collect();
        let slots: Vec<CVal> = args.iter().map(|_| CVal::Unit).collect();
        let t0 = std::time::Instant::now();
        let e = mir_eval(&m, &tb, &pol, i, &args, &slots, FUEL);
        let dt = t0.elapsed();
        let (kind, n, ret) = match &e {
            Ev::Done(fr, n) => ("Done", *n, show(&fr.locals[0])),
            Ev::Panic => ("Panic", 0, String::new()),
            Ev::Fuel => ("Fuel", 0, String::new()),
            Ev::GaveUp => ("GaveUp", 0, String::new()),
        };
        let t1 = std::time::Instant::now();
        let core = ctmir::vectors::check_vector(&p, &v);
        let dc = t1.elapsed();
        let core = match core { Ok(Some(n)) => format!("pass steps={n}"), Ok(None) => "panic".into(), Err(e) => format!("fail {}", String::from_utf8_lossy(&e)) };
        let ret = if ret.len() > 60 { format!("{}..", &ret[..60]) } else { ret };
        println!("probe {path} mir={kind} steps={n} time={:.2}s core: {core} time={:.2}s ret={ret}", dt.as_secs_f64(), dc.as_secs_f64());
    }
}

fn clone(v: &CVal) -> CVal { ctmir::interp_val::cclone(v) }
