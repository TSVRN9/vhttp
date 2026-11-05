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
