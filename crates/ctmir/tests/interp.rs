//! The verified interpreter, its arithmetic and the selftest: the old `tools/ct-driver/src/interp.rs`
//! tests (sanity programs, arithmetic edges, vector syntax) ported to `ctmir::interp`, and the
//! pipeline's selftest mode on `tiny.json`.
use ctcore::syntax::{AggKind, BinOp as B, Block, Body, Callee, ConstVal, Intrinsic as K, IntTy as T, Operand, Place, Program, Proj, Rvalue, Stmt, Term, Ty, UnOp};
use ctmir::interp::interp;
use ctmir::interp_arith::{binop_exec, cast_exec, unop_exec};
use ctmir::interp_val::{CLoc, CRoot, CVal};
use ctmir::pipeline::{pipeline, Mode};
use ctmir::vectors::{check_vector, parse_vector, Vector};

const TINY: &[u8] = include_bytes!("data/tiny.json");

fn pl(local: usize, proj: Vec<Proj>) -> Place { Place { local, proj } }
fn lp(local: usize) -> Place { pl(local, vec![]) }
fn cp(local: usize) -> Operand { Operand::Copy(lp(local)) }
fn k8(n: u128) -> Operand { Operand::Const(T::U8, n) }
fn set(d: Place, rv: Rvalue) -> Stmt { Stmt::Assign(d, rv) }
fn blk(stmts: Vec<Stmt>, term: Term) -> Block { Block { stmts, term } }
fn int(t: T) -> Ty { Ty::Int(t) }
fn mutt(t: Ty) -> Ty { Ty::Mut(Box::new(t)) }
fn shrt(t: Ty) -> Ty { Ty::Shr(Box::new(t)) }
fn arr(xs: &[u128]) -> CVal { CVal::Arr(xs.iter().map(|&x| CVal::Int(x)).collect()) }
fn shr(v: CVal) -> CVal { CVal::Shr(Box::new(v)) }
/// One fn with `nargs` parameters; local types matter only for `Mut` and `Shr` parameters.
fn prog(nargs: usize, locals: Vec<Ty>, blocks: Vec<Block>) -> Program { Program { fns: vec![Body { nargs, locals, blocks }] } }
fn units(n: usize) -> Vec<Ty> { (0..n).map(|_| Ty::Unit).collect() }

/// `interp` from `args` with no slots: the return value and the steps.
fn run(p: &Program, args: Vec<CVal>, fuel: u64) -> Option<(CVal, u64)> {
    let slots: Vec<CVal> = args.iter().map(|_| CVal::Unit).collect();
    interp(p, 0, &args, &slots, fuel).map(|(r, _, n)| (r, n))
}

/// A test rendering of a value.
fn d(v: &CVal) -> String {
    let l = |vs: &Vec<CVal>| vs.iter().map(d).collect::<Vec<_>>().join(",");
    match v {
        CVal::Int(n) => format!("{n:#x}"),
        CVal::Unit => "()".into(),
        CVal::Tup(vs) => format!("({})", l(vs)),
        CVal::Adt(k, vs) => format!("#{k}({})", l(vs)),
        CVal::Arr(vs) => format!("[{}]", l(vs)),
        CVal::Shr(b) => format!("&{}", d(b)),
        CVal::Mut(m) => format!("mut({})", match m.root { CRoot::Local(i) => format!("L{i}"), CRoot::Slot(j) => format!("S{j}") }),
    }
}

fn is(v: &CVal, w: &CVal) -> bool { d(v) == d(w) }

macro_rules! assert_run {
    ($got:expr, $want:expr, $steps:expr) => {{
        let (r, n) = $got.expect("run gave None");
        assert!(is(&r, &$want), "got {} want {}", d(&r), d(&$want));
        assert_eq!(n, $steps);
    }};
}

fn intr_prog(nargs: usize, k: K, args: Vec<Operand>) -> Program {
    let mut ls = units(nargs + 1);
    if nargs > 0 { ls[1] = mutt(Ty::Vec(Box::new(int(T::U8)))); }
    prog(nargs, ls, vec![blk(vec![], Term::Call(Callee::Intr(k), args, lp(0), 1)), blk(vec![], Term::Return)])
}

#[test]
fn sanity_switch_and_assert() {
    let switch = |v: u128, ts: Vec<(u128, usize)>, o: usize| prog(0, units(1), vec![
        blk(vec![], Term::Switch(k8(v), ts, o)),
        blk(vec![set(lp(0), Rvalue::Use(k8(10)))], Term::Return),
        blk(vec![set(lp(0), Rvalue::Use(k8(20)))], Term::Return),
    ]);
    assert_run!(run(&switch(1, vec![(0, 2), (1, 1), (1, 2)], 2), vec![], 3), CVal::Int(10), 3);
    assert_run!(run(&switch(5, vec![(0, 1), (1, 1)], 2), vec![], 3), CVal::Int(20), 3);
    let fail = prog(0, units(1), vec![blk(vec![], Term::Assert(Operand::Const(T::Bool, 1), false, 1)), blk(vec![], Term::Return)]);
    assert!(run(&fail, vec![], 3).is_none());
    let ret = prog(0, units(1), vec![blk(vec![], Term::Return)]);
    assert!(run(&ret, vec![], 0).is_none(), "fuel 0");
    assert!(run(&prog(0, units(1), vec![]), vec![], 9).is_none(), "no block");
}

#[test]
fn sanity_places() {
    // _0 = _1[_2]
    let p = prog(2, units(3), vec![blk(vec![set(lp(0), Rvalue::Use(Operand::Copy(pl(1, vec![Proj::Index(2)]))))], Term::Return)]);
    assert_run!(run(&p, vec![arr(&[10, 20, 30]), CVal::Int(1)], 1), CVal::Int(20), 2);
    assert_run!(run(&p, vec![arr(&[10, 20, 30]), CVal::Int(3)], 1), CVal::Unit, 2);
    // _2 = &_1; _0 = Len(*_2)
    let p = prog(1, units(3), vec![blk(vec![set(lp(2), Rvalue::RefShr(lp(1))), set(lp(0), Rvalue::Len(pl(2, vec![Proj::Deref])))], Term::Return)]);
    assert_run!(run(&p, vec![arr(&[1, 2, 3])], 1), CVal::Int(3), 3);
    // a `Variant` write keeps the tag: _1 as variant 1 . field 0 = 9; _0 = _1
    let p = prog(1, units(2), vec![blk(vec![
        set(pl(1, vec![Proj::Downcast(1), Proj::Field(0)]), Rvalue::Use(k8(9))),
        set(lp(0), Rvalue::Use(cp(1))),
    ], Term::Return)]);
    assert_run!(run(&p, vec![CVal::Adt(0, vec![CVal::Int(1)])], 1), CVal::Adt(0, vec![CVal::Int(9)]), 3);
    // a field write past the end pads with Unit
    let p = prog(1, units(2), vec![blk(vec![set(pl(1, vec![Proj::Field(2)]), Rvalue::Use(k8(7))), set(lp(0), Rvalue::Use(cp(1)))], Term::Return)]);
    assert_run!(run(&p, vec![CVal::Tup(vec![CVal::Int(1)])], 1), CVal::Tup(vec![CVal::Int(1), CVal::Unit, CVal::Int(7)]), 3);
    // Discr through a trailing Downcast
    let p = prog(1, units(2), vec![blk(vec![set(lp(0), Rvalue::Discr(pl(1, vec![Proj::Downcast(4)])))], Term::Return)]);
    assert_run!(run(&p, vec![CVal::Adt(2, vec![])], 1), CVal::Int(4), 2);
}

#[test]
fn sanity_ops() {
    let bin = |op: B| prog(2, units(3), vec![blk(vec![set(lp(0), Rvalue::Bin(op, T::U32, cp(1), cp(2)))], Term::Return)]);
    assert_run!(run(&bin(B::Div), vec![CVal::Int(7), CVal::Int(2)], 1), CVal::Int(3), 2);
    assert_run!(run(&bin(B::Shl), vec![CVal::Int(1), CVal::Int(3)], 1), CVal::Int(8), 2);
    let steps = prog(0, units(1), vec![blk(vec![set(lp(0), Rvalue::Use(k8(1))), set(lp(0), Rvalue::Use(k8(2)))], Term::Goto(1)), blk(vec![set(lp(0), Rvalue::Use(k8(3)))], Term::Return)]);
    assert_run!(run(&steps, vec![], 2), CVal::Int(3), 5);
    let agg = prog(1, units(2), vec![blk(vec![set(lp(0), Rvalue::Aggregate(AggKind::Adt(1), vec![cp(1), Operand::Lit(ConstVal::Arr(vec![ConstVal::Int(4)]))]))], Term::Return)]);
    assert_run!(run(&agg, vec![CVal::Int(5)], 1), CVal::Adt(1, vec![CVal::Int(5), arr(&[4])]), 2);
    let rep = prog(1, units(2), vec![blk(vec![set(lp(0), Rvalue::Repeat(cp(1), 3))], Term::Return)]);
    assert_run!(run(&rep, vec![CVal::Int(5)], 1), arr(&[5, 5, 5]), 2);
}

#[test]
fn sanity_calls() {
    // caller: _1 = 0; _2 = &mut _1; call g(_2) -> _3; _0 = _1. g(x: &mut u8) { *x = 7 }
    let caller = Body { nargs: 0, locals: units(4), blocks: vec![
        blk(vec![set(lp(1), Rvalue::Use(k8(0))), set(lp(2), Rvalue::RefMut(lp(1)))], Term::Call(Callee::Fn(1), vec![cp(2)], lp(3), 1)),
        blk(vec![set(lp(0), Rvalue::Use(cp(1)))], Term::Return),
    ] };
    let callee = Body { nargs: 1, locals: vec![Ty::Unit, mutt(int(T::U8))], blocks: vec![blk(vec![set(pl(1, vec![Proj::Deref]), Rvalue::Use(k8(7)))], Term::Return)] };
    let p = Program { fns: vec![caller, callee] };
    assert_run!(run(&p, vec![], 2), CVal::Int(7), 7);
    // a &mut root param: its slot comes back
    let p = prog(1, vec![int(T::U8), mutt(int(T::U8))], vec![blk(vec![
        set(pl(1, vec![Proj::Deref]), Rvalue::Bin(B::Add, T::U8, Operand::Copy(pl(1, vec![Proj::Deref])), k8(2))),
        set(lp(0), Rvalue::Use(Operand::Copy(pl(1, vec![Proj::Deref])))),
    ], Term::Return)]);
    let (r, sl, n) = interp(&p, 0, &vec![CVal::Int(99)], &vec![CVal::Int(5)], 1).unwrap();
    assert!(is(&r, &CVal::Int(7)) && is(&sl[0], &CVal::Int(7)) && n == 3);
}

#[test]
fn sanity_intrinsics() {
    let slot0 = || CVal::Mut(CLoc { root: CRoot::Slot(0), path: vec![] });
    let with = |p: &Program, slot: CVal, more: Vec<CVal>| {
        let mut args = vec![slot0()];
        args.extend(more);
        let mut slots = vec![slot];
        while slots.len() < args.len() { slots.push(CVal::Unit); }
        interp(p, 0, &args, &slots, 2).unwrap()
    };
    let (_, sl, n) = with(&intr_prog(1, K::VecPush, vec![cp(1), k8(9)]), arr(&[1]), vec![]);
    assert!(is(&sl[0], &arr(&[1, 9])) && n == 2);
    let (_, sl, n) = with(&intr_prog(2, K::VecExtendFromSlice, vec![cp(1), cp(2)]), arr(&[1]), vec![shr(arr(&[3, 4]))]);
    assert!(is(&sl[0], &arr(&[1, 3, 4])) && n == 4, "extend costs its length");
    let (_, sl, _) = with(&intr_prog(1, K::VecSet, vec![cp(1), Operand::Const(T::Usize, 1), k8(9)]), arr(&[5, 6]), vec![]);
    assert!(is(&sl[0], &arr(&[5, 9])));
    assert_run!(run(&intr_prog(0, K::Declassify, vec![k8(42)]), vec![], 2), CVal::Int(42), 2);
    assert_run!(run(&intr_prog(0, K::VecWithCapacity, vec![Operand::Const(T::Usize, 16)]), vec![], 2), arr(&[]), 2);
    let sub = prog(1, units(2), vec![blk(vec![], Term::Call(Callee::Intr(K::SliceSubrange), vec![cp(1), Operand::Const(T::Usize, 1), Operand::Const(T::Usize, 10)], lp(0), 1)), blk(vec![], Term::Return)]);
    assert_run!(run(&sub, vec![shr(arr(&[1, 2, 3]))], 2), shr(arr(&[2, 3])), 2);
    let idx = prog(1, units(2), vec![blk(vec![], Term::Call(Callee::Intr(K::VecIndex), vec![cp(1), Operand::Const(T::Usize, 1)], lp(0), 1)), blk(vec![], Term::Return)]);
    assert_run!(run(&idx, vec![shr(arr(&[10, 20]))], 2), shr(CVal::Int(20)), 2);
    assert_run!(run(&intr_prog(0, K::Wrapping(B::Sub, T::U64), vec![Operand::Const(T::U64, 1), Operand::Const(T::U64, 2)]), vec![], 2), CVal::Int(u64::MAX as u128), 2);
}

/// Rust's wrapping semantics per `IntTy`, at the edges `sem::binop`/`cast` define (the old
/// interpreter's `arithmetic_edges`), plus every op against native Rust on a grid of edge values.
#[test]
fn arithmetic_edges() {
    assert_eq!(binop_exec(&B::Sub, &T::U8, 0, 1), 0xff);
    assert_eq!(binop_exec(&B::Div, &T::I8, 0x80, 0xff), 0x80);
    assert_eq!(binop_exec(&B::Rem, &T::I8, 0x80, 0xff), 0);
    assert_eq!(binop_exec(&B::Div, &T::U32, 7, 0), 0);
    assert_eq!(binop_exec(&B::Rem, &T::I32, 7, 0), 0);
    assert_eq!(binop_exec(&B::Shl, &T::U32, 1, 33), 2);
    assert_eq!(binop_exec(&B::Shr, &T::I8, 0x80, 1), 0xc0);
    assert_eq!(binop_exec(&B::Lt, &T::I8, 0xff, 0), 1);
    assert_eq!(binop_exec(&B::Lt, &T::U8, 0xff, 0), 0);
    assert_eq!(binop_exec(&B::Add, &T::Bool, 1, 1), 0);
    assert_eq!(binop_exec(&B::Shl, &T::U128, 1, 127), 1 << 127);
    assert_eq!(unop_exec(&UnOp::Not, &T::U8, 0x0f), 0xf0);
    assert_eq!(unop_exec(&UnOp::Not, &T::Bool, 1), 0);
    assert_eq!(unop_exec(&UnOp::Neg, &T::I8, 1), 0xff);
    assert_eq!(cast_exec(&T::I8, &T::U32, 0xff), 0xffff_ffff);
    assert_eq!(cast_exec(&T::U8, &T::U32, 0xff), 0xff);
    assert_eq!(cast_exec(&T::U64, &T::U8, 0x1234), 0x34);
    assert_eq!(cast_exec(&T::I64, &T::U128, u64::MAX as u128), u128::MAX);
    assert_eq!(cast_exec(&T::Bool, &T::U8, 1), 1);
    let xs: [i128; 9] = [0, 1, 2, 3, -1, -2, i128::MIN, i128::MAX, 0x5a5a_5a5a_5a5a_5a5a_5a5a_5a5a_5a5a_5a5a];
    for &a in &xs {
        for &b in &xs {
            let (ua, ub) = (a as u128, b as u128);
            assert_eq!(binop_exec(&B::Mul, &T::I128, ua, ub), a.wrapping_mul(b) as u128);
            assert_eq!(binop_exec(&B::Shr, &T::I128, ua, ub), a.wrapping_shr(b as u32) as u128);
            assert_eq!(binop_exec(&B::Shr, &T::I16, ua & 0xffff, ub), (a as i16).wrapping_shr(b as u32) as u16 as u128);
            if b as i64 != 0 {
                assert_eq!(binop_exec(&B::Div, &T::I64, ua & u64::MAX as u128, ub & u64::MAX as u128), (a as i64).wrapping_div(b as i64) as u64 as u128);
            }
            if b as i32 != 0 {
                assert_eq!(binop_exec(&B::Rem, &T::I32, ua & 0xffff_ffff, ub & 0xffff_ffff), (a as i32).wrapping_rem(b as i32) as u32 as u128);
            }
            assert_eq!(binop_exec(&B::Ge, &T::Isize, ua, ub), ((a as i64) >= (b as i64)) as u128);
            assert_eq!(cast_exec(&T::I16, &T::I64, ua), (a as i16) as i64 as u64 as u128);
        }
    }
}

fn toks(s: &str) -> Vec<Vec<u8>> { s.split_whitespace().map(|t| t.as_bytes().to_vec()).collect() }

fn vector(s: &str) -> Result<Vector, String> { parse_vector(&toks(s)).map_err(|e| String::from_utf8_lossy(&e).into_owned()) }

#[test]
fn vector_syntax() {
    let v = vector("00ff - 0x2au128 mut:[0x1u64,0x2u64] => () [0x1u64]").unwrap();
    assert!(is(&v.args[0].1, &shr(arr(&[0, 0xff]))) && !v.args[0].0);
    assert!(is(&v.args[1].1, &shr(arr(&[]))));
    assert!(is(&v.args[2].1, &CVal::Int(0x2a)));
    assert!(v.args[3].0 && is(&v.args[3].1, &arr(&[1, 2])));
    assert!(is(&v.want[0], &CVal::Unit) && is(&v.want[1], &arr(&[1])));
    assert_eq!(v.bits, vec![None, None, Some(128), None]);
    let v = vector("=> None Some(0a)").unwrap();
    assert!(is(&v.want[0], &CVal::Adt(0, vec![])) && is(&v.want[1], &CVal::Adt(1, vec![arr(&[10])])));
    let v = vector("[(0x1u64,0x2u64),(0x3u64,0x4u64)] => Some((0x5u64,0x6usize))").unwrap();
    let pair = |a, b| CVal::Tup(vec![CVal::Int(a), CVal::Int(b)]);
    assert!(is(&v.args[0].1, &shr(CVal::Arr(vec![pair(1, 2), pair(3, 4)]))));
    assert!(is(&v.want[0], &CVal::Adt(1, vec![pair(5, 6)])));
    let v = vector("#0() true => #1(#0(0x105u64)) #2(0x7u8,[(0x1u64,0x2u64)]) false").unwrap();
    assert!(is(&v.args[0].1, &CVal::Adt(0, vec![])) && is(&v.args[1].1, &CVal::Int(1)) && is(&v.want[2], &CVal::Int(0)));
    assert!(is(&v.want[0], &CVal::Adt(1, vec![CVal::Adt(0, vec![CVal::Int(0x105)])])));
    assert!(vector("0x1u8 => panic").unwrap().panic);
    assert!(!vector("0x1u8 => panic 0x1u8").is_ok());
    for bad in ["0x1 => ()", "0x100u8 => ()", "abc => ()", "00", "=> True", "=> (0x1u8,0x2)", "=> #x(0x1u8)", "=> #1(0x1u8", "=> #1", "=> 0xu8"] {
        assert!(vector(bad).is_err(), "{bad}");
    }
}

/// A plain arg of a `Shr` param is passed by reference; widths and `mut:` must fit the params.
#[test]
fn vector_checks() {
    let deref = prog(1, vec![Ty::Adt(vec![vec![]]), shrt(Ty::Adt(vec![vec![]]))], vec![blk(vec![set(lp(0), Rvalue::Use(Operand::Copy(pl(1, vec![Proj::Deref]))))], Term::Return)]);
    assert_eq!(check_vector(&deref, &vector("#0() => #0()").unwrap()), Ok(Some(2)));
    let ret = || vec![blk(vec![], Term::Return)];
    let p = prog(1, vec![int(T::U8), int(T::U8)], ret());
    let chk = |p: &Program, s: &str| check_vector(p, &vector(s).unwrap()).map_err(|e| String::from_utf8_lossy(&e).into_owned());
    assert_eq!(chk(&p, "0x1u8 => 0x0u8"), Err("got () want 0x0".into()));
    assert!(chk(&p, "0x1u128 => ()").unwrap_err().contains("param #1"));
    assert!(chk(&p, "0x1usize => ()").unwrap_err().contains("param #1"));
    assert!(chk(&p, "0x1u8 0x1u8 => ()").unwrap_err().contains("2 args for 1 params"));
    assert!(chk(&p, "0x1u8 => 0x0u16").unwrap_err().contains("want #1: a 16-bit value for a 8-bit result"));
    assert!(chk(&p, "0x1u8 => () ()").unwrap_err().contains("2 expected values for 1 return value and 0 &mut params"));
    let p = prog(1, vec![Ty::Unit, mutt(int(T::U8))], ret());
    assert_eq!(chk(&p, "mut:0x7u8 => () 0x7u8"), Ok(Some(1)));
    assert!(chk(&p, "0x7u8 => () 0x7u8").unwrap_err().contains("`mut:`"));
    assert!(chk(&p, "mut:0x7u32 => () 0x7u8").unwrap_err().contains("param #1"));
    assert!(chk(&p, "mut:0x7u8 => () 0x7u16").unwrap_err().contains("want #2: a 16-bit value for a 8-bit result"));
    let abort = prog(0, units(1), vec![blk(vec![], Term::Abort)]);
    assert_eq!(chk(&abort, "=> panic"), Ok(None));
    assert!(chk(&abort, "=> ()").unwrap_err().contains("gave None"));
    assert!(chk(&prog(0, units(1), ret()), "=> panic").unwrap_err().contains("want panic"));
}

fn selftest(vectors: &str) -> Result<String, String> {
    pipeline(TINY, &vec![vec![]], &Mode::Selftest(vectors.as_bytes().to_vec()))
        .map(|r| String::from_utf8(r).unwrap())
        .map_err(|e| String::from_utf8_lossy(&e).into_owned())
}

/// The pipeline's selftest: one line per vector of the crate, in file order, duplicates kept.
#[test]
fn selftest_report() {
    let r = selftest("# a comment\ntiny::tiny 0a0b0c0d 0x5usize => 0x9u8 # the bounds check passes\n\
        other::f 00 => ()\ntiny::opt true => Some(0x3u8)\ntiny::opt false => None\ntiny::opt false => None\n\
        tiny::call 0a0b0c0d => 0xeu8\ntiny::opt true => None\ntiny::nope => ()\n").unwrap();
    let ls: Vec<&str> = r.lines().collect();
    assert_eq!(ls.len(), 7, "{r}");
    assert!(ls[0].starts_with("pass tiny::tiny steps="), "{r}");
    assert!(ls[1].starts_with("pass tiny::opt steps=") && ls[2] == ls[3] && ls[2].starts_with("pass tiny::opt"), "{r}");
    assert!(ls[4].starts_with("pass tiny::call steps="), "{r}");
    assert!(ls[5].starts_with("fail tiny::opt got #1(0x3) want #0()"), "{r}");
    assert!(ls[6].starts_with("fail tiny::nope translation failed: 1 error(s), first: Root"), "{r}");
    assert!(selftest("tiny::opt true Some(0x3u8)\n").unwrap_err().starts_with("vectors:1: no `=>`"));
    assert!(selftest("other::f 00 => ()\n").unwrap_err().contains("no selftest vector for analysed crate tiny"));
}
