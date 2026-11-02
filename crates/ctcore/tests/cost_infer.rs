//! The inference over the real shapes of `tests/cost_check.rs`, copied block for block.
use ctcore::cost::*;
use ctcore::cost_check::atoms_eq;
use ctcore::loops::*;
use ctcore::*;

const U: IntTy = IntTy::Usize;

fn pl(x: usize) -> Place { Place { local: x, proj: vec![] } }
fn cp(x: usize) -> Operand { Operand::Copy(pl(x)) }
fn k(n: u128) -> Operand { Operand::Const(IntTy::Usize, n) }
fn asg(x: usize, rv: Rvalue) -> Stmt { Stmt::Assign(pl(x), rv) }
fn set(x: usize, n: u128) -> Stmt { asg(x, Rvalue::Use(k(n))) }
fn copy(x: usize, y: usize) -> Stmt { asg(x, Rvalue::Use(cp(y))) }
fn lt(x: usize, a: Operand, b: Operand) -> Stmt { asg(x, Rvalue::Bin(BinOp::Lt, U, a, b)) }
fn gt(x: usize, a: Operand, b: Operand) -> Stmt { asg(x, Rvalue::Bin(BinOp::Gt, U, a, b)) }
fn inc(x: usize) -> Stmt { asg(x, Rvalue::Bin(BinOp::Add, U, cp(x), k(1))) }
fn sw(c: usize, zero: usize, other: usize) -> Term { Term::Switch(cp(c), vec![(0, zero)], other) }
fn intr(i: Intrinsic, args: Vec<Operand>, dst: usize, next: usize) -> Term { Term::Call(Callee::Intr(i), args, pl(dst), next) }
fn call(g: usize, args: Vec<Operand>, dst: usize, next: usize) -> Term { Term::Call(Callee::Fn(g), args, pl(dst), next) }
fn blk(stmts: Vec<Stmt>, term: Term) -> Block { Block { stmts, term } }
fn ret() -> Block { blk(vec![], Term::Return) }

fn usz() -> Ty { Ty::Int(IntTy::Usize) }
fn slice() -> Ty { Ty::Shr(Box::new(Ty::Slice(Box::new(Ty::Int(IntTy::U8))))) }
/// Local 0 is the return place, then the parameters' types, then usizes up to `n` locals.
fn body(nargs: usize, params: Vec<Ty>, n: usize, blocks: Vec<Block>) -> Body {
    let mut locals = vec![Ty::Unit];
    locals.extend(params);
    while locals.len() < n { locals.push(usz()); }
    Body { nargs, locals, blocks }
}

fn v(x: usize) -> Atom { Atom::Val(x, U) }
fn len(x: usize) -> Atom { Atom::Len(x) }
fn gap(a: Atom, b: Atom) -> Atom { Atom::Gap(Box::new(a), Box::new(b)) }
fn m0(n: u64) -> Mono { Mono { coef: n, atoms: vec![] } }
fn m1(n: u64, a: Atom) -> Mono { Mono { coef: n, atoms: vec![a] } }
fn m2(n: u64, a: Atom, b: Atom) -> Mono { Mono { coef: n, atoms: vec![a, b] } }
fn poly(monos: Vec<Mono>) -> Poly { Poly { monos } }
fn konst(n: u64) -> Poly { poly(vec![m0(n)]) }
fn bc(facts: Vec<Fact>, pot: Poly) -> BlockCert { BlockCert { facts, pot } }
fn cert(blocks: Vec<BlockCert>) -> Cert { Cert { blocks } }

fn loop_const() -> Body {
    body(0, vec![], 3, vec![
        blk(vec![set(1, 0)], Term::Goto(1)),
        blk(vec![lt(2, cp(1), k(10))], sw(2, 3, 2)),
        blk(vec![inc(1)], Term::Goto(1)),
        ret(),
    ])
}

fn loop_len() -> Body {
    body(1, vec![slice()], 6, vec![
        blk(vec![], intr(Intrinsic::VecLen, vec![cp(1)], 2, 1)),
        blk(vec![set(3, 0)], Term::Goto(2)),
        blk(vec![lt(5, cp(3), cp(2))], sw(5, 4, 3)),
        blk(vec![inc(3)], Term::Goto(2)),
        ret(),
    ])
}

fn nested() -> Body {
    body(1, vec![slice()], 15, vec![
        /* 0 */ blk(vec![], intr(Intrinsic::VecLen, vec![cp(1)], 2, 1)),
        /* 1 */ blk(vec![set(3, 0)], Term::Goto(2)),
        /* 2 */ blk(vec![copy(4, 3), lt(5, cp(4), cp(2))], sw(5, 9, 3)),
        /* 3 */ blk(vec![], intr(Intrinsic::VecIndex, vec![cp(1), cp(3)], 6, 4)),
        /* 4 */ blk(vec![copy(11, 3), asg(10, Rvalue::Bin(BinOp::Add, U, cp(11), k(1)))], Term::Goto(5)),
        /* 5 */ blk(vec![copy(12, 10), lt(13, cp(12), cp(2))], sw(13, 8, 6)),
        /* 6 */ blk(vec![], intr(Intrinsic::VecIndex, vec![cp(1), cp(10)], 14, 7)),
        /* 7 */ blk(vec![inc(10)], Term::Goto(5)),
        /* 8 */ blk(vec![inc(3)], Term::Goto(2)),
        /* 9 */ ret(),
    ])
}

fn ty_u8() -> Ty { Ty::Int(IntTy::U8) }
fn ty_u64() -> Ty { Ty::Int(IntTy::U64) }
fn ty_b() -> Ty { Ty::Int(IntTy::Bool) }
fn bin(o: BinOp, t: IntTy, x: usize, a: Operand, b: Operand) -> Stmt { asg(x, Rvalue::Bin(o, t, a, b)) }
fn c8(n: u128) -> Operand { Operand::Const(IntTy::U8, n) }
fn tuple_ref() -> Ty { Ty::Shr(Box::new(Ty::Tuple(vec![ty_u64(), ty_u64()]))) }
fn settings_ok_prog() -> Program {
    let (u, b, r, t) = (usz, ty_b, tuple_ref, ty_u64);
    let locals = vec![
        b(), Ty::Shr(Box::new(Ty::Vec(Box::new(Ty::Tuple(vec![t(), t()]))))), u(), u(), b(), u(), b(), t(), r(), u(),
        u(), u(), b(), u(), b(), t(), r(), u(), t(), r(), u(),
    ];
    let fld = |x: usize| Operand::Copy(Place { local: x, proj: vec![Proj::Deref, Proj::Field(0)] });
    let kb = |n: u128| Operand::Const(IntTy::Bool, n);
    let main = Body { nargs: 1, locals, blocks: vec![
        /* 0 */ blk(vec![], intr(Intrinsic::VecLen, vec![cp(1)], 2, 1)),
        /* 1 */ blk(vec![set(3, 0)], Term::Goto(2)),
        /* 2 */ blk(vec![copy(5, 3), lt(4, cp(5), cp(2))], sw(4, 15, 3)),
        /* 3 */ blk(vec![copy(9, 3)], intr(Intrinsic::VecIndex, vec![cp(1), cp(9)], 8, 4)),
        /* 4 */ blk(vec![asg(7, Rvalue::Use(fld(8)))], call(1, vec![cp(7)], 6, 5)),
        /* 5 */ blk(vec![], sw(6, 7, 6)),
        /* 6 */ blk(vec![asg(0, Rvalue::Use(kb(0)))], Term::Goto(16)),
        /* 7 */ blk(vec![copy(11, 3), asg(10, Rvalue::Bin(BinOp::Add, U, cp(11), k(1)))], Term::Goto(8)),
        /* 8 */ blk(vec![copy(13, 10), lt(12, cp(13), cp(2))], sw(12, 14, 9)),
        /* 9 */ blk(vec![copy(17, 10)], intr(Intrinsic::VecIndex, vec![cp(1), cp(17)], 16, 10)),
        /* 10 */ blk(vec![asg(15, Rvalue::Use(fld(16))), copy(20, 3)], intr(Intrinsic::VecIndex, vec![cp(1), cp(20)], 19, 11)),
        /* 11 */ blk(vec![asg(18, Rvalue::Use(fld(19))), asg(14, Rvalue::Bin(BinOp::Eq, IntTy::U64, cp(15), cp(18)))], sw(14, 13, 12)),
        /* 12 */ blk(vec![asg(0, Rvalue::Use(kb(0)))], Term::Goto(16)),
        /* 13 */ blk(vec![inc(10)], Term::Goto(8)),
        /* 14 */ blk(vec![inc(3)], Term::Goto(2)),
        /* 15 */ blk(vec![asg(0, Rvalue::Use(kb(1)))], Term::Goto(17)),
        /* 16 */ blk(vec![], Term::Goto(17)),
        /* 17 */ ret(),
    ] };
    let leaf = Body { nargs: 1, locals: vec![b(), t()], blocks: vec![ret()] };
    Program { fns: vec![main, leaf] }
}
fn prefix_prog() -> Program {
    let (u, b, t, e) = (usz, ty_b, ty_u64, ty_u8);
    let adt = Ty::Adt(vec![vec![], vec![t(), u()], vec![]]);
    let mut l = vec![adt, e(), Ty::Shr(Box::new(Ty::Slice(Box::new(e()))))];
    // _3.. in MIR order
    for ty in [u(), e(), e(), e(), e(), b(), b(), t(), t(), t(), u(), b(), u(), b(), u(), e(), u(), b(), t(), e(), t(), t(), t(), t(), b(), b(), t(), t(), t(), e(), u(), b(), u(), t()] { l.push(ty); }
    assert_eq!(l.len(), 37);
    let k8 = c8;
    let k64 = |n: u128| Operand::Const(IntTy::U64, n);
    let ag = |x: usize, v: usize, a: Vec<Operand>| asg(x, Rvalue::Aggregate(AggKind::Adt(v), a));
    let ca = |x: usize, from: IntTy, to: IntTy, y: usize| asg(x, Rvalue::Cast(from, to, cp(y)));
    let main = Body { nargs: 2, locals: l, blocks: vec![
        /* 0 */ blk(vec![asg(3, Rvalue::Len(pl(2)))], sw(3, 1, 2)),
        /* 1 */ blk(vec![ag(0, 0, vec![])], Term::Goto(23)),
        /* 2 */ blk(vec![bin(BinOp::Sub, IntTy::U8, 5, k8(8), cp(1)), bin(BinOp::Shr, IntTy::U8, 4, k8(255), cp(5)), lt(8, k(0), cp(3))], Term::Assert(cp(8), true, 3)),
        /* 3 */ blk(vec![asg(7, Rvalue::Use(Operand::Copy(Place { local: 2, proj: vec![Proj::Deref, Proj::ConstIndex(0)] }))), bin(BinOp::BitAnd, IntTy::U8, 6, cp(7), cp(4)), bin(BinOp::Lt, IntTy::U8, 9, cp(6), cp(4))], sw(9, 5, 4)),
        /* 4 */ blk(vec![ca(10, IntTy::U8, IntTy::U64, 6), ag(0, 1, vec![cp(10), k(1)])], Term::Goto(22)),
        /* 5 */ blk(vec![ca(11, IntTy::U8, IntTy::U64, 6), asg(12, Rvalue::Use(k64(1))), set(13, 1)], Term::Goto(6)),
        /* 6 */ blk(vec![copy(15, 13), bin(BinOp::Ge, U, 14, cp(15), cp(3))], sw(14, 8, 7)),
        /* 7 */ blk(vec![ag(0, 0, vec![])], Term::Goto(21)),
        /* 8 */ blk(vec![copy(17, 13), gt(16, cp(17), k(10))], sw(16, 10, 9)),
        /* 9 */ blk(vec![ag(0, 2, vec![])], Term::Goto(21)),
        /* 10 */ blk(vec![copy(19, 13), lt(20, cp(19), cp(3))], Term::Assert(cp(20), true, 11)),
        /* 11 */ blk(vec![
            asg(18, Rvalue::Use(Operand::Copy(Place { local: 2, proj: vec![Proj::Deref, Proj::Index(19)] }))),
            bin(BinOp::BitAnd, IntTy::U8, 22, cp(18), k8(127)), ca(21, IntTy::U8, IntTy::U64, 22), copy(25, 11),
            bin(BinOp::Sub, IntTy::U64, 24, k64(4611686018427387903), cp(25)), copy(26, 12), bin(BinOp::Eq, IntTy::U64, 27, cp(26), k64(0)),
        ], Term::Assert(cp(27), false, 12)),
        /* 12 */ blk(vec![bin(BinOp::Div, IntTy::U64, 23, cp(24), cp(26)), bin(BinOp::Gt, IntTy::U64, 28, cp(21), cp(23))], sw(28, 14, 13)),
        /* 13 */ blk(vec![ag(0, 2, vec![])], Term::Goto(20)),
        /* 14 */ blk(vec![copy(29, 11), copy(31, 12), bin(BinOp::Mul, IntTy::U64, 30, cp(21), cp(31)), bin(BinOp::Add, IntTy::U64, 11, cp(29), cp(30)), bin(BinOp::BitAnd, IntTy::U8, 32, cp(18), k8(128))], sw(32, 15, 16)),
        /* 15 */ blk(vec![asg(33, Rvalue::Bin(BinOp::Add, U, cp(13), k(1))), ag(0, 1, vec![cp(11), cp(33)])], Term::Goto(20)),
        /* 16 */ blk(vec![copy(35, 13), lt(34, cp(35), k(10))], sw(34, 18, 17)),
        /* 17 */ blk(vec![copy(36, 12), bin(BinOp::Mul, IntTy::U64, 12, cp(36), k64(128))], Term::Goto(19)),
        /* 18 */ blk(vec![], Term::Goto(19)),
        /* 19 */ blk(vec![inc(13)], Term::Goto(6)),
        /* 20 */ blk(vec![], Term::Goto(21)),
        /* 21 */ blk(vec![], Term::Goto(22)),
        /* 22 */ blk(vec![], Term::Goto(23)),
        /* 23 */ ret(),
    ] };
    Program { fns: vec![main] }
}
fn take_str_prog() -> Program {
    let vec8 = || Ty::Vec(Box::new(ty_u8()));
    let main = Body { nargs: 4, locals: vec![
        vec8(), Ty::Adt(vec![vec![], vec![vec8()]]), slice(), usz(), usz(), Ty::Int(IntTy::Isize), slice(),
    ], blocks: vec![
        /* 0 */ blk(vec![asg(5, Rvalue::Discr(pl(1)))], Term::Switch(cp(5), vec![(0, 2), (1, 3)], 1)),
        /* 1 */ blk(vec![], Term::Abort),
        /* 2 */ blk(vec![], intr(Intrinsic::SliceSubrange, vec![cp(2), cp(3), cp(4)], 6, 4)),
        /* 3 */ blk(vec![asg(0, Rvalue::Use(Operand::Copy(Place { local: 1, proj: vec![Proj::Downcast(1), Proj::Field(0)] })))], Term::Goto(6)),
        /* 4 */ blk(vec![], intr(Intrinsic::SliceToVec, vec![cp(6)], 0, 5)),
        /* 5 */ blk(vec![], Term::Goto(6)),
        /* 6 */ ret(),
    ] };
    Program { fns: vec![main] }
}

// ------------------------------------------------------------------ helpers

/// `analyze`, with every `Some` checked again here against the final summaries.
fn run(p: &Program) -> (Vec<Option<Poly>>, Vec<Cert>, Vec<CostWhy>) {
    let decl: Vec<Option<Vec<bool>>> = p.fns.iter().map(|_| None).collect();
    assert!(check_program(p, &decl).is_ok(), "ill-typed test program");
    let r = analyze(p);
    assert_eq!(r.0.len(), p.fns.len());
    for f in 0..p.fns.len() {
        if r.0[f].is_some() {
            assert!(check_cert(p, f, &r.1[f], &r.0), "fn {f}");
            assert!(matches!(r.2[f], CostWhy::Bounded), "fn {f}: Some, not Bounded");
        } else {
            assert!(!matches!(r.2[f], CostWhy::Bounded), "fn {f}: None, but Bounded");
        }
    }
    r
}

fn show(s: &Option<Poly>) -> String {
    let Some(s) = s else { return "None".to_string() };
    fn atom(a: &Atom) -> String {
        match a {
            Atom::Const(n) => n.to_string(),
            Atom::Val(x, _) => format!("V{x}"),
            Atom::Len(x) => format!("L{x}"),
            Atom::Gap(a, b) => format!("Gap({},{})", atom(a), atom(b)),
        }
    }
    let ms: Vec<String> = s.monos.iter().map(|m| {
        let at: Vec<String> = m.atoms.iter().map(atom).collect();
        format!("{}*[{}]", m.coef, at.join("."))
    }).collect();
    ms.join(" + ")
}

fn coef_of(s: &Poly, want: &Mono) -> Option<u64> {
    s.monos.iter().find(|m| atoms_eq(&m.atoms, &want.atoms)).map(|m| m.coef)
}

/// Each monomial of `s` is in `want`, at no more than `want`'s coefficient.
fn reproduces_or_beats(s: &Option<Poly>, want: Vec<Mono>) {
    let got = s.as_ref().expect("no bound");
    let shown = show(s);
    assert!(!got.monos.is_empty(), "{shown}");
    let want = Poly { monos: want };
    for m in &got.monos {
        assert!(m.atoms.len() <= 2, "{shown}");
        match coef_of(&want, m) {
            Some(c) => assert!(m.coef <= c, "{shown}: over the recipe at {}", m.coef),
            None => panic!("{shown}: a monomial the recipe doesn't have"),
        }
    }
}

/// The exact entry potential.
fn entry_is(s: &Option<Poly>, want: Vec<Mono>) {
    let got = s.as_ref().expect("no bound");
    let shown = show(s);
    assert_eq!(got.monos.len(), want.len(), "{shown}");
    let want = Poly { monos: want };
    for m in &got.monos {
        assert_eq!(coef_of(&want, m), Some(m.coef), "{shown}");
    }
}

// ------------------------------------------------------------------ the real shapes

#[test]
fn infers_real_settings_ok() {
    let r = run(&settings_ok_prog());
    entry_is(&r.0[0], vec![m2(13, len(1), len(1)), m1(40, len(1)), m0(33)]);
    // the recipe's header, and the inner loop's
    let (a, i) = (|| gap(v(2), v(3)), || gap(v(2), v(10)));
    let header = Some(copy_poly(&r.1[0].blocks[2].pot));
    entry_is(&header, vec![m2(13, v(2), a()), m1(27, a()), m1(13, v(2)), m0(30)]);
    let inner = Some(copy_poly(&r.1[0].blocks[8].pot));
    entry_is(&inner, vec![m1(13, i()), m2(13, v(2), a()), m1(27, a()), m0(18)]);
    let inc = Some(copy_poly(&r.1[0].blocks[14].pot));
    entry_is(&inc, vec![m2(13, v(2), a()), m1(27, a()), m0(5)]);
}

#[test]
fn infers_real_parse_prefix_int() {
    let r = run(&prefix_prog());
    reproduces_or_beats(&r.0[0], vec![m1(34, len(2)), m0(55)]);
    assert_eq!(coef_of(r.0[0].as_ref().unwrap(), &m1(0, len(2))), Some(34));
}

#[test]
fn infers_real_take_str() {
    let r = run(&take_str_prog());
    entry_is(&r.0[0], vec![m1(1, len(2)), m0(6)]);
}

/// `parse`: the bound is a call result, known only through `Le(_8, _4)` on the edge out of bb1.
#[test]
fn infers_real_bound_from_le_fact() {
    let leaf = body(0, vec![], 1, vec![ret()]);
    let deref = Place { local: 2, proj: vec![Proj::Deref] };
    let main = body(2, vec![usz(), Ty::Shr(Box::new(slice()))], 16, vec![
        blk(vec![asg(3, Rvalue::Use(Operand::Copy(deref))), asg(4, Rvalue::Len(pl(3)))], call(1, vec![], 8, 1)),
        blk(vec![gt(6, cp(8), cp(4))], sw(6, 2, 5)),
        blk(vec![set(13, 1)], Term::Goto(3)),
        blk(vec![copy(15, 13), lt(14, cp(15), cp(8))], sw(14, 5, 4)),
        blk(vec![inc(13)], Term::Goto(3)),
        ret(),
    ]);
    let r = run(&Program { fns: vec![main, leaf] });
    entry_is(&r.0[1], vec![m0(1)]);
    reproduces_or_beats(&r.0[0], vec![m1(5, len(2)), m0(14)]);
}

// ------------------------------------------------------------------ the plan's list

#[test]
fn infers_counted_const() {
    let r = run(&Program { fns: vec![loop_const()] });
    reproduces_or_beats(&r.0[0], vec![m0(47)]);
}

#[test]
fn infers_counted_len() {
    let r = run(&Program { fns: vec![loop_len()] });
    reproduces_or_beats(&r.0[0], vec![m1(4, len(1)), m0(8)]);
}

#[test]
fn infers_nested_quadratic() {
    let r = run(&Program { fns: vec![nested()] });
    let got = r.0[0].as_ref().unwrap();
    assert_eq!(coef_of(got, &m2(0, len(1), len(1))), Some(6), "{}", show(&r.0[0]));
    assert!(coef_of(got, &m1(0, len(1))).is_some(), "{}", show(&r.0[0]));
}

fn mid_body(exit_stmts: usize) -> Body {
    let exit: Vec<Stmt> = (0..exit_stmts).map(|_| set(16, 0)).collect();
    body(2, vec![usz(), slice()], 17, vec![
        /* 0 */ blk(vec![], intr(Intrinsic::VecLen, vec![cp(2)], 3, 1)),
        /* 1 */ blk(vec![set(13, 1)], Term::Goto(2)),
        /* 2 */ blk(vec![copy(15, 13), lt(14, cp(15), cp(3))], sw(14, 6, 3)),
        /* 3 */ blk(vec![gt(16, cp(13), k(9))], sw(16, 4, 7)),
        /* 4 */ blk(vec![], Term::Goto(5)),
        /* 5 */ blk(vec![inc(13)], Term::Goto(2)),
        /* 6 */ ret(),
        /* 7 */ blk(exit, Term::Goto(6)),
    ])
}

#[test]
fn infers_mid_body_exit() {
    let r = run(&Program { fns: vec![mid_body(0)] });
    reproduces_or_beats(&r.0[0], vec![m1(8, len(2)), m0(12)]);
}

/// An exit dearer than the loop's own path can't sit in the header's cheap form, and must not raise `P`.
#[test]
fn infers_mid_body_exit_dearer_than_the_path() {
    let r = run(&Program { fns: vec![mid_body(100)] });
    let got = r.0[0].as_ref().unwrap();
    assert_eq!(coef_of(got, &m1(0, len(2))), Some(8), "{}", show(&r.0[0]));
}

#[test]
fn infers_counter_from_one() {
    let b = body(1, vec![slice()], 6, vec![
        blk(vec![], intr(Intrinsic::VecLen, vec![cp(1)], 2, 1)),
        blk(vec![set(3, 1)], Term::Goto(2)),
        blk(vec![lt(5, cp(3), cp(2))], sw(5, 4, 3)),
        blk(vec![inc(3)], Term::Goto(2)),
        ret(),
    ]);
    let r = run(&Program { fns: vec![b] });
    reproduces_or_beats(&r.0[0], vec![m1(4, len(1)), m0(8)]);
}

#[test]
fn infers_call_chain() {
    let deref = Place { local: 2, proj: vec![Proj::Deref] };
    let callee = body(2, vec![usz(), Ty::Shr(Box::new(slice()))], 8, vec![
        blk(vec![asg(3, Rvalue::Use(Operand::Copy(deref))), asg(4, Rvalue::Len(pl(3))), set(5, 0)], Term::Goto(1)),
        blk(vec![lt(7, cp(5), cp(4))], sw(7, 3, 2)),
        blk(vec![inc(5)], Term::Goto(1)),
        ret(),
    ]);
    let main = body(1, vec![slice()], 4, vec![
        blk(vec![asg(3, Rvalue::RefShr(pl(1)))], call(2, vec![k(0), cp(3)], 2, 1)),
        ret(),
    ]);
    let top = body(1, vec![slice()], 3, vec![
        blk(vec![], call(0, vec![cp(1)], 2, 1)),
        blk(vec![], call(0, vec![cp(1)], 2, 2)),
        ret(),
    ]);
    // callers before callees in the vector: the order comes from `callee_order`
    let r = run(&Program { fns: vec![main, top, callee] });
    assert_eq!(coef_of(r.0[2].as_ref().unwrap(), &m1(0, len(2))), Some(4), "{}", show(&r.0[2]));
    assert_eq!(coef_of(r.0[0].as_ref().unwrap(), &m1(0, len(1))), Some(4), "{}", show(&r.0[0]));
    assert_eq!(coef_of(r.0[1].as_ref().unwrap(), &m1(0, len(1))), Some(8), "{}", show(&r.0[1]));
}

fn off_progress() -> Body {
    body(2, vec![usz(), usz()], 6, vec![
        blk(vec![set(3, 0)], Term::Goto(1)),
        blk(vec![lt(4, cp(3), cp(1))], sw(4, 3, 2)),
        blk(vec![asg(3, Rvalue::Bin(BinOp::Add, U, cp(3), cp(2)))], Term::Goto(1)),
        ret(),
    ])
}

#[test]
fn none_for_off_progress_loop() {
    let r = run(&Program { fns: vec![off_progress()] });
    assert!(r.0[0].is_none());
    assert!(matches!(r.2[0], CostWhy::NotCounted(1)));
}

#[test]
fn none_for_a_caller_of_none() {
    let caller = body(2, vec![usz(), usz()], 4, vec![blk(vec![], call(0, vec![cp(1), cp(2)], 3, 1)), ret()]);
    let r = run(&Program { fns: vec![off_progress(), caller] });
    assert!(r.0[1].is_none());
    assert!(matches!(r.2[1], CostWhy::CalleeNone(0)));
}

#[test]
fn none_for_recursion() {
    let f = body(0, vec![], 2, vec![blk(vec![], call(0, vec![], 1, 1)), ret()]);
    let p = Program { fns: vec![f] };
    let r = analyze(&p);
    assert!(r.0[0].is_none());
    assert!(matches!(r.2[0], CostWhy::Recursion));
}

#[test]
fn none_for_unknown_bound() {
    let leaf = body(0, vec![], 2, vec![ret()]);
    let main = body(0, vec![], 6, vec![
        blk(vec![], call(1, vec![], 2, 1)),
        blk(vec![set(3, 0)], Term::Goto(2)),
        blk(vec![lt(4, cp(3), cp(2))], sw(4, 4, 3)),
        blk(vec![inc(3)], Term::Goto(2)),
        ret(),
    ]);
    let r = run(&Program { fns: vec![main, leaf] });
    assert!(r.0[1].is_some());
    assert!(r.0[0].is_none());
    assert!(matches!(r.2[0], CostWhy::Validator(0)));
}

#[test]
fn none_for_not_wf() {
    let p = Program { fns: vec![body(0, vec![], 1, vec![blk(vec![], Term::Goto(99))])] };
    let r = analyze(&p);
    assert!(r.0[0].is_none());
    assert!(matches!(r.2[0], CostWhy::NotWf));
}

/// A writer in the body leaves no counter: `VecPush` on a `&mut`.
#[test]
fn none_for_writer_in_the_loop() {
    let mv = Ty::Mut(Box::new(Ty::Vec(Box::new(Ty::Int(IntTy::U8)))));
    let b = body(2, vec![mv, usz()], 6, vec![
        blk(vec![set(3, 0)], Term::Goto(1)),
        blk(vec![lt(4, cp(3), cp(2))], sw(4, 4, 2)),
        blk(vec![], intr(Intrinsic::VecPush, vec![cp(1), Operand::Const(IntTy::U8, 0)], 5, 3)),
        blk(vec![inc(3)], Term::Goto(1)),
        ret(),
    ]);
    let r = run(&Program { fns: vec![b] });
    assert!(r.0[0].is_none());
    assert!(matches!(r.2[0], CostWhy::NotCounted(1) | CostWhy::Validator(_)));
}

#[test]
fn none_for_degree_three() {
    // for i < n { for j < n { for l < n {} } }
    let b = body(1, vec![usz()], 9, vec![
        /* 0 */ blk(vec![set(2, 0)], Term::Goto(1)),
        /* 1 */ blk(vec![lt(5, cp(2), cp(1))], sw(5, 9, 2)),
        /* 2 */ blk(vec![set(3, 0)], Term::Goto(3)),
        /* 3 */ blk(vec![lt(6, cp(3), cp(1))], sw(6, 8, 4)),
        /* 4 */ blk(vec![set(4, 0)], Term::Goto(5)),
        /* 5 */ blk(vec![lt(7, cp(4), cp(1))], sw(7, 7, 6)),
        /* 6 */ blk(vec![inc(4)], Term::Goto(5)),
        /* 7 */ blk(vec![inc(3)], Term::Goto(3)),
        /* 8 */ blk(vec![inc(2)], Term::Goto(1)),
        /* 9 */ ret(),
    ]);
    let r = run(&Program { fns: vec![b] });
    assert!(r.0[0].is_none());
    assert!(matches!(r.2[0], CostWhy::DegreeCap), "{}", show(&r.0[0]));
}

#[test]
fn none_for_coefficient_overflow() {
    // nothing here reads the callee's frame: its potential is all constant, the sum of two doesn't fit
    let leaf = body(0, vec![], 1, vec![blk(vec![], Term::Return)]);
    let main = body(0, vec![], 2, vec![
        blk(vec![], call(1, vec![], 1, 1)),
        blk(vec![], call(1, vec![], 1, 2)),
        ret(),
    ]);
    let p = Program { fns: vec![main, leaf] };
    let cert_ok = build_cert(&p, 0, &vec![None, Some(konst(u64::MAX))]);
    assert!(matches!(cert_ok, Err(CostWhy::Overflow)));
}

#[test]
fn revalidation_drops_dependent_caller() {
    let callee = body(1, vec![slice()], 2, vec![blk(vec![], intr(Intrinsic::SliceToVec, vec![cp(1)], 0, 1)), ret()]);
    let main = body(1, vec![slice()], 3, vec![blk(vec![], call(1, vec![cp(1)], 2, 1)), ret()]);
    let p = Program { fns: vec![main, callee] };
    // the callee's is one lower than valid, the caller's valid against the callee's summary
    let cc = cert(vec![bc(vec![], poly(vec![m1(1, len(1)), m0(1)])), bc(vec![], konst(1))]);
    let mc = cert(vec![bc(vec![], poly(vec![m1(1, len(1)), m0(3)])), bc(vec![], konst(1))]);
    let sums = || vec![Some(copy_poly(&mc.blocks[0].pot)), Some(copy_poly(&cc.blocks[0].pot))];
    assert!(check_cert(&p, 0, &mc, &sums()));
    assert!(!check_cert(&p, 1, &cc, &sums()));
    let certs = vec![copy_cert(&mc), copy_cert(&cc)];
    let r = revalidate(&p, &certs, sums());
    assert!(r[0].is_none());
    assert!(r[1].is_none());
    // and with the callee's one higher, both stand
    let cc2 = cert(vec![bc(vec![], poly(vec![m1(1, len(1)), m0(2)])), bc(vec![], konst(1))]);
    let mc2 = cert(vec![bc(vec![], poly(vec![m1(1, len(1)), m0(4)])), bc(vec![], konst(1))]);
    let s2 = vec![Some(copy_poly(&mc2.blocks[0].pot)), Some(copy_poly(&cc2.blocks[0].pot))];
    let r = revalidate(&p, &vec![mc2, cc2], s2);
    assert!(r[0].is_some() && r[1].is_some());
}

fn copy_poly(p: &Poly) -> Poly { ctcore::cost_check::poly_copy(p) }
fn copy_cert(ct: &Cert) -> Cert {
    cert(ct.blocks.iter().map(|b| bc(b.facts.iter().map(ctcore::cost_check::fact_copy).collect(), copy_poly(&b.pot))).collect())
}

// ------------------------------------------------------------------ graphs and loops

#[test]
fn dominators_and_back_edges() {
    let b = nested();
    let dom = dominators(&b);
    assert!(dom[3][2] && dom[8][5] && dom[9][2] && dom[9][0]);
    assert!(!dom[2][3] && !dom[9][3] && !dom[8][7]);
    let mut be = back_edges(&b, &dom);
    be.sort();
    assert_eq!(be, vec![(7, 5), (8, 2)]);
    let inner = natural_loop(&b, 7, 5);
    let outer = natural_loop(&b, 8, 2);
    let set = |lp: &Vec<bool>| (0..10).filter(|i| lp[*i]).collect::<Vec<usize>>();
    assert_eq!(set(&inner), vec![5, 6, 7]);
    assert_eq!(set(&outer), vec![2, 3, 4, 5, 6, 7, 8]);
}

#[test]
fn unreachable_blocks_have_no_back_edges() {
    let b = body(0, vec![], 2, vec![ret(), blk(vec![], Term::Goto(2)), blk(vec![], Term::Goto(1))]);
    let dom = dominators(&b);
    assert!(back_edges(&b, &dom).is_empty());
}

#[test]
fn recognize_real_loops() {
    let b = nested();
    let c = recognize(&b, &natural_loop(&b, 8, 2), 2).unwrap();
    assert_eq!((c.header, c.counter, c.test_block, c.inc_block), (2, 3, 2, 8));
    assert!(matches!(c.bound, Atom::Val(2, IntTy::Usize)) && matches!(c.ty, IntTy::Usize));
    let c = recognize(&b, &natural_loop(&b, 7, 5), 5).unwrap();
    assert_eq!((c.header, c.counter, c.test_block, c.inc_block), (5, 10, 5, 7));
    let p = prefix_prog();
    let main = &p.fns[0];
    let c = recognize(main, &natural_loop(main, 19, 6), 6).unwrap();
    assert_eq!((c.header, c.counter, c.test_block, c.inc_block), (6, 13, 6, 19));
    assert!(matches!(c.bound, Atom::Val(3, IntTy::Usize)));
    let c = recognize(&loop_const(), &natural_loop(&loop_const(), 2, 1), 1).unwrap();
    assert!(matches!(c.bound, Atom::Const(10)));
    assert!(recognize(&off_progress(), &natural_loop(&off_progress(), 2, 1), 1).is_none());
}

#[test]
fn recognize_rejects_a_signed_counter_and_a_bound_written_in_the_loop() {
    let i = IntTy::I64;
    let signed = body(0, vec![Ty::Int(IntTy::I64)], 3, vec![
        blk(vec![asg(1, Rvalue::Use(Operand::Const(i64_ty(), 0)))], Term::Goto(1)),
        blk(vec![asg(2, Rvalue::Bin(BinOp::Lt, i64_ty(), Operand::Copy(pl(1)), Operand::Const(i64_ty(), 10)))], sw(2, 3, 2)),
        blk(vec![asg(1, Rvalue::Bin(BinOp::Add, i, cp(1), Operand::Const(i64_ty(), 1)))], Term::Goto(1)),
        ret(),
    ]);
    assert!(recognize(&signed, &natural_loop(&signed, 2, 1), 1).is_none());
    let moving = body(1, vec![usz()], 4, vec![
        blk(vec![set(2, 0)], Term::Goto(1)),
        blk(vec![lt(3, cp(2), cp(1))], sw(3, 3, 2)),
        blk(vec![inc(2), set(1, 9)], Term::Goto(1)),
        ret(),
    ]);
    assert!(recognize(&moving, &natural_loop(&moving, 2, 1), 1).is_none());
}
fn i64_ty() -> IntTy { IntTy::I64 }

/// A path round the loop that skips the increment isn't counted, though the increment dominates nothing wrong.
#[test]
fn recognize_rejects_a_path_without_the_increment() {
    let b = body(1, vec![usz()], 6, vec![
        blk(vec![set(2, 0)], Term::Goto(1)),
        blk(vec![lt(3, cp(2), cp(1))], sw(3, 5, 2)),
        blk(vec![copy(4, 2), gt(5, cp(4), k(3))], sw(5, 3, 4)),
        blk(vec![inc(2)], Term::Goto(1)),
        blk(vec![], Term::Goto(1)),
        ret(),
    ]);
    let mut lp = natural_loop(&b, 3, 1);
    let other = natural_loop(&b, 4, 1);
    for i in 0..lp.len() { lp[i] = lp[i] || other[i]; }
    assert!(recognize(&b, &lp, 1).is_none());
    let r = run(&Program { fns: vec![b] });
    assert!(matches!(r.2[0], CostWhy::NotCounted(1)));
}
