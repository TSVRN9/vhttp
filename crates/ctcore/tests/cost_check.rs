use ctcore::cost::*;
use ctcore::cost_check::check_cost_block;
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
fn c(n: u64) -> Atom { Atom::Const(n) }
fn gap(a: Atom, b: Atom) -> Atom { Atom::Gap(Box::new(a), Box::new(b)) }
fn m0(n: u64) -> Mono { Mono { coef: n, atoms: vec![] } }
fn m1(n: u64, a: Atom) -> Mono { Mono { coef: n, atoms: vec![a] } }
fn m2(n: u64, a: Atom, b: Atom) -> Mono { Mono { coef: n, atoms: vec![a, b] } }
fn poly(monos: Vec<Mono>) -> Poly { Poly { monos } }
fn konst(n: u64) -> Poly { poly(vec![m0(n)]) }
fn f_lt(a: Atom, b: Atom) -> Fact { Fact::Lt(a, b) }
fn f_le(a: Atom, b: Atom) -> Fact { Fact::Le(a, b) }
fn bc(facts: Vec<Fact>, pot: Poly) -> BlockCert { BlockCert { facts, pot } }
fn cert(blocks: Vec<BlockCert>) -> Cert { Cert { blocks } }

/// The first block's potential, rebuilt: `Poly` derives nothing.
fn pot0(ct: &Cert) -> Poly { copy_poly(&ct.blocks[0].pot) }
fn copy_atom(a: &Atom) -> Atom { ctcore::cost_check::atom_copy(a) }
fn copy_poly(p: &Poly) -> Poly {
    poly(p.monos.iter().map(|m| Mono { coef: m.coef, atoms: m.atoms.iter().map(copy_atom).collect() }).collect())
}

/// Every fn of `p` checks against its own certificate's entry potential.
fn all_ok(p: &Program, certs: &[Cert]) -> bool {
    // `theorem_cost` speaks only of typed programs: an ill-typed one would prove nothing here
    let decl: Vec<Option<Vec<bool>>> = p.fns.iter().map(|_| None).collect();
    assert!(check_program(p, &decl).is_ok(), "ill-typed test program");
    let sums: Vec<Option<Poly>> = certs.iter().map(|ct| Some(pot0(ct))).collect();
    (0..certs.len()).all(|f| check_cert(p, f, &certs[f], &sums))
}
fn one_ok(b: Body, ct: Cert) -> bool { all_ok(&Program { fns: vec![b] }, &[ct]) }

fn copy_cert(ct: &Cert) -> Cert {
    cert(ct.blocks.iter().map(|b| bc(b.facts.iter().map(ctcore::cost_check::fact_copy).collect(), copy_poly(&b.pot))).collect())
}
/// Accepted, and no single coefficient can drop by one. A loose but self-consistent certificate still passes.
fn assert_tight(p: &Program, certs: &[Cert]) {
    assert!(all_ok(p, certs));
    for f in 0..certs.len() {
        for b in 0..certs[f].blocks.len() {
            for m in 0..certs[f].blocks[b].pot.monos.len() {
                if certs[f].blocks[b].pot.monos[m].coef == 0 { continue; }
                let mut cs: Vec<Cert> = certs.iter().map(copy_cert).collect();
                cs[f].blocks[b].pot.monos[m].coef -= 1;
                assert!(!all_ok(p, &cs), "fn {f} bb{b} mono{m} can drop by one");
            }
        }
    }
}
fn one_tight(b: Body, ct: Cert) { assert_tight(&Program { fns: vec![b] }, &[ct]) }

// ------------------------------------------------------------------ straight lines and counted loops

#[test]
fn accepts_straight_line_const() {
    let b = body(0, vec![], 2, vec![blk(vec![set(1, 1), set(1, 2)], Term::Goto(1)), ret()]);
    one_tight(b, cert(vec![bc(vec![], konst(4)), bc(vec![], konst(1))]));
}

fn loop_const() -> Body {
    body(0, vec![], 3, vec![
        blk(vec![set(1, 0)], Term::Goto(1)),
        blk(vec![lt(2, cp(1), k(10))], sw(2, 3, 2)),
        blk(vec![inc(1)], Term::Goto(1)),
        ret(),
    ])
}

#[test]
fn accepts_counted_loop_const_bound() {
    let g = || gap(c(10), v(1));
    let ct = cert(vec![
        bc(vec![], konst(45)),
        bc(vec![], poly(vec![m1(4, g()), m0(3)])),
        bc(vec![f_lt(v(1), c(10))], poly(vec![m1(4, g()), m0(1)])),
        bc(vec![], konst(1)),
    ]);
    one_tight(loop_const(), ct);
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

/// `4·Gap(2, 3)` over the loop; `entry` is the constant at the entry, `body_c` the increment block's.
fn loop_len_cert(entry: u64, body_c: u64, body_facts: Vec<Fact>) -> Cert {
    let g = || gap(v(2), v(3));
    cert(vec![
        bc(vec![], poly(vec![m1(4, len(1)), m0(entry)])),
        bc(vec![], poly(vec![m1(4, v(2)), m0(5)])),
        bc(vec![], poly(vec![m1(4, g()), m0(3)])),
        bc(body_facts, poly(vec![m1(4, g()), m0(body_c)])),
        bc(vec![], konst(1)),
    ])
}

#[test]
fn accepts_counted_loop_len_bound() {
    one_tight(loop_len(), loop_len_cert(6, 1, vec![f_lt(v(3), v(2))]));
}

#[test]
fn rejects_pot_too_small_by_one() {
    assert!(!one_ok(loop_len(), loop_len_cert(5, 1, vec![f_lt(v(3), v(2))])));
    assert!(!one_ok(loop_len(), loop_len_cert(6, 0, vec![f_lt(v(3), v(2))])));
}

#[test]
fn rejects_missing_lt_fact() {
    assert!(!one_ok(loop_len(), loop_len_cert(6, 1, vec![])));
}

/// `_3 < _1` says nothing of `Gap(_2, _3)`: the increment finds an `Lt`, but on another bound.
#[test]
fn rejects_lt_on_another_bound() {
    let b = body(2, vec![usz(), usz()], 5, vec![
        blk(vec![set(3, 0)], Term::Goto(1)),
        blk(vec![lt(4, cp(3), cp(1))], sw(4, 3, 2)),
        blk(vec![inc(3)], Term::Goto(1)),
        ret(),
    ]);
    let g = || gap(v(2), v(3));
    let ct = cert(vec![
        bc(vec![], poly(vec![m1(4, v(2)), m0(5)])),
        bc(vec![], poly(vec![m1(4, g()), m0(3)])),
        bc(vec![f_lt(v(3), v(1))], poly(vec![m1(4, g()), m0(1)])),
        bc(vec![], konst(1)),
    ]);
    assert!(!one_ok(b, ct));
}

#[test]
fn rejects_wrong_successor_facts() {
    assert!(!one_ok(loop_len(), loop_len_cert(6, 1, vec![f_lt(v(3), v(2)), f_lt(v(2), v(3))])));
}

// ------------------------------------------------------------------ the real shapes

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

fn nested_cert(entry_c: u64) -> Cert {
    let a = || gap(v(2), v(3));
    let i = || gap(v(2), v(10));
    let outer = || f_lt(v(3), v(2));
    let inner = || f_lt(v(10), v(2));
    let rest = |extra: Vec<Mono>| {
        let mut ms = vec![m2(6, v(2), a()), m1(12, a())];
        ms.extend(extra);
        poly(ms)
    };
    cert(vec![
        bc(vec![], poly(vec![m2(6, len(1), len(1)), m1(18, len(1)), m0(entry_c)])),
        bc(vec![], poly(vec![m2(6, v(2), v(2)), m1(18, v(2)), m0(18)])),
        bc(vec![], rest(vec![m1(6, v(2)), m0(16)])),
        bc(vec![outer()], rest(vec![m1(6, v(2)), m0(13)])),
        bc(vec![outer()], rest(vec![m1(6, v(2)), m0(12)])),
        bc(vec![outer()], rest(vec![m1(6, i()), m0(9)])),
        bc(vec![outer(), inner()], rest(vec![m1(6, i()), m0(6)])),
        bc(vec![outer(), inner()], rest(vec![m1(6, i()), m0(5)])),
        bc(vec![outer()], rest(vec![m0(6)])),
        bc(vec![], konst(1)),
    ])
}

#[test]
fn accepts_nested_quadratic() {
    one_tight(nested(), nested_cert(19));
    assert!(!one_ok(nested(), nested_cert(18)));
}

#[test]
fn accepts_bound_from_le_fact() {
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
    let g = || gap(v(8), v(13));
    let ct = cert(vec![
        bc(vec![], poly(vec![m1(5, len(2)), m0(12)])),
        bc(vec![], poly(vec![m1(5, v(4)), m0(8)])),
        bc(vec![f_le(v(8), v(4))], poly(vec![m1(5, v(4)), m0(6)])),
        bc(vec![], poly(vec![m1(5, g()), m0(4)])),
        bc(vec![f_lt(v(13), v(8))], poly(vec![m1(5, g()), m0(1)])),
        bc(vec![], konst(1)),
    ]);
    assert_tight(&Program { fns: vec![main, leaf] }, &[ct, cert(vec![bc(vec![], konst(1))])]);
}

#[test]
fn accepts_mid_body_exit() {
    let b = body(2, vec![usz(), slice()], 17, vec![
        /* 0 */ blk(vec![], intr(Intrinsic::VecLen, vec![cp(2)], 3, 1)),
        /* 1 */ blk(vec![set(13, 1)], Term::Goto(2)),
        /* 2 */ blk(vec![copy(15, 13), lt(14, cp(15), cp(3))], sw(14, 6, 3)),
        /* 3 */ blk(vec![gt(16, cp(13), k(9))], sw(16, 4, 6)),
        /* 4 */ blk(vec![], Term::Goto(5)),
        /* 5 */ blk(vec![inc(13)], Term::Goto(2)),
        /* 6 */ ret(),
    ]);
    let g = || gap(v(3), v(13));
    let f = || vec![f_lt(v(13), v(3))];
    let ct = cert(vec![
        bc(vec![], poly(vec![m1(8, len(2)), m0(9)])),
        bc(vec![], poly(vec![m1(8, v(3)), m0(8)])),
        bc(vec![], poly(vec![m1(8, g()), m0(6)])),
        bc(f(), poly(vec![m1(8, g()), m0(3)])),
        bc(f(), poly(vec![m1(8, g()), m0(1)])),
        bc(f(), poly(vec![m1(8, g()), m0(0)])),
        bc(vec![], konst(1)),
    ]);
    one_tight(b, ct);
}

#[test]
fn accepts_len_cost_intrinsic() {
    let b = body(1, vec![slice()], 13, vec![
        blk(vec![], intr(Intrinsic::SliceSubrange, vec![cp(1), k(0), k(4)], 12, 1)),
        blk(vec![], intr(Intrinsic::SliceToVec, vec![cp(12)], 0, 2)),
        ret(),
    ]);
    let ct = cert(vec![
        bc(vec![], poly(vec![m1(1, len(1)), m0(3)])),
        bc(vec![], poly(vec![m1(1, len(12)), m0(2)])),
        bc(vec![], konst(1)),
    ]);
    one_tight(b, ct);
}

fn len_callee() -> (Body, Cert) { len_callee_of(slice()) }
fn len_callee_of(param: Ty) -> (Body, Cert) {
    let b = body(1, vec![param], 2, vec![blk(vec![], intr(Intrinsic::SliceToVec, vec![cp(1)], 0, 1)), ret()]);
    (b, cert(vec![bc(vec![], poly(vec![m1(1, len(1)), m0(2)])), bc(vec![], konst(1))]))
}

#[test]
fn accepts_arg_is_dst() {
    let main = body(1, vec![slice()], 4, vec![
        blk(vec![asg(3, Rvalue::RefShr(pl(1)))], call(1, vec![cp(3)], 3, 1)),
        ret(),
    ]);
    let (g, gc) = len_callee();
    let ct = cert(vec![bc(vec![], poly(vec![m1(1, len(1)), m0(5)])), bc(vec![], konst(1))]);
    assert_tight(&Program { fns: vec![main, g] }, &[ct, gc]);
}

#[test]
fn accepts_call_with_summary() {
    let main = body(1, vec![slice()], 3, vec![
        blk(vec![], call(1, vec![cp(1)], 2, 1)),
        blk(vec![], call(1, vec![cp(1)], 2, 2)),
        ret(),
    ]);
    let (g, gc) = len_callee();
    let ct = cert(vec![
        bc(vec![], poly(vec![m1(2, len(1)), m0(7)])),
        bc(vec![], poly(vec![m1(1, len(1)), m0(4)])),
        bc(vec![], konst(1)),
    ]);
    assert_tight(&Program { fns: vec![main, g] }, &[ct, gc]);
}

#[test]
fn accepts_double_ref_len() {
    let deref = Place { local: 2, proj: vec![Proj::Deref] };
    let callee = body(2, vec![usz(), Ty::Shr(Box::new(slice()))], 8, vec![
        blk(vec![asg(3, Rvalue::Use(Operand::Copy(deref))), asg(4, Rvalue::Len(pl(3))), set(5, 0)], Term::Goto(1)),
        blk(vec![lt(7, cp(5), cp(4))], sw(7, 3, 2)),
        blk(vec![inc(5)], Term::Goto(1)),
        ret(),
    ]);
    let g = || gap(v(4), v(5));
    let cc = cert(vec![
        bc(vec![], poly(vec![m1(4, len(2)), m0(7)])),
        bc(vec![], poly(vec![m1(4, g()), m0(3)])),
        bc(vec![f_lt(v(5), v(4))], poly(vec![m1(4, g()), m0(1)])),
        bc(vec![], konst(1)),
    ]);
    let main = body(1, vec![slice()], 4, vec![
        blk(vec![asg(3, Rvalue::RefShr(pl(1)))], call(1, vec![k(0), cp(3)], 2, 1)),
        ret(),
    ]);
    let ct = cert(vec![bc(vec![], poly(vec![m1(4, len(1)), m0(10)])), bc(vec![], konst(1))]);
    assert_tight(&Program { fns: vec![main, callee] }, &[ct, cc]);
}

/// `Val(4)·Len(1)` pulls to `Len(2)·Len(1)`, which must sort. Not `assert_tight`: nothing reads the
/// return block's monomial, which exists only to be pulled, so only the entry's coefficients are tight.
#[test]
fn accepts_images_sort() {
    let b = || body(2, vec![slice(), slice()], 6, vec![
        blk(vec![asg(4, Rvalue::Len(pl(2)))], Term::Goto(1)),
        ret(),
    ]);
    let ct = |q: u64, n: u64| cert(vec![
        bc(vec![], poly(vec![m2(q, len(1), len(2)), m0(n)])),
        bc(vec![], poly(vec![m2(1, v(4), len(1)), m0(1)])),
    ]);
    assert!(one_ok(b(), ct(1, 3)));
    assert!(!one_ok(b(), ct(0, 3)));
    assert!(!one_ok(b(), ct(1, 2)));
}

// ------------------------------------------------------------------ real MIR, block for block

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
fn settings_ok_cert(entry: u64) -> Cert {
    let a = || gap(v(2), v(3));
    let i = || gap(v(2), v(10));
    let outer = || f_lt(v(3), v(2));
    let inner = || f_lt(v(10), v(2));
    let mid = |extra: Vec<Mono>| { let mut ms = vec![m2(13, v(2), a()), m1(17, a())]; ms.extend(extra); poly(ms) };
    cert(vec![
        /* 0 */ bc(vec![], poly(vec![m2(13, len(1), len(1)), m1(30, len(1)), m0(entry)])),
        /* 1 */ bc(vec![], poly(vec![m2(13, v(2), v(2)), m1(30, v(2)), m0(29)])),
        /* 2 */ bc(vec![], mid(vec![m1(13, v(2)), m0(27)])),
        /* 3 */ bc(vec![outer()], mid(vec![m1(13, v(2)), m0(24)])),
        /* 4 */ bc(vec![outer()], mid(vec![m1(13, v(2)), m0(22)])),
        /* 5 */ bc(vec![outer()], mid(vec![m1(13, v(2)), m0(19)])),
        /* 6 */ bc(vec![], konst(4)),
        /* 7 */ bc(vec![outer()], mid(vec![m1(13, v(2)), m0(18)])),
        /* 8 */ bc(vec![outer()], mid(vec![m1(13, i()), m0(15)])),
        /* 9 */ bc(vec![outer(), inner()], mid(vec![m1(13, i()), m0(12)])),
        /* 10 */ bc(vec![outer(), inner()], mid(vec![m1(13, i()), m0(10)])),
        /* 11 */ bc(vec![outer(), inner()], mid(vec![m1(13, i()), m0(7)])),
        /* 12 */ bc(vec![], konst(4)),
        /* 13 */ bc(vec![outer(), inner()], mid(vec![m1(13, i()), m0(4)])),
        /* 14 */ bc(vec![outer()], mid(vec![m0(12)])),
        /* 15 */ bc(vec![], konst(3)),
        /* 16 */ bc(vec![], konst(2)),
        /* 17 */ bc(vec![], konst(1)),
    ])
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
fn prefix_cert(entry: u64) -> Cert {
    let g = || gap(v(3), v(13));
    let f = || vec![f_lt(v(13), v(3))];
    let lp = |n: u64| poly(vec![m1(34, g()), m0(n)]);
    cert(vec![
        /* 0 */ bc(vec![], poly(vec![m1(34, len(2)), m0(entry)])),
        /* 1 */ bc(vec![], konst(3)),
        /* 2 */ bc(vec![], poly(vec![m1(34, v(3)), m0(45)])),
        /* 3 */ bc(vec![], poly(vec![m1(34, v(3)), m0(41)])),
        /* 4 */ bc(vec![], konst(5)),
        /* 5 */ bc(vec![], poly(vec![m1(34, v(3)), m0(37)])),
        /* 6 */ bc(vec![], lp(33)),
        /* 7 */ bc(vec![], konst(5)),
        /* 8 */ bc(f(), lp(30)),
        /* 9 */ bc(vec![], konst(5)),
        /* 10 */ bc(f(), lp(27)),
        /* 11 */ bc(f(), lp(24)),
        /* 12 */ bc(f(), lp(16)),
        /* 13 */ bc(vec![], konst(6)),
        /* 14 */ bc(f(), lp(13)),
        /* 15 */ bc(vec![], konst(7)),
        /* 16 */ bc(f(), lp(7)),
        /* 17 */ bc(f(), lp(4)),
        /* 18 */ bc(f(), lp(2)),
        /* 19 */ bc(f(), lp(1)),
        /* 20 */ bc(vec![], konst(4)),
        /* 21 */ bc(vec![], konst(3)),
        /* 22 */ bc(vec![], konst(2)),
        /* 23 */ bc(vec![], konst(1)),
    ])
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
fn take_str_cert(entry: u64) -> Cert {
    cert(vec![
        bc(vec![], poly(vec![m1(1, len(2)), m0(entry)])),
        bc(vec![], poly(vec![])),
        bc(vec![], poly(vec![m1(1, len(2)), m0(4)])),
        bc(vec![], konst(3)),
        bc(vec![], poly(vec![m1(1, len(6)), m0(3)])),
        bc(vec![], konst(2)),
        bc(vec![], konst(1)),
    ])
}

fn leaf_cert() -> Cert { cert(vec![bc(vec![], konst(1))]) }

#[test]
fn accepts_real_settings_ok() {
    let p = settings_ok_prog();
    assert_tight(&p, &[settings_ok_cert(30), leaf_cert()]);
}

#[test]
fn accepts_real_parse_prefix_int() {
    assert_tight(&prefix_prog(), &[prefix_cert(47)]);
}

#[test]
fn accepts_real_take_str() {
    assert_tight(&take_str_prog(), &[take_str_cert(6)]);
}

// ------------------------------------------------------------------ rejections

#[test]
fn rejects_unknown_atom_in_rhs() {
    let leaf = body(0, vec![], 1, vec![ret()]);
    let main = body(0, vec![], 9, vec![blk(vec![], call(1, vec![], 8, 1)), ret()]);
    let ct = cert(vec![bc(vec![], poly(vec![m1(1, v(8)), m0(100)])), bc(vec![], poly(vec![m1(1, v(8)), m0(1)]))]);
    assert!(!all_ok(&Program { fns: vec![main, leaf] }, &[ct, cert(vec![bc(vec![], konst(1))])]));
}

#[test]
fn rejects_entry_facts_nonempty() {
    let b = body(0, vec![], 2, vec![blk(vec![], Term::Goto(1)), ret()]);
    let ct = cert(vec![bc(vec![f_le(c(0), c(1))], konst(2)), bc(vec![], konst(1))]);
    assert!(!one_ok(b, ct));
}

#[test]
fn rejects_summary_mismatch() {
    let b = || body(0, vec![], 1, vec![ret()]);
    let p = Program { fns: vec![b()] };
    let ct = cert(vec![bc(vec![], konst(2))]);
    assert!(check_cert(&p, 0, &ct, &vec![Some(konst(2))]));
    assert!(!check_cert(&p, 0, &ct, &vec![Some(konst(3))]));
    assert!(!check_cert(&p, 0, &ct, &vec![None]));
    assert!(!check_cert(&p, 0, &ct, &vec![]));
    // a callee with no summary fails its caller's block
    let main = body(0, vec![], 2, vec![blk(vec![], call(1, vec![], 1, 1)), ret()]);
    let p2 = Program { fns: vec![main, b()] };
    let mc = cert(vec![bc(vec![], konst(9)), bc(vec![], konst(1))]);
    assert!(!check_cert(&p2, 0, &mc, &vec![Some(konst(9)), None]));
    assert!(check_cert(&p2, 0, &mc, &vec![Some(konst(9)), Some(konst(2))]));
}

#[test]
fn rejects_signed_counter() {
    let i = IntTy::I64;
    let sv = || Atom::Val(1, IntTy::I64);
    let b = body(0, vec![Ty::Int(IntTy::I64)], 3, vec![
        blk(vec![asg(1, Rvalue::Use(Operand::Const(IntTy::I64, 0)))], Term::Goto(1)),
        blk(vec![asg(2, Rvalue::Bin(BinOp::Lt, IntTy::I64, Operand::Copy(pl(1)), Operand::Const(IntTy::I64, 10)))], sw(2, 3, 2)),
        blk(vec![asg(1, Rvalue::Bin(BinOp::Add, i, cp(1), Operand::Const(IntTy::I64, 1)))], Term::Goto(1)),
        ret(),
    ]);
    let g = || gap(c(10), sv());
    let ct = cert(vec![
        bc(vec![], konst(45)),
        bc(vec![], poly(vec![m1(4, g()), m0(3)])),
        bc(vec![f_lt(sv(), c(10))], poly(vec![m1(4, g()), m0(1)])),
        bc(vec![], konst(1)),
    ]);
    let sums = vec![Some(konst(45))];
    let p = Program { fns: vec![b] };
    assert!(check_program(&p, &vec![None]).is_ok());
    assert!(check_cost_block(&p, 0, 0, &ct, &sums));
    assert!(check_cost_block(&p, 0, 3, &ct, &sums));
    // neither the test's edge nor the increment rule speaks for a signed counter
    assert!(!check_cost_block(&p, 0, 1, &ct, &sums));
    assert!(!check_cost_block(&p, 0, 2, &ct, &sums));
    assert!(!check_cert(&p, 0, &ct, &sums));
}

#[test]
fn rejects_non_canonical_pot() {
    let a = || m2(1, len(1), v(2));
    let b = body(1, vec![slice()], 3, vec![blk(vec![], Term::Goto(1)), ret()]);
    let bad = cert(vec![bc(vec![], poly(vec![a(), m0(2)])), bc(vec![], konst(1))]);
    assert!(!one_ok(b, bad));
}

// ------------------------------------------------------------------ `&mut` and the writer rule

fn mut_vec() -> Ty { Ty::Mut(Box::new(Ty::Vec(Box::new(Ty::Int(IntTy::U8))))) }
fn deref1() -> Place { Place { local: 1, proj: vec![Proj::Deref] } }
fn one_atom_next(next: Mono, entry: Vec<Mono>) -> Cert {
    cert(vec![bc(vec![], poly(entry)), bc(vec![], poly(vec![next, m0(1)]))])
}

/// `_3 = g(_1)`, `g` charging `Len(1)`, with a `Len(1) + 2` summary read through the arg.
fn call_on_arg(param: fn() -> Ty, next: Mono, entry: Vec<Mono>) -> bool {
    let (p, certs) = call_on_arg_prog(param, next, entry);
    all_ok(&p, &certs)
}
fn call_on_arg_prog(param: fn() -> Ty, next: Mono, mut entry: Vec<Mono>) -> (Program, [Cert; 2]) {
    let param2 = param();
    let param = param();
    let main = body(2, vec![param, usz()], 4, vec![blk(vec![], call(1, vec![cp(1)], 3, 1)), ret()]);
    let (g, gc) = len_callee_of(param2);
    entry.push(m1(1, len(1)));
    assert!(entry.len() == 3);
    (Program { fns: vec![main, g] }, [one_atom_next(next, entry), gc])
}

#[test]
fn accepts_mut_arg_charge_read_before_the_call() {
    // the summary's `Len(1)` crosses the call through the callee's slot; nothing after the call reads an atom
    let (p, certs) = call_on_arg_prog(mut_vec, m0(0), vec![m0(4), m0(0)]);
    assert_tight(&p, &certs);
}

#[test]
fn writer_call_loses_every_local() {
    // a `Mut` arg may write any non-`Mut` local, so `_2` is lost; a shared arg keeps it
    assert!(call_on_arg(slice, m1(1, v(2)), vec![m1(1, v(2)), m0(4)]));
    assert!(!call_on_arg(mut_vec, m1(1, v(2)), vec![m1(1, v(2)), m0(4)]));
    assert!(!call_on_arg(mut_vec, m1(1, len(1)), vec![m1(1, len(1)), m0(4)]));
}

fn push_prog(arg: Ty) -> Body {
    body(2, vec![arg, usz()], 4, vec![blk(vec![], intr(Intrinsic::VecPush, vec![cp(1), cp(2)], 3, 1)), ret()])
}

#[test]
fn writer_intrinsic_loses_every_local() {
    assert!(one_ok(push_prog(mut_vec()), one_atom_next(m0(0), vec![m0(2)])));
    assert!(!one_ok(push_prog(mut_vec()), one_atom_next(m1(1, v(2)), vec![m1(1, v(2)), m0(2)])));
    assert!(!one_ok(push_prog(mut_vec()), one_atom_next(m1(1, len(1)), vec![m1(1, len(1)), m0(2)])));
    assert!(one_ok(push_prog(slice()), one_atom_next(m1(1, v(2)), vec![m1(1, v(2)), m0(2)])));
}

fn deref_write_prog() -> Body {
    body(2, vec![mut_vec(), usz()], 3, vec![
        blk(vec![Stmt::Assign(deref1(), Rvalue::Use(k(0)))], Term::Goto(1)),
        ret(),
    ])
}

#[test]
fn writer_statement_loses_every_local() {
    assert!(one_ok(deref_write_prog(), one_atom_next(m0(0), vec![m0(3)])));
    assert!(!one_ok(deref_write_prog(), one_atom_next(m1(1, v(2)), vec![m1(1, v(2)), m0(3)])));
}

/// `_2 = 0`: a `Mut` local may target `_2`, so a direct write loses what it reads too.
fn direct_write_prog(param: Ty) -> Body {
    body(2, vec![param, usz()], 3, vec![blk(vec![set(2, 0)], Term::Goto(1)), ret()])
}

#[test]
fn direct_write_loses_mut_locals() {
    let next = || m1(1, len(1));
    assert!(one_ok(direct_write_prog(slice()), one_atom_next(next(), vec![next(), m0(3)])));
    assert!(!one_ok(direct_write_prog(mut_vec()), one_atom_next(next(), vec![next(), m0(3)])));
}
