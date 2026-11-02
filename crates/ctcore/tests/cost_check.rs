use ctcore::cost::*;
use ctcore::cost_check::{check_cert_parts as check, check_cost_block};
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
    let sums: Vec<Option<Poly>> = certs.iter().map(|ct| Some(pot0(ct))).collect();
    (0..certs.len()).all(|f| check(p, f, &certs[f], &sums))
}
fn one_ok(b: Body, ct: Cert) -> bool { all_ok(&Program { fns: vec![b] }, &[ct]) }

// ------------------------------------------------------------------ straight lines and counted loops

#[test]
fn accepts_straight_line_const() {
    let b = body(0, vec![], 2, vec![blk(vec![set(1, 1), set(1, 2)], Term::Goto(1)), ret()]);
    assert!(one_ok(b, cert(vec![bc(vec![], konst(4)), bc(vec![], konst(1))])));
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
    assert!(one_ok(loop_const(), ct));
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
    assert!(one_ok(loop_len(), loop_len_cert(6, 1, vec![f_lt(v(3), v(2))])));
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
    assert!(one_ok(nested(), nested_cert(19)));
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
    assert!(all_ok(&Program { fns: vec![main, leaf] }, &[ct, cert(vec![bc(vec![], konst(1))])]));
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
    assert!(one_ok(b, ct));
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
    assert!(one_ok(b, ct));
}

fn len_callee() -> (Body, Cert) {
    let b = body(1, vec![slice()], 2, vec![blk(vec![], intr(Intrinsic::SliceToVec, vec![cp(1)], 0, 1)), ret()]);
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
    assert!(all_ok(&Program { fns: vec![main, g] }, &[ct, gc]));
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
    assert!(all_ok(&Program { fns: vec![main, g] }, &[ct, gc]));
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
    assert!(all_ok(&Program { fns: vec![main, callee] }, &[ct, cc]));
}

// ------------------------------------------------------------------ rejections

#[test]
fn rejects_unknown_atom_in_rhs() {
    let leaf = body(0, vec![], 1, vec![ret()]);
    let main = body(0, vec![], 9, vec![blk(vec![], call(1, vec![], 8, 1)), ret()]);
    let ct = cert(vec![bc(vec![], konst(100)), bc(vec![], poly(vec![m1(1, v(8)), m0(1)]))]);
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
    assert!(check(&p, 0, &ct, &vec![Some(konst(2))]));
    assert!(!check(&p, 0, &ct, &vec![Some(konst(3))]));
    assert!(!check(&p, 0, &ct, &vec![None]));
    assert!(!check(&p, 0, &ct, &vec![]));
    // a callee with no summary fails its caller's block
    let main = body(0, vec![], 2, vec![blk(vec![], call(1, vec![], 1, 1)), ret()]);
    let p2 = Program { fns: vec![main, b()] };
    let mc = cert(vec![bc(vec![], konst(9)), bc(vec![], konst(1))]);
    assert!(!check(&p2, 0, &mc, &vec![Some(konst(9)), None]));
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
    assert!(!check_cost_block(&Program { fns: vec![body(0, vec![], 1, vec![])] }, 0, 0, &ct, &sums));
    let p = Program { fns: vec![b] };
    // neither the test's edge nor the increment rule speaks for a signed counter
    assert!(!check_cost_block(&p, 0, 1, &ct, &sums));
    assert!(!check_cost_block(&p, 0, 2, &ct, &sums));
    assert!(!check(&p, 0, &ct, &sums));
}

#[test]
fn rejects_non_canonical_pot() {
    let a = || m2(1, len(1), v(2));
    let b = body(1, vec![slice()], 3, vec![blk(vec![], Term::Goto(1)), ret()]);
    let bad = cert(vec![bc(vec![], poly(vec![a(), m0(2)])), bc(vec![], konst(1))]);
    assert!(!one_ok(b, bad));
}
