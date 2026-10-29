use ctcore::check::check_prog;
use ctcore::ct::FnLab;
use ctcore::*;

fn u8t() -> Ty { Ty::Int(IntTy::U8) }
fn int(t: IntTy) -> Ty { Ty::Int(t) }
fn rep(n: usize, t: impl Fn() -> Ty) -> Vec<Ty> { (0..n).map(|_| t()).collect() }
fn bx(t: Ty) -> Box<Ty> { Box::new(t) }
fn pl(x: usize) -> Place { Place { local: x, proj: vec![] } }
fn cp(x: usize) -> Operand { Operand::Copy(pl(x)) }
fn asg(x: usize, rv: Rvalue) -> Stmt { Stmt::Assign(pl(x), rv) }
fn bin(op: BinOp, t: IntTy, a: Operand, b: Operand) -> Rvalue { Rvalue::Bin(op, t, a, b) }
fn blk(stmts: Vec<Stmt>, term: Term) -> Block { Block { stmts, term } }
fn body(nargs: usize, locals: Vec<Ty>, blocks: Vec<Block>) -> Body { Body { nargs, locals, blocks } }
fn one(b: Body) -> Program { Program { fns: vec![b] } }
fn call(g: usize, args: Vec<Operand>, dst: usize, next: usize) -> Term { Term::Call(Callee::Fn(g), args, pl(dst), next) }
fn intr(k: Intrinsic, args: Vec<Operand>, dst: usize, next: usize) -> Term { Term::Call(Callee::Intr(k), args, pl(dst), next) }
fn ret() -> Block { blk(vec![], Term::Return) }

fn kname(k: &RejectKind) -> String {
    match k {
        RejectKind::SecretSwitch => "SecretSwitch".into(),
        RejectKind::SecretAssert => "SecretAssert".into(),
        RejectKind::SecretIndex => "SecretIndex".into(),
        RejectKind::SecretDivOperand => "SecretDivOperand".into(),
        RejectKind::SecretShift => "SecretShift".into(),
        RejectKind::SecretAlloc => "SecretAlloc".into(),
        RejectKind::SecretRange => "SecretRange".into(),
        RejectKind::ArgLabel(j) => format!("ArgLabel({j})"),
        RejectKind::RetLabel => "RetLabel".into(),
        RejectKind::MutLabel => "MutLabel".into(),
        RejectKind::NotWf => "NotWf".into(),
        RejectKind::Recursion => "Recursion".into(),
        RejectKind::InferFailed => "InferFailed".into(),
    }
}

fn kinds(rs: &[Reject]) -> Vec<String> { rs.iter().map(|r| kname(&r.kind)).collect() }

fn accepts(p: &Program, decl: Vec<Option<Vec<bool>>>) -> Vec<FnLab> {
    match check_program(p, &decl) {
        Ok(ls) => ls,
        Err(rs) => panic!("rejected: {:?}", kinds(&rs)),
    }
}

/// `check_program` rejects, and `explain`'s sites (its `Err`) include `want`.
fn rejects(p: &Program, decl: Vec<Option<Vec<bool>>>, want: &str) -> Vec<String> {
    match check_program(p, &decl) {
        Ok(_) => panic!("accepted, wanted {want}"),
        Err(rs) => {
            let ks = kinds(&rs);
            assert!(ks.iter().any(|k| k == want), "wanted {want}, got {ks:?}");
            ks
        }
    }
}

fn sec(n: usize) -> Option<Vec<bool>> { Some(vec![true; n]) }

#[test]
fn accepts_masked_select() {
    // fn sel(c, a, b: u8) -> u8 { let m = 0 - c; (a & m) | (b & !m) }, all secret
    let p = one(body(3, rep(8, u8t), vec![blk(vec![
        asg(4, bin(BinOp::Sub, IntTy::U8, Operand::Const(IntTy::U8, 0), cp(1))),
        asg(5, bin(BinOp::BitAnd, IntTy::U8, cp(2), cp(4))),
        asg(6, Rvalue::Un(UnOp::Not, IntTy::U8, cp(4))),
        asg(7, bin(BinOp::BitAnd, IntTy::U8, cp(3), cp(6))),
        asg(0, bin(BinOp::BitOr, IntTy::U8, cp(5), cp(7))),
    ], Term::Return)]));
    let ls = accepts(&p, vec![sec(3)]);
    assert!(ls[0].locals[0] && ls[0].locals[1..4].iter().all(|s| *s));
}

#[test]
fn rejects_secret_switch() {
    let p = one(body(1, vec![Ty::Unit, u8t()], vec![blk(vec![], Term::Switch(cp(1), vec![(0, 1)], 1)), ret()]));
    rejects(&p, vec![sec(1)], "SecretSwitch");
}

#[test]
fn rejects_secret_assert() {
    let p = one(body(1, vec![Ty::Unit, int(IntTy::Bool)], vec![blk(vec![], Term::Assert(cp(1), true, 1)), ret()]));
    rejects(&p, vec![sec(1)], "SecretAssert");
}

#[test]
fn rejects_short_circuit_on_secret() {
    // fn f(a: bool /* secret */, b: bool) -> bool { a && b }, as MIR: a switch on the lhs
    let p = one(body(2, rep(3, || int(IntTy::Bool)), vec![
        blk(vec![], Term::Switch(cp(1), vec![(0, 2)], 1)),
        blk(vec![asg(0, Rvalue::Use(cp(2)))], Term::Goto(3)),
        blk(vec![asg(0, Rvalue::Use(Operand::Const(IntTy::Bool, 0)))], Term::Goto(3)),
        ret(),
    ]));
    rejects(&p, vec![Some(vec![true, false])], "SecretSwitch");
}

#[test]
fn rejects_secret_index() {
    // fn f(arr: [u8; 4], i: usize /* secret */) -> u8 { arr[i] }
    let rd = Operand::Copy(Place { local: 1, proj: vec![Proj::Index(2)] });
    let p = one(body(2, vec![u8t(), Ty::Array(bx(u8t()), 4), int(IntTy::Usize)], vec![blk(vec![asg(0, Rvalue::Use(rd))], Term::Return)]));
    rejects(&p, vec![Some(vec![false, true])], "SecretIndex");
}

fn div_prog(op: BinOp) -> Program {
    one(body(2, rep(3, || int(IntTy::U32)), vec![blk(vec![asg(0, bin(op, IntTy::U32, cp(1), cp(2)))], Term::Return)]))
}

#[test]
fn rejects_secret_divisor() {
    rejects(&div_prog(BinOp::Div), vec![Some(vec![false, true])], "SecretDivOperand");
}

#[test]
fn rejects_secret_dividend() {
    rejects(&div_prog(BinOp::Div), vec![Some(vec![true, false])], "SecretDivOperand");
}

#[test]
fn rejects_secret_shift_amount() {
    rejects(&div_prog(BinOp::Shl), vec![Some(vec![false, true])], "SecretShift");
}

#[test]
fn accepts_constant_shift_of_secret() {
    let sh = bin(BinOp::Shl, IntTy::U32, cp(1), Operand::Const(IntTy::U32, 3));
    let p = one(body(1, rep(2, || int(IntTy::U32)), vec![blk(vec![asg(0, sh)], Term::Return)]));
    let ls = accepts(&p, vec![sec(1)]);
    assert!(ls[0].locals[0]);
}

#[test]
fn accepts_len_of_secret_slice() {
    // fn f(s: &[u8] /* secret */) -> usize { s.len() }
    let len = Rvalue::Len(Place { local: 1, proj: vec![Proj::Deref] });
    let p = one(body(1, vec![int(IntTy::Usize), Ty::Shr(bx(Ty::Slice(bx(u8t()))))], vec![blk(vec![asg(0, len)], Term::Return)]));
    let ls = accepts(&p, vec![sec(1)]);
    assert!(ls[0].locals[1] && !ls[0].locals[0]);
}

#[test]
fn rejects_secret_with_capacity() {
    let p = one(body(1, vec![Ty::Vec(bx(u8t())), int(IntTy::Usize)],
        vec![blk(vec![], intr(Intrinsic::VecWithCapacity, vec![cp(1)], 0, 1)), ret()]));
    rejects(&p, vec![sec(1)], "SecretAlloc");
}

#[test]
fn rejects_secret_arg_to_public_param() {
    // fn g(x: u8) {}  (unlabeled)   fn f(s: u8 /* secret */) { g(s) }
    let g = body(1, vec![Ty::Unit, u8t()], vec![ret()]);
    let f = body(1, vec![Ty::Unit, u8t(), Ty::Unit], vec![blk(vec![], call(0, vec![cp(1)], 2, 1)), ret()]);
    rejects(&Program { fns: vec![g, f] }, vec![None, sec(1)], "ArgLabel(0)");
}

#[test]
fn rejects_secret_ret_to_public_dst() {
    // fn g(x: u8) -> u8 { x }   fn f(a: u8) { let d = g(a); }, under hand labels: g's return is
    // secret and d public (inference would raise d)
    let g = body(1, vec![u8t(), u8t()], vec![blk(vec![asg(0, Rvalue::Use(cp(1)))], Term::Return)]);
    let f = body(1, vec![Ty::Unit, u8t(), u8t()], vec![blk(vec![], call(0, vec![cp(1)], 2, 1)), ret()]);
    let p = Program { fns: vec![g, f] };
    let ls = vec![FnLab { locals: vec![true, true] }, FnLab { locals: vec![false, false, false] }];
    assert!(!check_prog(&p, &ls));
    let ks = kinds(&explain(&p, &ls));
    assert!(ks.iter().any(|k| k == "RetLabel"), "got {ks:?}");
}

#[test]
fn rejects_mut_label_mismatch() {
    // fn g(x: &mut u8) {}  (unlabeled: x public)   fn f(s: u8 /* secret */) { g(&mut s) }
    let g = body(1, vec![Ty::Unit, Ty::Mut(bx(u8t()))], vec![ret()]);
    let f = body(1, vec![Ty::Unit, u8t(), Ty::Mut(bx(u8t())), Ty::Unit],
        vec![blk(vec![asg(2, Rvalue::RefMut(pl(1)))], call(0, vec![cp(2)], 3, 1)), ret()]);
    let ks = rejects(&Program { fns: vec![g, f] }, vec![None, sec(1)], "MutLabel");
    assert!(ks.iter().any(|k| k == "ArgLabel(0)"), "the param is named: {ks:?}");
}

#[test]
fn inference_raises_buffer_for_secret_mut_param() {
    // fn g(x: &mut u8 /* secret */) {}   fn f() { let mut s = 0; g(&mut s) }: s becomes secret
    let g = body(1, vec![Ty::Unit, Ty::Mut(bx(u8t()))], vec![ret()]);
    let f = body(0, vec![Ty::Unit, u8t(), Ty::Mut(bx(u8t())), Ty::Unit], vec![
        blk(vec![asg(1, Rvalue::Use(Operand::Const(IntTy::U8, 0))), asg(2, Rvalue::RefMut(pl(1)))], call(0, vec![cp(2)], 3, 1)),
        ret(),
    ]);
    let ls = accepts(&Program { fns: vec![g, f] }, vec![sec(1), None]);
    assert!(ls[1].locals[2] && ls[1].locals[1]);
}

#[test]
fn rejects_mut_in_tuple_wf() {
    let p = one(body(0, vec![Ty::Unit, Ty::Tuple(vec![Ty::Mut(bx(u8t()))])], vec![ret()]));
    rejects(&p, vec![None], "NotWf");
}

#[test]
fn accepts_declassified_branch() {
    // fn f(x: u8 /* secret */) { let d = declassify(x); if d == 0 { .. } }
    let p = one(body(1, vec![Ty::Unit, u8t(), u8t()], vec![
        blk(vec![], intr(Intrinsic::Declassify, vec![cp(1)], 2, 1)),
        blk(vec![], Term::Switch(cp(2), vec![(0, 2)], 2)),
        ret(),
    ]));
    let ls = accepts(&p, vec![sec(1)]);
    assert!(ls[0].locals[1] && !ls[0].locals[2]);
}

#[test]
fn inference_propagates_callee_secret_ret() {
    // fn f(a: u8) -> u8 { g(a) }   fn g(x: u8 /* secret */) -> u8 { x }; the caller comes first
    let f = body(1, rep(3, u8t), vec![blk(vec![], call(1, vec![cp(1)], 2, 1)), blk(vec![asg(0, Rvalue::Use(cp(2)))], Term::Return)]);
    let g = body(1, vec![u8t(), u8t()], vec![blk(vec![asg(0, Rvalue::Use(cp(1)))], Term::Return)]);
    let ls = accepts(&Program { fns: vec![f, g] }, vec![None, sec(1)]);
    assert!(ls[1].locals[0] && ls[0].locals[2] && ls[0].locals[0] && !ls[0].locals[1]);
}

#[test]
fn unlabeled_callee_is_all_public() {
    // fn f() -> u8 { g(5) }   fn g(x: u8) -> u8 { x + 1 }  (unlabeled)
    let f = body(0, vec![u8t()], vec![blk(vec![], call(1, vec![Operand::Const(IntTy::U8, 5)], 0, 1)), ret()]);
    let g = body(1, rep(3, u8t), vec![blk(vec![
        asg(2, bin(BinOp::Add, IntTy::U8, cp(1), Operand::Const(IntTy::U8, 1))),
        asg(0, Rvalue::Use(cp(2))),
    ], Term::Return)]);
    let ls = accepts(&Program { fns: vec![f, g] }, vec![None, None]);
    assert!(ls[1].locals.len() == 3 && ls[1].locals.iter().all(|s| !*s) && !ls[0].locals[0]);
}

#[test]
fn rejects_recursion() {
    let p = one(body(1, vec![Ty::Unit, u8t(), Ty::Unit], vec![blk(vec![], call(0, vec![cp(1)], 2, 1)), ret()]));
    rejects(&p, vec![sec(1)], "Recursion");
}
