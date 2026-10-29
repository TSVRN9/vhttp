//! Sanity lemmas pinning the semantics on tiny literal programs. Spec code cannot build a
//! `Vec`, so each lemma takes the program through premises on its views.
//!
//! Proof pattern: every lemma hides the run/statement/call/intrinsic definitions at the top and
//! reveals each one only inside the `assert .. by` step that unfolds it, so each step is checked
//! in a small context and a wrong semantics fails on that step's assertion, not on rlimit.
#[allow(unused_imports)]
use crate::sem::*;
#[allow(unused_imports)]
use crate::syntax::*;
use vstd::prelude::*;

verus! {

pub open spec fn local(pl: Place, x: usize) -> bool { pl.local == x && pl.proj@.len() == 0 }

pub open spec fn slot0() -> Loc { Loc { root: Root::Slot(0), path: seq![] } }

pub open spec fn fr1(v: Val) -> Frame { Frame { locals: seq![v], slots: seq![] } }

/// `_0 = const n_u8; return`
pub open spec fn ret_const(blk: Block, n: u128) -> bool {
    &&& blk.stmts@.len() == 1
    &&& blk.stmts@[0] matches Stmt::Assign(d, Rvalue::Use(Operand::Const(IntTy::U8, m))) && m == n && local(d, 0)
    &&& blk.term == Term::Return
}

/// `switchInt(const c_u8) -> [ts.., otherwise: o]` in bb0 (no statements); bb1 and bb2 store
/// 10 and 20 in `_0` and return.
pub open spec fn switch_prog(p: Program, c: u128, ts: Seq<(u128, usize)>, o: usize) -> bool {
    &&& p.fns@.len() == 1
    &&& p.fns@[0].blocks@.len() == 3
    &&& p.fns@[0].blocks@[0].stmts@.len() == 0
    &&& p.fns@[0].blocks@[0].term matches Term::Switch(c2, ts2, o2) && c2 == Operand::Const(IntTy::U8, c)
            && ts2@ == ts && o2 == o
    &&& ret_const(p.fns@[0].blocks@[1], 10)
    &&& ret_const(p.fns@[0].blocks@[2], 20)
}

/// `switchInt(const 1) -> [0: bb2, 1: bb1, 1: bb2, otherwise: bb2]` takes the first match, bb1.
pub proof fn sanity_switch_matching_target(p: Program)
    requires switch_prog(p, 1, seq![(0u128, 2usize), (1u128, 1usize), (1u128, 2usize)], 2),
    ensures run_fn(p, 0, fr1(Val::Unit), 3) == Some((fr1(Val::Int(10)), seq![Event::Cond(1)], 3nat)),
{
    hide(run_from);
    hide(exec_stmts);
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    let e = Seq::<Event>::empty();
    let b1 = p.fns@[0].blocks@[1].stmts@;
    assert(exec_stmts(p.fns@[0].blocks@[0].stmts@, 0, fr1(Val::Unit)) == (fr1(Val::Unit), e)) by { reveal(exec_stmts); }
    assert(exec_stmts(b1, 0, fr1(Val::Unit)) == (fr1(Val::Int(10)), e)) by {
        reveal_with_fuel(exec_stmts, 2);
        assert(exec_stmt(fr1(Val::Unit), b1[0]).0.locals =~= seq![Val::Int(10)]);
    }
    assert(run_from(p, 0, 1, fr1(Val::Unit), 2) == Some((fr1(Val::Int(10)), e, 2nat))) by { reveal(run_from); }
    if let Term::Switch(_, ts, _) = p.fns@[0].blocks@[0].term {
        assert(switch_target(ts@, 0, 1, 2) == 1) by { reveal_with_fuel(switch_target, 2); }
    }
    assert(seq![Event::Cond(1)] + e =~= seq![Event::Cond(1)]);
    assert(run_from(p, 0, 0, fr1(Val::Unit), 3) == Some((fr1(Val::Int(10)), seq![Event::Cond(1)], 3nat))) by { reveal(run_from); }
}

/// `switchInt(const 5) -> [0: bb1, 1: bb1, otherwise: bb2]` takes `otherwise`, bb2.
pub proof fn sanity_switch_otherwise(p: Program)
    requires switch_prog(p, 5, seq![(0u128, 1usize), (1u128, 1usize)], 2),
    ensures run_fn(p, 0, fr1(Val::Unit), 3) == Some((fr1(Val::Int(20)), seq![Event::Cond(5)], 3nat)),
{
    hide(run_from);
    hide(exec_stmts);
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    let e = Seq::<Event>::empty();
    let b2 = p.fns@[0].blocks@[2].stmts@;
    assert(exec_stmts(p.fns@[0].blocks@[0].stmts@, 0, fr1(Val::Unit)) == (fr1(Val::Unit), e)) by { reveal(exec_stmts); }
    assert(exec_stmts(b2, 0, fr1(Val::Unit)) == (fr1(Val::Int(20)), e)) by {
        reveal_with_fuel(exec_stmts, 2);
        assert(exec_stmt(fr1(Val::Unit), b2[0]).0.locals =~= seq![Val::Int(20)]);
    }
    assert(run_from(p, 0, 2, fr1(Val::Unit), 2) == Some((fr1(Val::Int(20)), e, 2nat))) by { reveal(run_from); }
    if let Term::Switch(_, ts, _) = p.fns@[0].blocks@[0].term {
        assert(switch_target(ts@, 0, 5, 2) == 2) by { reveal_with_fuel(switch_target, 3); }
    }
    assert(seq![Event::Cond(5)] + e =~= seq![Event::Cond(5)]);
    assert(run_from(p, 0, 0, fr1(Val::Unit), 3) == Some((fr1(Val::Int(20)), seq![Event::Cond(5)], 3nat))) by { reveal(run_from); }
}

/// `assert(const 1_bool == false) -> bb1` fails although the condition is nonzero.
pub proof fn sanity_assert_failure_is_none(p: Program)
    requires
        p.fns@.len() == 1,
        p.fns@[0].blocks@.len() == 2,
        p.fns@[0].blocks@[0].stmts@.len() == 0,
        p.fns@[0].blocks@[0].term matches Term::Assert(c, exp, b) && c == Operand::Const(IntTy::Bool, 1) && !exp && b == 1,
        p.fns@[0].blocks@[1].stmts@.len() == 0,
        p.fns@[0].blocks@[1].term == Term::Return,
    ensures run_fn(p, 0, fr1(Val::Unit), 3) is None,
{
    hide(run_from);
    hide(exec_stmts);
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    let e = Seq::<Event>::empty();
    assert(exec_stmts(p.fns@[0].blocks@[0].stmts@, 0, fr1(Val::Unit)) == (fr1(Val::Unit), e)) by { reveal(exec_stmts); }
    assert(exec_stmts(p.fns@[0].blocks@[1].stmts@, 0, fr1(Val::Unit)) == (fr1(Val::Unit), e)) by { reveal(exec_stmts); }
    assert(run_from(p, 0, 1, fr1(Val::Unit), 2) == Some((fr1(Val::Unit), e, 1nat))) by { reveal(run_from); }
    assert(run_from(p, 0, 0, fr1(Val::Unit), 3) is None) by { reveal(run_from); }
}

/// `_0 = _1[_2]` with `_2 = 1` reads 20 and emits `Idx(1)`.
pub proof fn sanity_index_emits_idx(p: Program)
    requires
        p.fns@.len() == 1,
        p.fns@[0].blocks@.len() == 1,
        p.fns@[0].blocks@[0].stmts@.len() == 1,
        p.fns@[0].blocks@[0].stmts@[0] matches Stmt::Assign(d, Rvalue::Use(Operand::Copy(src)))
            && local(d, 0) && src.local == 1 && src.proj@ == seq![Proj::Index(2)],
        p.fns@[0].blocks@[0].term == Term::Return,
    ensures ({
        let a = Val::Arr(seq![Val::Int(10), Val::Int(20), Val::Int(30)]);
        run_fn(p, 0, Frame { locals: seq![Val::Unit, a, Val::Int(1)], slots: seq![] }, 1)
            == Some((Frame { locals: seq![Val::Int(20), a, Val::Int(1)], slots: seq![] }, seq![Event::Idx(1)], 2nat))
    }),
{
    hide(run_from);
    hide(exec_stmts);
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    let e = Seq::<Event>::empty();
    let a = Val::Arr(seq![Val::Int(10), Val::Int(20), Val::Int(30)]);
    let fr = Frame { locals: seq![Val::Unit, a, Val::Int(1)], slots: seq![] };
    let f1 = Frame { locals: seq![Val::Int(20), a, Val::Int(1)], slots: seq![] };
    let ss = p.fns@[0].blocks@[0].stmts@;
    assert(exec_stmts(ss, 0, fr) == (f1, seq![Event::Idx(1)])) by {
        reveal_with_fuel(exec_stmts, 2);
        if let Stmt::Assign(d, Rvalue::Use(Operand::Copy(src))) = ss[0] {
            let ps = src.proj@;
            let l1 = Loc { root: Root::Local(1), path: seq![PE::Index(1)] };
            assert(step(fr, Cur::L(local_loc(1)), ps[0]) == (Cur::L(l1), seq![Event::Idx(1)]));
            assert(walk(fr, ps, 1, Cur::L(l1)) == (Cur::L(l1), e));
            assert(walk(fr, ps, 0, Cur::L(local_loc(1))) == (Cur::L(l1), seq![Event::Idx(1)]));
            assert(read_at(get(a, PE::Index(1)), l1.path.drop_first()) == Val::Int(20));
            assert(read_place(fr, src) == (Val::Int(20), seq![Event::Idx(1)]));
            assert(walk(fr, d.proj@, 0, Cur::L(local_loc(0))) == (Cur::L(local_loc(0)), e));
        }
        assert(exec_stmt(fr, ss[0]).0.locals =~= f1.locals);
        assert(exec_stmt(fr, ss[0]).1 =~= seq![Event::Idx(1)]);
        assert(seq![Event::Idx(1)] + e =~= seq![Event::Idx(1)]);
    }
    assert(run_from(p, 0, 0, fr, 1) == Some((f1, seq![Event::Idx(1)], 2nat))) by { reveal(run_from); }
}

/// `_0 = Bin(op, U32, _1, _2); return`
pub open spec fn bin_prog(p: Program, op: BinOp) -> bool {
    &&& p.fns@.len() == 1
    &&& p.fns@[0].blocks@.len() == 1
    &&& p.fns@[0].blocks@[0].stmts@.len() == 1
    &&& p.fns@[0].blocks@[0].stmts@[0] matches Stmt::Assign(d, Rvalue::Bin(o, IntTy::U32, Operand::Copy(a), Operand::Copy(b)))
            && o == op && local(d, 0) && local(a, 1) && local(b, 2)
    &&& p.fns@[0].blocks@[0].term == Term::Return
}

pub open spec fn fr3(a: Val, b: Val, c: Val) -> Frame { Frame { locals: seq![a, b, c], slots: seq![] } }

/// `_0 = _1 / _2` with 7 and 2 emits `DivOps(7, 2)`; the quotient stays symbolic.
pub proof fn sanity_div_emits_operands(p: Program)
    requires bin_prog(p, BinOp::Div),
    ensures
        run_fn(p, 0, fr3(Val::Unit, Val::Int(7), Val::Int(2)), 1)
            == Some((fr3(Val::Int(binop(BinOp::Div, IntTy::U32, 7, 2)), Val::Int(7), Val::Int(2)), seq![Event::DivOps(7, 2)], 2nat)),
{
    hide(run_from);
    hide(exec_stmts);
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    let fr = fr3(Val::Unit, Val::Int(7), Val::Int(2));
    let f1 = fr3(Val::Int(binop(BinOp::Div, IntTy::U32, 7, 2)), Val::Int(7), Val::Int(2));
    let ss = p.fns@[0].blocks@[0].stmts@;
    assert(exec_stmts(ss, 0, fr) == (f1, seq![Event::DivOps(7, 2)])) by {
        reveal_with_fuel(exec_stmts, 2);
        assert(exec_stmt(fr, ss[0]).0.locals =~= f1.locals);
        assert(exec_stmt(fr, ss[0]).1 =~= seq![Event::DivOps(7, 2)]);
        assert(seq![Event::DivOps(7, 2)] + Seq::<Event>::empty() =~= seq![Event::DivOps(7, 2)]);
    }
    assert(run_from(p, 0, 0, fr, 1) == Some((f1, seq![Event::DivOps(7, 2)], 2nat))) by { reveal(run_from); }
}

/// `_0 = _1 << _2` with 1 and 3 emits `Shamt(3)`; the result stays symbolic.
pub proof fn sanity_shift_emits_amount(p: Program)
    requires bin_prog(p, BinOp::Shl),
    ensures
        run_fn(p, 0, fr3(Val::Unit, Val::Int(1), Val::Int(3)), 1)
            == Some((fr3(Val::Int(binop(BinOp::Shl, IntTy::U32, 1, 3)), Val::Int(1), Val::Int(3)), seq![Event::Shamt(3)], 2nat)),
{
    hide(run_from);
    hide(exec_stmts);
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    let fr = fr3(Val::Unit, Val::Int(1), Val::Int(3));
    let f1 = fr3(Val::Int(binop(BinOp::Shl, IntTy::U32, 1, 3)), Val::Int(1), Val::Int(3));
    let ss = p.fns@[0].blocks@[0].stmts@;
    assert(exec_stmts(ss, 0, fr) == (f1, seq![Event::Shamt(3)])) by {
        reveal_with_fuel(exec_stmts, 2);
        assert(exec_stmt(fr, ss[0]).0.locals =~= f1.locals);
        assert(exec_stmt(fr, ss[0]).1 =~= seq![Event::Shamt(3)]);
        assert(seq![Event::Shamt(3)] + Seq::<Event>::empty() =~= seq![Event::Shamt(3)]);
    }
    assert(run_from(p, 0, 0, fr, 1) == Some((f1, seq![Event::Shamt(3)], 2nat))) by { reveal(run_from); }
}

/// 2 blocks, 3 statements: 3 statements + 2 terminators = 5 steps.
pub proof fn sanity_steps_count(p: Program)
    requires
        p.fns@.len() == 1,
        p.fns@[0].blocks@.len() == 2,
        p.fns@[0].blocks@[0].stmts@.len() == 2,
        p.fns@[0].blocks@[0].stmts@[0] matches Stmt::Assign(d, Rvalue::Use(Operand::Const(IntTy::U8, 1))) && local(d, 0),
        p.fns@[0].blocks@[0].stmts@[1] matches Stmt::Assign(d, Rvalue::Use(Operand::Const(IntTy::U8, 2))) && local(d, 0),
        p.fns@[0].blocks@[0].term == Term::Goto(1),
        ret_const(p.fns@[0].blocks@[1], 3),
    ensures run_fn(p, 0, fr1(Val::Unit), 2) == Some((fr1(Val::Int(3)), Seq::<Event>::empty(), 5nat)),
{
    hide(run_from);
    hide(exec_stmts);
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    let e = Seq::<Event>::empty();
    let s0 = p.fns@[0].blocks@[0].stmts@;
    let s1 = p.fns@[0].blocks@[1].stmts@;
    assert(exec_stmts(s0, 0, fr1(Val::Unit)) == (fr1(Val::Int(2)), e)) by {
        reveal_with_fuel(exec_stmts, 3);
        assert(exec_stmt(fr1(Val::Unit), s0[0]).0.locals =~= seq![Val::Int(1)]);
        assert(exec_stmt(fr1(Val::Int(1)), s0[1]).0.locals =~= seq![Val::Int(2)]);
    }
    assert(exec_stmts(s1, 0, fr1(Val::Int(2))) == (fr1(Val::Int(3)), e)) by {
        reveal_with_fuel(exec_stmts, 2);
        assert(exec_stmt(fr1(Val::Int(2)), s1[0]).0.locals =~= seq![Val::Int(3)]);
    }
    assert(run_from(p, 0, 1, fr1(Val::Int(2)), 1) == Some((fr1(Val::Int(3)), e, 2nat))) by { reveal(run_from); }
    assert(e + e =~= e);
    assert(run_from(p, 0, 0, fr1(Val::Unit), 2) == Some((fr1(Val::Int(3)), e, 5nat))) by { reveal(run_from); }
}

pub open spec fn fr4(a: Val, b: Val, c: Val) -> Frame { Frame { locals: seq![a, b, c, Val::Unit], slots: seq![] } }

pub open spec fn wb_cf(x: u128) -> Frame { Frame { locals: seq![Val::Unit, Val::Mut(slot0())], slots: seq![Val::Int(x)] } }

/// `_2 = &mut _1`
proof fn wb_refmut(st: Stmt)
    requires st matches Stmt::Assign(d, Rvalue::RefMut(s)) && local(d, 2) && local(s, 1),
    ensures exec_stmt(fr4(Val::Unit, Val::Int(0), Val::Unit), st) == (fr4(Val::Unit, Val::Int(0), Val::Mut(local_loc(1))), Seq::<Event>::empty()),
{
    let e = Seq::<Event>::empty();
    let (fa, fb) = (fr4(Val::Unit, Val::Int(0), Val::Unit), fr4(Val::Unit, Val::Int(0), Val::Mut(local_loc(1))));
    if let Stmt::Assign(d, Rvalue::RefMut(s)) = st {
        assert(place_loc(fa, s) == Some((local_loc(1), e)));
        assert(place_loc(fa, d) == Some((local_loc(2), e)));
    }
    assert(exec_stmt(fa, st).0.locals =~= fb.locals);
    assert(e + e =~= e);
}

/// Caller bb0's statements `_1 = 0; _2 = &mut _1`.
proof fn wb_bb0(s0: Seq<Stmt>)
    requires
        s0.len() == 2,
        s0[0] matches Stmt::Assign(d, Rvalue::Use(Operand::Const(IntTy::U8, 0))) && local(d, 1),
        s0[1] matches Stmt::Assign(d, Rvalue::RefMut(s)) && local(d, 2) && local(s, 1),
    ensures exec_stmts(s0, 0, fr4(Val::Unit, Val::Unit, Val::Unit)) == (fr4(Val::Unit, Val::Int(0), Val::Mut(local_loc(1))), Seq::<Event>::empty()),
{
    let e = Seq::<Event>::empty();
    let (fr, fa, fb) = (fr4(Val::Unit, Val::Unit, Val::Unit), fr4(Val::Unit, Val::Int(0), Val::Unit), fr4(Val::Unit, Val::Int(0), Val::Mut(local_loc(1))));
    assert(exec_stmt(fr, s0[0]).0.locals =~= fa.locals);
    wb_refmut(s0[1]);
    assert(exec_stmts(s0, 2, fb) == (fb, e));
    assert(exec_stmts(s0, 1, fa) == (fb, e));
}

/// Entering the callee with `_2 = Mut(Local(1), [])`, local 1 holding 0.
proof fn wb_enter(p: Program, args: Seq<Operand>)
    requires p.fns@.len() == 2, p.fns@[1].locals@.len() == 2, args.len() == 1, args[0] matches Operand::Copy(a) && local(a, 2),
    ensures call_enter(p, 1, fr4(Val::Unit, Val::Int(0), Val::Mut(local_loc(1))), args) == (wb_cf(0), seq![Some(local_loc(1))], Seq::<Event>::empty()),
{
    let fb = fr4(Val::Unit, Val::Int(0), Val::Mut(local_loc(1)));
    assert(op_vals(fb, args) =~= seq![Val::Mut(local_loc(1))]);
    assert(ops_ev(fb, args.drop_last()) == Seq::<Event>::empty());
    let (c, wb, ae) = call_enter(p, 1, fb, args);
    assert(c.locals =~= wb_cf(0).locals);
    assert(c.slots =~= wb_cf(0).slots);
    assert(wb =~= seq![Some(local_loc(1))]);
    assert(ae =~= Seq::<Event>::empty());
}

/// The callee `*_1 = 7; return` run from `wb_cf(0)`.
proof fn wb_callee(p: Program)
    requires
        p.fns@.len() == 2,
        p.fns@[1].blocks@.len() == 1,
        p.fns@[1].blocks@[0].stmts@.len() == 1,
        p.fns@[1].blocks@[0].stmts@[0] matches Stmt::Assign(d, Rvalue::Use(Operand::Const(IntTy::U8, 7)))
            && d.local == 1 && d.proj@ == seq![Proj::Deref],
        p.fns@[1].blocks@[0].term == Term::Return,
    ensures run_from(p, 1, 0, wb_cf(0), 1) == Some((wb_cf(7), Seq::<Event>::empty(), 2nat)),
{
    hide(run_from);
    hide(exec_stmts);
    hide(exec_stmt);
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    let e = Seq::<Event>::empty();
    let cs = p.fns@[1].blocks@[0].stmts@;
    assert(exec_stmt(wb_cf(0), cs[0]) == (wb_cf(7), e)) by {
        reveal(exec_stmt);
        if let Stmt::Assign(d, _) = cs[0] {
            assert(walk(wb_cf(0), d.proj@, 1, Cur::L(slot0())) == (Cur::L(slot0()), e));
            assert(place_loc(wb_cf(0), d) == Some((slot0(), e)));
        }
        assert(exec_stmt(wb_cf(0), cs[0]).0.slots =~= wb_cf(7).slots);
        assert(e + e =~= e);
    }
    assert(exec_stmts(cs, 0, wb_cf(0)) == (wb_cf(7), e)) by {
        reveal_with_fuel(exec_stmts, 2);
        assert(e + e =~= e);
    }
    assert(run_from(p, 1, 0, wb_cf(0), 1) == Some((wb_cf(7), e, 2nat))) by { reveal(run_from); }
}

/// Caller bb1 `_0 = _1; return` after the write-back.
proof fn wb_bb1(p: Program)
    requires
        p.fns@.len() == 2,
        p.fns@[0].blocks@.len() == 2,
        p.fns@[0].blocks@[1].stmts@.len() == 1,
        p.fns@[0].blocks@[1].stmts@[0] matches Stmt::Assign(d, Rvalue::Use(Operand::Copy(s))) && local(d, 0) && local(s, 1),
        p.fns@[0].blocks@[1].term == Term::Return,
    ensures run_from(p, 0, 1, fr4(Val::Unit, Val::Int(7), Val::Mut(local_loc(1))), 1)
        == Some((fr4(Val::Int(7), Val::Int(7), Val::Mut(local_loc(1))), Seq::<Event>::empty(), 2nat)),
{
    hide(run_from);
    hide(exec_stmts);
    hide(exec_stmt);
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    let e = Seq::<Event>::empty();
    let (fc, fd) = (fr4(Val::Unit, Val::Int(7), Val::Mut(local_loc(1))), fr4(Val::Int(7), Val::Int(7), Val::Mut(local_loc(1))));
    let s1 = p.fns@[0].blocks@[1].stmts@;
    assert(exec_stmt(fc, s1[0]) == (fd, e)) by {
        reveal(exec_stmt);
        assert(exec_stmt(fc, s1[0]).0.locals =~= fd.locals);
        assert(e + e =~= e);
    }
    assert(exec_stmts(s1, 0, fc) == (fd, e)) by {
        reveal_with_fuel(exec_stmts, 2);
        assert(e + e =~= e);
    }
    assert(run_from(p, 0, 1, fc, 1) == Some((fd, e, 2nat))) by { reveal(run_from); }
}

/// Caller fn 0: `_1 = 0; _2 = &mut _1; _3 = f1(_2) -> bb1`, `bb1: _0 = _1; return`.
/// Callee fn 1 (one `&mut u8` parameter): `*_1 = 7; return`. The caller sees 7.
pub proof fn sanity_mut_arg_written_back(p: Program)
    requires
        p.fns@.len() == 2,
        p.fns@[0].blocks@.len() == 2,
        p.fns@[0].blocks@[0].stmts@.len() == 2,
        p.fns@[0].blocks@[0].stmts@[0] matches Stmt::Assign(d, Rvalue::Use(Operand::Const(IntTy::U8, 0))) && local(d, 1),
        p.fns@[0].blocks@[0].stmts@[1] matches Stmt::Assign(d, Rvalue::RefMut(s)) && local(d, 2) && local(s, 1),
        p.fns@[0].blocks@[0].term matches Term::Call(Callee::Fn(1), args, d, 1)
            && args@.len() == 1 && local(d, 3) && (args@[0] matches Operand::Copy(a) && local(a, 2)),
        p.fns@[0].blocks@[1].stmts@.len() == 1,
        p.fns@[0].blocks@[1].stmts@[0] matches Stmt::Assign(d, Rvalue::Use(Operand::Copy(s))) && local(d, 0) && local(s, 1),
        p.fns@[0].blocks@[1].term == Term::Return,
        p.fns@[1].locals@.len() == 2,
        p.fns@[1].blocks@.len() == 1,
        p.fns@[1].blocks@[0].stmts@.len() == 1,
        p.fns@[1].blocks@[0].stmts@[0] matches Stmt::Assign(d, Rvalue::Use(Operand::Const(IntTy::U8, 7)))
            && d.local == 1 && d.proj@ == seq![Proj::Deref],
        p.fns@[1].blocks@[0].term == Term::Return,
    ensures
        run_fn(p, 0, fr4(Val::Unit, Val::Unit, Val::Unit), 2)
            == Some((fr4(Val::Int(7), Val::Int(7), Val::Mut(local_loc(1))), Seq::<Event>::empty(), 7nat)),
{
    hide(run_from);
    hide(exec_stmts);
    hide(exec_stmt);
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    let e = Seq::<Event>::empty();
    let m1 = Val::Mut(local_loc(1));
    let (fr, fb, fc) = (fr4(Val::Unit, Val::Unit, Val::Unit), fr4(Val::Unit, Val::Int(0), m1), fr4(Val::Unit, Val::Int(7), m1));
    wb_bb0(p.fns@[0].blocks@[0].stmts@);
    wb_callee(p);
    wb_bb1(p);
    if let Term::Call(_, args, dst, _) = p.fns@[0].blocks@[0].term {
        wb_enter(p, args@);
        assert(call_leave(fb, wb_cf(7), seq![Some(local_loc(1))], dst) == (fc, e)) by {
            reveal(call_leave);
            let wb = seq![Some(local_loc(1))];
            assert(write_back(fb, wb_cf(7).slots, wb.drop_last()) == fb);
            assert(write_back(fb, wb_cf(7).slots, wb).locals =~= fc.locals);
            assert(call_leave(fb, wb_cf(7), wb, dst).0.locals =~= fc.locals);
        }
    }
    assert(e + e + e + e + e =~= e);
    assert(run_from(p, 0, 0, fr, 2) == Some((fr4(Val::Int(7), Val::Int(7), m1), e, 7nat))) by { reveal(run_from); }
}

pub open spec fn arr3() -> Val { Val::Arr(seq![Val::Int(1), Val::Int(2), Val::Int(3)]) }

/// `_2 = &_1`
proof fn shr_ref(st: Stmt)
    requires st matches Stmt::Assign(d, Rvalue::RefShr(s)) && local(d, 2) && local(s, 1),
    ensures exec_stmt(fr3(Val::Unit, arr3(), Val::Unit), st) == (fr3(Val::Unit, arr3(), Val::Shr(Box::new(arr3()))), Seq::<Event>::empty()),
{
    let e = Seq::<Event>::empty();
    let a = arr3();
    let fr = fr3(Val::Unit, a, Val::Unit);
    if let Stmt::Assign(d, Rvalue::RefShr(s)) = st {
        assert(read_place(fr, s) == (a, e));
        assert(place_loc(fr, d) == Some((local_loc(2), e)));
    }
    assert(exec_stmt(fr, st).0.locals =~= fr3(Val::Unit, a, Val::Shr(Box::new(a))).locals);
    assert(e + e =~= e);
}

/// `_0 = Len(*_2)` with `_2 = Shr(arr3)`.
proof fn shr_len(st: Stmt)
    requires st matches Stmt::Assign(d, Rvalue::Len(s)) && local(d, 0) && s.local == 2 && s.proj@ == seq![Proj::Deref],
    ensures exec_stmt(fr3(Val::Unit, arr3(), Val::Shr(Box::new(arr3()))), st)
        == (fr3(Val::Int(3), arr3(), Val::Shr(Box::new(arr3()))), Seq::<Event>::empty()),
{
    let e = Seq::<Event>::empty();
    let a = arr3();
    let fb = fr3(Val::Unit, a, Val::Shr(Box::new(a)));
    if let Stmt::Assign(d, Rvalue::Len(s)) = st {
        assert(walk(fb, s.proj@, 1, Cur::V(a)) == (Cur::V(a), e));
        assert(read_place(fb, s) == (a, e));
        assert(place_loc(fb, d) == Some((local_loc(0), e)));
    }
    assert(exec_stmt(fb, st).0.locals =~= fr3(Val::Int(3), a, Val::Shr(Box::new(a))).locals);
    assert(e + e =~= e);
}

/// `_2 = &_1; _0 = Len(*_2); return`: the snapshot has the array's length.
pub proof fn sanity_shr_snapshot(p: Program)
    requires
        p.fns@.len() == 1,
        p.fns@[0].blocks@.len() == 1,
        p.fns@[0].blocks@[0].stmts@.len() == 2,
        p.fns@[0].blocks@[0].stmts@[0] matches Stmt::Assign(d, Rvalue::RefShr(s)) && local(d, 2) && local(s, 1),
        p.fns@[0].blocks@[0].stmts@[1] matches Stmt::Assign(d, Rvalue::Len(s)) && local(d, 0) && s.local == 2
            && s.proj@ == seq![Proj::Deref],
        p.fns@[0].blocks@[0].term == Term::Return,
    ensures ({
        let a = arr3();
        run_fn(p, 0, fr3(Val::Unit, a, Val::Unit), 1)
            == Some((fr3(Val::Int(3), a, Val::Shr(Box::new(a))), Seq::<Event>::empty(), 3nat))
    }),
{
    hide(run_from);
    hide(exec_stmts);
    hide(exec_stmt);
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    let e = Seq::<Event>::empty();
    let a = arr3();
    let (fr, fb, fc) = (fr3(Val::Unit, a, Val::Unit), fr3(Val::Unit, a, Val::Shr(Box::new(a))), fr3(Val::Int(3), a, Val::Shr(Box::new(a))));
    let ss = p.fns@[0].blocks@[0].stmts@;
    shr_ref(ss[0]);
    shr_len(ss[1]);
    assert(exec_stmts(ss, 0, fr) == (fc, e)) by {
        reveal_with_fuel(exec_stmts, 3);
        assert(e + e =~= e);
    }
    assert(run_from(p, 0, 0, fr, 1) == Some((fc, e, 3nat))) by { reveal(run_from); }
}

/// Operands whose own events are all empty have empty `ops_ev`.
proof fn ops_ev_empty(fr: Frame, ops: Seq<Operand>)
    requires forall|j: int| 0 <= j < ops.len() ==> (#[trigger] eval_op(fr, ops[j])).1 == Seq::<Event>::empty(),
    ensures ops_ev(fr, ops) == Seq::<Event>::empty(),
    decreases ops.len(),
{
    if ops.len() > 0 {
        let d = ops.drop_last();
        assert forall|j: int| 0 <= j < d.len() implies (#[trigger] eval_op(fr, d[j])).1 == Seq::<Event>::empty() by {
            assert(d[j] == ops[j]);
        }
        ops_ev_empty(fr, d);
        assert(eval_op(fr, ops[ops.len() - 1]).1 == Seq::<Event>::empty());
        assert(Seq::<Event>::empty() + Seq::<Event>::empty() =~= Seq::<Event>::empty());
    }
}

/// `bb0: _0 = k(args) -> bb1`, `bb1: return`.
pub open spec fn intr_prog(p: Program, k: Intrinsic) -> bool {
    &&& p.fns@.len() == 1
    &&& p.fns@[0].blocks@.len() == 2
    &&& p.fns@[0].blocks@[0].stmts@.len() == 0
    &&& p.fns@[0].blocks@[0].term matches Term::Call(Callee::Intr(k2), _, d, 1) && k2 == k && local(d, 0)
    &&& p.fns@[0].blocks@[1].stmts@.len() == 0
    &&& p.fns@[0].blocks@[1].term == Term::Return
}

pub open spec fn intr_args(p: Program) -> Seq<Operand> { p.fns@[0].blocks@[0].term->Call_1@ }

pub open spec fn fr2(a: Val, b: Val, slots: Seq<Val>) -> Frame { Frame { locals: seq![a, b], slots } }

/// `_0 = Vec::push(_1, const 9_u8)` with `_1 = Mut(Slot(0), [])` and slot 0 = `[1]`.
pub proof fn sanity_push_appends(p: Program)
    requires
        intr_prog(p, Intrinsic::VecPush),
        intr_args(p).len() == 2,
        intr_args(p)[0] matches Operand::Copy(a) && local(a, 1),
        intr_args(p)[1] == Operand::Const(IntTy::U8, 9),
    ensures
        run_fn(p, 0, fr2(Val::Unit, Val::Mut(slot0()), seq![Val::Arr(seq![Val::Int(1)])]), 2)
            == Some((fr2(Val::Unit, Val::Mut(slot0()), seq![Val::Arr(seq![Val::Int(1), Val::Int(9)])]), Seq::<Event>::empty(), 2nat)),
{
    hide(run_from);
    hide(exec_stmts);
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    let e = Seq::<Event>::empty();
    let fr = fr2(Val::Unit, Val::Mut(slot0()), seq![Val::Arr(seq![Val::Int(1)])]);
    let f2 = fr2(Val::Unit, Val::Mut(slot0()), seq![Val::Arr(seq![Val::Int(1), Val::Int(9)])]);
    let args = intr_args(p);
    assert(exec_stmts(p.fns@[0].blocks@[0].stmts@, 0, fr) == (fr, e)) by { reveal(exec_stmts); }
    assert(exec_stmts(p.fns@[0].blocks@[1].stmts@, 0, f2) == (f2, e)) by { reveal(exec_stmts); }
    if let Term::Call(_, _, dst, _) = p.fns@[0].blocks@[0].term {
        assert(exec_intr(Intrinsic::VecPush, fr, args, dst) == Some((f2, e, 0nat))) by {
            reveal(exec_intr);
            if let Operand::Copy(a) = args[0] { assert(read_place(fr, a).1 == e); }
            assert(eval_op(fr, args[0]).1 == e);
            assert(eval_op(fr, args[1]).1 == e);
            ops_ev_empty(fr, args);
            assert(op_vals(fr, args) =~= seq![Val::Mut(slot0()), Val::Int(9)]);
            assert(seq![Val::Int(1)] + seq![Val::Int(9)] =~= seq![Val::Int(1), Val::Int(9)]);
            assert(write_loc(fr, slot0(), Val::Arr(seq![Val::Int(1), Val::Int(9)])).slots =~= f2.slots);
            assert(grow(fr, Val::Mut(slot0()), seq![Val::Int(9)]) == Some(f2));
            assert(assign(f2, dst, Val::Unit).0.locals =~= f2.locals);
            assert(e + e + e =~= e);
        }
    }
    assert(run_from(p, 0, 1, f2, 1) == Some((f2, e, 1nat))) by { reveal(run_from); }
    assert(e + e + e =~= e);
    assert(run_from(p, 0, 0, fr, 2) == Some((f2, e, 2nat))) by { reveal(run_from); }
}

/// A push onto an `Arr` of length usize::MAX gives `None` (Rust: capacity overflow).
pub proof fn sanity_push_overflow_is_none(p: Program)
    requires
        intr_prog(p, Intrinsic::VecPush),
        intr_args(p).len() == 2,
        intr_args(p)[0] matches Operand::Copy(a) && local(a, 1),
        intr_args(p)[1] == Operand::Const(IntTy::U8, 9),
    ensures run_fn(p, 0, fr2(Val::Unit, Val::Mut(slot0()), seq![Val::Arr(Seq::new(USIZE_MAX, |i: int| Val::Unit))]), 2) is None,
{
    hide(run_from);
    hide(exec_stmts);
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    let fr = fr2(Val::Unit, Val::Mut(slot0()), seq![Val::Arr(Seq::new(USIZE_MAX, |i: int| Val::Unit))]);
    let args = intr_args(p);
    assert(exec_stmts(p.fns@[0].blocks@[0].stmts@, 0, fr) == (fr, Seq::<Event>::empty())) by { reveal(exec_stmts); }
    if let Term::Call(_, _, dst, _) = p.fns@[0].blocks@[0].term {
        assert(exec_intr(Intrinsic::VecPush, fr, args, dst) is None) by {
            reveal(exec_intr);
            assert(op_vals(fr, args) =~= seq![Val::Mut(slot0()), Val::Int(9)]);
            assert(grow(fr, Val::Mut(slot0()), seq![Val::Int(9)]) is None);
        }
    }
    assert(run_from(p, 0, 0, fr, 2) is None) by { reveal(run_from); }
}

/// `_0 = declassify(_1)` with 42 emits `Declass(42)`.
pub proof fn sanity_declassify_event(p: Program)
    requires
        intr_prog(p, Intrinsic::Declassify),
        intr_args(p).len() == 1,
        intr_args(p)[0] matches Operand::Copy(a) && local(a, 1),
    ensures
        run_fn(p, 0, fr2(Val::Unit, Val::Int(42), seq![]), 2)
            == Some((fr2(Val::Int(42), Val::Int(42), seq![]), seq![Event::Declass(Val::Int(42))], 2nat)),
{
    hide(run_from);
    hide(exec_stmts);
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    let e = Seq::<Event>::empty();
    let ev = seq![Event::Declass(Val::Int(42))];
    let fr = fr2(Val::Unit, Val::Int(42), seq![]);
    let f2 = fr2(Val::Int(42), Val::Int(42), seq![]);
    let args = intr_args(p);
    assert(exec_stmts(p.fns@[0].blocks@[0].stmts@, 0, fr) == (fr, e)) by { reveal(exec_stmts); }
    assert(exec_stmts(p.fns@[0].blocks@[1].stmts@, 0, f2) == (f2, e)) by { reveal(exec_stmts); }
    if let Term::Call(_, _, dst, _) = p.fns@[0].blocks@[0].term {
        assert(exec_intr(Intrinsic::Declassify, fr, args, dst) == Some((f2, ev, 0nat))) by {
            reveal(exec_intr);
            if let Operand::Copy(a) = args[0] { assert(read_place(fr, a) == (Val::Int(42), e)); }
            assert(eval_op(fr, args[0]).1 == e);
            ops_ev_empty(fr, args);
            assert(op_vals(fr, args) =~= seq![Val::Int(42)]);
            assert(assign(fr, dst, Val::Int(42)).0.locals =~= f2.locals);
            assert(e + ev + e =~= ev);
        }
    }
    assert(run_from(p, 0, 1, f2, 1) == Some((f2, e, 1nat))) by { reveal(run_from); }
    assert(e + ev + e =~= ev);
    assert(run_from(p, 0, 0, fr, 2) == Some((f2, ev, 2nat))) by { reveal(run_from); }
}

/// `_0 = slice_subrange(_1, 1, 10)` on a 3-element slice clamps `hi` to 3: `dst = &[2, 3]`,
/// so `len(dst) <= len(r)`; the event keeps the raw bounds.
pub proof fn sanity_subrange_clamps(p: Program)
    requires
        intr_prog(p, Intrinsic::SliceSubrange),
        intr_args(p).len() == 3,
        intr_args(p)[0] matches Operand::Copy(a) && local(a, 1),
        intr_args(p)[1] == Operand::Const(IntTy::Usize, 1),
        intr_args(p)[2] == Operand::Const(IntTy::Usize, 10),
    ensures ({
        let r = Val::Shr(Box::new(Val::Arr(seq![Val::Int(1), Val::Int(2), Val::Int(3)])));
        let d = Val::Shr(Box::new(Val::Arr(seq![Val::Int(2), Val::Int(3)])));
        run_fn(p, 0, fr2(Val::Unit, r, seq![]), 2) == Some((fr2(d, r, seq![]), seq![Event::Range(1, 10)], 2nat))
    }),
{
    hide(run_from);
    hide(exec_stmts);
    hide(exec_intr);
    hide(call_enter);
    hide(call_leave);
    let e = Seq::<Event>::empty();
    let ev = seq![Event::Range(1, 10)];
    let r = Val::Shr(Box::new(Val::Arr(seq![Val::Int(1), Val::Int(2), Val::Int(3)])));
    let d = Val::Shr(Box::new(Val::Arr(seq![Val::Int(2), Val::Int(3)])));
    let fr = fr2(Val::Unit, r, seq![]);
    let f2 = fr2(d, r, seq![]);
    let args = intr_args(p);
    assert(exec_stmts(p.fns@[0].blocks@[0].stmts@, 0, fr) == (fr, e)) by { reveal(exec_stmts); }
    assert(exec_stmts(p.fns@[0].blocks@[1].stmts@, 0, f2) == (f2, e)) by { reveal(exec_stmts); }
    if let Term::Call(_, _, dst, _) = p.fns@[0].blocks@[0].term {
        assert(exec_intr(Intrinsic::SliceSubrange, fr, args, dst) == Some((f2, ev, 0nat))) by {
            reveal(exec_intr);
            if let Operand::Copy(a) = args[0] { assert(read_place(fr, a) == (r, e)); }
            assert(eval_op(fr, args[0]).1 == e);
            assert(eval_op(fr, args[1]).1 == e);
            assert(eval_op(fr, args[2]).1 == e);
            ops_ev_empty(fr, args);
            assert(op_vals(fr, args) =~= seq![r, Val::Int(1), Val::Int(10)]);
            assert(seq![Val::Int(1), Val::Int(2), Val::Int(3)].subrange(1, 3) =~= seq![Val::Int(2), Val::Int(3)]);
            assert(assign(fr, dst, d).0.locals =~= f2.locals);
            assert(e + ev + e =~= ev);
        }
    }
    assert(run_from(p, 0, 1, f2, 1) == Some((f2, e, 1nat))) by { reveal(run_from); }
    assert(e + ev + e =~= ev);
    assert(run_from(p, 0, 0, fr, 2) == Some((f2, ev, 2nat))) by { reveal(run_from); }
}

pub proof fn sanity_fuel_zero_is_none(p: Program)
    requires
        p.fns@.len() == 1,
        p.fns@[0].blocks@.len() == 1,
        p.fns@[0].blocks@[0].stmts@.len() == 0,
        p.fns@[0].blocks@[0].term == Term::Return,
    ensures run_fn(p, 0, fr1(Val::Unit), 0) is None,
{
}

/// One `&mut u8` parameter: local 1 holds `Mut(Slot(0), [])`, whatever `args[0]` is.
pub proof fn sanity_entry_mut_param(p: Program)
    requires
        p.fns@.len() == 1,
        p.fns@[0].nargs == 1,
        p.fns@[0].locals@ == seq![Ty::Unit, Ty::Mut(Box::new(Ty::Int(IntTy::U8)))],
    ensures
        init_entry(p, 0, seq![Val::Int(5)], seq![Val::Int(6)])
            == (Frame { locals: seq![Val::Unit, Val::Mut(slot0())], slots: seq![Val::Int(6)] }),
{
    assert(init_entry(p, 0, seq![Val::Int(5)], seq![Val::Int(6)]).locals =~= seq![Val::Unit, Val::Mut(slot0())]);
}

} // verus!
