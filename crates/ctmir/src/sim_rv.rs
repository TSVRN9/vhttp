//! The simulation, rvalues: on equal frames, a lowered rvalue's temps and image evaluate to MIR's
//! value with MIR's events.
#[allow(unused_imports)]
use crate::mir::*;
#[allow(unused_imports)]
use crate::rel::*;
#[allow(unused_imports)]
use crate::sem::*;
#[allow(unused_imports)]
use crate::sim::*;
#[allow(unused_imports)]
use crate::sim_exec::*;
#[allow(unused_imports)]
use crate::sim_op::*;
#[allow(unused_imports)]
use ctcore::sem::{Event, Frame, Val};
#[allow(unused_imports)]
use ctcore::syntax as c;
use vstd::prelude::*;

verus! {

/// The outcome of a core statement image's temps and rvalue against MIR's rvalue.
pub open spec fn rv_sim(fm: Frame, fc0: Frame, pre: Seq<c::Stmt>, base: nat, cr: c::Rvalue, r: (Val, Seq<Event>, nat)) -> bool {
    let (fc1, e0) = ctcore::sem::exec_stmts(pre, 0, fc0);
    &&& e0 == Seq::<Event>::empty() && same_out(fc0, fc1, base, base + pre.len()) && fr_rel(fm, fc1)
    &&& r.0 == ctcore::sem::eval_rv(fc1, cr).0 && r.1 == ctcore::sem::eval_rv(fc1, cr).1 && r.2 == pre.len()
}

/// A single operand's image: run its temps, then it evaluates as in MIR.
pub proof fn lemma_one(m: MirCrate, b: Body, fm: Frame, fc0: Frame, x: Operand, y: c::Operand, pre: Seq<c::Stmt>, base: nat)
    requires lowers_op(m, b, x, y, pre, base), fr_rel(fm, fc0), fm.locals.len() <= base,
        fc0.locals.len() >= base + pre.len(), eval_op(m, fm, x) is Some,
    ensures ({
        let (fc1, e0) = ctcore::sem::exec_stmts(pre, 0, fc0);
        let (v, e, k) = eval_op(m, fm, x)->Some_0;
        &&& e0 == Seq::<Event>::empty() && same_out(fc0, fc1, base, base + pre.len()) && fr_rel(fm, fc1)
        &&& v == ctcore::sem::eval_op(fc1, y).0 && e == ctcore::sem::eval_op(fc1, y).1 && k == pre.len()
    }),
{
    lemma_op_img(m, b, x, y, pre, base, fc0);
    let (fc1, _) = ctcore::sem::exec_stmts(pre, 0, fc0);
    lemma_same_out_rel(fm, fc0, fc1, base, base + pre.len());
    lemma_op_eval(m, fm, fc1, x, y, base, base + pre.len());
}

/// Two operands' images, the first's temps first.
proof fn lemma_two(m: MirCrate, b: Body, fm: Frame, fc0: Frame, x: Operand, y: Operand, cx: c::Operand, cy: c::Operand, pre: Seq<c::Stmt>, base: nat)
    requires two_ops(m, b, x, y, cx, cy, pre, base), fr_rel(fm, fc0), fm.locals.len() <= base,
        fc0.locals.len() >= base + pre.len(), eval_op(m, fm, x) is Some, eval_op(m, fm, y) is Some,
    ensures ({
        let (fc1, e0) = ctcore::sem::exec_stmts(pre, 0, fc0);
        let (vx, ex, kx) = eval_op(m, fm, x)->Some_0;
        let (vy, ey, ky) = eval_op(m, fm, y)->Some_0;
        &&& e0 == Seq::<Event>::empty() && same_out(fc0, fc1, base, base + pre.len()) && fr_rel(fm, fc1)
        &&& vx == ctcore::sem::eval_op(fc1, cx).0 && ex == ctcore::sem::eval_op(fc1, cx).1
        &&& vy == ctcore::sem::eval_op(fc1, cy).0 && ey == ctcore::sem::eval_op(fc1, cy).1 && kx + ky == pre.len()
    }),
{
    let n = op_charge(m, x);
    let len = pre.len() as int;
    lemma_xs_all(pre, fc0);
    lemma_xs_split(pre, 0, n as int, len, fc0);
    let (g1, _) = xs(pre, 0, n as int, fc0);
    lemma_op_img(m, b, x, cx, pre.subrange(0, n as int), base, fc0);
    lemma_xs_len(pre, 0, n as int, fc0);
    lemma_op_img(m, b, y, cy, pre.subrange(n as int, len), base + n, g1);
    let (fc1, _) = ctcore::sem::exec_stmts(pre, 0, fc0);
    lemma_op_good_survives(m, x, cx, base, base + n, g1, fc1, base + n, base + pre.len());
    lemma_same_out_trans(fc0, g1, fc1, base, base + n, base + pre.len());
    lemma_same_out_rel(fm, fc0, fc1, base, base + pre.len());
    lemma_op_eval(m, fm, fc1, x, cx, base, base + n);
    lemma_op_eval(m, fm, fc1, y, cy, base + n, base + pre.len());
    assert(Seq::<Event>::empty() + Seq::<Event>::empty() == Seq::<Event>::empty());
}

/// `bin_ev` is core's `op_ev` at the mapped operator.
pub proof fn lemma_bin_ev(op: BinOp, a: u128, c0: u128)
    requires core_bin(op) is Some,
    ensures bin_ev(op, a, c0) == ctcore::sem::op_ev(core_bin(op)->Some_0, a, c0),
{
}

pub proof fn lemma_rv_bin(m: MirCrate, b: Body, fm: Frame, fc0: Frame, op: BinOp, x: Operand, y: Operand, cr: c::Rvalue, pre: Seq<c::Stmt>, base: nat)
    requires lowers_rv(m, b, Rvalue::BinaryOp(op, x, y), cr, pre, base), fr_rel(fm, fc0), fm.locals.len() <= base,
        fc0.locals.len() >= base + pre.len(), rv_bin(m, b, fm, op, x, y) is Some,
    ensures rv_sim(fm, fc0, pre, base, cr, rv_bin(m, b, fm, op, x, y)->Some_0),
{
    lemma_two(m, b, fm, fc0, x, y, cr->Bin_2, cr->Bin_3, pre, base);
    let (a, c0) = (eval_op(m, fm, x)->Some_0.0->Int_0, eval_op(m, fm, y)->Some_0.0->Int_0);
    lemma_bin_ev(op, a, c0);
}

/// Rvalues that read one place (no temps).
pub proof fn lemma_rv_place(m: MirCrate, b: Body, fm: Frame, fc0: Frame, rv: Rvalue, cr: c::Rvalue, pre: Seq<c::Stmt>, base: nat)
    requires lowers_rv(m, b, rv, cr, pre, base), fr_rel(fm, fc0), eval_rv(m, b, fm, rv) is Some,
        rv is Ref || rv is Len || rv is Discriminant || rv is CopyForDeref || rv matches Rvalue::UnaryOp(UnOp::PtrMetadata, _),
    ensures rv_sim(fm, fc0, pre, base, cr, eval_rv(m, b, fm, rv)->Some_0),
{
    assert(pre.len() == 0);
    match rv {
        Rvalue::Ref(_, bk, p) => {
            match bk {
                BorrowKind::Shared => lemma_read_place(fm, fc0, p, cr->RefShr_0),
                _ => lemma_place(fm, fc0, p, cr->RefMut_0),
            }
        },
        Rvalue::Len(p) => {
            lemma_read_place(fm, fc0, p, cr->Len_0);
        },
        Rvalue::CopyForDeref(p) => lemma_read_place(fm, fc0, p, cr->Use_0->Copy_0),
        Rvalue::Discriminant(p) => {
            lemma_read_place(fm, fc0, p, cr->Discr_0);
        },
        Rvalue::UnaryOp(_, x) => {
            let p = match x { Operand::Copy(p) => p, Operand::Move(p) => p, _ => x->Copy_0 };
            lemma_read_place(fm, fc0, p, cr->Len_0);
            if let Val::Mut(l) = read_place(fm, p)->Some_0.0 { lemma_load(fm, fc0, l); }
        },
        _ => {},
    }
}

/// Rvalues of one operand.
pub proof fn lemma_rv_one(m: MirCrate, b: Body, fm: Frame, fc0: Frame, rv: Rvalue, cr: c::Rvalue, pre: Seq<c::Stmt>, base: nat)
    requires lowers_rv(m, b, rv, cr, pre, base), fr_rel(fm, fc0), fm.locals.len() <= base,
        fc0.locals.len() >= base + pre.len(), eval_rv(m, b, fm, rv) is Some,
        rv is Use || rv is Cast || rv is Repeat || rv matches Rvalue::UnaryOp(UnOp::Not, _) || rv matches Rvalue::UnaryOp(UnOp::Neg, _),
    ensures rv_sim(fm, fc0, pre, base, cr, eval_rv(m, b, fm, rv)->Some_0),
{
    match rv {
        Rvalue::Use(x, _) => lemma_rv_use(m, b, fm, fc0, rv, x, cr, pre, base),
        Rvalue::UnaryOp(_, x) => lemma_rv_un(m, b, fm, fc0, rv, x, cr, pre, base),
        Rvalue::Cast(ck, x, _) => lemma_rv_cast(m, b, fm, fc0, rv, x, cr, pre, base),
        Rvalue::Repeat(x, _) => lemma_rv_repeat(m, b, fm, fc0, rv, x, cr, pre, base),
        _ => {},
    }
}

proof fn lemma_rv_use(m: MirCrate, b: Body, fm: Frame, fc0: Frame, rv: Rvalue, x: Operand, cr: c::Rvalue, pre: Seq<c::Stmt>, base: nat)
    requires lowers_rv(m, b, rv, cr, pre, base), fr_rel(fm, fc0), fm.locals.len() <= base,
        fc0.locals.len() >= base + pre.len(), eval_rv(m, b, fm, rv) is Some, rv is Use, rv->Use_0 == x,
    ensures rv_sim(fm, fc0, pre, base, cr, eval_rv(m, b, fm, rv)->Some_0),
{
    lemma_one(m, b, fm, fc0, x, cr->Use_0, pre, base);
}

proof fn lemma_rv_un(m: MirCrate, b: Body, fm: Frame, fc0: Frame, rv: Rvalue, x: Operand, cr: c::Rvalue, pre: Seq<c::Stmt>, base: nat)
    requires lowers_rv(m, b, rv, cr, pre, base), fr_rel(fm, fc0), fm.locals.len() <= base,
        fc0.locals.len() >= base + pre.len(), eval_rv(m, b, fm, rv) is Some,
        rv matches Rvalue::UnaryOp(UnOp::Not, _) || rv matches Rvalue::UnaryOp(UnOp::Neg, _), rv->UnaryOp_1 == x,
    ensures rv_sim(fm, fc0, pre, base, cr, eval_rv(m, b, fm, rv)->Some_0),
{
    lemma_one(m, b, fm, fc0, x, cr->Un_2, pre, base);
}

proof fn lemma_rv_cast(m: MirCrate, b: Body, fm: Frame, fc0: Frame, rv: Rvalue, x: Operand, cr: c::Rvalue, pre: Seq<c::Stmt>, base: nat)
    requires lowers_rv(m, b, rv, cr, pre, base), fr_rel(fm, fc0), fm.locals.len() <= base,
        fc0.locals.len() >= base + pre.len(), eval_rv(m, b, fm, rv) is Some, rv is Cast, rv->Cast_1 == x,
    ensures rv_sim(fm, fc0, pre, base, cr, eval_rv(m, b, fm, rv)->Some_0),
{
    if rv->Cast_0 is IntToInt { lemma_one(m, b, fm, fc0, x, cr->Cast_2, pre, base); }
    else { lemma_one(m, b, fm, fc0, x, cr->Use_0, pre, base); }
}

proof fn lemma_rv_repeat(m: MirCrate, b: Body, fm: Frame, fc0: Frame, rv: Rvalue, x: Operand, cr: c::Rvalue, pre: Seq<c::Stmt>, base: nat)
    requires lowers_rv(m, b, rv, cr, pre, base), fr_rel(fm, fc0), fm.locals.len() <= base,
        fc0.locals.len() >= base + pre.len(), eval_rv(m, b, fm, rv) is Some, rv is Repeat, rv->Repeat_0 == x,
    ensures rv_sim(fm, fc0, pre, base, cr, eval_rv(m, b, fm, rv)->Some_0),
{
    lemma_one(m, b, fm, fc0, x, cr->Repeat_0, pre, base);
    let (fc1, _) = ctcore::sem::exec_stmts(pre, 0, fc0);
    let v = eval_op(m, fm, x)->Some_0.0;
    let n = cr->Repeat_1 as nat;
    assert(Seq::new(n, |_i: int| v) =~= Seq::new(n, |_j: int| ctcore::sem::eval_op(fc1, cr->Repeat_0).0));
}

pub proof fn lemma_rv_agg(m: MirCrate, b: Body, fm: Frame, fc0: Frame, ak: AggregateKind, os: Vec<Operand>, cr: c::Rvalue, pre: Seq<c::Stmt>, base: nat)
    requires lowers_rv(m, b, Rvalue::Aggregate(ak, os), cr, pre, base), fr_rel(fm, fc0), fm.locals.len() <= base,
        fc0.locals.len() >= base + pre.len(), rv_agg(m, fm, ak, os@) is Some,
    ensures rv_sim(fm, fc0, pre, base, cr, rv_agg(m, fm, ak, os@)->Some_0),
{
    hide(lowers_ops);
    hide(eval_ops);
    lemma_ops(m, b, fm, fc0, os@, cr->Aggregate_1@, pre, base);
}

} // verus!
