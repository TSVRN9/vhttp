//! The simulation, operands: an operand's image (a place copy, or a constant's temps) and operand
//! lists, whose temps run one after another before the statement that reads them.
#[allow(unused_imports)]
use crate::mir::*;
#[allow(unused_imports)]
use crate::rel::*;
#[allow(unused_imports)]
use crate::sem::*;
#[allow(unused_imports)]
use crate::sim::*;
#[allow(unused_imports)]
use crate::sim_const::*;
#[allow(unused_imports)]
use crate::sim_exec::*;
#[allow(unused_imports)]
use ctcore::sem::{Event, Frame, Val};
#[allow(unused_imports)]
use ctcore::syntax as c;
use vstd::prelude::*;

verus! {

/// After its temps ran, operand image `y` of `x` is ready at `g`: a constant's value is in its temps
/// `lo..hi`; a place copy reads the same place.
pub open spec fn op_good(m: MirCrate, x: Operand, y: c::Operand, lo: nat, hi: nat, g: Frame) -> bool {
    match x {
        Operand::Copy(p) => y is Copy && y->Copy_0.local == p.local && projs_rel(p.projection@, y->Copy_0.proj@),
        Operand::Move(p) => y is Copy && y->Copy_0.local == p.local && projs_rel(p.projection@, y->Copy_0.proj@),
        Operand::Constant(k) => const_val(m, k) is Some && dep(y, lo, hi) && vr(const_val(m, k)->Some_0.0, ctcore::sem::eval_op(g, y).0)
            && ctcore::sem::eval_op(g, y).1 == Seq::<Event>::empty(),
        _ => false,
    }
}

pub proof fn lemma_op_good_survives(m: MirCrate, x: Operand, y: c::Operand, lo: nat, hi: nat, g1: Frame, g2: Frame, lo2: nat, hi2: nat)
    requires op_good(m, x, y, lo, hi, g1), same_out(g1, g2, lo2, hi2), g1.locals.len() >= hi, hi <= lo2 || hi2 <= lo,
    ensures op_good(m, x, y, lo, hi, g2),
{
    if x is Constant { lemma_dep_survives(y, lo, hi, g1, g2, lo2, hi2); }
}

/// One operand's image runs its temps and is then ready.
pub proof fn lemma_op_img(m: MirCrate, b: Body, x: Operand, y: c::Operand, pre: Seq<c::Stmt>, base: nat, g0: Frame)
    requires lowers_op(m, b, x, y, pre, base), g0.locals.len() >= base + pre.len(),
    ensures ({
        let (g1, e) = ctcore::sem::exec_stmts(pre, 0, g0);
        &&& e == Seq::<Event>::empty() && same_out(g0, g1, base, base + pre.len())
        &&& op_good(m, x, y, base, base + pre.len(), g1)
    }),
{
    match x {
        Operand::Constant(k) => lemma_const(m, k, y, pre, base, g0),
        _ => {},
    }
}

/// A ready operand evaluates as in MIR: an agreeing value, the same events.
pub proof fn lemma_op_eval(m: MirCrate, fm: Frame, fc: Frame, x: Operand, y: c::Operand, lo: nat, hi: nat)
    requires op_good(m, x, y, lo, hi, fc), fr_rel(fm, fc), pure_fr(fm), eval_op(m, fm, x) is Some,
    ensures vr(eval_op(m, fm, x)->Some_0.0, ctcore::sem::eval_op(fc, y).0), eval_op(m, fm, x)->Some_0.1 == ctcore::sem::eval_op(fc, y).1,
{
    match x {
        Operand::Copy(p) => lemma_read_place(fm, fc, p, y->Copy_0),
        Operand::Move(p) => lemma_read_place(fm, fc, p, y->Copy_0),
        _ => {},
    }
}

/// The first `n` operands' images, run in order.
pub proof fn lemma_ops_prefix(m: MirCrate, b: Body, os: Seq<Operand>, ys: Seq<c::Operand>, pre: Seq<c::Stmt>, base: nat, n: nat, fc0: Frame)
    requires lowers_ops(m, b, os, ys, pre, base), n <= os.len(), fc0.locals.len() >= base + pre.len(),
    ensures ({
        let (g, e) = xs(pre, 0, ops_charge(m, os, n) as int, fc0);
        &&& e == Seq::<Event>::empty() && same_out(fc0, g, base, base + ops_charge(m, os, n))
        &&& ops_charge(m, os, n) <= pre.len()
        &&& forall|i: nat| i < n ==> op_good(m, #[trigger] os[i as int], ys[i as int], base + ops_charge(m, os, i), base + ops_charge(m, os, i + 1), g)
    }),
    decreases n,
{
    hide(op_good);
    hide(lowers_op);
    hide(lowers_ops);
    if n == 0 {
        lemma_xs_empty(pre, 0, fc0);
    } else {
        let k = (n - 1) as nat;
        lemma_ops_prefix(m, b, os, ys, pre, base, k, fc0);
        lemma_ops_at(m, b, os, ys, pre, base, k);
        lemma_charge_mono(m, os, n, os.len());
        let (lo, hi) = (ops_charge(m, os, k), ops_charge(m, os, n));
        let (g1, e1) = xs(pre, 0, lo as int, fc0);
        lemma_xs_split(pre, 0, lo as int, hi as int, fc0);
        lemma_xs_len(pre, 0, lo as int, fc0);
        let seg = pre.subrange(lo as int, hi as int);
        lemma_op_img(m, b, os[k as int], ys[k as int], seg, base + lo, g1);
        let (g2, e2) = xs(pre, lo as int, hi as int, g1);
        assert(e1 + e2 == Seq::<Event>::empty());
        lemma_same_out_trans(fc0, g1, g2, base, base + lo, base + hi);
        assert forall|i: nat| i < n implies op_good(m, #[trigger] os[i as int], ys[i as int], base + ops_charge(m, os, i), base + ops_charge(m, os, i + 1), g2) by {
            if i < k {
                lemma_charge_mono(m, os, i + 1, k);
                lemma_op_good_survives(m, os[i as int], ys[i as int], base + ops_charge(m, os, i), base + ops_charge(m, os, i + 1), g1, g2, base + lo, base + hi);
            }
        }
    }
}

proof fn lemma_ops_at(m: MirCrate, b: Body, os: Seq<Operand>, ys: Seq<c::Operand>, pre: Seq<c::Stmt>, base: nat, k: nat)
    requires lowers_ops(m, b, os, ys, pre, base), k < os.len(),
    ensures lowers_op(m, b, os[k as int], ys[k as int], pre.subrange(ops_charge(m, os, k) as int, ops_charge(m, os, k + 1) as int), base + ops_charge(m, os, k)),
        pre.len() == ops_charge(m, os, os.len()), ys.len() == os.len(),
{
}

pub proof fn lemma_charge_mono(m: MirCrate, os: Seq<Operand>, j: nat, n: nat)
    requires j <= n <= os.len(),
    ensures ops_charge(m, os, j) <= ops_charge(m, os, n),
    decreases n - j,
{
    if j < n { lemma_charge_mono(m, os, j, (n - 1) as nat); }
}

/// Ready operands evaluate as MIR's `eval_ops`: agreeing values, the same events, and the temps
/// are the constant charges.
pub proof fn lemma_ops_eval(m: MirCrate, fm: Frame, fc: Frame, os: Seq<Operand>, ys: Seq<c::Operand>, base: nat, n: nat)
    requires
        fr_rel(fm, fc), pure_fr(fm), n <= os.len(), ys.len() == os.len(), eval_ops(m, fm, os, n) is Some,
        forall|i: nat| i < n ==> op_good(m, #[trigger] os[i as int], ys[i as int], base + ops_charge(m, os, i), base + ops_charge(m, os, i + 1), fc),
    ensures ({
        let (vs, e, k) = eval_ops(m, fm, os, n)->Some_0;
        &&& vrs(vs, ctcore::sem::op_vals(fc, ys.subrange(0, n as int)))
        &&& e == ctcore::sem::ops_ev(fc, ys.subrange(0, n as int))
        &&& k == ops_charge(m, os, n)
    }),
    decreases n,
{
    if n > 0 {
        let k = (n - 1) as nat;
        lemma_ops_eval(m, fm, fc, os, ys, base, k);
        assert(op_good(m, os[k as int], ys[k as int], base + ops_charge(m, os, k), base + ops_charge(m, os, n), fc));
        lemma_op_eval(m, fm, fc, os[k as int], ys[k as int], base + ops_charge(m, os, k), base + ops_charge(m, os, n));
        let yn = ys.subrange(0, n as int);
        assert(yn.drop_last() =~= ys.subrange(0, k as int));
        assert(yn.last() == ys[k as int]);
        let (vs1, _, _) = eval_ops(m, fm, os, k)->Some_0;
        let (v, _, _) = eval_op(m, fm, os[k as int])->Some_0;
        let cvs = ctcore::sem::op_vals(fc, yn);
        assert forall|i: int| 0 <= i < n implies vr(#[trigger] vs1.push(v)[i], cvs[i]) by {
            if i < k { assert(ctcore::sem::op_vals(fc, ys.subrange(0, k as int))[i] == cvs[i]); }
        }
        if let Operand::Constant(c0) = os[k as int] {} else {}
    }
}

/// A lowered operand list: run its temps, then its values and events are MIR's.
pub proof fn lemma_ops(m: MirCrate, b: Body, fm: Frame, fc0: Frame, os: Seq<Operand>, ys: Seq<c::Operand>, pre: Seq<c::Stmt>, base: nat)
    requires lowers_ops(m, b, os, ys, pre, base), fr_rel(fm, fc0), pure_fr(fm), fm.locals.len() <= base,
        fc0.locals.len() >= base + pre.len(), eval_ops(m, fm, os, os.len()) is Some,
    ensures ({
        let (fc1, e0) = ctcore::sem::exec_stmts(pre, 0, fc0);
        let (vs, e, k) = eval_ops(m, fm, os, os.len())->Some_0;
        &&& e0 == Seq::<Event>::empty() && same_out(fc0, fc1, base, base + pre.len()) && fr_rel(fm, fc1)
        &&& vrs(vs, ctcore::sem::op_vals(fc1, ys)) && e == ctcore::sem::ops_ev(fc1, ys) && k == pre.len()
    }),
{
    lemma_ops_prefix(m, b, os, ys, pre, base, os.len(), fc0);
    lemma_xs_all(pre, fc0);
    let (fc1, _) = ctcore::sem::exec_stmts(pre, 0, fc0);
    lemma_same_out_rel(fm, fc0, fc1, base, base + pre.len());
    lemma_ops_eval(m, fm, fc1, os, ys, base, os.len());
    assert(ys.subrange(0, os.len() as int) =~= ys);
}

} // verus!
