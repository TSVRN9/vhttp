//! The simulation, core-side helpers: running a slice of a core block's statements, the temps a
//! constant's image assigns, and the operands that read only those temps.
#[allow(unused_imports)]
use crate::sim::*;
#[allow(unused_imports)]
use ctcore::sem::{Event, Frame, Val};
#[allow(unused_imports)]
use ctcore::syntax as c;
use vstd::prelude::*;

verus! {

/// Core's statements `ss[lo..hi]` from `fr`.
pub open spec fn xs(ss: Seq<c::Stmt>, lo: int, hi: int, fr: Frame) -> (Frame, Seq<Event>) {
    ctcore::sem::exec_stmts(ss.subrange(lo, hi), 0, fr)
}

proof fn lemma_exec_drop(s: Seq<c::Stmt>, j: nat, f: Frame)
    requires j <= s.len(),
    ensures ctcore::sem::exec_stmts(s, j, f) == ctcore::sem::exec_stmts(s.subrange(j as int, s.len() as int), 0, f),
    decreases s.len() - j,
{
    let s2 = s.subrange(j as int, s.len() as int);
    if j < s.len() {
        let (f1, _) = ctcore::sem::exec_stmt(f, s[j as int]);
        lemma_exec_drop(s, j + 1, f1);
        lemma_exec_drop(s2, 1, f1);
        assert(s2.subrange(1, s2.len() as int) =~= s.subrange((j + 1) as int, s.len() as int));
        assert(s2[0] == s[j as int]);
    }
}

proof fn lemma_exec_take(s: Seq<c::Stmt>, k: nat, j: nat, f: Frame)
    requires k <= j <= s.len(),
    ensures ({
        let (f1, e1) = ctcore::sem::exec_stmts(s.subrange(0, j as int), k, f);
        let (f2, e2) = ctcore::sem::exec_stmts(s, j, f1);
        ctcore::sem::exec_stmts(s, k, f) == (f2, e1 + e2)
    }),
    decreases j - k,
{
    let t = s.subrange(0, j as int);
    if k == j {
        let (f2, e2) = ctcore::sem::exec_stmts(s, j, f);
        assert(Seq::<Event>::empty() + e2 == e2);
    } else {
        let (g, e) = ctcore::sem::exec_stmt(f, s[k as int]);
        assert(t[k as int] == s[k as int]);
        lemma_exec_take(s, k + 1, j, g);
        let (f1, e1) = ctcore::sem::exec_stmts(t, k + 1, g);
        let (f2, e2) = ctcore::sem::exec_stmts(s, j, f1);
        assert(e + (e1 + e2) == (e + e1) + e2);
    }
}

pub proof fn lemma_xs_split(ss: Seq<c::Stmt>, lo: int, mid: int, hi: int, fr: Frame)
    requires 0 <= lo <= mid <= hi <= ss.len(),
    ensures ({
        let (f1, e1) = xs(ss, lo, mid, fr);
        let (f2, e2) = xs(ss, mid, hi, f1);
        xs(ss, lo, hi, fr) == (f2, e1 + e2)
    }),
{
    let s = ss.subrange(lo, hi);
    let j = (mid - lo) as nat;
    lemma_exec_take(s, 0, j, fr);
    assert(s.subrange(0, j as int) =~= ss.subrange(lo, mid));
    let (f1, _) = xs(ss, lo, mid, fr);
    lemma_exec_drop(s, j, f1);
    assert(s.subrange(j as int, s.len() as int) =~= ss.subrange(mid, hi));
}

pub proof fn lemma_xs_one(ss: Seq<c::Stmt>, i: int, fr: Frame)
    requires 0 <= i < ss.len(),
    ensures xs(ss, i, i + 1, fr) == ctcore::sem::exec_stmt(fr, ss[i]),
{
    let s = ss.subrange(i, i + 1);
    assert(s[0] == ss[i]);
    let (f1, e1) = ctcore::sem::exec_stmt(fr, ss[i]);
    assert(ctcore::sem::exec_stmts(s, 1, f1) == (f1, Seq::<Event>::empty()));
    assert(e1 + Seq::<Event>::empty() == e1);
}

pub proof fn lemma_xs_empty(ss: Seq<c::Stmt>, i: int, fr: Frame)
    requires 0 <= i <= ss.len(),
    ensures xs(ss, i, i, fr) == (fr, Seq::<Event>::empty()),
{
}

pub proof fn lemma_xs_all(ss: Seq<c::Stmt>, fr: Frame)
    ensures xs(ss, 0, ss.len() as int, fr) == ctcore::sem::exec_stmts(ss, 0, fr),
{
    assert(ss.subrange(0, ss.len() as int) =~= ss);
}

/// The assignment of a whole local (a temp).
pub proof fn lemma_tmp_assign(fr: Frame, s: c::Stmt, x: nat)
    requires s is Assign, s->Assign_0.local == x, s->Assign_0.proj@.len() == 0, x < fr.locals.len(),
    ensures ctcore::sem::exec_stmt(fr, s) == (
        Frame { locals: fr.locals.update(x as int, ctcore::sem::eval_rv(fr, s->Assign_1).0), slots: fr.slots },
        ctcore::sem::eval_rv(fr, s->Assign_1).1),
{
    let pl = s->Assign_0;
    let (v, e1) = ctcore::sem::eval_rv(fr, s->Assign_1);
    assert(ctcore::sem::place_walk(fr, pl) == (ctcore::sem::Cur::L(ctcore::sem::local_loc(x)), Seq::<Event>::empty()));
    assert(e1 + Seq::<Event>::empty() == e1);
}

/// Core statements keep the frame's shape.
pub proof fn lemma_stmt_len(fr: Frame, s: c::Stmt)
    ensures ctcore::sem::exec_stmt(fr, s).0.locals.len() == fr.locals.len(), ctcore::sem::exec_stmt(fr, s).0.slots.len() == fr.slots.len(),
{
}

pub proof fn lemma_stmts_len(ss: Seq<c::Stmt>, k: nat, fr: Frame)
    requires k <= ss.len(),
    ensures ctcore::sem::exec_stmts(ss, k, fr).0.locals.len() == fr.locals.len(), ctcore::sem::exec_stmts(ss, k, fr).0.slots.len() == fr.slots.len(),
    decreases ss.len() - k,
{
    if k < ss.len() {
        lemma_stmt_len(fr, ss[k as int]);
        lemma_stmts_len(ss, k + 1, ctcore::sem::exec_stmt(fr, ss[k as int]).0);
    }
}

pub proof fn lemma_xs_len(ss: Seq<c::Stmt>, lo: int, hi: int, fr: Frame)
    requires 0 <= lo <= hi <= ss.len(),
    ensures xs(ss, lo, hi, fr).0.locals.len() == fr.locals.len(), xs(ss, lo, hi, fr).0.slots.len() == fr.slots.len(),
{
    lemma_stmts_len(ss.subrange(lo, hi), 0, fr);
}

// ------------------------------------------------------------------ frames that differ only at temps

/// `f1` is `f0` except at locals `lo..hi`.
pub open spec fn same_out(f0: Frame, f1: Frame, lo: nat, hi: nat) -> bool {
    &&& f1.locals.len() == f0.locals.len() && f1.slots == f0.slots
    &&& forall|i: int| 0 <= i < f0.locals.len() && !(lo <= i < hi) ==> #[trigger] f1.locals[i] == f0.locals[i]
}

pub proof fn lemma_same_out_trans(f0: Frame, f1: Frame, f2: Frame, lo: nat, mid: nat, hi: nat)
    requires same_out(f0, f1, lo, mid), same_out(f1, f2, mid, hi), lo <= mid <= hi,
    ensures same_out(f0, f2, lo, hi),
{
    assert forall|i: int| 0 <= i < f0.locals.len() && !(lo <= i < hi) implies #[trigger] f2.locals[i] == f0.locals[i] by {
        assert(f2.locals[i] == f1.locals[i]);
    }
}

/// A frame changed only at temps at or after the MIR locals keeps the frame relation.
pub proof fn lemma_same_out_rel(fm: Frame, f0: Frame, f1: Frame, lo: nat, hi: nat)
    requires fr_rel(fm, f0), same_out(f0, f1, lo, hi), fm.locals.len() <= lo,
    ensures fr_rel(fm, f1),
{
    assert forall|i: int| 0 <= i < fm.locals.len() implies #[trigger] fm.locals[i] == f1.locals[i] by {
        assert(f1.locals[i] == f0.locals[i]);
    }
}

/// An operand that reads only temps `lo..hi` (a whole temp) or nothing.
pub open spec fn dep(y: c::Operand, lo: nat, hi: nat) -> bool {
    match y {
        c::Operand::Copy(q) => q.proj@.len() == 0 && lo <= q.local < hi,
        _ => true,
    }
}

pub proof fn lemma_dep_eval(y: c::Operand, lo: nat, hi: nat, g1: Frame, g2: Frame)
    requires dep(y, lo, hi), g1.locals.len() >= hi, g2.locals.len() >= hi,
        forall|i: int| lo <= i < hi ==> #[trigger] g1.locals[i] == g2.locals[i],
    ensures ctcore::sem::eval_op(g1, y) == ctcore::sem::eval_op(g2, y),
{
    if let c::Operand::Copy(q) = y {
        assert(ctcore::sem::place_walk(g1, q) == (ctcore::sem::Cur::L(ctcore::sem::local_loc(q.local as nat)), Seq::<Event>::empty()));
        assert(ctcore::sem::place_walk(g2, q) == (ctcore::sem::Cur::L(ctcore::sem::local_loc(q.local as nat)), Seq::<Event>::empty()));
        assert(g1.locals[q.local as int] == g2.locals[q.local as int]);
    }
}

/// A `dep` operand survives a later change at other temps.
pub proof fn lemma_dep_survives(y: c::Operand, lo: nat, hi: nat, g1: Frame, g2: Frame, lo2: nat, hi2: nat)
    requires dep(y, lo, hi), same_out(g1, g2, lo2, hi2), g1.locals.len() >= hi, hi <= lo2 || hi2 <= lo,
    ensures ctcore::sem::eval_op(g1, y) == ctcore::sem::eval_op(g2, y),
{
    assert forall|i: int| lo <= i < hi implies #[trigger] g1.locals[i] == g2.locals[i] by {}
    lemma_dep_eval(y, lo, hi, g1, g2);
}

/// A whole temp read: its value, no events.
pub proof fn lemma_eval_tmp(fr: Frame, y: c::Operand, x: nat)
    requires rel_is_tmp(y, x), x < fr.locals.len(),
    ensures ctcore::sem::eval_op(fr, y) == (fr.locals[x as int], Seq::<Event>::empty()),
{
    let q = y->Copy_0;
    assert(ctcore::sem::place_walk(fr, q) == (ctcore::sem::Cur::L(ctcore::sem::local_loc(x)), Seq::<Event>::empty()));
}

pub open spec fn rel_is_tmp(y: c::Operand, x: nat) -> bool { crate::rel::is_tmp(y, x) }

/// Operands that read only whole temps or nothing emit no events.
pub proof fn lemma_ops_ev_dep(fr: Frame, ops: Seq<c::Operand>, lo: nat, hi: nat)
    requires forall|i: int| 0 <= i < ops.len() ==> dep(#[trigger] ops[i], lo, hi),
    ensures ctcore::sem::ops_ev(fr, ops) == Seq::<Event>::empty(),
    decreases ops.len(),
{
    if ops.len() > 0 {
        lemma_ops_ev_dep(fr, ops.drop_last(), lo, hi);
        let y = ops.last();
        assert(dep(y, lo, hi));
        if let c::Operand::Copy(q) = y {
            assert(ctcore::sem::place_walk(fr, q) == (ctcore::sem::Cur::L(ctcore::sem::local_loc(q.local as nat)), Seq::<Event>::empty()));
        }
        assert(Seq::<Event>::empty() + Seq::<Event>::empty() == Seq::<Event>::empty());
    }
}

/// The result of an image `(y, pre)` at temps `base..`: run from `fc0`, only the temps change and
/// nothing is emitted, and `y` (reading only those temps) agrees with the MIR value `v`.
pub open spec fn img_ok(pre: Seq<c::Stmt>, base: nat, y: c::Operand, v: Val, fc0: Frame) -> bool {
    let (fc1, e) = ctcore::sem::exec_stmts(pre, 0, fc0);
    &&& e == Seq::<Event>::empty()
    &&& same_out(fc0, fc1, base, base + pre.len())
    &&& dep(y, base, base + pre.len())
    &&& v == ctcore::sem::eval_op(fc1, y).0 && ctcore::sem::eval_op(fc1, y).1 == Seq::<Event>::empty()
}

/// Images one after another (an ADT constant's fields, or an operand list): run in order, each
/// image's operand agrees with its value at the end.
pub proof fn lemma_imgs(pre: Seq<c::Stmt>, base: nat, ops: Seq<c::Operand>, cnt: spec_fn(nat) -> nat, val: spec_fn(nat) -> Val, n: nat, fc0: Frame)
    requires
        cnt(0) == 0, forall|i: nat| i < n ==> #[trigger] cnt(i) <= cnt(i + 1), cnt(n) <= pre.len(), ops.len() >= n,
        fc0.locals.len() >= base + cnt(n),
        forall|i: nat, g: Frame| i < n && g.locals.len() == fc0.locals.len()
            ==> #[trigger] img_ok(pre.subrange(cnt(i) as int, cnt(i + 1) as int), base + cnt(i), ops[i as int], val(i), g),
    ensures ({
        let (g, e) = xs(pre, 0, cnt(n) as int, fc0);
        &&& e == Seq::<Event>::empty()
        &&& same_out(fc0, g, base, base + cnt(n))
        &&& forall|i: nat| i < n ==> dep(ops[i as int], base + cnt(i), base + cnt(i + 1))
            && val(i) == ctcore::sem::eval_op(g, #[trigger] ops[i as int]).0 && ctcore::sem::eval_op(g, ops[i as int]).1 == Seq::<Event>::empty()
    }),
    decreases n,
{
    if n == 0 {
        lemma_xs_empty(pre, 0, fc0);
    } else {
        let k = (n - 1) as nat;
        lemma_imgs(pre, base, ops, cnt, val, k, fc0);
        assert(cnt(k) <= cnt(n));
        let (g1, e1) = xs(pre, 0, cnt(k) as int, fc0);
        lemma_xs_split(pre, 0, cnt(k) as int, cnt(n) as int, fc0);
        let seg = pre.subrange(cnt(k) as int, cnt(n) as int);
        assert(img_ok(seg, base + cnt(k), ops[k as int], val(k), g1));
        let (g2, e2) = xs(pre, cnt(k) as int, cnt(n) as int, g1);
        assert(e1 + e2 == Seq::<Event>::empty());
        lemma_same_out_trans(fc0, g1, g2, base, base + cnt(k), base + cnt(n));
        assert forall|i: nat| i < n implies dep(ops[i as int], base + cnt(i), base + cnt(i + 1))
            && val(i) == ctcore::sem::eval_op(g2, #[trigger] ops[i as int]).0 && ctcore::sem::eval_op(g2, ops[i as int]).1 == Seq::<Event>::empty() by {
            if i < k {
                lemma_cnt_mono(cnt, i + 1, k);
                lemma_dep_survives(ops[i as int], base + cnt(i), base + cnt(i + 1), g1, g2, base + cnt(k), base + cnt(n));
            }
        };
    }
}

pub proof fn lemma_cnt_mono(cnt: spec_fn(nat) -> nat, j: nat, n: nat)
    requires j <= n, forall|i: nat| i < n ==> #[trigger] cnt(i) <= cnt(i + 1),
    ensures cnt(j) <= cnt(n),
    decreases n - j,
{
    if j < n { lemma_cnt_mono(cnt, j, (n - 1) as nat); assert(cnt((n - 1) as nat) <= cnt(n)); }
}

} // verus!
