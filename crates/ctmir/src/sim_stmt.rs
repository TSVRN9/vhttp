//! The simulation, statements and a block's statement list: MIR's `exec_stmts` against core's run
//! of the block's statement images (`soff` segments), with the statement typing facts `stmt_tf`.
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
use crate::sim_pure::*;
#[allow(unused_imports)]
use crate::sim_rv::*;
#[allow(unused_imports)]
use ctcore::sem::{Event, Frame, Loc, Val};
#[allow(unused_imports)]
use ctcore::syntax as c;
use vstd::prelude::*;

verus! {

/// Any lowered rvalue: run its temps, then it evaluates as in MIR.
pub proof fn lemma_rv(m: MirCrate, b: Body, fm: Frame, fc0: Frame, rv: Rvalue, cr: c::Rvalue, pre: Seq<c::Stmt>, base: nat)
    requires lowers_rv(m, b, rv, cr, pre, base), fr_rel(fm, fc0), pure_fr(fm), fm.locals.len() <= base,
        fc0.locals.len() >= base + pre.len(), eval_rv(m, b, fm, rv) is Some, rv_tf(m, b, fm, rv),
    ensures rv_sim(fm, fc0, pre, base, cr, eval_rv(m, b, fm, rv)->Some_0),
{
    match rv {
        Rvalue::BinaryOp(op, x, y) => lemma_rv_bin(m, b, fm, fc0, op, x, y, cr, pre, base),
        Rvalue::Aggregate(ak, ops) => lemma_rv_agg(m, b, fm, fc0, ak, ops, cr, pre, base),
        Rvalue::UnaryOp(UnOp::PtrMetadata, _) | Rvalue::Ref(..) | Rvalue::Len(_) | Rvalue::Discriminant(_) | Rvalue::CopyForDeref(_) =>
            lemma_rv_place(m, b, fm, fc0, rv, cr, pre, base),
        _ => lemma_rv_one(m, b, fm, fc0, rv, cr, pre, base),
    }
}

/// A statement's typing facts (Task 6 report): the rvalue's (`rv_tf`), a shared borrow's snapshot
/// is `Mut`-free (`shr_tf`), and the store keeps unit-shaped values unit-shaped (`mws`).
pub open spec fn stmt_tf(m: MirCrate, b: Body, fm: Frame, s: Statement) -> bool {
    match s.kind {
        StatementKind::Assign(p, rv) => rv_tf(m, b, fm, rv) && shr_tf(fm, rv) && store_tf(fm, p, eval_rv(m, b, fm, rv)),
        _ => true,
    }
}

/// A store of the rvalue's value into the place keeps unit-shaped values unit-shaped.
pub open spec fn store_tf(fm: Frame, p: Place, r: Option<(Val, Seq<Event>, nat)>) -> bool {
    match (r, eval_place(fm, p)) {
        (Some((v, _, _)), Some((PRes::At(l), _))) => root_val(fm, l.root) is Some ==> mws(root_val(fm, l.root)->Some_0, l.path, v),
        _ => true,
    }
}

/// The simulation of one step: frames related and pure, the same events, steps = core statements.
pub open spec fn stmt_sim(fm2: Frame, e: Seq<Event>, k: nat, cs: Seq<c::Stmt>, fc0: Frame) -> bool {
    let (fc2, ce) = ctcore::sem::exec_stmts(cs, 0, fc0);
    &&& fr_rel(fm2, fc2) && pure_fr(fm2) && e == ce && k == cs.len() && fc2.locals.len() == fc0.locals.len()
}

proof fn lemma_assign(m: MirCrate, b: Body, nloc: nat, ncore: nat, fm: Frame, fc0: Frame, s: Statement, p: Place, rv: Rvalue, cs: Seq<c::Stmt>)
    requires
        s.kind == StatementKind::Assign(p, rv), lowers_stmt(m, b, nloc, ncore, s, cs),
        fr_rel(fm, fc0), pure_fr(fm), fm.locals.len() == nloc, fc0.locals.len() == ncore,
        eval_rv(m, b, fm, rv) is Some, eval_place(fm, p) matches Some((PRes::At(l), _)) && store(fm, l, eval_rv(m, b, fm, rv)->Some_0.0) is Some,
        stmt_tf(m, b, fm, s),
    ensures ({
        let (v, e1, k) = eval_rv(m, b, fm, rv)->Some_0;
        let (l, e2) = (eval_place(fm, p)->Some_0.0->At_0, eval_place(fm, p)->Some_0.1);
        stmt_sim(store(fm, l, v)->Some_0, e1 + e2, 1 + k, cs, fc0)
    }),
{
    let pre = cs.drop_last();
    let last = cs.last();
    let (cp, cr) = (last->Assign_0, last->Assign_1);
    let base = choose|base: nat| tmps_in(base, (cs.len() - 1) as nat, nloc, ncore) && #[trigger] lowers_rv(m, b, rv, cr, pre, base);
    let (v, e1, k) = eval_rv(m, b, fm, rv)->Some_0;
    let (l, e2) = (eval_place(fm, p)->Some_0.0->At_0, eval_place(fm, p)->Some_0.1);
    lemma_rv(m, b, fm, fc0, rv, cr, pre, base);
    lemma_rv_pure(m, b, fm, rv);
    let (fc1, _) = ctcore::sem::exec_stmts(pre, 0, fc0);
    let len = cs.len() as int;
    lemma_xs_all(cs, fc0);
    lemma_xs_split(cs, 0, len - 1, len, fc0);
    assert(cs.subrange(0, len - 1) =~= pre);
    lemma_xs_one(cs, len - 1, fc1);
    lemma_place(fm, fc1, p, cp);
    let (cv, ce1) = ctcore::sem::eval_rv(fc1, cr);
    lemma_store(fm, fc1, l, v, cv);
    let (fc2, ce) = ctcore::sem::exec_stmts(cs, 0, fc0);
    assert(fc2 == ctcore::sem::write_loc(fc1, l, cv));
    assert(ce == Seq::<Event>::empty() + (ce1 + e2));
    assert(Seq::<Event>::empty() + (ce1 + e2) == e1 + e2);
}

pub proof fn lemma_stmt(m: MirCrate, b: Body, nloc: nat, ncore: nat, fm: Frame, fc0: Frame, s: Statement, cs: Seq<c::Stmt>)
    requires lowers_stmt(m, b, nloc, ncore, s, cs), fr_rel(fm, fc0), pure_fr(fm), fm.locals.len() == nloc, fc0.locals.len() == ncore,
        exec_stmt(m, b, fm, s) is Some, stmt_tf(m, b, fm, s),
    ensures ({
        let (fm2, e, k) = exec_stmt(m, b, fm, s)->Some_0;
        stmt_sim(fm2, e, k, cs, fc0) && fm2.locals.len() == nloc
    }),
{
    reveal(exec_stmt);
    match s.kind {
        StatementKind::Assign(p, rv) => {
            lemma_assign(m, b, nloc, ncore, fm, fc0, s, p, rv, cs);
        },
        _ => {},
    }
}

/// The statement typing facts along MIR's run of the first `n` statements.
pub open spec fn stmts_tf(m: MirCrate, b: Body, fm: Frame, ss: Seq<Statement>, n: nat) -> bool
    decreases n,
{
    n == 0 || n > ss.len() || (stmts_tf(m, b, fm, ss, (n - 1) as nat)
        && (exec_stmts(m, b, fm, ss, (n - 1) as nat) matches Some((f1, _, _)) ==> stmt_tf(m, b, f1, ss[n - 1])))
}

/// A block's statements are lowered one after another into `cs`.
pub open spec fn ss_rel(m: MirCrate, b: Body, nloc: nat, ncore: nat, ss: Seq<Statement>, cs: Seq<c::Stmt>) -> bool {
    &&& soff(m, ss, ss.len()) <= cs.len()
    &&& forall|i: int| 0 <= i < ss.len() ==> lowers_stmt(m, b, nloc, ncore, #[trigger] ss[i], cs.subrange(soff(m, ss, i as nat) as int, soff(m, ss, (i + 1) as nat) as int))
}

pub proof fn lemma_soff_mono(m: MirCrate, ss: Seq<Statement>, i: nat, j: nat)
    requires i <= j <= ss.len(),
    ensures soff(m, ss, i) <= soff(m, ss, j),
    decreases j - i,
{
    if i < j { lemma_soff_mono(m, ss, i, (j - 1) as nat); }
}

pub proof fn lemma_stmts(m: MirCrate, b: Body, nloc: nat, ncore: nat, fm: Frame, fc0: Frame, ss: Seq<Statement>, cs: Seq<c::Stmt>, n: nat)
    requires ss_rel(m, b, nloc, ncore, ss, cs), n <= ss.len(), fr_rel(fm, fc0), pure_fr(fm), fm.locals.len() == nloc, fc0.locals.len() == ncore,
        exec_stmts(m, b, fm, ss, n) is Some, stmts_tf(m, b, fm, ss, n),
    ensures ({
        let (fm2, e, k) = exec_stmts(m, b, fm, ss, n)->Some_0;
        let (fc2, ce) = xs(cs, 0, soff(m, ss, n) as int, fc0);
        &&& fr_rel(fm2, fc2) && pure_fr(fm2) && e == ce && k == soff(m, ss, n)
        &&& fc2.locals.len() == ncore && fm2.locals.len() == nloc
    }),
    decreases n,
{
    hide(lowers_stmt);
    hide(exec_stmt);
    if n == 0 {
        lemma_xs_empty(cs, 0, fc0);
    } else {
        let k = (n - 1) as nat;
        lemma_stmts(m, b, nloc, ncore, fm, fc0, ss, cs, k);
        lemma_soff_mono(m, ss, n, ss.len());
        let (fm1, e1, s1) = exec_stmts(m, b, fm, ss, k)->Some_0;
        let (lo, hi) = (soff(m, ss, k), soff(m, ss, n));
        let (fc1, ce1) = xs(cs, 0, lo as int, fc0);
        let seg = cs.subrange(lo as int, hi as int);
        assert(lowers_stmt(m, b, nloc, ncore, ss[k as int], seg));
        lemma_stmt(m, b, nloc, ncore, fm1, fc1, ss[k as int], seg);
        lemma_xs_split(cs, 0, lo as int, hi as int, fc0);
    }
}

} // verus!
