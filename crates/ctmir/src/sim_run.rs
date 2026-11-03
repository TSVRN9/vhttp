//! The simulation, terminators without calls and the run: by induction on fuel, a completed MIR run
//! of a reached block whose reached blocks are call-free is matched by core's run of the image block
//! with the same trace and steps, from related frames to related frames.
#[allow(unused_imports)]
use crate::mir::*;
#[allow(unused_imports)]
use crate::policy::*;
#[allow(unused_imports)]
use crate::rel::*;
#[allow(unused_imports)]
use crate::sem::*;
#[allow(unused_imports)]
use crate::sim::*;
#[allow(unused_imports)]
use crate::sim_exec::*;
#[allow(unused_imports)]
use crate::sim_rv::*;
#[allow(unused_imports)]
use crate::sim_stmt::*;
#[allow(unused_imports)]
use ctcore::sem::{Event, Frame, Val};
#[allow(unused_imports)]
use ctcore::syntax as c;
use vstd::prelude::*;

verus! {

pub proof fn lemma_switch_target(ts: Seq<(u128, usize)>, k: nat, d: u128, ow: usize)
    requires k <= ts.len(),
    ensures ctcore::sem::switch_target(ts, k, d, ow) == match find_from(ts, |br: (u128, usize)| br.0 == d, k) {
        Some(j) => ts[j as int].1, None => ow },
    decreases ts.len() - k,
{
    if k < ts.len() && ts[k as int].0 != d { lemma_switch_target(ts, k + 1, d, ow); }
}

/// Where a core `Goto`/`Switch`/`Assert` goes from `fr`, with the events it emits.
pub open spec fn core_jump(t: c::Term, fr: Frame) -> Option<(nat, Seq<Event>)> {
    match t {
        c::Term::Goto(b2) => Some((b2 as nat, Seq::<Event>::empty())),
        c::Term::Switch(op, ts, ow) => {
            let (v, e) = ctcore::sem::eval_op(fr, op);
            Some((ctcore::sem::switch_target(ts@, 0, ctcore::sem::as_int(v), ow) as nat, e + seq![Event::Cond(ctcore::sem::as_int(v))]))
        },
        c::Term::Assert(op, exp, b2) => {
            let (v, e) = ctcore::sem::eval_op(fr, op);
            if (ctcore::sem::as_int(v) != 0) == exp { Some((b2 as nat, e + seq![Event::Cond(ctcore::sem::as_int(v))])) } else { None }
        },
        _ => None,
    }
}

pub proof fn lemma_run_from_jump(p: c::Program, f: nat, bb: nat, fc: Frame, fuel: nat)
    requires fuel > 0, f < p.fns@.len(), bb < p.fns@[f as int].blocks@.len(),
        core_jump(p.fns@[f as int].blocks@[bb as int].term, ctcore::sem::exec_stmts(p.fns@[f as int].blocks@[bb as int].stmts@, 0, fc).0) is Some,
    ensures ({
        let blk = p.fns@[f as int].blocks@[bb as int];
        let (f1, t1) = ctcore::sem::exec_stmts(blk.stmts@, 0, fc);
        let (t, e) = core_jump(blk.term, f1)->Some_0;
        ctcore::sem::run_from(p, f, bb, fc, fuel) == match ctcore::sem::run_from(p, f, t, f1, (fuel - 1) as nat) {
            Some((f2, t2, n2)) => Some((f2, t1 + e + t2, blk.stmts@.len() + 1 + n2)),
            None => None,
        }
    }),
{
    let blk = p.fns@[f as int].blocks@[bb as int];
    let (f1, t1) = ctcore::sem::exec_stmts(blk.stmts@, 0, fc);
    assert(t1 + Seq::<Event>::empty() == t1);
    match blk.term {
        c::Term::Switch(op, _, _) => {
            let (v, e) = ctcore::sem::eval_op(f1, op);
            let ce = seq![Event::Cond(ctcore::sem::as_int(v))];
            if let Some((_, t2, _)) = ctcore::sem::run_from(p, f, core_jump(blk.term, f1)->Some_0.0, f1, (fuel - 1) as nat) {
                assert(t1 + e + ce + t2 == t1 + (e + ce) + t2);
            }
        },
        c::Term::Assert(op, _, _) => {
            let (v, e) = ctcore::sem::eval_op(f1, op);
            let ce = seq![Event::Cond(ctcore::sem::as_int(v))];
            if let Some((_, t2, _)) = ctcore::sem::run_from(p, f, core_jump(blk.term, f1)->Some_0.0, f1, (fuel - 1) as nat) {
                assert(t1 + e + ce + t2 == t1 + (e + ce) + t2);
            }
        },
        _ => {},
    }
}

/// A MIR `Goto`/`SwitchInt`/`Assert` that jumps: core's image (after its temps) jumps to the same
/// block with the same events; the step count is 1 plus the temps.
pub proof fn lemma_term_jump(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, nloc: nat, ncore: nat, kind: TerminatorKind,
    pre: Seq<c::Stmt>, ct: c::Term, base: nat, f1: Frame, fcs: Frame, fuel: nat)
    requires
        lowers_term_at(m, pol, ord, b, nloc, ncore, kind, pre, ct, base), tmps_in(base, pre.len(), nloc, ncore),
        kind is Goto || kind is SwitchInt || kind is Assert,
        fr_rel(f1, fcs), pure_fr(f1), f1.locals.len() == nloc, fcs.locals.len() == ncore,
        step_term(m, cpol(pol), b, kind, f1, fuel) is Jump,
    ensures ({
        let (fct, ept) = ctcore::sem::exec_stmts(pre, 0, fcs);
        let st = step_term(m, cpol(pol), b, kind, f1, fuel);
        &&& ept == Seq::<Event>::empty() && fr_rel(f1, fct) && fct.locals.len() == ncore
        &&& st->Jump_1 == f1 && core_jump(ct, fct) == Some((st->Jump_0, st->Jump_2)) && st->Jump_3 == 1 + pre.len()
    }),
{
    match kind {
        TerminatorKind::Goto { .. } => {},
        TerminatorKind::SwitchInt { discr, targets } => {
            lemma_one(m, b, f1, fcs, discr, ct->Switch_0, pre, base);
            lemma_switch_target(targets.branches@, 0, eval_op(m, f1, discr)->Some_0.0->Int_0, targets.otherwise);
            lemma_stmts_len(pre, 0, fcs);
        },
        TerminatorKind::Assert { cond, .. } => {
            lemma_one(m, b, f1, fcs, cond, ct->Assert_0, pre, base);
            lemma_stmts_len(pre, 0, fcs);
        },
        _ => {},
    }
}

/// The reached blocks have no `Call` or `Drop` terminator (the spec's call-free fallback).
pub open spec fn call_free(b: Body, r: Seq<bool>) -> bool {
    forall|bb: int| 0 <= bb < r.len() && r[bb] ==> !((#[trigger] b.blocks@[bb]).terminator.kind is Call || b.blocks@[bb].terminator.kind is Drop)
}

/// The typing facts along MIR's run from block `bb` (call-free): each block's statements'.
pub open spec fn run_tf(m: MirCrate, pol: CallPolicy, b: Body, bb: nat, fm: Frame, fuel: nat) -> bool
    decreases fuel,
{
    fuel == 0 || bb >= b.blocks@.len() || {
        let blk = b.blocks@[bb as int];
        let n = blk.statements@.len();
        &&& stmts_tf(m, b, fm, blk.statements@, n)
        &&& exec_stmts(m, b, fm, blk.statements@, n) matches Some((f1, _, _)) ==> match step_term(m, pol, b, blk.terminator.kind, f1, fuel) {
            Step::Jump(t, f2, _, _) => run_tf(m, pol, b, t, f2, (fuel - 1) as nat),
            _ => true,
        }
    }
}

/// What a body and its image share, unpacked for one reached block.
proof fn lemma_reached(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, cb: c::Body, r: Seq<bool>, bb: nat)
    requires lowers_body(m, pol, ord, j, cb, r), bb < r.len(), r[bb as int],
    ensures ({
        let b = inst_body(m, j)->Some_0;
        let (nloc, ncore) = (b.locals@.len(), cb.locals@.len());
        let blk = b.blocks@[bb as int];
        let cblk = cb.blocks@[bb as int];
        let n = blk.statements@.len();
        let cs = cblk.stmts@;
        &&& bb < b.blocks@.len() && bb < cb.blocks@.len() && block_ok(m, cpol(pol), b, blk) && succs_in(blk.terminator.kind, marks(r))
        &&& ss_rel(m, b, nloc, ncore, blk.statements@, cs)
        &&& lowers_term(m, pol, ord, b, nloc, ncore, blk.terminator.kind, cs.subrange(soff(m, blk.statements@, n) as int, cs.len() as int), cblk.term)
    }),
{
    let b = inst_body(m, j)->Some_0;
    assert(block_rel(m, pol, ord, b, b.locals@.len(), cb.locals@.len(), r, b.blocks@[bb as int], cb.blocks@[bb as int], r[bb as int]));
}

pub open spec fn body_sim_pre(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, p: c::Program, g: nat, r: Seq<bool>) -> bool {
    &&& g < p.fns@.len() && lowers_body(m, pol, ord, j, p.fns@[g as int], r)
    &&& call_free(inst_body(m, j)->Some_0, r)
}

pub open spec fn run_ok(m: MirCrate, pol: CallPolicy, b: Body, bb: nat, fm: Frame, fuel: nat, p: c::Program, g: nat, fc: Frame) -> bool {
    run_block(m, pol, b, bb, fm, fuel) matches Out::Done(fm2, e, s) ==> (ctcore::sem::run_from(p, g, bb, fc, fuel) matches Some((fc2, ce, cn))
        && fr_rel(fm2, fc2) && e == ce && s == cn)
}

/// The run induction (call-free).
pub proof fn lemma_block(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, p: c::Program, g: nat, r: Seq<bool>, bb: nat, fm: Frame, fc: Frame, fuel: nat)
    requires body_sim_pre(m, pol, ord, j, p, g, r), bb < r.len(), r[bb as int],
        fr_rel(fm, fc), pure_fr(fm), fm.locals.len() == inst_body(m, j)->Some_0.locals@.len(), fc.locals.len() == p.fns@[g as int].locals@.len(),
        run_tf(m, cpol(pol), inst_body(m, j)->Some_0, bb, fm, fuel),
    ensures run_ok(m, cpol(pol), inst_body(m, j)->Some_0, bb, fm, fuel, p, g, fc),
    decreases fuel, 2nat,
{
    let b = inst_body(m, j)->Some_0;
    let cb = p.fns@[g as int];
    if fuel > 0 && run_block(m, cpol(pol), b, bb, fm, fuel) is Done {
        lemma_reached(m, pol, ord, j, cb, r, bb);
        assert(blk_pre_ok(m, pol, ord, j, p, g, r, bb));
        lemma_block_step(m, pol, ord, j, p, g, r, bb, fm, fc, fuel);
    }
}

pub open spec fn blk_pre_ok(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, p: c::Program, g: nat, r: Seq<bool>, bb: nat) -> bool {
    let b = inst_body(m, j)->Some_0;
    let cb = p.fns@[g as int];
    let blk = b.blocks@[bb as int];
    let cs = cb.blocks@[bb as int].stmts@;
    let n = blk.statements@.len();
    &&& bb < b.blocks@.len() && bb < cb.blocks@.len() && block_ok(m, cpol(pol), b, blk) && succs_in(blk.terminator.kind, marks(r))
    &&& ss_rel(m, b, b.locals@.len(), cb.locals@.len(), blk.statements@, cs)
    &&& lowers_term(m, pol, ord, b, b.locals@.len(), cb.locals@.len(), blk.terminator.kind, cs.subrange(soff(m, blk.statements@, n) as int, cs.len() as int), cb.blocks@[bb as int].term)
}

pub open spec fn blk_lo(m: MirCrate, b: Body, bb: nat) -> nat { soff(m, b.blocks@[bb as int].statements@, b.blocks@[bb as int].statements@.len()) }

/// The statement part of a block: MIR's statements against core's statement images; the
/// terminator's temps follow.
proof fn lemma_block_pre(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, p: c::Program, g: nat, r: Seq<bool>, bb: nat, fm: Frame, fc: Frame, fuel: nat)
    requires body_sim_pre(m, pol, ord, j, p, g, r), blk_pre_ok(m, pol, ord, j, p, g, r, bb),
        fr_rel(fm, fc), pure_fr(fm), fm.locals.len() == inst_body(m, j)->Some_0.locals@.len(), fc.locals.len() == p.fns@[g as int].locals@.len(),
        run_tf(m, cpol(pol), inst_body(m, j)->Some_0, bb, fm, fuel), fuel > 0,
        exec_stmts(m, inst_body(m, j)->Some_0, fm, inst_body(m, j)->Some_0.blocks@[bb as int].statements@, inst_body(m, j)->Some_0.blocks@[bb as int].statements@.len()) is Some,
    ensures post_stmts(m, pol, j, p, g, bb, fm, fc, fuel),
{
    lemma_rb_unfold(m, cpol(pol), inst_body(m, j)->Some_0, bb, fm, fuel);
    let b = inst_body(m, j)->Some_0;
    let cb = p.fns@[g as int];
    let ss = b.blocks@[bb as int].statements@;
    let cs = cb.blocks@[bb as int].stmts@;
    let lo = blk_lo(m, b, bb) as int;
    assert(lo <= cs.len());
    lemma_stmts(m, b, b.locals@.len(), cb.locals@.len(), fm, fc, ss, cs, ss.len());
    lemma_xs_all(cs, fc);
    lemma_xs_split(cs, 0, lo, cs.len() as int, fc);
}

/// `run_block` of a block whose statements succeed, one step.
proof fn lemma_rb_unfold(m: MirCrate, pol: CallPolicy, b: Body, bb: nat, fm: Frame, fuel: nat)
    requires fuel > 0, bb < b.blocks@.len(), block_ok(m, pol, b, b.blocks@[bb as int]),
        exec_stmts(m, b, fm, b.blocks@[bb as int].statements@, b.blocks@[bb as int].statements@.len()) is Some,
    ensures ({
        let blk = b.blocks@[bb as int];
        let (f1, e1, s1) = exec_stmts(m, b, fm, blk.statements@, blk.statements@.len())->Some_0;
        run_block(m, pol, b, bb, fm, fuel) == match step_term(m, pol, b, blk.terminator.kind, f1, fuel) {
            Step::Stop(Out::Done(f2, e2, s2)) => Out::Done(f2, e1 + e2, s1 + s2),
            Step::Stop(o) => o,
            Step::Jump(t, f2, e2, s2) => match run_block(m, pol, b, t, f2, (fuel - 1) as nat) {
                Out::Done(f3, e3, s3) => Out::Done(f3, e1 + e2 + e3, s1 + s2 + s3),
                o => o,
            },
        }
    }),
{
}

/// Core's `Return` block.
proof fn lemma_rf_ret(p: c::Program, f: nat, bb: nat, fc: Frame, fuel: nat)
    requires fuel > 0, f < p.fns@.len(), bb < p.fns@[f as int].blocks@.len(), p.fns@[f as int].blocks@[bb as int].term is Return,
    ensures ({
        let blk = p.fns@[f as int].blocks@[bb as int];
        let (f1, t1) = ctcore::sem::exec_stmts(blk.stmts@, 0, fc);
        ctcore::sem::run_from(p, f, bb, fc, fuel) == Some((f1, t1, blk.stmts@.len() + 1))
    }),
{
}

proof fn lemma_block_step(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, p: c::Program, g: nat, r: Seq<bool>, bb: nat, fm: Frame, fc: Frame, fuel: nat)
    requires body_sim_pre(m, pol, ord, j, p, g, r), bb < r.len(), r[bb as int], fuel > 0,
        fr_rel(fm, fc), pure_fr(fm), fm.locals.len() == inst_body(m, j)->Some_0.locals@.len(), fc.locals.len() == p.fns@[g as int].locals@.len(),
        run_tf(m, cpol(pol), inst_body(m, j)->Some_0, bb, fm, fuel), run_block(m, cpol(pol), inst_body(m, j)->Some_0, bb, fm, fuel) is Done,
        blk_pre_ok(m, pol, ord, j, p, g, r, bb),
    ensures run_ok(m, cpol(pol), inst_body(m, j)->Some_0, bb, fm, fuel, p, g, fc),
    decreases fuel, 1nat,
{
    hide(lowers_term_at);
    hide(ss_rel);
    hide(exec_stmts);
    hide(ctcore::sem::exec_stmts);
    hide(xs);
    hide(fr_rel);
    hide(pure_fr);
    hide(run_ok);
    hide(blk_pre_ok);
    hide(run_tf);
    hide(ctcore::sem::run_from);
    hide(lowers_body);
    hide(body_sim_pre);
    hide(post_stmts);
    hide(step_term);
    let b = inst_body(m, j)->Some_0;
    let blk = b.blocks@[bb as int];
    let ss = blk.statements@;
    assert(bb < b.blocks@.len() && block_ok(m, cpol(pol), b, blk)) by { reveal(blk_pre_ok); }
    assert(exec_stmts(m, b, fm, ss, ss.len()) is Some) by { reveal(run_block); }
    lemma_block_pre(m, pol, ord, j, p, g, r, bb, fm, fc, fuel);
    let (f1, e1, s1) = exec_stmts(m, b, fm, ss, ss.len())->Some_0;
    let st = step_term(m, cpol(pol), b, blk.terminator.kind, f1, fuel);
    assert(blk_f1(m, b, bb, fm) == f1);
    if st is Jump {
        lemma_block_jump(m, pol, ord, j, p, g, r, bb, fm, fc, fuel);
    } else {
        lemma_block_ret(m, pol, ord, j, p, g, r, bb, fm, fc, fuel);
    }
}

pub open spec fn blk_f1(m: MirCrate, b: Body, bb: nat, fm: Frame) -> Frame {
    exec_stmts(m, b, fm, b.blocks@[bb as int].statements@, b.blocks@[bb as int].statements@.len())->Some_0.0
}

pub open spec fn post_stmts(m: MirCrate, pol: Policy, j: nat, p: c::Program, g: nat, bb: nat, fm: Frame, fc: Frame, fuel: nat) -> bool {
    let b = inst_body(m, j)->Some_0;
    let cs = p.fns@[g as int].blocks@[bb as int].stmts@;
    let ss = b.blocks@[bb as int].statements@;
    let lo = blk_lo(m, b, bb);
    let (f1, e1, s1) = exec_stmts(m, b, fm, ss, ss.len())->Some_0;
    let (fcs, ce1) = xs(cs, 0, lo as int, fc);
    let (fct, ept) = ctcore::sem::exec_stmts(cs.subrange(lo as int, cs.len() as int), 0, fcs);
    &&& exec_stmts(m, b, fm, ss, ss.len()) is Some
    &&& lo <= cs.len() && fr_rel(f1, fcs) && pure_fr(f1) && e1 == ce1 && s1 == lo
    &&& f1.locals.len() == b.locals@.len() && fcs.locals.len() == p.fns@[g as int].locals@.len()
    &&& ctcore::sem::exec_stmts(cs, 0, fc) == (fct, ce1 + ept)
    &&& match step_term(m, cpol(pol), b, b.blocks@[bb as int].terminator.kind, f1, fuel) {
        Step::Jump(t, f2, _, _) => run_tf(m, cpol(pol), b, t, f2, (fuel - 1) as nat),
        _ => true,
    }
    &&& run_block(m, cpol(pol), b, bb, fm, fuel) == match step_term(m, cpol(pol), b, b.blocks@[bb as int].terminator.kind, f1, fuel) {
        Step::Stop(Out::Done(f2, e2, s2)) => Out::Done(f2, e1 + e2, s1 + s2),
        Step::Stop(o) => o,
        Step::Jump(t, f2, e2, s2) => match run_block(m, cpol(pol), b, t, f2, (fuel - 1) as nat) {
            Out::Done(f3, e3, s3) => Out::Done(f3, e1 + e2 + e3, s1 + s2 + s3),
            o => o,
        },
    }
}

proof fn lemma_block_ret(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, p: c::Program, g: nat, r: Seq<bool>, bb: nat, fm: Frame, fc: Frame, fuel: nat)
    requires body_sim_pre(m, pol, ord, j, p, g, r), blk_pre_ok(m, pol, ord, j, p, g, r, bb), fuel > 0, bb < r.len(), r[bb as int],
        post_stmts(m, pol, j, p, g, bb, fm, fc, fuel), run_block(m, cpol(pol), inst_body(m, j)->Some_0, bb, fm, fuel) is Done,
        !(step_term(m, cpol(pol), inst_body(m, j)->Some_0, inst_body(m, j)->Some_0.blocks@[bb as int].terminator.kind, blk_f1(m, inst_body(m, j)->Some_0, bb, fm), fuel) is Jump),
    ensures run_ok(m, cpol(pol), inst_body(m, j)->Some_0, bb, fm, fuel, p, g, fc),
{
    hide(exec_stmts);
    hide(ctcore::sem::run_from);
    hide(lowers_body);
    let b = inst_body(m, j)->Some_0;
    let cb = p.fns@[g as int];
    let (nloc, ncore) = (b.locals@.len(), cb.locals@.len());
    let blk = b.blocks@[bb as int];
    let cblk = cb.blocks@[bb as int];
    let cs = cblk.stmts@;
    let kind = blk.terminator.kind;
    let lo = blk_lo(m, b, bb) as int;
    let pre = cs.subrange(lo, cs.len() as int);
    let (f1, e1, s1) = exec_stmts(m, b, fm, blk.statements@, blk.statements@.len())->Some_0;
    let (fcs, ce1) = xs(cs, 0, lo, fc);
    let st = step_term(m, cpol(pol), b, kind, f1, fuel);
    assert(!(kind is Call || kind is Drop));
    assert(kind is Return) by {
        if !(kind is Return) { assert(!(st is Stop && st->Stop_0 is Done)); }
    }
    let base = choose|base: nat| tmps_in(base, pre.len(), nloc, ncore) && #[trigger] lowers_term_at(m, pol, ord, b, nloc, ncore, kind, pre, cblk.term, base);
    assert(pre.len() == 0 && cblk.term is Return);
    lemma_xs_empty(cs, lo, fcs);
    lemma_rf_ret(p, g, bb, fc, fuel);
    assert(e1 + Seq::<Event>::empty() == e1);
    assert(ce1 + Seq::<Event>::empty() == ce1);
}

proof fn lemma_jump_facts(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, p: c::Program, g: nat, r: Seq<bool>, bb: nat, fm: Frame, fc: Frame, fuel: nat)
    requires body_sim_pre(m, pol, ord, j, p, g, r), blk_pre_ok(m, pol, ord, j, p, g, r, bb), fuel > 0, bb < r.len(), r[bb as int],
        post_stmts(m, pol, j, p, g, bb, fm, fc, fuel),
        step_term(m, cpol(pol), inst_body(m, j)->Some_0, inst_body(m, j)->Some_0.blocks@[bb as int].terminator.kind, blk_f1(m, inst_body(m, j)->Some_0, bb, fm), fuel) is Jump,
    ensures ({
        let b = inst_body(m, j)->Some_0;
        let blk = b.blocks@[bb as int];
        let cs = p.fns@[g as int].blocks@[bb as int].stmts@;
        let lo = blk_lo(m, b, bb) as int;
        let (f1, e1, s1) = exec_stmts(m, b, fm, blk.statements@, blk.statements@.len())->Some_0;
        let (fcs, ce1) = xs(cs, 0, lo, fc);
        let fct = ctcore::sem::exec_stmts(cs.subrange(lo, cs.len() as int), 0, fcs).0;
        let st = step_term(m, cpol(pol), b, blk.terminator.kind, f1, fuel);
        let (t, f2, e2, s2) = (st->Jump_0, st->Jump_1, st->Jump_2, st->Jump_3);
        &&& fr_rel(f2, fct) && pure_fr(f2) && f2.locals.len() == b.locals@.len() && fct.locals.len() == p.fns@[g as int].locals@.len()
        &&& t < r.len() && r[t as int] && run_tf(m, cpol(pol), b, t, f2, (fuel - 1) as nat)
        &&& ctcore::sem::run_from(p, g, bb, fc, fuel) == match ctcore::sem::run_from(p, g, t, fct, (fuel - 1) as nat) {
            Some((f3, t3, n3)) => Some((f3, e1 + e2 + t3, s1 + s2 + n3)), None => None }
        &&& run_block(m, cpol(pol), b, bb, fm, fuel) == match run_block(m, cpol(pol), b, t, f2, (fuel - 1) as nat) {
            Out::Done(f3, e3, s3) => Out::Done(f3, e1 + e2 + e3, s1 + s2 + s3), o => o }
    }),
{
    hide(exec_stmts);
    hide(ctcore::sem::exec_stmts);
    hide(xs);
    hide(fr_rel);
    hide(pure_fr);
    hide(run_block);
    hide(ctcore::sem::run_from);
    hide(lowers_body);
    hide(run_tf);
    hide(lowers_term_at);
    hide(step_term);
    hide(blk_pre_ok);
    hide(body_sim_pre);
    hide(post_stmts);
    hide(lowers_term);
    hide(ss_rel);
    let b = inst_body(m, j)->Some_0;
    let cb = p.fns@[g as int];
    let (nloc, ncore) = (b.locals@.len(), cb.locals@.len());
    let blk = b.blocks@[bb as int];
    let cblk = cb.blocks@[bb as int];
    let cs = cblk.stmts@;
    let kind = blk.terminator.kind;
    let lo = blk_lo(m, b, bb) as int;
    let pre = cs.subrange(lo, cs.len() as int);
    let (f1, e1, s1) = exec_stmts(m, b, fm, blk.statements@, blk.statements@.len())->Some_0;
    let (fcs, ce1) = xs(cs, 0, lo, fc);
    let st = step_term(m, cpol(pol), b, kind, f1, fuel);
    assert(blk_f1(m, b, bb, fm) == f1);
    assert(g < p.fns@.len() && bb < r.len() && r[bb as int] && !(kind is Call || kind is Drop)) by { reveal(body_sim_pre); reveal(blk_pre_ok); }
    assert(lowers_term(m, pol, ord, b, nloc, ncore, kind, pre, cblk.term) && succs_in(kind, marks(r)) && bb < cb.blocks@.len()) by { reveal(blk_pre_ok); }
    assert(post_stmts(m, pol, j, p, g, bb, fm, fc, fuel));
    assert(fr_rel(f1, fcs) && pure_fr(f1) && e1 == ce1 && f1.locals.len() == nloc && fcs.locals.len() == ncore && lo <= cs.len()) by { reveal(post_stmts); }
    assert(kind is Goto || kind is SwitchInt || kind is Assert) by { reveal(step_term); }
    assert(run_tf(m, cpol(pol), b, st->Jump_0, st->Jump_1, (fuel - 1) as nat)) by { reveal(post_stmts); }
    let (t, f2, e2, s2) = (st->Jump_0, st->Jump_1, st->Jump_2, st->Jump_3);
    let (fct, ept) = ctcore::sem::exec_stmts(pre, 0, fcs);
    assert(ctcore::sem::exec_stmts(cs, 0, fc) == (fct, ce1 + ept)) by { reveal(post_stmts); }
    assert(run_block(m, cpol(pol), b, bb, fm, fuel) == match run_block(m, cpol(pol), b, t, f2, (fuel - 1) as nat) {
        Out::Done(f3, e3, s3) => Out::Done(f3, e1 + e2 + e3, s1 + s2 + s3), o => o }) by { reveal(post_stmts); }
    assert(s1 == lo) by { reveal(post_stmts); }
    lemma_jump_core(m, pol, ord, b, nloc, ncore, kind, pre, cblk.term, f1, fcs, fuel, p, g, bb, fc, cs, lo, ce1);
    lemma_jump_reached(kind, marks(r), st, m, cpol(pol), b, f1, fuel);
    lemma_marks_len(r, t);
}

/// Core's side of a jump: the terminator's temps, then the jump, from related frames.
proof fn lemma_jump_core(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, nloc: nat, ncore: nat, kind: TerminatorKind, pre: Seq<c::Stmt>,
    ct: c::Term, f1: Frame, fcs: Frame, fuel: nat, p: c::Program, g: nat, bb: nat, fc: Frame, cs: Seq<c::Stmt>, lo: int, ce1: Seq<Event>)
    requires
        lowers_term(m, pol, ord, b, nloc, ncore, kind, pre, ct), kind is Goto || kind is SwitchInt || kind is Assert,
        fr_rel(f1, fcs), pure_fr(f1), f1.locals.len() == nloc, fcs.locals.len() == ncore,
        step_term(m, cpol(pol), b, kind, f1, fuel) is Jump, fuel > 0,
        g < p.fns@.len(), bb < p.fns@[g as int].blocks@.len(), p.fns@[g as int].blocks@[bb as int].stmts@ == cs, p.fns@[g as int].blocks@[bb as int].term == ct,
        0 <= lo <= cs.len(), pre == cs.subrange(lo, cs.len() as int),
        ctcore::sem::exec_stmts(cs, 0, fc) == (ctcore::sem::exec_stmts(pre, 0, fcs).0, ce1 + ctcore::sem::exec_stmts(pre, 0, fcs).1),
    ensures ({
        let fct = ctcore::sem::exec_stmts(pre, 0, fcs).0;
        let st = step_term(m, cpol(pol), b, kind, f1, fuel);
        let (t, f2, e2, s2) = (st->Jump_0, st->Jump_1, st->Jump_2, st->Jump_3);
        &&& fr_rel(f1, fct) && f2 == f1 && fct.locals.len() == ncore
        &&& ctcore::sem::run_from(p, g, bb, fc, fuel) == match ctcore::sem::run_from(p, g, t, fct, (fuel - 1) as nat) {
            Some((f3, t3, n3)) => Some((f3, ce1 + e2 + t3, (lo + s2 + n3) as nat)), None => None }
    }),
{
    hide(step_term);
    hide(lowers_term_at);
    let base = choose|base: nat| tmps_in(base, pre.len(), nloc, ncore) && #[trigger] lowers_term_at(m, pol, ord, b, nloc, ncore, kind, pre, ct, base);
    lemma_term_jump(m, pol, ord, b, nloc, ncore, kind, pre, ct, base, f1, fcs, fuel);
    assert(ce1 + Seq::<Event>::empty() == ce1);
    lemma_run_from_jump(p, g, bb, fc, fuel);
    assert(cs.len() == lo + pre.len());
}

proof fn lemma_block_jump(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, p: c::Program, g: nat, r: Seq<bool>, bb: nat, fm: Frame, fc: Frame, fuel: nat)
    requires body_sim_pre(m, pol, ord, j, p, g, r), blk_pre_ok(m, pol, ord, j, p, g, r, bb), fuel > 0, bb < r.len(), r[bb as int],
        post_stmts(m, pol, j, p, g, bb, fm, fc, fuel), run_block(m, cpol(pol), inst_body(m, j)->Some_0, bb, fm, fuel) is Done,
        step_term(m, cpol(pol), inst_body(m, j)->Some_0, inst_body(m, j)->Some_0.blocks@[bb as int].terminator.kind, blk_f1(m, inst_body(m, j)->Some_0, bb, fm), fuel) is Jump,
    ensures run_ok(m, cpol(pol), inst_body(m, j)->Some_0, bb, fm, fuel, p, g, fc),
    decreases fuel, 0nat,
{
    hide(exec_stmts);
    hide(ctcore::sem::exec_stmts);
    hide(xs);
    hide(fr_rel);
    hide(pure_fr);
    hide(run_ok);
    hide(ctcore::sem::run_from);
    hide(run_tf);
    hide(step_term);
    hide(blk_pre_ok);
    hide(body_sim_pre);
    hide(post_stmts);
    let b = inst_body(m, j)->Some_0;
    let blk = b.blocks@[bb as int];
    let cs = p.fns@[g as int].blocks@[bb as int].stmts@;
    let lo = blk_lo(m, b, bb) as int;
    let (f1, e1, s1) = exec_stmts(m, b, fm, blk.statements@, blk.statements@.len())->Some_0;
    let (fcs, ce1) = xs(cs, 0, lo, fc);
    let fct = ctcore::sem::exec_stmts(cs.subrange(lo, cs.len() as int), 0, fcs).0;
    let st = step_term(m, cpol(pol), b, blk.terminator.kind, f1, fuel);
    let (t, f2, e2, s2) = (st->Jump_0, st->Jump_1, st->Jump_2, st->Jump_3);
    lemma_jump_facts(m, pol, ord, j, p, g, r, bb, fm, fc, fuel);
    lemma_block(m, pol, ord, j, p, g, r, t, f2, fct, (fuel - 1) as nat);
    reveal(run_ok);
    if let Out::Done(f3, e3, s3) = run_block(m, cpol(pol), b, t, f2, (fuel - 1) as nat) {
        assert((e1 + e2) + e3 == e1 + e2 + e3);
    }
}

proof fn lemma_marks_len(r: Seq<bool>, t: nat)
    requires marks(r).contains(t),
    ensures t < r.len() && r[t as int],
{
    crate::lower_fn::lemma_marks(r, t);
}

/// A jump goes to a successor.
proof fn lemma_jump_reached(kind: TerminatorKind, rs: Set<nat>, st: Step, m: MirCrate, pol: CallPolicy, b: Body, f1: Frame, fuel: nat)
    requires succs_in(kind, rs), st == step_term(m, pol, b, kind, f1, fuel), st is Jump, kind is Goto || kind is SwitchInt || kind is Assert,
    ensures rs.contains(st->Jump_0),
{
    if let TerminatorKind::SwitchInt { discr, targets } = kind {
        if let Some((Val::Int(d), _, _)) = eval_op(m, f1, discr) {
            let pr = |br: (u128, BasicBlockIdx)| br.0 == d;
            crate::sem_subset::lemma_find(targets.branches@, pr, 0);
        }
    }
}

} // verus!
