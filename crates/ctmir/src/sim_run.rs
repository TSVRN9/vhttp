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
use crate::sim_call::*;
#[allow(unused_imports)]
use crate::sim_exec::*;
#[allow(unused_imports)]
use crate::sim_op::*;
#[allow(unused_imports)]
use crate::sim_rv::*;
#[allow(unused_imports)]
use crate::sim_stmt::*;
#[allow(unused_imports)]
use ctcore::sem::{Cur, Event, Frame, Loc, Val};
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
        fr_rel(f1, fcs), f1.locals.len() == nloc, fcs.locals.len() == ncore,
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

/// Every fn of the program is the image of its instance (`lowers_rs`, its reached marks chosen).
pub open spec fn prog_ok(m: MirCrate, pol: Policy, ord: Seq<usize>, p: c::Program) -> bool {
    &&& ord.len() == p.fns@.len()
    &&& forall|h: int| 0 <= h < ord.len() ==> #[trigger] fn_ok(m, pol, ord, p, h)
}

pub open spec fn fn_ok(m: MirCrate, pol: Policy, ord: Seq<usize>, p: c::Program, h: int) -> bool {
    exists|r: Seq<bool>| #[trigger] lowers_body(m, pol, ord, ord[h] as nat, p.fns@[h], r)
}

pub open spec fn body_sim_pre(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, p: c::Program, g: nat, r: Seq<bool>) -> bool {
    &&& g < p.fns@.len() && lowers_body(m, pol, ord, j, p.fns@[g as int], r)
    &&& prog_ok(m, pol, ord, p) && j == ord[g as int]
}

/// A reached block that jumps (to `t`, MIR frame `f2`): core's block, after the terminator, continues
/// at `t` from `fnext`, related to `f2`, with the same events and steps so far.
pub open spec fn jump_sim(m: MirCrate, pol: Policy, j: nat, p: c::Program, g: nat, r: Seq<bool>, bb: nat, fm: Frame, fc: Frame, fuel: nat, fnext: Frame) -> bool {
    let b = inst_body(m, j)->Some_0;
    let blk = b.blocks@[bb as int];
    let (f1, e1, s1) = exec_stmts(m, b, fm, blk.statements@, blk.statements@.len())->Some_0;
    let st = step_term(m, cpol(pol), b, blk.terminator.kind, f1, fuel);
    let (t, f2, e2, s2) = (st->Jump_0, st->Jump_1, st->Jump_2, st->Jump_3);
    &&& fr_rel(f2, fnext) && f2.locals.len() == b.locals@.len() && fnext.locals.len() == p.fns@[g as int].locals@.len()
    &&& t < r.len() && r[t as int]
    &&& ctcore::sem::run_from(p, g, bb, fc, fuel) == match ctcore::sem::run_from(p, g, t, fnext, (fuel - 1) as nat) {
        Some((f3, t3, n3)) => Some((f3, e1 + e2 + t3, s1 + s2 + n3)), None => None }
    &&& run_block(m, cpol(pol), b, bb, fm, fuel) == match run_block(m, cpol(pol), b, t, f2, (fuel - 1) as nat) {
        Out::Done(f3, e3, s3) => Out::Done(f3, e1 + e2 + e3, s1 + s2 + s3), o => o }
}

pub open spec fn run_ok(m: MirCrate, pol: CallPolicy, b: Body, bb: nat, fm: Frame, fuel: nat, p: c::Program, g: nat, fc: Frame) -> bool {
    run_block(m, pol, b, bb, fm, fuel) matches Out::Done(fm2, e, s) ==> (ctcore::sem::run_from(p, g, bb, fc, fuel) matches Some((fc2, ce, cn))
        && fr_rel(fm2, fc2) && e == ce && s == cn)
}

/// The run induction (call-free).
pub proof fn lemma_block(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, p: c::Program, g: nat, r: Seq<bool>, bb: nat, fm: Frame, fc: Frame, fuel: nat)
    requires body_sim_pre(m, pol, ord, j, p, g, r), bb < r.len(), r[bb as int],
        fr_rel(fm, fc), fm.locals.len() == inst_body(m, j)->Some_0.locals@.len(), fc.locals.len() == p.fns@[g as int].locals@.len(),
    ensures run_ok(m, cpol(pol), inst_body(m, j)->Some_0, bb, fm, fuel, p, g, fc),
    decreases fuel, 5nat,
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
        fr_rel(fm, fc), fm.locals.len() == inst_body(m, j)->Some_0.locals@.len(), fc.locals.len() == p.fns@[g as int].locals@.len(),
        fuel > 0,
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
        fr_rel(fm, fc), fm.locals.len() == inst_body(m, j)->Some_0.locals@.len(), fc.locals.len() == p.fns@[g as int].locals@.len(),
        run_block(m, cpol(pol), inst_body(m, j)->Some_0, bb, fm, fuel) is Done,
        blk_pre_ok(m, pol, ord, j, p, g, r, bb),
    ensures run_ok(m, cpol(pol), inst_body(m, j)->Some_0, bb, fm, fuel, p, g, fc),
    decreases fuel, 4nat,
{
    hide(call_step);
    hide(drop_step);
    hide(body_call);
    hide(mir_run);
    hide(lowers_term_at);
    hide(ss_rel);
    hide(exec_stmts);
    hide(ctcore::sem::exec_stmts);
    hide(xs);
    hide(fr_rel);
    hide(run_ok);
    hide(blk_pre_ok);
    hide(ctcore::sem::run_from);
    hide(lowers_body);
    hide(body_sim_pre);
    hide(post_stmts);
    hide(step_term);
    hide(prog_ok);
    hide(jump_sim);
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
    &&& lo <= cs.len() && fr_rel(f1, fcs) && e1 == ce1 && s1 == lo
    &&& f1.locals.len() == b.locals@.len() && fcs.locals.len() == p.fns@[g as int].locals@.len()
    &&& ctcore::sem::exec_stmts(cs, 0, fc) == (fct, ce1 + ept)
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
    lemma_cd_not_done(m, cpol(pol), b, kind, f1, fuel);
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

proof fn lemma_jump_facts(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, p: c::Program, g: nat, r: Seq<bool>, bb: nat, fm: Frame, fc: Frame, fuel: nat) -> (fnext: Frame)
    requires body_sim_pre(m, pol, ord, j, p, g, r), blk_pre_ok(m, pol, ord, j, p, g, r, bb), fuel > 0, bb < r.len(), r[bb as int],
        post_stmts(m, pol, j, p, g, bb, fm, fc, fuel),
        step_term(m, cpol(pol), inst_body(m, j)->Some_0, inst_body(m, j)->Some_0.blocks@[bb as int].terminator.kind, blk_f1(m, inst_body(m, j)->Some_0, bb, fm), fuel) is Jump,
        !(inst_body(m, j)->Some_0.blocks@[bb as int].terminator.kind is Call || inst_body(m, j)->Some_0.blocks@[bb as int].terminator.kind is Drop),
    ensures jump_sim(m, pol, j, p, g, r, bb, fm, fc, fuel, fnext),
        ({
        let b = inst_body(m, j)->Some_0;
        let blk = b.blocks@[bb as int];
        let cs = p.fns@[g as int].blocks@[bb as int].stmts@;
        let lo = blk_lo(m, b, bb) as int;
        let (f1, e1, s1) = exec_stmts(m, b, fm, blk.statements@, blk.statements@.len())->Some_0;
        let (fcs, ce1) = xs(cs, 0, lo, fc);
        let fct = ctcore::sem::exec_stmts(cs.subrange(lo, cs.len() as int), 0, fcs).0;
        let st = step_term(m, cpol(pol), b, blk.terminator.kind, f1, fuel);
        let (t, f2, e2, s2) = (st->Jump_0, st->Jump_1, st->Jump_2, st->Jump_3);
        &&& fr_rel(f2, fct) && f2.locals.len() == b.locals@.len() && fct.locals.len() == p.fns@[g as int].locals@.len()
        &&& t < r.len() && r[t as int]
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
    hide(run_block);
    hide(ctcore::sem::run_from);
    hide(lowers_body);
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
    assert(g < p.fns@.len() && bb < r.len() && r[bb as int]) by { reveal(body_sim_pre); reveal(blk_pre_ok); }
    assert(lowers_term(m, pol, ord, b, nloc, ncore, kind, pre, cblk.term) && succs_in(kind, marks(r)) && bb < cb.blocks@.len()) by { reveal(blk_pre_ok); }
    assert(kind is Goto || kind is SwitchInt || kind is Assert) by { reveal(step_term); }
    let (t, f2, e2, s2) = (st->Jump_0, st->Jump_1, st->Jump_2, st->Jump_3);
    let (fct, ept) = ctcore::sem::exec_stmts(pre, 0, fcs);
    lemma_post_jump(m, pol, j, p, g, bb, fm, fc, fuel);
    lemma_jump_core(m, pol, ord, b, nloc, ncore, kind, pre, cblk.term, f1, fcs, fuel, p, g, bb, fc, cs, lo, ce1);
    lemma_jump_reached(kind, marks(r), st, m, cpol(pol), b, f1, fuel);
    lemma_marks_len(r, t);
    fct
}

/// `post_stmts` unpacked for a jump.
proof fn lemma_post_jump(m: MirCrate, pol: Policy, j: nat, p: c::Program, g: nat, bb: nat, fm: Frame, fc: Frame, fuel: nat)
    requires post_stmts(m, pol, j, p, g, bb, fm, fc, fuel),
        step_term(m, cpol(pol), inst_body(m, j)->Some_0, inst_body(m, j)->Some_0.blocks@[bb as int].terminator.kind, blk_f1(m, inst_body(m, j)->Some_0, bb, fm), fuel) is Jump,
    ensures ({
        let b = inst_body(m, j)->Some_0;
        let blk = b.blocks@[bb as int];
        let cs = p.fns@[g as int].blocks@[bb as int].stmts@;
        let lo = blk_lo(m, b, bb) as int;
        let (f1, e1, s1) = exec_stmts(m, b, fm, blk.statements@, blk.statements@.len())->Some_0;
        let (fcs, ce1) = xs(cs, 0, lo, fc);
        let (fct, ept) = ctcore::sem::exec_stmts(cs.subrange(lo, cs.len() as int), 0, fcs);
        let st = step_term(m, cpol(pol), b, blk.terminator.kind, f1, fuel);
        let (t, f2, e2, s2) = (st->Jump_0, st->Jump_1, st->Jump_2, st->Jump_3);
        &&& lo <= cs.len() && fr_rel(f1, fcs) && e1 == ce1 && s1 == lo
        &&& f1.locals.len() == b.locals@.len() && fcs.locals.len() == p.fns@[g as int].locals@.len()
        &&& ctcore::sem::exec_stmts(cs, 0, fc) == (fct, ce1 + ept)
        &&& run_block(m, cpol(pol), b, bb, fm, fuel) == match run_block(m, cpol(pol), b, t, f2, (fuel - 1) as nat) {
            Out::Done(f3, e3, s3) => Out::Done(f3, e1 + e2 + e3, s1 + s2 + s3), o => o }
    }),
{
    hide(fr_rel);
}

/// Core's side of a jump: the terminator's temps, then the jump, from related frames.
proof fn lemma_jump_core(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, nloc: nat, ncore: nat, kind: TerminatorKind, pre: Seq<c::Stmt>,
    ct: c::Term, f1: Frame, fcs: Frame, fuel: nat, p: c::Program, g: nat, bb: nat, fc: Frame, cs: Seq<c::Stmt>, lo: int, ce1: Seq<Event>)
    requires
        lowers_term(m, pol, ord, b, nloc, ncore, kind, pre, ct), kind is Goto || kind is SwitchInt || kind is Assert,
        fr_rel(f1, fcs), f1.locals.len() == nloc, fcs.locals.len() == ncore,
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
    decreases fuel, 3nat,
{
    hide(exec_stmts);
    hide(ctcore::sem::exec_stmts);
    hide(xs);
    hide(fr_rel);
    hide(run_ok);
    hide(jump_sim);
    hide(ctcore::sem::run_from);
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
    let st = step_term(m, cpol(pol), b, blk.terminator.kind, f1, fuel);
    let (t, f2, e2, s2) = (st->Jump_0, st->Jump_1, st->Jump_2, st->Jump_3);
    let kind = blk.terminator.kind;
    let fnext = if kind is Call {
        lemma_call_facts(m, pol, ord, j, p, g, r, bb, fm, fc, fuel)
    } else if kind is Drop {
        lemma_drop_facts(m, pol, ord, j, p, g, r, bb, fm, fc, fuel)
    } else {
        lemma_jump_facts(m, pol, ord, j, p, g, r, bb, fm, fc, fuel)
    };
    reveal(jump_sim);
    lemma_block(m, pol, ord, j, p, g, r, t, f2, fnext, (fuel - 1) as nat);
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

/// A `Call` or `Drop` step never stops with a completed run.
proof fn lemma_cd_not_done(m: MirCrate, pol: CallPolicy, b: Body, kind: TerminatorKind, f1: Frame, fuel: nat)
    ensures (kind is Call || kind is Drop) ==> !(step_term(m, pol, b, kind, f1, fuel) matches Step::Stop(Out::Done(_, _, _))),
{
}

/// Core's outcome of a call terminator from `f1`: the frame after the destination is written, the
/// events and the extra steps (an intrinsic's cost, or the callee's steps).
pub open spec fn call_out(p: c::Program, ct: c::Term, f1: Frame, fuel: nat) -> Option<(Frame, Seq<Event>, nat)> {
    match ct {
        c::Term::Call(c::Callee::Intr(k), args, dst, _) => ctcore::sem::exec_intr(k, f1, args@, dst),
        c::Term::Call(c::Callee::Fn(h), args, dst, _) => {
            let (cf, wb, ae) = ctcore::sem::call_enter(p, h as nat, f1, args@);
            match ctcore::sem::run_from(p, h as nat, 0, cf, (fuel - 1) as nat) {
                Some((cf2, ct2, cn)) => {
                    let (f2, de) = ctcore::sem::call_leave(f1, cf2, wb, dst);
                    Some((f2, ae + ct2 + de, cn))
                },
                None => None,
            }
        },
        _ => None,
    }
}

proof fn lemma_rf_call(p: c::Program, f: nat, bb: nat, fc: Frame, fuel: nat)
    requires fuel > 0, f < p.fns@.len(), bb < p.fns@[f as int].blocks@.len(), p.fns@[f as int].blocks@[bb as int].term is Call,
    ensures ({
        let blk = p.fns@[f as int].blocks@[bb as int];
        let (f1, t1) = ctcore::sem::exec_stmts(blk.stmts@, 0, fc);
        ctcore::sem::run_from(p, f, bb, fc, fuel) == match call_out(p, blk.term, f1, fuel) {
            Some((f2, e, x)) => match ctcore::sem::run_from(p, f, blk.term->Call_3 as nat, f2, (fuel - 1) as nat) {
                Some((f3, t3, n3)) => Some((f3, t1 + e + t3, blk.stmts@.len() + 1 + x + n3)),
                None => None,
            },
            None => None,
        }
    }),
{
    hide(ctcore::sem::run_from);
    hide(ctcore::sem::exec_stmts);
    hide(ctcore::sem::exec_intr);
    hide(ctcore::sem::call_enter);
    hide(ctcore::sem::call_leave);
    let blk = p.fns@[f as int].blocks@[bb as int];
    let (f1, t1) = ctcore::sem::exec_stmts(blk.stmts@, 0, fc);
    if blk.term->Call_0 is Fn {
        lemma_rf_fn(p, f, bb, fc, fuel);
        let (cf, wb, ae) = ctcore::sem::call_enter(p, blk.term->Call_0->Fn_0 as nat, f1, blk.term->Call_1@);
        if let Some((cf2, ct2, cn)) = ctcore::sem::run_from(p, blk.term->Call_0->Fn_0 as nat, 0, cf, (fuel - 1) as nat) {
            let (f2, de) = ctcore::sem::call_leave(f1, cf2, wb, blk.term->Call_2);
            if let Some((f3, t3, n3)) = ctcore::sem::run_from(p, f, blk.term->Call_3 as nat, f2, (fuel - 1) as nat) {
                assert(t1 + ae + ct2 + de + t3 == t1 + (ae + ct2 + de) + t3);
            }
        }
    } else {
        lemma_rf_intr(p, f, bb, fc, fuel);
    }
}

/// What a callee's `lowers_body` gives its call site: the entry block is reached, and the core
/// body has at least the MIR locals.
proof fn lemma_lb_entry(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, cb: c::Body, r: Seq<bool>)
    requires lowers_body(m, pol, ord, j, cb, r),
    ensures r.len() > 0 && r[0], inst_body(m, j) is Some, inst_body(m, j)->Some_0.locals@.len() <= cb.locals@.len(),
        forall|k: int| 0 <= k < inst_body(m, j)->Some_0.locals@.len() ==> !ul_arr(m, #[trigger] inst_body(m, j)->Some_0.locals@[k].ty),
{
    let b = inst_body(m, j)->Some_0;
    assert forall|k: int| 0 <= k < b.locals@.len() implies !ul_arr(m, #[trigger] b.locals@[k].ty) by {
        assert(lowers_ty(m, b.locals@[k].ty, cb.locals@[k], tyf()));
    }
}

/// `step_term` of a call or a drop.
pub proof fn lemma_step_cd(m: MirCrate, pol: CallPolicy, b: Body, kind: TerminatorKind, f1: Frame, fuel: nat)
    ensures
        kind matches TerminatorKind::Call { func, args, destination, target, unwind: _ } ==> match target {
            Some(tb) => step_term(m, pol, b, kind, f1, fuel) == call_step(m, pol, b, func, args@, destination, tb as nat, f1, fuel),
            None => step_term(m, pol, b, kind, f1, fuel) == Step::Stop(Out::Panic),
        },
        kind matches TerminatorKind::Drop { place, target, unwind: _ } ==> step_term(m, pol, b, kind, f1, fuel) == drop_step(m, pol, b, place, target as nat, f1, fuel),
{
}

/// A no-op drop that jumps.
pub proof fn lemma_drop_noop(m: MirCrate, pol: CallPolicy, b: Body, place: Place, tb: nat, fr: Frame, fuel: nat)
    requires drop_step(m, pol, b, place, tb, fr, fuel) is Jump,
        place_ty(m, b, place) matches Some(t) && drop_row(m, t) matches Some(d) && (d.empty || vec_int(m, t)),
    ensures eval_place(fr, place) matches Some((PRes::At(_), _)),
        drop_step(m, pol, b, place, tb, fr, fuel) == Step::Jump(tb, fr, eval_place(fr, place)->Some_0.1, 1),
{
}

/// `body_call` that returns, unpacked.
pub proof fn lemma_body_call_ok(m: MirCrate, pol: CallPolicy, j: nat, cb: Body, vs: Seq<Val>, fr: Frame, fuel: nat)
    requires body_call(m, pol, j, cb, vs, fr, fuel) is Ok,
    ensures ({
        let o = mir_run(m, pol, j, mir_entry(m, j, vs, call_slots(m, cb, fr, vs)), (fuel - 1) as nat);
        &&& fuel > 0 && args_ok(m, cb, fr, vs) && o is Done
        &&& return_to(m, cb, fr, vs, o->Done_0) is Some
        &&& body_call(m, pol, j, cb, vs, fr, fuel) == Ok::<(Val, Frame, Seq<Event>, nat), Out>((return_to(m, cb, fr, vs, o->Done_0)->Some_0.0,
                return_to(m, cb, fr, vs, o->Done_0)->Some_0.1, o->Done_1, o->Done_2))
    }),
{
}

/// A drop through glue that jumps, unpacked.
pub proof fn lemma_drop_parts(m: MirCrate, pol: CallPolicy, b: Body, place: Place, tb: nat, fr: Frame, fuel: nat)
    requires drop_step(m, pol, b, place, tb, fr, fuel) is Jump,
        place_ty(m, b, place) matches Some(t) && drop_row(m, t) matches Some(d) && !(d.empty || vec_int(m, t)),
    ensures ({
        let d = drop_row(m, place_ty(m, b, place)->Some_0)->Some_0;
        let (jg, gb) = glue_of(m, d.glue)->Some_0;
        let (pl, e) = eval_place(fr, place)->Some_0;
        let r = body_call(m, pol, jg, gb, seq![Val::Mut(pl->At_0)], fr, fuel);
        &&& eval_place(fr, place) is Some && pl is At && glue_of(m, d.glue) is Some && r is Ok
        &&& drop_step(m, pol, b, place, tb, fr, fuel) == Step::Jump(tb, r->Ok_0.1, e + r->Ok_0.2, 2 + r->Ok_0.3)
    }),
{
}

/// A call that jumps, unpacked: the callee, the arguments, the destination, and the leaf or body
/// outcome stored there.
pub open spec fn call_res(m: MirCrate, pol: CallPolicy, b: Body, j: nat, gargs: GenericArgs, vs: Seq<Val>, dest: Place, fr: Frame, fuel: nat)
    -> Result<(Val, Frame, Seq<Event>, nat), Out>
{
    let key = m.insts@[j as int].key@;
    if is_leaf(m, pol, key, gargs) {
        match leaf_call(m, pol, key, gargs, place_ty(m, b, dest), vs, fr) { Some(x) => Ok(x), None => Err(Out::Panic) }
    } else {
        match inst_body(m, j) { Some(cb) => body_call(m, pol, j, cb, vs, fr, fuel), None => Err(Out::Unsup) }
    }
}

pub proof fn lemma_call_parts(m: MirCrate, pol: CallPolicy, b: Body, func: Operand, args: Seq<Operand>, dest: Place, tb: nat, fr: Frame, fuel: nat)
    requires call_step(m, pol, b, func, args, dest, tb, fr, fuel) is Jump,
    ensures ({
        let (j, gargs) = callee_of(m, func)->Some_0;
        let (vs, e1, k1) = eval_ops(m, fr, args, args.len())->Some_0;
        let (pl, e2) = eval_place(fr, dest)->Some_0;
        let r = call_res(m, pol, b, j, gargs, vs, dest, fr, fuel);
        &&& callee_of(m, func) is Some && j < m.insts@.len() && eval_ops(m, fr, args, args.len()) is Some
        &&& eval_place(fr, dest) is Some && pl is At && r is Ok && store(r->Ok_0.1, pl->At_0, r->Ok_0.0) is Some
        &&& call_step(m, pol, b, func, args, dest, tb, fr, fuel)
            == Step::Jump(tb, store(r->Ok_0.1, pl->At_0, r->Ok_0.0)->Some_0, e1 + r->Ok_0.2 + e2, 1 + k1 + r->Ok_0.3)
    }),
{
}

/// The MIR parts of a call step that jumps.
pub open spec fn mcall(m: MirCrate, b: Body, args: Seq<Operand>, dest: Place, f1: Frame) -> (Seq<Val>, Seq<Event>, nat, Loc) {
    let (vs, e1, k1) = eval_ops(m, f1, args, args.len())->Some_0;
    (vs, e1, k1, eval_place(f1, dest)->Some_0.0->At_0)
}

/// A leaf call: core's intrinsic, after the arguments' temps, matches MIR's call step.
proof fn lemma_call_leaf(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, func: Operand, args: Seq<Operand>, dest: Place, tb: BasicBlockIdx,
    pre: Seq<c::Stmt>, base: nat, ct: c::Term, f1: Frame, fcs: Frame, fuel: nat, p: c::Program)
    requires
        lowers_call(m, pol, ord, b, func, args, dest, tb, pre, base, ct), fr_rel(f1, fcs), f1.locals.len() <= base,
        fcs.locals.len() >= base + pre.len(),
        call_step(m, cpol(pol), b, func, args, dest, tb as nat, f1, fuel) is Jump,
        ct->Call_0 is Intr,
    ensures ({
        let st = call_step(m, cpol(pol), b, func, args, dest, tb as nat, f1, fuel);
        let (fct, ept) = ctcore::sem::exec_stmts(pre, 0, fcs);
        &&& ept == Seq::<Event>::empty() && fct.locals.len() == fcs.locals.len()
        &&& call_out(p, ct, fct, fuel) matches Some((f3c, e, x)) && fr_rel(st->Jump_1, f3c) && e == st->Jump_2 && st->Jump_3 == 1 + pre.len() + x
            && f3c.locals.len() == fcs.locals.len()
        &&& st->Jump_1.locals.len() == f1.locals.len() && st->Jump_0 == tb
    }),
{
    hide(call_step);
    hide(drop_step);
    hide(body_call);
    hide(mir_run);
    hide(lowers_ops);
    hide(fr_rel);
    lemma_call_parts(m, cpol(pol), b, func, args, dest, tb as nat, f1, fuel);
    let (j, gargs) = callee_of(m, func)->Some_0;
    let key = m.insts@[j as int].key@;
    let (vs, e1, k1, l) = mcall(m, b, args, dest, f1);
    let dty = place_ty(m, b, dest);
    lemma_ops(m, b, f1, fcs, args, ct->Call_1@, pre, base);
    let (fct, _) = ctcore::sem::exec_stmts(pre, 0, fcs);
    lemma_stmts_len(pre, 0, fcs);
    let k = ct->Call_0->Intr_0;
    lemma_leaf(m, cpol(pol), key, gargs, dty, vs, f1, fct);
    let (v, f2, e3, x) = leaf_call(m, cpol(pol), key, gargs, dty, vs, f1)->Some_0;
    let (f2c, _, _) = ctcore::sem::intr_eff(k, fct, vs)->Some_0;
    lemma_lowers_place(m, b, dest, ct->Call_2, true);
    lemma_dest(f1, f2c, dest, ct->Call_2);
    lemma_store(f2, f2c, l, v);
    assert(e1 + e3 + Seq::<Event>::empty() == e1 + e3);
}

/// A body call: core's call (copy-in, the callee's run, write-back, destination) matches MIR's,
/// by the induction hypothesis for the callee at one less fuel.
proof fn lemma_call_body(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, func: Operand, args: Seq<Operand>, dest: Place, tb: BasicBlockIdx,
    pre: Seq<c::Stmt>, base: nat, ct: c::Term, f1: Frame, fcs: Frame, fuel: nat, p: c::Program)
    requires
        prog_ok(m, pol, ord, p),
        lowers_call(m, pol, ord, b, func, args, dest, tb, pre, base, ct), fr_rel(f1, fcs), f1.locals.len() <= base,
        fcs.locals.len() >= base + pre.len(),
        call_step(m, cpol(pol), b, func, args, dest, tb as nat, f1, fuel) is Jump, fuel > 0,
        ct->Call_0 is Fn,
    ensures ({
        let st = call_step(m, cpol(pol), b, func, args, dest, tb as nat, f1, fuel);
        let (fct, ept) = ctcore::sem::exec_stmts(pre, 0, fcs);
        &&& ept == Seq::<Event>::empty() && fct.locals.len() == fcs.locals.len()
        &&& call_out(p, ct, fct, fuel) matches Some((f3c, e, x)) && fr_rel(st->Jump_1, f3c) && e == st->Jump_2 && st->Jump_3 == 1 + pre.len() + x
            && f3c.locals.len() == fcs.locals.len()
        &&& st->Jump_1.locals.len() == f1.locals.len() && st->Jump_0 == tb
    }),
    decreases fuel, 1nat,
{
    hide(ctcore::sem::call_enter);
    hide(ctcore::sem::call_leave);
    hide(ctcore::sem::ops_ev);
    hide(ctcore::sem::op_vals);
    hide(mir_entry);
    hide(call_slots);
    hide(eval_ops);
    hide(eval_place);
    hide(return_to);
    hide(store);
    hide(lowers_body);
    hide(lowers_call);
    hide(lowers_drop);
    hide(body_sim_pre);
    hide(call_step);
    hide(drop_step);
    hide(body_call);
    hide(mir_run);
    hide(lowers_ops);
    hide(fr_rel);
    lemma_call_parts(m, cpol(pol), b, func, args, dest, tb as nat, f1, fuel);
    let (j, gargs) = callee_of(m, func)->Some_0;
    let cb = inst_body(m, j)->Some_0;
    let (vs, e1, k1, l) = mcall(m, b, args, dest, f1);
    assert(!is_leaf(m, cpol(pol), m.insts@[j as int].key@, gargs) && inst_body(m, j) is Some && fn_of(ord, ct->Call_0->Fn_0, j)
        && lowers_ops(m, b, args, ct->Call_1@, pre, base) && lowers_place(m, b, dest, ct->Call_2, true) && dest_ok(dest)
        && ct is Call && ct->Call_3 == tb) by { reveal(lowers_call); }
    assert(call_res(m, cpol(pol), b, j, gargs, vs, dest, f1, fuel) == body_call(m, cpol(pol), j, cb, vs, f1, fuel));
    lemma_body_call_ok(m, cpol(pol), j, cb, vs, f1, fuel);
    let h = ct->Call_0->Fn_0 as nat;
    lemma_ops(m, b, f1, fcs, args, ct->Call_1@, pre, base);
    let (fct, _) = ctcore::sem::exec_stmts(pre, 0, fcs);
    lemma_stmts_len(pre, 0, fcs);
    // the callee: its image is fn h, and the induction hypothesis applies to its run
    assert(h < ord.len() && ord[h as int] as nat == j);
    assert(fn_ok(m, pol, ord, p, h as int));
    let rh = choose|rh: Seq<bool>| lowers_body(m, pol, ord, ord[h as int] as nat, p.fns@[h as int], rh);
    assert(lowers_body(m, pol, ord, ord[h as int] as nat, p.fns@[h as int], rh));
    lemma_lb_entry(m, pol, ord, j, p.fns@[h as int], rh);
    assert(body_sim_pre(m, pol, ord, j, p, h, rh)) by { reveal(body_sim_pre); }
    let me = mir_entry(m, j, vs, call_slots(m, cb, f1, vs));
    lemma_call_entry(m, j, cb, p, h, f1, fct, ct->Call_1@, vs);
    let (cfe, wb, ae) = ctcore::sem::call_enter(p, h, fct, ct->Call_1@);
    lemma_block(m, pol, ord, j, p, h, rh, 0, me, cfe, (fuel - 1) as nat);
    let o = mir_run(m, cpol(pol), j, me, (fuel - 1) as nat);
    assert(o == run_block(m, cpol(pol), inst_body(m, j)->Some_0, 0, me, (fuel - 1) as nat)) by { reveal(mir_run); }
    assert(o is Done);
    let (cf, e3, s3) = (o->Done_0, o->Done_1, o->Done_2);
    let (cfc, _, _) = ctcore::sem::run_from(p, h, 0, cfe, (fuel - 1) as nat)->Some_0;
    lemma_lowers_place(m, b, dest, ct->Call_2, true);
    assert(fr_rel(f1, fct));
    assert(args_ok(m, cb, f1, vs));
    assert(fr_rel(cf, cfc));
    assert(return_to(m, cb, f1, vs, cf) is Some);
    assert(eval_place(f1, dest) is Some);
    assert(store(return_to(m, cb, f1, vs, cf)->Some_0.1, eval_place(f1, dest)->Some_0.0->At_0, return_to(m, cb, f1, vs, cf)->Some_0.0) is Some);
    lemma_leave(m, cb, f1, fct, vs, cf, cfc, dest, ct->Call_2);
    let rt = return_to(m, cb, f1, vs, cf)->Some_0;
    let f3m = store(rt.1, l, rt.0)->Some_0;
    let st = call_step(m, cpol(pol), b, func, args, dest, tb as nat, f1, fuel);
    assert(call_res(m, cpol(pol), b, j, gargs, vs, dest, f1, fuel) == Ok::<(Val, Frame, Seq<Event>, nat), Out>((rt.0, rt.1, e3, s3)));
    assert(eval_place(f1, dest)->Some_0.1 == Seq::<Event>::empty());
    assert(st == Step::Jump(tb as nat, f3m, e1 + e3 + Seq::<Event>::empty(), 1 + k1 + s3));
    assert(wb == wb_of(vs) && ae == e1);
    lemma_body_out(p, ct, fct, fuel, h, wb, ae, cfe, cfc, e3, s3, f3m, st, e1, pre.len());
}

/// The core outcome of a body call, assembled.
proof fn lemma_body_out(p: c::Program, ct: c::Term, fct: Frame, fuel: nat, h: nat, wb: Seq<Option<Loc>>, ae: Seq<Event>, cfe: Frame, cfc: Frame,
    e3: Seq<Event>, s3: nat, f3m: Frame, st: Step, e1: Seq<Event>, n: nat)
    requires
        ct is Call && ct->Call_0 == c::Callee::Fn(h as usize), h as usize as nat == h,
        ctcore::sem::call_enter(p, h, fct, ct->Call_1@) == (cfe, wb, ae),
        ctcore::sem::run_from(p, h, 0, cfe, (fuel - 1) as nat) == Some((cfc, e3, s3)),
        fr_rel(f3m, ctcore::sem::call_leave(fct, cfc, wb, ct->Call_2).0), ctcore::sem::call_leave(fct, cfc, wb, ct->Call_2).1 == Seq::<Event>::empty(),
        st is Jump && st->Jump_1 == f3m && st->Jump_2 == ae + e3 + Seq::<Event>::empty() && st->Jump_3 == 1 + n + s3,
        ctcore::sem::call_leave(fct, cfc, wb, ct->Call_2).0.locals.len() == fct.locals.len(),
    ensures call_out(p, ct, fct, fuel) matches Some((f3c, e, x)) && fr_rel(st->Jump_1, f3c) && e == st->Jump_2 && st->Jump_3 == 1 + n + x
        && f3c.locals.len() == fct.locals.len(),
{
}

/// A call terminator that jumps.
proof fn lemma_call_facts(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, p: c::Program, g: nat, r: Seq<bool>, bb: nat, fm: Frame, fc: Frame, fuel: nat) -> (fnext: Frame)
    requires body_sim_pre(m, pol, ord, j, p, g, r), blk_pre_ok(m, pol, ord, j, p, g, r, bb), fuel > 0, bb < r.len(), r[bb as int],
        post_stmts(m, pol, j, p, g, bb, fm, fc, fuel),
        step_term(m, cpol(pol), inst_body(m, j)->Some_0, inst_body(m, j)->Some_0.blocks@[bb as int].terminator.kind, blk_f1(m, inst_body(m, j)->Some_0, bb, fm), fuel) is Jump,
        inst_body(m, j)->Some_0.blocks@[bb as int].terminator.kind is Call,
    ensures jump_sim(m, pol, j, p, g, r, bb, fm, fc, fuel, fnext),
    decreases fuel, 2nat,
{
    hide(call_step);
    hide(drop_step);
    hide(body_call);
    hide(mir_run);
    hide(exec_stmts);
    hide(ctcore::sem::exec_stmts);
    hide(xs);
    hide(fr_rel);
    hide(run_block);
    hide(ctcore::sem::run_from);
    hide(lowers_body);
    hide(lowers_term_at);
    hide(step_term);
    hide(blk_pre_ok);
    hide(body_sim_pre);
    hide(post_stmts);
    hide(lowers_term);
    hide(ss_rel);
    hide(lowers_call);
    hide(call_out);
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
    assert(g < p.fns@.len() && prog_ok(m, pol, ord, p)) by { reveal(body_sim_pre); }
    assert(lowers_term(m, pol, ord, b, nloc, ncore, kind, pre, cblk.term) && succs_in(kind, marks(r)) && bb < cb.blocks@.len()) by { reveal(blk_pre_ok); }
    lemma_post_jump(m, pol, j, p, g, bb, fm, fc, fuel);
    let (func, args, dest) = (kind->Call_func, kind->Call_args@, kind->Call_destination);
    lemma_step_cd(m, cpol(pol), b, kind, f1, fuel);
    let tb = kind->Call_target->Some_0;
    reveal(lowers_term);
    let base = choose|base: nat| tmps_in(base, pre.len(), nloc, ncore) && #[trigger] lowers_term_at(m, pol, ord, b, nloc, ncore, kind, pre, cblk.term, base);
    assert(lowers_call(m, pol, ord, b, func, args, dest, tb, pre, base, cblk.term)) by { reveal(lowers_term_at); }
    let ct = cblk.term;
    assert(ct is Call && ct->Call_3 == tb) by { reveal(lowers_call); }
    if ct->Call_0 is Intr {
        lemma_call_leaf(m, pol, ord, b, func, args, dest, tb, pre, base, ct, f1, fcs, fuel, p);
    } else {
        lemma_call_body(m, pol, ord, b, func, args, dest, tb, pre, base, ct, f1, fcs, fuel, p);
    }
    let (fct, ept) = ctcore::sem::exec_stmts(pre, 0, fcs);
    let (f3c, ec, x) = call_out(p, ct, fct, fuel)->Some_0;
    lemma_rf_call(p, g, bb, fc, fuel);
    assert(ce1 + ept == ce1);
    assert(cs.len() == lo + pre.len());
    lemma_jump_reached_cd(kind, marks(r), st, m, cpol(pol), b, f1, fuel);
    lemma_marks_len(r, tb as nat);
    assert(ce1 + ec + Seq::<Event>::empty() == ce1 + ec);
    f3c
}

/// A write to a core temp (at or after the MIR locals) keeps the frames related.
proof fn lemma_tmp_write(fm: Frame, g: Frame, x: nat, w: Val)
    requires fr_rel(fm, g), fm.locals.len() <= x,
    ensures fr_rel(fm, ctcore::sem::write_loc(g, ctcore::sem::local_loc(x), w)),
        ctcore::sem::write_loc(g, ctcore::sem::local_loc(x), w).locals.len() == g.locals.len(),
{
    let g2 = ctcore::sem::write_loc(g, ctcore::sem::local_loc(x), w);
    assert forall|i: int| 0 <= i < fm.locals.len() implies #[trigger] fm.locals[i] == g2.locals[i] by { assert(fm.locals[i] == g.locals[i]); }
}

/// A drop through glue: core's `x = &mut place` and its call of the glue's fn match MIR's glue call.
proof fn lemma_drop_glue(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, nloc: nat, ncore: nat, place: Place, target: BasicBlockIdx,
    pre: Seq<c::Stmt>, ct: c::Term, f1: Frame, fcs: Frame, fuel: nat, p: c::Program)
    requires
        prog_ok(m, pol, ord, p), lowers_drop(m, ord, b, nloc, ncore, place, target, pre, ct),
        fr_rel(f1, fcs), f1.locals.len() == nloc, fcs.locals.len() == ncore, fuel > 0,
        drop_step(m, cpol(pol), b, place, target as nat, f1, fuel) is Jump,
        place_ty(m, b, place) matches Some(t) && drop_row(m, t) matches Some(d) && !(d.empty || vec_int(m, t)),
    ensures ({
        let st = drop_step(m, cpol(pol), b, place, target as nat, f1, fuel);
        let (fct, ept) = ctcore::sem::exec_stmts(pre, 0, fcs);
        &&& ept == Seq::<Event>::empty() && fct.locals.len() == fcs.locals.len()
        &&& call_out(p, ct, fct, fuel) matches Some((f3c, e, x)) && fr_rel(st->Jump_1, f3c) && e == st->Jump_2 && st->Jump_3 == 1 + pre.len() + x
            && f3c.locals.len() == fcs.locals.len()
        &&& st->Jump_1.locals.len() == f1.locals.len() && st->Jump_0 == target
    }),
    decreases fuel, 1nat,
{
    hide(ctcore::sem::call_enter);
    hide(ctcore::sem::call_leave);
    hide(ctcore::sem::ops_ev);
    hide(ctcore::sem::op_vals);
    hide(mir_entry);
    hide(call_slots);
    hide(eval_ops);
    hide(eval_place);
    hide(return_to);
    hide(store);
    hide(lowers_body);
    hide(lowers_call);
    hide(lowers_drop);
    hide(body_sim_pre);
    hide(call_step);
    hide(drop_step);
    hide(body_call);
    hide(mir_run);
    hide(fr_rel);
    let t = place_ty(m, b, place)->Some_0;
    let d = drop_row(m, t)->Some_0;
    let (jg, gb) = glue_of(m, d.glue)->Some_0;
    let s0 = pre[0];
    let x = s0->Assign_0.local as nat;
    let cp = s0->Assign_1->RefMut_0;
    let y = ct->Call_2;
    assert(glue_of(m, d.glue) is Some && no_index(place) && pre.len() == 1 && s0 is Assign && s0->Assign_0.proj@.len() == 0
        && s0->Assign_1 is RefMut && lowers_place(m, b, place, cp, true) && nloc <= x < ncore
        && ct is Call && ct->Call_0 is Fn && fn_of(ord, ct->Call_0->Fn_0, jg) && ct->Call_3 == target
        && ct->Call_1@.len() == 1 && is_tmp(ct->Call_1@[0], x) && y.proj@.len() == 0 && nloc <= y.local < ncore && y.local != x) by { reveal(lowers_drop); }
    lemma_drop_parts(m, cpol(pol), b, place, target as nat, f1, fuel);
    let (l, e) = (eval_place(f1, place)->Some_0.0->At_0, eval_place(f1, place)->Some_0.1);
    let vs = seq![Val::Mut(l)];
    lemma_body_call_ok(m, cpol(pol), jg, gb, vs, f1, fuel);
    lemma_noidx_ev(f1, place);
    // x = &mut place
    lemma_lowers_place(m, b, place, cp, true);
    lemma_place(f1, fcs, place, cp);
    lemma_tmp_assign(fcs, s0, x);
    let fct = Frame { locals: fcs.locals.update(x as int, Val::Mut(l)), slots: fcs.slots };
    assert(ctcore::sem::eval_rv(fcs, s0->Assign_1) == (Val::Mut(l), Seq::<Event>::empty()));
    assert(ctcore::sem::exec_stmts(pre, 1, fct) == (fct, Seq::<Event>::empty()));
    assert(ctcore::sem::exec_stmts(pre, 0, fcs) == (fct, Seq::<Event>::empty() + Seq::<Event>::empty()));
    assert(Seq::<Event>::empty() + Seq::<Event>::empty() == Seq::<Event>::empty());
    assert(fr_rel(f1, fct)) by {
        reveal(fr_rel);
        assert forall|i: int| 0 <= i < f1.locals.len() implies #[trigger] f1.locals[i] == fct.locals[i] by { assert(f1.locals[i] == fcs.locals[i]); }
    }
    // the call of the glue's fn on `x`
    let cargs = ct->Call_1@;
    lemma_eval_tmp(fct, cargs[0], x);
    assert(ctcore::sem::op_vals(fct, cargs) =~= vs) by { reveal(ctcore::sem::op_vals); }
    assert(ctcore::sem::ops_ev(fct, cargs) == Seq::<Event>::empty()) by { reveal(ctcore::sem::ops_ev); lemma_ops_ev_dep(fct, cargs, x, x + 1); }
    let h = ct->Call_0->Fn_0 as nat;
    assert(h < ord.len() && ord[h as int] as nat == jg);
    assert(fn_ok(m, pol, ord, p, h as int));
    let rh = choose|rh: Seq<bool>| lowers_body(m, pol, ord, ord[h as int] as nat, p.fns@[h as int], rh);
    assert(lowers_body(m, pol, ord, ord[h as int] as nat, p.fns@[h as int], rh));
    lemma_lb_entry(m, pol, ord, jg, p.fns@[h as int], rh);
    assert(body_sim_pre(m, pol, ord, jg, p, h, rh)) by { reveal(body_sim_pre); }
    let me = mir_entry(m, jg, vs, call_slots(m, gb, f1, vs));
    lemma_call_entry(m, jg, gb, p, h, f1, fct, cargs, vs);
    let (cfe, wb, ae) = ctcore::sem::call_enter(p, h, fct, cargs);
    lemma_block(m, pol, ord, jg, p, h, rh, 0, me, cfe, (fuel - 1) as nat);
    let o = mir_run(m, cpol(pol), jg, me, (fuel - 1) as nat);
    assert(o == run_block(m, cpol(pol), inst_body(m, jg)->Some_0, 0, me, (fuel - 1) as nat)) by { reveal(mir_run); }
    assert(o is Done);
    let (cf, e2, s2) = (o->Done_0, o->Done_1, o->Done_2);
    let (cfc, _, _) = ctcore::sem::run_from(p, h, 0, cfe, (fuel - 1) as nat)->Some_0;
    assert(ctcore::sem::run_from(p, h, 0, cfe, (fuel - 1) as nat) == Some((cfc, e2, s2)));
    assert(fr_rel(cf, cfc));
    // write-back, then the unit result into temp y
    let (v, f2) = return_to(m, gb, f1, vs, cf)->Some_0;
    assert(write_back(m, gb, f1, vs, cf.slots, vs.len()) == Some(f2)) by { reveal(return_to); }
    assert(fr_rel(cf, cfc) ==> cf.slots == cfc.slots) by { reveal(fr_rel); }
    lemma_wb(m, gb, f1, fct, vs, cf.slots, 1);
    assert(wb_of(vs).subrange(0, 1) =~= wb_of(vs));
    assert(wb == wb_of(vs) && ae == Seq::<Event>::empty());
    let gw = ctcore::sem::write_back(fct, cfc.slots, wb);
    assert(fr_rel(f2, gw));
    let rv = ctcore::sem::nth(cfc.locals, 0);
    assert(ctcore::sem::place_walk(gw, y) == (Cur::L(ctcore::sem::local_loc(y.local as nat)), Seq::<Event>::empty()));
    assert(ctcore::sem::call_leave(fct, cfc, wb, y) == (ctcore::sem::write_loc(gw, ctcore::sem::local_loc(y.local as nat), rv), Seq::<Event>::empty()))
        by { reveal(ctcore::sem::call_leave); }
    lemma_tmp_write(f2, gw, y.local as nat, rv);
    let st = drop_step(m, cpol(pol), b, place, target as nat, f1, fuel);
    assert(st == Step::Jump(target as nat, f2, e + e2, 2 + s2));
    assert(e + e2 == ae + e2 + Seq::<Event>::empty());
    lemma_body_out(p, ct, fct, fuel, h, wb, ae, cfe, cfc, e2, s2, f2, st, Seq::<Event>::empty(), pre.len());
}

spec fn reveal_fr_slots(cf: Frame, cfc: Frame) -> bool { fr_rel(cf, cfc) ==> cf.slots == cfc.slots }

/// A drop terminator that jumps.
proof fn lemma_drop_facts(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, p: c::Program, g: nat, r: Seq<bool>, bb: nat, fm: Frame, fc: Frame, fuel: nat) -> (fnext: Frame)
    requires body_sim_pre(m, pol, ord, j, p, g, r), blk_pre_ok(m, pol, ord, j, p, g, r, bb), fuel > 0, bb < r.len(), r[bb as int],
        post_stmts(m, pol, j, p, g, bb, fm, fc, fuel),
        step_term(m, cpol(pol), inst_body(m, j)->Some_0, inst_body(m, j)->Some_0.blocks@[bb as int].terminator.kind, blk_f1(m, inst_body(m, j)->Some_0, bb, fm), fuel) is Jump,
        inst_body(m, j)->Some_0.blocks@[bb as int].terminator.kind is Drop,
    ensures jump_sim(m, pol, j, p, g, r, bb, fm, fc, fuel, fnext),
    decreases fuel, 2nat,
{
    hide(call_step);
    hide(drop_step);
    hide(body_call);
    hide(mir_run);
    hide(exec_stmts);
    hide(ctcore::sem::exec_stmts);
    hide(xs);
    hide(fr_rel);
    hide(run_block);
    hide(ctcore::sem::run_from);
    hide(lowers_body);
    hide(lowers_term_at);
    hide(step_term);
    hide(blk_pre_ok);
    hide(body_sim_pre);
    hide(post_stmts);
    hide(lowers_term);
    hide(ss_rel);
    hide(lowers_drop);
    hide(call_out);
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
    assert(g < p.fns@.len() && prog_ok(m, pol, ord, p)) by { reveal(body_sim_pre); }
    assert(lowers_term(m, pol, ord, b, nloc, ncore, kind, pre, cblk.term) && succs_in(kind, marks(r)) && bb < cb.blocks@.len()) by { reveal(blk_pre_ok); }
    lemma_post_jump(m, pol, j, p, g, bb, fm, fc, fuel);
    let (place, target) = (kind->Drop_place, kind->Drop_target);
    lemma_step_cd(m, cpol(pol), b, kind, f1, fuel);
    reveal(lowers_term);
    let base = choose|base: nat| tmps_in(base, pre.len(), nloc, ncore) && #[trigger] lowers_term_at(m, pol, ord, b, nloc, ncore, kind, pre, cblk.term, base);
    assert(lowers_drop(m, ord, b, nloc, ncore, place, target, pre, cblk.term)) by { reveal(lowers_term_at); }
    let ct = cblk.term;
    lemma_jump_reached_cd(kind, marks(r), st, m, cpol(pol), b, f1, fuel);
    lemma_marks_len(r, target as nat);
    let t = place_ty(m, b, place)->Some_0;
    assert(place_ty(m, b, place) is Some && drop_row(m, t) is Some && no_index(place)) by { reveal(lowers_drop); }
    let d = drop_row(m, t)->Some_0;
    if d.empty || vec_int(m, t) {
        assert(pre.len() == 0 && ct == c::Term::Goto(target)) by { reveal(lowers_drop); }
        lemma_drop_noop(m, cpol(pol), b, place, target as nat, f1, fuel);
        lemma_noidx_ev(f1, place);
        lemma_xs_empty(cs, lo, fcs);
        assert(cs.len() == lo);
        assert(ctcore::sem::exec_stmts(pre, 0, fcs) == (fcs, Seq::<Event>::empty())) by { reveal(ctcore::sem::exec_stmts); }
        assert(ce1 + Seq::<Event>::empty() == ce1);
        lemma_run_from_jump(p, g, bb, fc, fuel);
        fcs
    } else {
        lemma_drop_glue(m, pol, ord, b, nloc, ncore, place, target, pre, ct, f1, fcs, fuel, p);
        let (fct, ept) = ctcore::sem::exec_stmts(pre, 0, fcs);
        let (f3c, ec, x) = call_out(p, ct, fct, fuel)->Some_0;
        assert(ct is Call) by { reveal(lowers_drop); }
        assert(ct->Call_3 == target) by { reveal(lowers_drop); }
        lemma_rf_call(p, g, bb, fc, fuel);
        assert(ce1 + ept == ce1);
        assert(cs.len() == lo + pre.len());
        f3c
    }
}

/// A call or drop jumps to its target.
proof fn lemma_jump_reached_cd(kind: TerminatorKind, rs: Set<nat>, st: Step, m: MirCrate, pol: CallPolicy, b: Body, f1: Frame, fuel: nat)
    requires succs_in(kind, rs), st == step_term(m, pol, b, kind, f1, fuel), st is Jump, kind is Call || kind is Drop,
    ensures rs.contains(st->Jump_0),
        kind is Call ==> kind->Call_target is Some && st->Jump_0 == kind->Call_target->Some_0,
        kind is Drop ==> st->Jump_0 == kind->Drop_target,
{
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
