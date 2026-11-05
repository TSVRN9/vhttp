//! Progress for the subset: on an `in_subset` instance, a run's outcome is never `Unsup`, from
//! any frame at any fuel. So a `None` from `mir_run_fn` there is a `Panic` or `Fuel`. Proved per
//! terminator, then by induction on fuel over the closure `s` and the block sets `rs`.
#[cfg(verus_keep_ghost)]
use crate::mir::*;
#[cfg(verus_keep_ghost)]
use crate::sem::*;
#[cfg(verus_keep_ghost)]
use ctcore::sem::{Frame, Val};
use vstd::prelude::*;

verus! {

/// `find_from` returns an index in range at which `p` holds.
pub proof fn lemma_find<T>(s: Seq<T>, p: spec_fn(T) -> bool, k: nat)
    ensures find_from(s, p, k) matches Some(i) ==> k <= i < s.len() && p(s[i as int]),
    decreases s.len() - k,
{
    if k < s.len() && !p(s[k as int]) { lemma_find(s, p, k + 1); }
}

/// The induction hypothesis at fuel `f`: no callee in `s` and no block of `rs(j)` gives `Unsup`.
pub open spec fn ih(m: MirCrate, pol: CallPolicy, s: Set<nat>, rs: spec_fn(nat) -> Set<nat>, f: nat) -> bool {
    (forall|j: nat, fr: Frame| #[trigger] s.contains(j) ==> !(#[trigger] mir_run(m, pol, j, fr, f) is Unsup))
    && (forall|j: nat, bb: nat, fr: Frame| s.contains(j) && #[trigger] rs(j).contains(bb)
        ==> !(#[trigger] run_block(m, pol, inst_body(m, j)->Some_0, bb, fr, f) is Unsup))
}

/// A terminator step that is not `Unsup` and only jumps into `r`.
pub open spec fn step_good(st: Step, r: Set<nat>) -> bool {
    match st { Step::Jump(t, _, _, _) => r.contains(t), Step::Stop(o) => !(o is Unsup) }
}

proof fn lemma_body_call(m: MirCrate, pol: CallPolicy, s: Set<nat>, rs: spec_fn(nat) -> Set<nat>, j: nat, cb: Body, vs: Seq<Val>, fr: Frame, fuel: nat)
    requires fuel > 0, ih(m, pol, s, rs, (fuel - 1) as nat), s.contains(j),
    ensures body_call(m, pol, j, cb, vs, fr, fuel) matches Err(o) ==> !(o is Unsup),
{
    if args_ok(m, cb, fr, vs) {
        let f = mir_entry(m, j, vs, call_slots(m, cb, fr, vs));
        assert(!(mir_run(m, pol, j, f, (fuel - 1) as nat) is Unsup));
    }
}

proof fn lemma_call(m: MirCrate, pol: CallPolicy, s: Set<nat>, rs: spec_fn(nat) -> Set<nat>, b: Body, t: TerminatorKind, fr: Frame, fuel: nat, r: Set<nat>)
    requires fuel > 0, ih(m, pol, s, rs, (fuel - 1) as nat), t is Call, term_ok(m, pol, b, t), callees_in(m, pol, b, t, s), succs_in(t, r),
    ensures step_good(step_term(m, pol, b, t, fr, fuel), r),
{
    let (func, args, dest) = (t->Call_func, t->Call_args@, t->Call_destination);
    if t->Call_target is None { return; }
    let (j, g) = callee_of(m, func)->Some_0;
    if !is_leaf(m, pol, m.insts@[j as int].key@, g) {
        let cb = inst_body(m, j)->Some_0;
        match (eval_ops(m, fr, args, args.len()), eval_place(fr, dest)) {
            (Some((vs, _, _)), Some((PRes::At(_), _))) => lemma_body_call(m, pol, s, rs, j, cb, vs, fr, fuel),
            _ => {},
        }
    }
}

proof fn lemma_drop(m: MirCrate, pol: CallPolicy, s: Set<nat>, rs: spec_fn(nat) -> Set<nat>, b: Body, t: TerminatorKind, fr: Frame, fuel: nat, r: Set<nat>)
    requires fuel > 0, ih(m, pol, s, rs, (fuel - 1) as nat), t is Drop, term_ok(m, pol, b, t), callees_in(m, pol, b, t, s), succs_in(t, r),
    ensures step_good(step_term(m, pol, b, t, fr, fuel), r),
{
    let place = t->Drop_place;
    let ty = place_ty(m, b, place)->Some_0;
    let d = drop_row(m, ty)->Some_0;
    if !(d.empty || vec_int(m, ty)) {
        let (j, gb) = glue_of(m, d.glue)->Some_0;
        match eval_place(fr, place) {
            Some((PRes::At(l), _)) => lemma_body_call(m, pol, s, rs, j, gb, seq![Val::Mut(l)], fr, fuel),
            _ => {},
        }
    }
}

proof fn lemma_switch(m: MirCrate, fr: Frame, x: Operand, tg: SwitchTargets, r: Set<nat>)
    requires r.contains(tg.otherwise as nat), forall|k: int| 0 <= k < tg.branches@.len() ==> r.contains((#[trigger] tg.branches@[k]).1 as nat),
    ensures step_good(switch_step(m, fr, x, tg), r),
{
    if let Some((Val::Int(d), _, _)) = eval_op(m, fr, x) {
        let p = |br: (u128, BasicBlockIdx)| br.0 == d;
        lemma_find(tg.branches@, p, 0);
        if let Some(k) = find(tg.branches@, p) { assert(r.contains(tg.branches@[k as int].1 as nat)); }
    }
}

/// Per construct: an in-subset terminator steps to a non-`Unsup` outcome or into `r`.
pub proof fn lemma_term(m: MirCrate, pol: CallPolicy, s: Set<nat>, rs: spec_fn(nat) -> Set<nat>, b: Body, t: TerminatorKind, fr: Frame, fuel: nat, r: Set<nat>)
    requires fuel > 0, ih(m, pol, s, rs, (fuel - 1) as nat), term_ok(m, pol, b, t), callees_in(m, pol, b, t, s), succs_in(t, r),
    ensures step_good(step_term(m, pol, b, t, fr, fuel), r),
{
    match t {
        TerminatorKind::Call { .. } => lemma_call(m, pol, s, rs, b, t, fr, fuel, r),
        TerminatorKind::Drop { .. } => lemma_drop(m, pol, s, rs, b, t, fr, fuel, r),
        TerminatorKind::SwitchInt { discr, targets } => lemma_switch(m, fr, discr, targets, r),
        _ => {},
    }
}

/// The induction on fuel.
pub proof fn lemma_ih(m: MirCrate, pol: CallPolicy, s: Set<nat>, rs: spec_fn(nat) -> Set<nat>, fuel: nat)
    requires closed(m, pol, s, rs),
    ensures ih(m, pol, s, rs, fuel),
    decreases fuel,
{
    if fuel > 0 {
        lemma_ih(m, pol, s, rs, (fuel - 1) as nat);
        assert forall|j: nat, bb: nat, fr: Frame| s.contains(j) && #[trigger] rs(j).contains(bb)
            implies !(#[trigger] run_block(m, pol, inst_body(m, j)->Some_0, bb, fr, fuel) is Unsup) by {
            lemma_block(m, pol, s, rs, j, bb, fr, fuel);
        };
        assert forall|j: nat, fr: Frame| #[trigger] s.contains(j) implies !(#[trigger] mir_run(m, pol, j, fr, fuel) is Unsup) by {
            assert(body_in(m, pol, s, rs, j));
            lemma_block(m, pol, s, rs, j, 0, fr, fuel);
        };
    }
}

proof fn lemma_block(m: MirCrate, pol: CallPolicy, s: Set<nat>, rs: spec_fn(nat) -> Set<nat>, j: nat, bb: nat, fr: Frame, fuel: nat)
    requires closed(m, pol, s, rs), s.contains(j), rs(j).contains(bb), fuel > 0, ih(m, pol, s, rs, (fuel - 1) as nat),
    ensures !(run_block(m, pol, inst_body(m, j)->Some_0, bb, fr, fuel) is Unsup),
{
    assert(body_in(m, pol, s, rs, j));
    let b = inst_body(m, j)->Some_0;
    let blk = b.blocks@[bb as int];
    assert(bb < b.blocks@.len() && block_ok(m, pol, b, blk));
    reveal(block_ok);
    match exec_stmts(m, b, fr, blk.statements@, blk.statements@.len()) {
        Some((f1, e1, s1)) => {
            let st = step_term(m, pol, b, blk.terminator.kind, f1, fuel);
            lemma_term(m, pol, s, rs, b, blk.terminator.kind, f1, fuel, rs(j));
            match st {
                Step::Jump(t, f2, _, _) => {
                    assert(rs(j).contains(t));
                    assert(!(run_block(m, pol, b, t, f2, (fuel - 1) as nat) is Unsup));
                },
                Step::Stop(_) => {},
            }
        },
        None => {},
    }
}

/// **Progress.** On an in-subset instance no run is `Unsup`: a `None` from `mir_run_fn` is a panic
/// (in the sense of `Out::Panic`) or fuel.
pub proof fn theorem_in_subset_no_unsup(m: MirCrate, pol: CallPolicy, i: nat, fr: Frame, fuel: nat)
    requires in_subset(m, pol, i),
    ensures !(mir_run(m, pol, i, fr, fuel) is Unsup),
{
    let (s, rs) = choose|s: Set<nat>, rs: spec_fn(nat) -> Set<nat>| #[trigger] closed(m, pol, s, rs) && s.contains(i);
    lemma_ih(m, pol, s, rs, fuel);
}

} // verus!
