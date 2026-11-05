//! The MIR evaluator, part two: exec mirrors of `sem`'s terminators and block runs, and
//! `mir_eval`, proved against `mir_run`. A `Done`, `Panic` or `Fuel` it reports is `mir_run`'s;
//! `GaveUp` (a cap, a count past `u64`, an `Unsup` arm, an arm the evaluator leaves out) claims
//! nothing (addendum decision 2). Only in-subset instances run: the ghost witness `(s, rs)` of
//! `in_subset` makes every block the run enters `block_ok`, so no block is checked at run time.
use crate::eval::*;
use crate::eval_tab::*;
use crate::interp_val::*;
use crate::mir::*;
use crate::policy::Policy;
#[cfg(verus_keep_ghost)]
use crate::policy::cpol;
#[cfg(verus_keep_ghost)]
use crate::sem::*;
#[cfg(verus_keep_ghost)]
use ctcore::sem::Frame;
use vstd::prelude::*;

verus! {

pub enum Ev { Done(CFrame, u64), Panic, Fuel, GaveUp }

/// Addendum decision 2: each outcome the evaluator reports is the spec's.
pub open spec fn ev_ok(o: Out, r: Ev) -> bool {
    match r {
        Ev::Done(f, n) => o matches Out::Done(g, _, s) && fv(f) == g && n as nat == s,
        Ev::Panic => o is Panic,
        Ev::Fuel => o is Fuel,
        Ev::GaveUp => true,
    }
}

/// A terminator's outcome: a jump (or a `Return`) with its steps, the frame updated in place.
pub enum St { Jump(usize, u64), Ret(u64), Panic, Fuel, GaveUp }

pub open spec fn st_ok(f1: Frame, r: St, st: Step) -> bool {
    match r {
        St::Jump(t, n) => st matches Step::Jump(t2, f2, _, s2) && t2 == t as nat && f2 == f1 && s2 == n as nat,
        St::Ret(n) => st matches Step::Stop(Out::Done(f2, _, s2)) && f2 == f1 && s2 == n as nat,
        St::Panic => st matches Step::Stop(Out::Panic),
        St::Fuel => st matches Step::Stop(Out::Fuel),
        St::GaveUp => true,
    }
}

// ------------------------------------------------------------------ the subset witness

/// What `closed` gives for a block of an instance in `s`.
proof fn lemma_in(m: MirCrate, pol: CallPolicy, s: Set<nat>, rs: spec_fn(nat) -> Set<nat>, j: nat, b: Body, bb: nat)
    requires closed(m, pol, s, rs), s.contains(j), inst_body(m, j) == Some(b), rs(j).contains(bb),
    ensures bb < b.blocks@.len(), block_ok(m, pol, b, b.blocks@[bb as int]),
        succs_in(b.blocks@[bb as int].terminator.kind, rs(j)), callees_in(m, pol, b, b.blocks@[bb as int].terminator.kind, s),
{
    assert(body_in(m, pol, s, rs, j));
}

proof fn lemma_entry_in(m: MirCrate, pol: CallPolicy, s: Set<nat>, rs: spec_fn(nat) -> Set<nat>, j: nat)
    requires closed(m, pol, s, rs), s.contains(j),
    ensures inst_body(m, j) is Some, rs(j).contains(0),
{
    assert(body_in(m, pol, s, rs, j));
}

// ------------------------------------------------------------------ terminators

/// `SwitchInt`'s target: the first branch whose value is `d` (`find`), else `otherwise`.
fn switch_target(tg: &SwitchTargets, d: u128) -> (t: usize)
    ensures t as nat == match find(tg.branches@, |br: (u128, BasicBlockIdx)| br.0 == d) {
            Some(j) => tg.branches@[j as int].1 as nat,
            None => tg.otherwise as nat,
        },
        t == tg.otherwise || exists|k: int| 0 <= k < tg.branches@.len() && t == (#[trigger] tg.branches@[k]).1,
{
    let mut k: usize = 0;
    while k < tg.branches.len()
        invariant k <= tg.branches@.len(), forall|l: int| 0 <= l < k ==> (#[trigger] tg.branches@[l]).0 != d,
        decreases tg.branches.len() - k,
    {
        if tg.branches[k].0 == d {
            proof { crate::look::lemma_find(tg.branches@, |br: (u128, BasicBlockIdx)| br.0 == d, k as nat); }
            return tg.branches[k].1;
        }
        k += 1;
    }
    proof { crate::look::lemma_find(tg.branches@, |br: (u128, BasicBlockIdx)| br.0 == d, k as nat); }
    tg.otherwise
}

fn e_switch(m: &MirCrate, tb: &Tabs, fr: &CFrame, x: &Operand, tg: &SwitchTargets) -> (r: St)
    requires tabs_ok(*m, *tb),
    ensures st_ok(fv(*fr), r, switch_step(*m, fv(*fr), *x, *tg)),
        r matches St::Jump(t, _) ==> t == tg.otherwise || exists|k: int| 0 <= k < tg.branches@.len() && t == (#[trigger] tg.branches@[k]).1,
{
    match e_eval_op(m, tb, fr, x) {
        Ok((CVal::Int(d), k)) => {
            if k == u64::MAX { return St::GaveUp; }
            St::Jump(switch_target(tg, d), 1 + k)
        },
        Ok((_v, _)) => { proof { lemma_cv(_v); } St::Panic },
        Err(Halt::Panic) => St::Panic,
        Err(Halt::GaveUp) => St::GaveUp,
    }
}

fn e_assert(m: &MirCrate, tb: &Tabs, fr: &CFrame, x: &Operand, expected: bool, target: BasicBlockIdx) -> (r: St)
    requires tabs_ok(*m, *tb),
    ensures st_ok(fv(*fr), r, assert_step(*m, fv(*fr), *x, expected, target)), r matches St::Jump(t, _) ==> t == target,
{
    match e_eval_op(m, tb, fr, x) {
        Ok((CVal::Int(c), k)) => {
            if (c == 0 || c == 1) && (c == 1) == expected {
                if k == u64::MAX { return St::GaveUp; }
                St::Jump(target, 1 + k)
            } else { St::Panic }
        },
        Ok((_v, _)) => { proof { lemma_cv(_v); } St::Panic },
        Err(Halt::Panic) => St::Panic,
        Err(Halt::GaveUp) => St::GaveUp,
    }
}

/// `step_term` (call-free: `Call` and `Drop` give up).
#[allow(unused_variables)] // used by the call arms (T2b)
fn e_step_term(m: &MirCrate, tb: &Tabs, pol: &Policy, Ghost(s): Ghost<Set<nat>>, Ghost(rs): Ghost<spec_fn(nat) -> Set<nat>>,
    j: usize, b: &Body, bb: usize, fr: &mut CFrame, fuel: u64) -> (r: St)
    requires
        tabs_ok(*m, *tb), closed(*m, cpol(*pol), s, rs), s.contains(j as nat), *b == inst_body(*m, j as nat)->Some_0,
        inst_body(*m, j as nat) is Some, rs(j as nat).contains(bb as nat), bb < b.blocks@.len(), fuel > 0,
        succs_in(b.blocks@[bb as int].terminator.kind, rs(j as nat)),
    ensures
        st_ok(fv(*final(fr)), r, step_term(*m, cpol(*pol), *b, b.blocks@[bb as int].terminator.kind, fv(*old(fr)), fuel as nat)),
        r matches St::Jump(t, _) ==> rs(j as nat).contains(t as nat),
{
    match &b.blocks[bb].terminator.kind {
        TerminatorKind::Goto { target } => St::Jump(*target, 1),
        TerminatorKind::SwitchInt { discr, targets } => e_switch(m, tb, fr, discr, targets),
        TerminatorKind::Assert { cond, expected, msg: _, target, unwind: _ } => e_assert(m, tb, fr, cond, *expected, *target),
        TerminatorKind::Return => St::Ret(1),
        TerminatorKind::Unreachable | TerminatorKind::Abort => St::Panic,
        _ => St::GaveUp,
    }
}

// ------------------------------------------------------------------ runs

/// `cur` is what remains of `o0` after `k` steps.
pub open spec fn rel_out(o0: Out, cur: Out, k: nat) -> bool {
    match cur {
        Out::Done(g, _, n) => o0 matches Out::Done(g0, _, n0) && g0 == g && n0 == n + k,
        Out::Panic => o0 is Panic,
        Out::Fuel => o0 is Fuel,
        Out::Unsup => o0 is Unsup,
    }
}

/// `run_block` from block `bb` of instance `j`'s body, looping over the jumps.
#[verifier::loop_isolation(false)]
fn e_blocks(m: &MirCrate, tb: &Tabs, pol: &Policy, Ghost(s): Ghost<Set<nat>>, Ghost(rs): Ghost<spec_fn(nat) -> Set<nat>>,
    j: usize, b: &Body, fr: CFrame, fuel: u64) -> (r: Ev)
    requires
        tabs_ok(*m, *tb), closed(*m, cpol(*pol), s, rs), s.contains(j as nat), inst_body(*m, j as nat) == Some(*b),
    ensures ev_ok(run_block(*m, cpol(*pol), *b, 0, fv(fr), fuel as nat), r),
{
    let ghost p = cpol(*pol);
    let ghost o0 = run_block(*m, p, *b, 0, fv(fr), fuel as nat);
    proof { lemma_entry_in(*m, p, s, rs, j as nat); }
    let mut fr = fr;
    let mut bb: usize = 0;
    let mut fc: u64 = fuel;
    let mut steps: u64 = 0;
    loop
        invariant
            fc <= fuel, rs(j as nat).contains(bb as nat),
            rel_out(o0, run_block(*m, p, *b, bb as nat, fv(fr), fc as nat), steps as nat),
        decreases fc,
    {
        if fc == 0 { return Ev::Fuel; }
        proof { lemma_in(*m, p, s, rs, j as nat, *b, bb as nat); }
        let ghost f0 = fv(fr);
        let blk = &b.blocks[bb];
        let n1 = match e_exec_stmts(m, tb, b, &mut fr, &blk.statements) {
            Ok(n) => n,
            Err(Halt::Panic) => return Ev::Panic,
            Err(Halt::GaveUp) => return Ev::GaveUp,
        };
        let st = e_step_term(m, tb, pol, Ghost(s), Ghost(rs), j, b, bb, &mut fr, fc);
        match st {
            St::Jump(t, n2) => {
                if steps > u64::MAX - n1 || steps + n1 > u64::MAX - n2 { return Ev::GaveUp; }
                steps = steps + n1 + n2;
                bb = t;
            },
            St::Ret(n2) => {
                if steps > u64::MAX - n1 || steps + n1 > u64::MAX - n2 { return Ev::GaveUp; }
                return Ev::Done(fr, steps + n1 + n2);
            },
            St::Panic => return Ev::Panic,
            St::Fuel => return Ev::Fuel,
            St::GaveUp => return Ev::GaveUp,
        }
        fc = fc - 1;
    }
}

/// `mir_run` of instance `j` from `fr`.
pub fn e_run(m: &MirCrate, tb: &Tabs, pol: &Policy, Ghost(s): Ghost<Set<nat>>, Ghost(rs): Ghost<spec_fn(nat) -> Set<nat>>,
    j: usize, fr: CFrame, fuel: u64) -> (r: Ev)
    requires tabs_ok(*m, *tb), closed(*m, cpol(*pol), s, rs), s.contains(j as nat),
    ensures ev_ok(mir_run(*m, cpol(*pol), j as nat, fv(fr), fuel as nat), r),
{
    match t_inst_body(m, tb, j) {
        Some(b) => e_blocks(m, tb, pol, Ghost(s), Ghost(rs), j, b, fr, fuel),
        None => Ev::GaveUp,
    }
}

/// **The evaluator.** A `Done`, `Panic` or `Fuel` is `mir_run`'s from `mir_entry` (addendum
/// decision 2).
pub fn mir_eval(m: &MirCrate, tb: &Tabs, pol: &Policy, i: usize, args: &Vec<CVal>, slots: &Vec<CVal>, fuel: u64) -> (r: Ev)
    requires tabs_ok(*m, *tb), in_subset(*m, cpol(*pol), i as nat),
    ensures ev_ok(mir_run(*m, cpol(*pol), i as nat, mir_entry(*m, i as nat, cvs(args@), cvs(slots@)), fuel as nat), r),
{
    let ghost (s, rs) = choose|s: Set<nat>, rs: spec_fn(nat) -> Set<nat>| #[trigger] closed(*m, cpol(*pol), s, rs) && s.contains(i as nat);
    match e_mir_entry(m, tb, i, clone_vec(args), clone_vec(slots)) {
        Ok(fr) => e_run(m, tb, pol, Ghost(s), Ghost(rs), i, fr, fuel),
        Err(_) => Ev::GaveUp,
    }
}

} // verus!
