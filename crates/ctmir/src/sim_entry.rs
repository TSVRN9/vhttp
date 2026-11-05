//! The simulation, entry frames and the theorem: the entry frames are equal on the MIR locals, and a
//! completed MIR run of a translated fn is core's run of its image.
#[allow(unused_imports)]
use crate::lower::FnInfo;
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
use crate::sim_run::*;
#[allow(unused_imports)]
use crate::sim_call::*;
#[allow(unused_imports)]
use ctcore::sem::{Frame, Loc, Root, Val};
#[allow(unused_imports)]
use ctcore::syntax as c;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

verus! {

pub open spec fn pointee(m: MirCrate, t: Ty) -> Ty { rigid(m, t)->Some_0->Ref_1 }

/// The entry arguments of `insts[i]`: one argument and one slot per parameter; every argument is a
/// well-typed value of its parameter's type; a `&mut T` parameter's slot is a well-typed `T`, any
/// other parameter's slot is `Unit` (as core's `call_enter` makes it).
pub open spec fn wt_args(m: MirCrate, i: nat, args: Seq<Val>, slots: Seq<Val>) -> bool {
    inst_body(m, i) matches Some(b) && args.len() == b.arg_count && slots.len() == b.arg_count && b.arg_count < b.locals@.len()
    && forall|j: int| 0 <= j < b.arg_count ==> {
        &&& wt_val(m, b.locals@[j + 1].ty, #[trigger] args[j])
        &&& if is_mut_ref(m, b.locals@[j + 1].ty) { wt_val(m, pointee(m, b.locals@[j + 1].ty), slots[j]) } else { slots[j] == Val::Unit }
    }
}

/// A well-typed value of a type free of `&mut` holds no `Mut`.
pub proof fn lemma_wt_mf(m: MirCrate, ty: Ty, v: Val, fuel: nat)
    requires wt_rec(m, ty, v), ty_free(m, ty, fuel, false),
    ensures mut_free(v),
    decreases v,
{
    let (t, fu) = match rigid(m, ty) { Some(RigidTy::Pat(base, _)) => (base, (fuel - 1) as nat), _ => (ty, fuel) };
    assert(t == strip_pat(m, ty));
    assert(ty_free(m, t, fu, false));
    let f = (fu - 1) as nat;
    match v {
        Val::Tup(vs) => {
            let ts = rigid(m, t)->Some_0->Tuple_0;
            assert forall|i: int| 0 <= i < vs.len() implies mut_free(#[trigger] vs[i]) by { lemma_wt_mf(m, ts@[i], vs[i], f); }
        },
        Val::Arr(vs) => {
            let e = match rigid(m, t)->Some_0 { RigidTy::Array(e, _) => e, RigidTy::Slice(e) => e, _ => vec_elem(m, t)->Some_0 };
            assert forall|i: int| 0 <= i < vs.len() implies mut_free(#[trigger] vs[i]) by { lemma_wt_mf(m, e, vs[i], f); }
        },
        Val::Adt(k, vs) => {
            let a = adt_row(m, t)->Some_0;
            assert forall|i: int| 0 <= i < vs.len() implies mut_free(#[trigger] vs[i]) by {
                assert(ty_free(m, a.variants@[k as int].fields@[i], f, false));
                lemma_wt_mf(m, a.variants@[k as int].fields@[i], vs[i], f);
            }
        },
        Val::Shr(b) => { lemma_wt_mf(m, rigid(m, t)->Some_0->Ref_1, *b, f); },
        _ => {},
    }
}

/// Well-typed values keep arrays within `usize`.
pub proof fn lemma_wt_len(m: MirCrate, ty: Ty, v: Val)
    requires wt_rec(m, ty, v),
    ensures ctcore::sem::len_ok(v),
    decreases v,
{
    let t = strip_pat(m, ty);
    match v {
        Val::Tup(vs) => {
            let ts = rigid(m, t)->Some_0->Tuple_0;
            assert forall|i: int| 0 <= i < vs.len() implies ctcore::sem::len_ok(#[trigger] vs[i]) by { lemma_wt_len(m, ts@[i], vs[i]); }
        },
        Val::Arr(vs) => {
            let e = match rigid(m, t)->Some_0 { RigidTy::Array(e, _) => e, RigidTy::Slice(e) => e, _ => vec_elem(m, t)->Some_0 };
            assert forall|i: int| 0 <= i < vs.len() implies ctcore::sem::len_ok(#[trigger] vs[i]) by { lemma_wt_len(m, e, vs[i]); }
        },
        Val::Adt(k, vs) => {
            let a = adt_row(m, t)->Some_0;
            assert forall|i: int| 0 <= i < vs.len() implies ctcore::sem::len_ok(#[trigger] vs[i]) by { lemma_wt_len(m, a.variants@[k as int].fields@[i], vs[i]); }
        },
        Val::Shr(b) => { lemma_wt_len(m, rigid(m, t)->Some_0->Ref_1, *b); },
        _ => {},
    }
}

pub proof fn lemma_mf_no_mut(v: Val)
    requires mut_free(v),
    ensures ctcore::ct::no_mut(v),
    decreases v,
{
    match v {
        Val::Tup(vs) => { assert forall|i: int| 0 <= i < vs.len() implies ctcore::ct::no_mut(#[trigger] vs[i]) by { lemma_mf_no_mut(vs[i]); } },
        Val::Adt(_, vs) => { assert forall|i: int| 0 <= i < vs.len() implies ctcore::ct::no_mut(#[trigger] vs[i]) by { lemma_mf_no_mut(vs[i]); } },
        Val::Arr(vs) => { assert forall|i: int| 0 <= i < vs.len() implies ctcore::ct::no_mut(#[trigger] vs[i]) by { lemma_mf_no_mut(vs[i]); } },
        Val::Shr(b) => lemma_mf_no_mut(*b),
        _ => {},
    }
}

/// The core type is `Mut` exactly when the MIR type is `&mut`.
pub proof fn lemma_lowers_ty_mut(m: MirCrate, t: Ty, ct: c::Ty, fuel: nat)
    requires lowers_ty(m, t, ct, fuel),
    ensures (ct is Mut) == is_mut_ref(m, t),
{
    if rigid(m, t) matches Some(RigidTy::Adt(_, _)) {
        assert(lowers_adt_ty(m, t, ct, (fuel - 1) as nat));
    }
}

/// A parameter's facts: a non-`&mut` argument and every slot hold no `Mut`; `len_ok` throughout.
proof fn lemma_param(m: MirCrate, b: Body, args: Seq<Val>, slots: Seq<Val>, j: int)
    requires sig_ok(m, b), wt_args_at(m, b, args, slots, j), 0 <= j < b.arg_count,
    ensures !is_mut_ref(m, b.locals@[j + 1].ty) ==> mut_free(args[j]), mut_free(slots[j]),
        ctcore::sem::len_ok(args[j]), ctcore::sem::len_ok(slots[j]),
{
    let ty = b.locals@[j + 1].ty;
    assert(1 <= j + 1 <= b.arg_count);
    lemma_wt_len(m, ty, args[j]);
    if is_mut_ref(m, ty) {
        lemma_wt_mf(m, pointee(m, ty), slots[j], tfuel(m));
        lemma_wt_len(m, pointee(m, ty), slots[j]);
    } else {
        lemma_wt_mf(m, ty, args[j], tfuel(m));
    }
}

pub open spec fn wt_args_at(m: MirCrate, b: Body, args: Seq<Val>, slots: Seq<Val>, j: int) -> bool {
    &&& wt_val(m, b.locals@[j + 1].ty, args[j])
    &&& if is_mut_ref(m, b.locals@[j + 1].ty) { wt_val(m, pointee(m, b.locals@[j + 1].ty), slots[j]) } else { slots[j] == Val::Unit }
}

/// The entry frames are related (for any arguments, one per parameter: both sides put the same
/// values there).
pub proof fn lemma_entry(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, p: c::Program, g: nat, r: Seq<bool>, args: Seq<Val>, slots: Seq<Val>)
    requires g < p.fns@.len(), lowers_body(m, pol, ord, j, p.fns@[g as int], r), args.len() >= inst_body(m, j)->Some_0.arg_count,
    ensures ({
        let (fm, fc) = (mir_entry(m, j, args, slots), ctcore::sem::init_entry(p, g, args, slots));
        &&& fr_rel(fm, fc)
        &&& fm.locals.len() == inst_body(m, j)->Some_0.locals@.len() && fc.locals.len() == p.fns@[g as int].locals@.len()
    }),
{
    let b = inst_body(m, j)->Some_0;
    let cb = p.fns@[g as int];
    let (fm, fc) = (mir_entry(m, j, args, slots), ctcore::sem::init_entry(p, g, args, slots));
    assert forall|k: int| 0 <= k < fm.locals.len() implies #[trigger] fm.locals[k] == fc.locals[k] by {
        assert(lowers_ty(m, b.locals@[k].ty, cb.locals@[k], tyf()));
        lemma_lowers_ty_mut(m, b.locals@[k].ty, cb.locals@[k], tyf());
    }
}

/// `wt_args` gives ctcore's entry premises (`theorem_ct`'s `args_agree` facts, `theorem_cost`'s).
pub proof fn lemma_entry_premises(m: MirCrate, pol: Policy, root: Seq<u8>, p: c::Program, infos: Seq<FnInfo>, g: nat, args: Seq<Val>, slots: Seq<Val>)
    requires lowers(m, pol, root, p, infos), g < p.fns@.len(), wt_args(m, infos[g as int].inst as nat, args, slots),
    ensures ctcore::cost::entry_plc(p, g, args, slots), ctcore::cost::vals_len_ok(args), ctcore::cost::vals_len_ok(slots),
{
    let rs = choose|rs: Seq<Seq<bool>>| lowers_rs(m, pol, root, p, infos, rs);
    let j = infos[g as int].inst as nat;
    assert(lowers_body(m, pol, ords(infos), j, p.fns@[g as int], rs[g as int]));
    let b = inst_body(m, j)->Some_0;
    let cb = p.fns@[g as int];
    assert forall|j2: int| 0 <= j2 < b.arg_count implies #[trigger] wt_args_at(m, b, args, slots, j2) by {}
    assert forall|k: int| 0 <= k < cb.nargs implies
        (!(cb.locals@[1 + k] is Mut) ==> ctcore::ct::no_mut(#[trigger] args[k])) && ctcore::ct::no_mut(slots[k])
        && ctcore::sem::len_ok(args[k]) && ctcore::sem::len_ok(slots[k]) by {
        assert(lowers_ty(m, b.locals@[k + 1].ty, cb.locals@[k + 1], tyf()));
        lemma_lowers_ty_mut(m, b.locals@[k + 1].ty, cb.locals@[k + 1], tyf());
        lemma_param(m, b, args, slots, k);
        assert(cb.locals@[1 + k] == cb.locals@[k + 1]);
        if !is_mut_ref(m, b.locals@[k + 1].ty) { lemma_mf_no_mut(args[k]); }
        lemma_mf_no_mut(slots[k]);
    }
    assert forall|k: int| 0 <= k < cb.nargs && !(cb.locals@[1 + k] is Mut) implies ctcore::ct::no_mut(#[trigger] args[k]) by {}
    assert forall|k: int| 0 <= k < cb.nargs implies ctcore::ct::no_mut(#[trigger] slots[k]) by {
        lemma_param(m, b, args, slots, k);
        lemma_mf_no_mut(slots[k]);
    }
    assert forall|k: int| 0 <= k < args.len() implies ctcore::sem::len_ok(#[trigger] args[k]) by {}
    assert forall|k: int| 0 <= k < slots.len() implies ctcore::sem::len_ok(#[trigger] slots[k]) by { lemma_param(m, b, args, slots, k); }
}

/// A completed run keeps the frame's locals (MIR's writes never change a frame's shape).
pub proof fn lemma_run_len(m: MirCrate, pol: CallPolicy, b: Body, bb: nat, fm: Frame, fuel: nat)
    ensures run_block(m, pol, b, bb, fm, fuel) matches Out::Done(f2, _, _) ==> f2.locals.len() == fm.locals.len(),
    decreases fuel,
{
    if fuel > 0 && bb < b.blocks@.len() && block_ok(m, pol, b, b.blocks@[bb as int]) {
        let blk = b.blocks@[bb as int];
        lemma_stmts_mlen(m, b, fm, blk.statements@, blk.statements@.len());
        if let Some((f1, _, _)) = exec_stmts(m, b, fm, blk.statements@, blk.statements@.len()) {
            let st = step_term(m, pol, b, blk.terminator.kind, f1, fuel);
            lemma_step_len(m, pol, b, blk.terminator.kind, f1, fuel);
            if let Step::Jump(t, f2, _, _) = st { lemma_run_len(m, pol, b, t, f2, (fuel - 1) as nat); }
        }
    }
}

proof fn lemma_store_len(fr: Frame, l: Loc, w: Val)
    ensures store(fr, l, w) matches Some(f) ==> f.locals.len() == fr.locals.len(),
{
}

proof fn lemma_mwb_len(m: MirCrate, cb: Body, fr: Frame, vs: Seq<Val>, cs: Seq<Val>, n: nat)
    ensures write_back(m, cb, fr, vs, cs, n) matches Some(f) ==> f.locals.len() == fr.locals.len(),
    decreases n,
{
    if n > 0 && n <= vs.len() {
        lemma_mwb_len(m, cb, fr, vs, cs, (n - 1) as nat);
        if let Some(f) = write_back(m, cb, fr, vs, cs, (n - 1) as nat) { lemma_store_len(f, vs[n - 1]->Mut_0, cs[n - 1]); }
    }
}

proof fn lemma_leaf_len(m: MirCrate, pol: CallPolicy, key: Seq<u8>, gargs: GenericArgs, dty: Option<Ty>, vs: Seq<Val>, fr: Frame)
    ensures leaf_call(m, pol, key, gargs, dty, vs, fr) matches Some((_, f, _, _)) ==> f.locals.len() == fr.locals.len(),
{
}

proof fn lemma_bc_len(m: MirCrate, pol: CallPolicy, j: nat, cb: Body, vs: Seq<Val>, fr: Frame, fuel: nat)
    ensures body_call(m, pol, j, cb, vs, fr, fuel) matches Ok((_, f, _, _)) ==> f.locals.len() == fr.locals.len(),
{
    if body_call(m, pol, j, cb, vs, fr, fuel) is Ok {
        lemma_body_call_ok(m, pol, j, cb, vs, fr, fuel);
        let o = mir_run(m, pol, j, mir_entry(m, j, vs, call_slots(m, cb, fr, vs)), (fuel - 1) as nat);
        lemma_mwb_len(m, cb, fr, vs, o->Done_0.slots, vs.len());
    }
}

/// A step that jumps keeps the frame's locals.
proof fn lemma_step_len(m: MirCrate, pol: CallPolicy, b: Body, kind: TerminatorKind, f1: Frame, fuel: nat)
    ensures step_term(m, pol, b, kind, f1, fuel) matches Step::Jump(_, f2, _, _) ==> f2.locals.len() == f1.locals.len(),
        step_term(m, pol, b, kind, f1, fuel) matches Step::Stop(Out::Done(f2, _, _)) ==> f2 == f1,
{
    lemma_step_cd(m, pol, b, kind, f1, fuel);
    lemma_cd_done(m, pol, b, kind, f1, fuel);
    match kind {
        TerminatorKind::Call { func, args, destination, target: Some(tb), unwind: _ } => {
            if call_step(m, pol, b, func, args@, destination, tb as nat, f1, fuel) is Jump {
                lemma_call_parts(m, pol, b, func, args@, destination, tb as nat, f1, fuel);
                let (j, gargs) = callee_of(m, func)->Some_0;
                let (vs, _, _) = eval_ops(m, f1, args@, args@.len())->Some_0;
                let r = call_res(m, pol, b, j, gargs, vs, destination, f1, fuel);
                lemma_leaf_len(m, pol, m.insts@[j as int].key@, gargs, place_ty(m, b, destination), vs, f1);
                if let Some(cb) = inst_body(m, j) { lemma_bc_len(m, pol, j, cb, vs, f1, fuel); }
                lemma_store_len(r->Ok_0.1, eval_place(f1, destination)->Some_0.0->At_0, r->Ok_0.0);
            }
        },
        TerminatorKind::Drop { place, target, unwind: _ } => {
            if drop_step(m, pol, b, place, target as nat, f1, fuel) is Jump {
                let t = place_ty(m, b, place)->Some_0;
                let d = drop_row(m, t)->Some_0;
                if !(d.empty || vec_int(m, t)) {
                    lemma_drop_parts(m, pol, b, place, target as nat, f1, fuel);
                    let (jg, gb) = glue_of(m, d.glue)->Some_0;
                    lemma_bc_len(m, pol, jg, gb, seq![Val::Mut(eval_place(f1, place)->Some_0.0->At_0)], f1, fuel);
                } else {
                    lemma_drop_noop(m, pol, b, place, target as nat, f1, fuel);
                }
            }
        },
        _ => {},
    }
}

proof fn lemma_cd_done(m: MirCrate, pol: CallPolicy, b: Body, kind: TerminatorKind, f1: Frame, fuel: nat)
    ensures !(kind is Call || kind is Drop) ==> (step_term(m, pol, b, kind, f1, fuel) matches Step::Jump(_, f2, _, _) ==> f2 == f1),
        step_term(m, pol, b, kind, f1, fuel) matches Step::Stop(Out::Done(f2, _, _)) ==> f2 == f1,
{
}

pub proof fn lemma_stmts_mlen(m: MirCrate, b: Body, fm: Frame, ss: Seq<Statement>, n: nat)
    ensures exec_stmts(m, b, fm, ss, n) matches Some((f2, _, _)) ==> f2.locals.len() == fm.locals.len(),
    decreases n,
{
    if n > 0 && n <= ss.len() {
        lemma_stmts_mlen(m, b, fm, ss, (n - 1) as nat);
        if let Some((f1, _, _)) = exec_stmts(m, b, fm, ss, (n - 1) as nat) {
            reveal(exec_stmt);
        }
    }
}

/// **The simulation.** A completed MIR run of a translated fn, from one argument and one slot per
/// parameter, is matched by core's run of its image from the same arguments at the same fuel: the
/// same trace and the same steps, and the final frames are equal on the MIR locals (so the return
/// local `0`) and on the slots.
pub proof fn theorem_sim(m: MirCrate, pol: Policy, root: Seq<u8>, p: c::Program, infos: Seq<FnInfo>, g: nat,
    args: Seq<Val>, slots: Seq<Val>, fuel: nat)
    requires lowers(m, pol, root, p, infos), g < p.fns@.len(), wt_args(m, infos[g as int].inst as nat, args, slots),
    ensures ({
        let i = infos[g as int].inst as nat;
        mir_run_fn(m, cpol(pol), i, mir_entry(m, i, args, slots), fuel) matches Some((fm, t, n)) ==>
            ctcore::sem::run_fn(p, g, ctcore::sem::init_entry(p, g, args, slots), fuel) matches Some((fc, t2, n2))
            && t2 == t && n2 == n && fr_rel(fm, fc) && fm.locals.len() == inst_body(m, i)->Some_0.locals@.len()
    }),
{
    hide(lowers_body);
    hide(mir_entry);
    hide(ctcore::sem::init_entry);
    hide(fr_rel);
    hide(run_ok);
    let rs = choose|rs: Seq<Seq<bool>>| lowers_rs(m, pol, root, p, infos, rs);
    let j = infos[g as int].inst as nat;
    let r = rs[g as int];
    let ord = ords(infos);
    assert(lowers_body(m, pol, ord, j, p.fns@[g as int], r));
    assert(r.len() > 0 && r[0]) by { reveal(lowers_body); }
    let b = inst_body(m, j)->Some_0;
    lemma_prog_ok(m, pol, root, p, infos, rs);
    assert(ord[g as int] as nat == j);
    lemma_entry(m, pol, ord, j, p, g, r, args, slots);
    lemma_block(m, pol, ord, j, p, g, r, 0, mir_entry(m, j, args, slots), ctcore::sem::init_entry(p, g, args, slots), fuel);
    reveal(run_ok);
    lemma_run_len(m, cpol(pol), b, 0, mir_entry(m, j, args, slots), fuel);
}

/// `lowers_rs` gives the program-wide premise of the run induction.
proof fn lemma_prog_ok(m: MirCrate, pol: Policy, root: Seq<u8>, p: c::Program, infos: Seq<FnInfo>, rs: Seq<Seq<bool>>)
    requires lowers_rs(m, pol, root, p, infos, rs),
    ensures prog_ok(m, pol, ords(infos), p),
{
    hide(lowers_body);
    let ord = ords(infos);
    assert forall|h: int| 0 <= h < ord.len() implies #[trigger] fn_ok(m, pol, ord, p, h) by {
        assert(ord[h] == infos[h].inst);
        assert(lowers_body(m, pol, ord, infos[h].inst as nat, p.fns@[h], rs[h]));
    }
}

} // verus!
