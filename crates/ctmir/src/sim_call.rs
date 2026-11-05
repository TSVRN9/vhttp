//! The simulation, calls (non-recursive parts): a call destination's place, the callee's entry
//! frame (`&mut` arguments copied into slots), the write-back of the slots, and core's `run_from`
//! of a block ending in a call.
#[allow(unused_imports)]
use crate::mir::*;
#[allow(unused_imports)]
use crate::rel::*;
#[allow(unused_imports)]
use crate::sem::*;
#[allow(unused_imports)]
use crate::sim::*;
#[cfg(verus_keep_ghost)]
use ctcore::sem::{get, put, read_at, write_at};
#[allow(unused_imports)]
use ctcore::sem::{Cur, Event, Frame, Loc, Root, Val, PE};
#[allow(unused_imports)]
use ctcore::syntax as c;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ destinations

/// The location step of a projection that reads nothing (`Field`, `ConstantIndex`, `Downcast`).
pub open spec fn dpe(e: ProjectionElem) -> PE {
    match e {
        ProjectionElem::Field(i, _) => PE::Field(i as nat),
        ProjectionElem::ConstantIndex { offset, min_length: _, from_end: _ } => PE::Index(offset as nat),
        ProjectionElem::Downcast(k) => PE::Variant(k as nat),
        _ => PE::Field(0),
    }
}

pub open spec fn dpath(ps: Seq<ProjectionElem>, n: nat) -> Seq<PE>
    decreases n,
{
    if n == 0 || n > ps.len() { seq![] } else { dpath(ps, (n - 1) as nat).push(dpe(ps[n - 1])) }
}

pub open spec fn no_read(ps: Seq<ProjectionElem>) -> bool {
    forall|k: int| 0 <= k < ps.len() ==> !(#[trigger] ps[k] is Index) && !(ps[k] is Deref)
}

proof fn lemma_dest_prefix(fm: Frame, g: Frame, ps: Seq<ProjectionElem>, qs: Seq<c::Proj>, root: Root, n: nat)
    requires no_read(ps), projs_rel(ps, qs), n <= ps.len(), places(fm, PRes::At(Loc { root, path: seq![] }), ps, n) is Some,
    ensures places(fm, PRes::At(Loc { root, path: seq![] }), ps, n) == Some((PRes::At(Loc { root, path: dpath(ps, n) }), Seq::<Event>::empty())),
        ctcore::sem::walk(g, qs.subrange(0, n as int), 0, Cur::L(Loc { root, path: seq![] })) == (Cur::L(Loc { root, path: dpath(ps, n) }), Seq::<Event>::empty()),
    decreases n,
{
    if n > 0 {
        let k = (n - 1) as nat;
        lemma_dest_prefix(fm, g, ps, qs, root, k);
        let qn = qs.subrange(0, n as int);
        assert(qn.drop_last() == qs.subrange(0, k as int));
        lemma_walk_snoc(g, qn, 0, Cur::L(Loc { root, path: seq![] }));
        assert(lowers_proj(ps[k as int], qs[k as int]));
        assert(Seq::<Event>::empty() + Seq::<Event>::empty() == Seq::<Event>::empty());
    }
}

/// A destination that reads nothing: the same location on every frame, no events.
pub proof fn lemma_dest(fm: Frame, g: Frame, p: Place, q: c::Place)
    requires dest_ok(p), q.local == p.local, projs_rel(p.projection@, q.proj@), eval_place(fm, p) is Some,
    ensures ({
        let l = Loc { root: Root::Local(p.local as nat), path: dpath(p.projection@, p.projection@.len()) };
        &&& eval_place(fm, p) == Some((PRes::At(l), Seq::<Event>::empty()))
        &&& ctcore::sem::place_walk(g, q) == (Cur::L(l), Seq::<Event>::empty())
        &&& ctcore::sem::place_loc(g, q) == Some((l, Seq::<Event>::empty()))
    }),
{
    assert(no_read(p.projection@));
    assert(q.proj@.subrange(0, q.proj@.len() as int) == q.proj@);
    lemma_dest_prefix(fm, g, p.projection@, q.proj@, Root::Local(p.local as nat), p.projection@.len());
}

proof fn lemma_noidx_prefix(fm: Frame, base: PRes, ps: Seq<ProjectionElem>, n: nat)
    requires forall|k: int| 0 <= k < ps.len() ==> !(#[trigger] ps[k] is Index), n <= ps.len(), places(fm, base, ps, n) is Some,
    ensures places(fm, base, ps, n)->Some_0.1 == Seq::<Event>::empty(),
    decreases n,
{
    if n > 0 {
        lemma_noidx_prefix(fm, base, ps, (n - 1) as nat);
        assert(!(ps[n - 1] is Index));
        assert(Seq::<Event>::empty() + Seq::<Event>::empty() == Seq::<Event>::empty());
    }
}

/// A place without `Index` emits nothing.
pub proof fn lemma_noidx_ev(fm: Frame, p: Place)
    requires no_index(p), eval_place(fm, p) is Some,
    ensures eval_place(fm, p)->Some_0.1 == Seq::<Event>::empty(),
{
    lemma_noidx_prefix(fm, PRes::At(Loc { root: Root::Local(p.local as nat), path: seq![] }), p.projection@, p.projection@.len());
}

// ------------------------------------------------------------------ entry and write-back

/// Core's write-back locations of argument values `vs`.
pub open spec fn wb_of(vs: Seq<Val>) -> Seq<Option<Loc>> { Seq::new(vs.len(), |j: int| match vs[j] { Val::Mut(l) => Some(l), _ => None }) }

/// `args_ok`: a `&mut` parameter gets a location, any other a value that is not one.
pub proof fn lemma_arg_mut(m: MirCrate, cb: Body, fr: Frame, vs: Seq<Val>, j: int)
    requires args_ok(m, cb, fr, vs), 0 <= j < vs.len(),
    ensures (vs[j] is Mut) == is_mut_ref(m, cb.locals@[j + 1].ty),
        is_mut_ref(m, cb.locals@[j + 1].ty) ==> load(fr, vs[j]->Mut_0) is Some,
{
    assert(arg_ok(m, cb, fr, vs, j));
}

/// The callee's entry frames agree: core's `call_enter` frame against MIR's `mir_entry` of the
/// copied-in slots.
pub proof fn lemma_call_entry(m: MirCrate, j: nat, cb: Body, p: c::Program, h: nat, fr: Frame, fc: Frame, cargs: Seq<c::Operand>, vs: Seq<Val>)
    requires inst_body(m, j) == Some(cb), args_ok(m, cb, fr, vs), fr_rel(fr, fc), ctcore::sem::op_vals(fc, cargs) == vs,
        h < p.fns@.len(), cb.locals@.len() <= p.fns@[h as int].locals@.len(),
        forall|k: int| 0 <= k < cb.locals@.len() ==> !ul_arr(m, #[trigger] cb.locals@[k].ty),
    ensures ({
        let (cf, wb, ae) = ctcore::sem::call_enter(p, h, fc, cargs);
        &&& fr_rel(mir_entry(m, j, vs, call_slots(m, cb, fr, vs)), cf) && wb == wb_of(vs) && ae == ctcore::sem::ops_ev(fc, cargs)
        &&& mir_entry(m, j, vs, call_slots(m, cb, fr, vs)).locals.len() == cb.locals@.len() && cf.locals.len() == p.fns@[h as int].locals@.len()
    }),
{
    let (cf, wb, ae) = ctcore::sem::call_enter(p, h, fc, cargs);
    let me = mir_entry(m, j, vs, call_slots(m, cb, fr, vs));
    assert forall|k: int| 0 <= k < me.locals.len() implies #[trigger] me.locals[k] == cf.locals[k] by {
        if 1 <= k <= cb.arg_count { lemma_arg_mut(m, cb, fr, vs, k - 1); }
    }
    let cs = call_slots(m, cb, fr, vs);
    assert forall|k: int| 0 <= k < vs.len() implies #[trigger] cs[k] == cf.slots[k] by {
        lemma_arg_mut(m, cb, fr, vs, k);
        if is_mut_ref(m, cb.locals@[k + 1].ty) { lemma_load(fr, fc, vs[k]->Mut_0); }
    }
    assert(cs =~= cf.slots);
    assert(wb =~= wb_of(vs));
}

/// The write-back of the first `n` parameters keeps the frames related.
pub proof fn lemma_wb(m: MirCrate, cb: Body, fr: Frame, fc: Frame, vs: Seq<Val>, cs: Seq<Val>, n: nat)
    requires fr_rel(fr, fc), args_ok(m, cb, fr, vs), n <= vs.len(), write_back(m, cb, fr, vs, cs, n) is Some,
    ensures fr_rel(write_back(m, cb, fr, vs, cs, n)->Some_0, ctcore::sem::write_back(fc, cs, wb_of(vs).subrange(0, n as int))),
        ctcore::sem::write_back(fc, cs, wb_of(vs).subrange(0, n as int)).locals.len() == fc.locals.len(),
        write_back(m, cb, fr, vs, cs, n)->Some_0.locals.len() == fr.locals.len(),
    decreases n,
{
    let w = wb_of(vs).subrange(0, n as int);
    if n == 0 {
        assert(w.len() == 0);
    } else {
        let k = (n - 1) as nat;
        lemma_wb(m, cb, fr, fc, vs, cs, k);
        assert(w.drop_last() =~= wb_of(vs).subrange(0, k as int));
        lemma_arg_mut(m, cb, fr, vs, k as int);
        let f = write_back(m, cb, fr, vs, cs, k)->Some_0;
        let g = ctcore::sem::write_back(fc, cs, wb_of(vs).subrange(0, k as int));
        if is_mut_ref(m, cb.locals@[n as int].ty) {
            lemma_store(f, g, vs[k as int]->Mut_0, cs[k as int]);
        }
    }
}

/// Core's `call_leave`: the write-back, then the destination (one that reads nothing) gets the
/// return value.
pub proof fn lemma_leave(m: MirCrate, cb: Body, fr: Frame, fc: Frame, vs: Seq<Val>, cf: Frame, cfc: Frame, dest: Place, dst: c::Place)
    requires fr_rel(fr, fc), args_ok(m, cb, fr, vs), fr_rel(cf, cfc), return_to(m, cb, fr, vs, cf) is Some,
        dest_ok(dest), dst.local == dest.local, projs_rel(dest.projection@, dst.proj@), eval_place(fr, dest) is Some,
        store(return_to(m, cb, fr, vs, cf)->Some_0.1, eval_place(fr, dest)->Some_0.0->At_0, return_to(m, cb, fr, vs, cf)->Some_0.0) is Some,
    ensures ({
        let (v, f2) = return_to(m, cb, fr, vs, cf)->Some_0;
        let l = eval_place(fr, dest)->Some_0.0->At_0;
        let (f3c, de) = ctcore::sem::call_leave(fc, cfc, wb_of(vs), dst);
        &&& fr_rel(store(f2, l, v)->Some_0, f3c) && de == Seq::<Event>::empty() && f3c.locals.len() == fc.locals.len()
        &&& eval_place(fr, dest)->Some_0.1 == Seq::<Event>::empty() && store(f2, l, v)->Some_0.locals.len() == fr.locals.len()
    }),
{
    let (v, f2) = return_to(m, cb, fr, vs, cf)->Some_0;
    lemma_wb(m, cb, fr, fc, vs, cf.slots, vs.len());
    assert(wb_of(vs).subrange(0, vs.len() as int) =~= wb_of(vs));
    let g = ctcore::sem::write_back(fc, cfc.slots, wb_of(vs));
    assert(cf.locals[0] == cfc.locals[0]);
    lemma_dest(fr, g, dest, dst);
    lemma_store(f2, g, eval_place(fr, dest)->Some_0.0->At_0, v);
}

// ------------------------------------------------------------------ leaves

/// The core intrinsic of a std row (`intr_of`'s std arm).
pub open spec fn std_intr(f: StdFn) -> c::Intrinsic {
    match f {
        StdFn::VecNew => c::Intrinsic::VecNew,
        StdFn::VecWithCapacity => c::Intrinsic::VecWithCapacity,
        StdFn::VecPush => c::Intrinsic::VecPush,
        StdFn::VecExtendFromSlice => c::Intrinsic::VecExtendFromSlice,
        StdFn::VecAsSlice => c::Intrinsic::VecAsSlice,
        StdFn::ArrayAsSlice => c::Intrinsic::ArrayAsSlice,
        StdFn::VecLen => c::Intrinsic::VecLen,
        StdFn::VecSet => c::Intrinsic::VecSet,
        StdFn::VecIndex => c::Intrinsic::VecIndex,
        StdFn::SliceSubrange => c::Intrinsic::SliceSubrange,
        StdFn::SliceToVec => c::Intrinsic::SliceToVec,
        StdFn::Wrapping(op, it) => c::Intrinsic::Wrapping(op, it),
        StdFn::GhostNew => c::Intrinsic::GhostUnit,
    }
}

/// An intrinsic's extra cost from its argument values (`intr_cost` is this at `op_vals`).
pub open spec fn cost_of(k: c::Intrinsic, fr: Frame, vs: Seq<Val>) -> nat {
    match k {
        c::Intrinsic::VecExtendFromSlice => ctcore::sem::elems(fr, ctcore::sem::nth(vs, 1)).len(),
        c::Intrinsic::SliceToVec => ctcore::sem::elems(fr, ctcore::sem::nth(vs, 0)).len(),
        _ => 0,
    }
}

/// A leaf's MIR outcome is core's intrinsic effect on the related frame.
pub open spec fn leaf_sim(k: c::Intrinsic, r: (Val, Frame, Seq<Event>, nat), fc: Frame, vs: Seq<Val>) -> bool {
    ctcore::sem::intr_eff(k, fc, vs) matches Some((f2c, v, ie)) && v == r.0 && ie == r.2 && fr_rel(r.1, f2c)
        && f2c.locals.len() == fc.locals.len() && cost_of(k, fc, vs) == r.3
}

/// `write_at` through one more step.
pub proof fn lemma_write_at_snoc(v: Val, p: Seq<PE>, e: PE, w: Val)
    ensures write_at(v, p.push(e), w) == write_at(v, p, put(read_at(v, p), e, w)),
    decreases p.len(),
{
    let q = p.push(e);
    if p.len() == 0 {
        assert(q.drop_first() =~= Seq::<PE>::empty());
        assert(q[0] == e);
        assert(write_at(get(v, e), q.drop_first(), w) == w);
        assert(write_at(v, q, w) == put(v, e, w));
        assert(read_at(v, p) == v);
    } else {
        assert(q.drop_first() =~= p.drop_first().push(e));
        assert(q[0] == p[0]);
        let g = get(v, p[0]);
        lemma_write_at_snoc(g, p.drop_first(), e, w);
        assert(read_at(v, p) == read_at(g, p.drop_first()));
        assert(write_at(v, q, w) == put(v, p[0], write_at(g, q.drop_first(), w)));
        assert(write_at(v, p, put(read_at(v, p), e, w)) == put(v, p[0], write_at(g, p.drop_first(), put(read_at(v, p), e, w))));
    }
}

proof fn lemma_row_vec(m: MirCrate, f: StdFn, dty: Option<Ty>, vs: Seq<Val>, fr: Frame, fc: Frame)
    requires fr_rel(fr, fc), std_apply(m, f, dty, vs, fr) is Some,
        f is VecPush || f is VecExtendFromSlice || f is VecSet,
    ensures leaf_sim(std_intr(f), std_apply(m, f, dty, vs, fr)->Some_0, fc, vs),
{
    let (l, xs) = mut_arr(fr, vs[0])->Some_0;
    lemma_load(fr, fc, l);
    match f {
        StdFn::VecPush => {
            assert(xs.push(vs[1]) =~= xs + seq![vs[1]]);
            lemma_store(fr, fc, l, Val::Arr(xs.push(vs[1])));
        },
        StdFn::VecExtendFromSlice => {
            let ys = shr_arr(vs[1])->Some_0;
            lemma_store(fr, fc, l, Val::Arr(xs + ys));
        },
        _ => {
            let i = vs[1]->Int_0;
            let w = Val::Arr(xs.update(i as int, vs[2]));
            lemma_store(fr, fc, l, w);
            let l2 = Loc { root: l.root, path: l.path.push(PE::Index(i as nat)) };
            match l.root {
                Root::Local(n) => lemma_write_at_snoc(fc.locals[n as int], l.path, PE::Index(i as nat), vs[2]),
                Root::Slot(n) => lemma_write_at_snoc(fc.slots[n as int], l.path, PE::Index(i as nat), vs[2]),
            }
            assert(ctcore::sem::write_loc(fc, l2, vs[2]) == ctcore::sem::write_loc(fc, l, w));
        },
    }
}

proof fn lemma_row_pure(m: MirCrate, f: StdFn, dty: Option<Ty>, vs: Seq<Val>, fr: Frame, fc: Frame)
    requires fr_rel(fr, fc), std_apply(m, f, dty, vs, fr) is Some, !(dty matches Some(t) && ul_arr(m, t)),
        !(f is VecPush || f is VecExtendFromSlice || f is VecSet),
        f is Wrapping ==> (f->Wrapping_0 is Add || f->Wrapping_0 is Sub),
    ensures leaf_sim(std_intr(f), std_apply(m, f, dty, vs, fr)->Some_0, fc, vs),
{
    match f {
        StdFn::SliceSubrange => {
            let xs = shr_arr(vs[0])->Some_0;
            let (lo, hi) = (vs[1]->Int_0, vs[2]->Int_0);
            assert(ctcore::sem::elems(fc, vs[0]) == xs);
        },
        StdFn::Wrapping(op, it) => {},
        _ => {},
    }
}

/// The std rows.
pub proof fn lemma_std_row(m: MirCrate, key: Seq<u8>, gargs: GenericArgs, dty: Option<Ty>, vs: Seq<Val>, fr: Frame, fc: Frame)
    requires fr_rel(fr, fc), std_model(m, key, gargs) is Some, std_apply(m, std_model(m, key, gargs)->Some_0, dty, vs, fr) is Some,
        !(dty matches Some(t) && ul_arr(m, t)),
    ensures leaf_sim(std_intr(std_model(m, key, gargs)->Some_0), std_apply(m, std_model(m, key, gargs)->Some_0, dty, vs, fr)->Some_0, fc, vs),
{
    let f = std_model(m, key, gargs)->Some_0;
    assert(f is Wrapping ==> (f->Wrapping_0 is Add || f->Wrapping_0 is Sub));
    if f is VecPush || f is VecExtendFromSlice || f is VecSet { lemma_row_vec(m, f, dty, vs, fr, fc); }
    else { lemma_row_pure(m, f, dty, vs, fr, fc); }
}

/// A leaf call (policy or std): its intrinsic, run on the related frame.
pub proof fn lemma_leaf(m: MirCrate, pol: CallPolicy, key: Seq<u8>, gargs: GenericArgs, dty: Option<Ty>, vs: Seq<Val>, fr: Frame, fc: Frame)
    requires fr_rel(fr, fc), leaf_call(m, pol, key, gargs, dty, vs, fr) is Some, intr_of(m, pol, key, gargs) is Some,
        !(dty matches Some(t) && ul_arr(m, t)),
    ensures leaf_sim(intr_of(m, pol, key, gargs)->Some_0, leaf_call(m, pol, key, gargs, dty, vs, fr)->Some_0, fc, vs),
{
    if !pol.declassify.contains(key) && !pol.ghost_unit.contains(key) {
        lemma_std_row(m, key, gargs, dty, vs, fr, fc);
        assert(intr_of(m, pol, key, gargs) == Some(std_intr(std_model(m, key, gargs)->Some_0)));
    }
}

// ------------------------------------------------------------------ core's call blocks

/// Core's block ending in a call of fn `h`.
pub proof fn lemma_rf_fn(p: c::Program, f: nat, bb: nat, fc: Frame, fuel: nat)
    requires fuel > 0, f < p.fns@.len(), bb < p.fns@[f as int].blocks@.len(),
        p.fns@[f as int].blocks@[bb as int].term matches c::Term::Call(c::Callee::Fn(_), _, _, _),
    ensures ({
        let blk = p.fns@[f as int].blocks@[bb as int];
        let (h, args, dst, next) = (blk.term->Call_0->Fn_0, blk.term->Call_1, blk.term->Call_2, blk.term->Call_3);
        let (f1, t1) = ctcore::sem::exec_stmts(blk.stmts@, 0, fc);
        let (cf, wb, ae) = ctcore::sem::call_enter(p, h as nat, f1, args@);
        ctcore::sem::run_from(p, f, bb, fc, fuel) == match ctcore::sem::run_from(p, h as nat, 0, cf, (fuel - 1) as nat) {
            Some((cf2, ct, cn)) => {
                let (f2, de) = ctcore::sem::call_leave(f1, cf2, wb, dst);
                match ctcore::sem::run_from(p, f, next as nat, f2, (fuel - 1) as nat) {
                    Some((f3, t3, n3)) => Some((f3, t1 + ae + ct + de + t3, blk.stmts@.len() + 1 + cn + n3)),
                    None => None,
                }
            },
            None => None,
        }
    }),
{
}

/// Core's block ending in an intrinsic call.
pub proof fn lemma_rf_intr(p: c::Program, f: nat, bb: nat, fc: Frame, fuel: nat)
    requires fuel > 0, f < p.fns@.len(), bb < p.fns@[f as int].blocks@.len(),
        p.fns@[f as int].blocks@[bb as int].term matches c::Term::Call(c::Callee::Intr(_), _, _, _),
    ensures ({
        let blk = p.fns@[f as int].blocks@[bb as int];
        let (k, args, dst, next) = (blk.term->Call_0->Intr_0, blk.term->Call_1, blk.term->Call_2, blk.term->Call_3);
        let (f1, t1) = ctcore::sem::exec_stmts(blk.stmts@, 0, fc);
        ctcore::sem::run_from(p, f, bb, fc, fuel) == match ctcore::sem::exec_intr(k, f1, args@, dst) {
            Some((f2, e, x)) => match ctcore::sem::run_from(p, f, next as nat, f2, (fuel - 1) as nat) {
                Some((f3, t3, n3)) => Some((f3, t1 + e + t3, blk.stmts@.len() + 1 + x + n3)),
                None => None,
            },
            None => None,
        }
    }),
{
}

} // verus!
