//! The simulation (Task 6), stage 1: frames and places. MIR and core values are the same `Val`s:
//! every producer of a value builds the same value on both sides (unit-like values are `Unit` on
//! both: sem's alignment), so the frame relation is equality on the MIR locals and the slots, with
//! core's temps (after the MIR locals) ignored. Both sides navigate values with the shared
//! `get`/`put`/`read_at`/`write_at`, so equality survives stale `&mut` locations and
//! inactive-variant navigation without any typing.
#[allow(unused_imports)]
use crate::mir::*;
#[allow(unused_imports)]
use crate::rel::*;
#[allow(unused_imports)]
use crate::sem::*;
#[cfg(verus_keep_ghost)]
use ctcore::sem::write_at;
#[allow(unused_imports)]
use ctcore::sem::{Cur, Event, Frame, Loc, Root, Val, PE};
#[allow(unused_imports)]
use ctcore::syntax as c;
use vstd::prelude::*;

verus! {

/// The MIR frame against the core frame: equal MIR locals and slots; core's temps are ignored.
pub open spec fn fr_rel(fm: Frame, fc: Frame) -> bool {
    &&& fm.locals.len() <= fc.locals.len()
    &&& forall|i: int| 0 <= i < fm.locals.len() ==> #[trigger] fm.locals[i] == fc.locals[i]
    &&& fm.slots == fc.slots
}

/// A MIR load is core's read of the same location.
pub proof fn lemma_load(fm: Frame, fc: Frame, l: Loc)
    requires fr_rel(fm, fc), load(fm, l) is Some,
    ensures load(fm, l)->Some_0 == ctcore::sem::read_loc(fc, l),
{
    if let Root::Local(i) = l.root { assert(fm.locals[i as int] == fc.locals[i as int]); }
}

/// A MIR store and core's write of the same location keep the frames related.
pub proof fn lemma_store(fm: Frame, fc: Frame, l: Loc, w: Val)
    requires fr_rel(fm, fc), store(fm, l, w) is Some,
    ensures fr_rel(store(fm, l, w)->Some_0, ctcore::sem::write_loc(fc, l, w)),
        ctcore::sem::write_loc(fc, l, w).locals.len() == fc.locals.len(),
        store(fm, l, w)->Some_0.locals.len() == fm.locals.len(),
{
    let fm2 = store(fm, l, w)->Some_0;
    let fc2 = ctcore::sem::write_loc(fc, l, w);
    match l.root {
        Root::Local(i) => {
            assert(fm.locals[i as int] == fc.locals[i as int]);
            assert forall|k: int| 0 <= k < fm2.locals.len() implies #[trigger] fm2.locals[k] == fc2.locals[k] by {
                if k != i { assert(fm.locals[k] == fc.locals[k]); }
            }
        },
        Root::Slot(j) => {
            assert forall|k: int| 0 <= k < fm2.locals.len() implies #[trigger] fm2.locals[k] == fc2.locals[k] by {
                assert(fm.locals[k] == fc.locals[k]);
            }
        },
    }
}

// ------------------------------------------------------------------ places

/// A MIR place cursor against core's: the same location, or the same snapshot.
pub open spec fn cur_rel(p: PRes, q: Cur) -> bool {
    match (p, q) {
        (PRes::At(l), Cur::L(l2)) => l == l2,
        (PRes::Snap(v), Cur::V(c)) => v == c,
        _ => false,
    }
}

/// Core's walk, last projection last (`walk` is first projection first).
pub proof fn lemma_walk_snoc(fr: Frame, ps: Seq<c::Proj>, k: nat, c0: Cur)
    requires k < ps.len(),
    ensures ({
        let (c1, e1) = ctcore::sem::walk(fr, ps.drop_last(), k, c0);
        let (c2, e2) = ctcore::sem::step(fr, c1, ps.last());
        ctcore::sem::walk(fr, ps, k, c0) == (c2, e1 + e2)
    }),
    decreases ps.len() - k,
{
    let (c1, e1) = ctcore::sem::step(fr, c0, ps[k as int]);
    if k + 1 == ps.len() {
        assert(ctcore::sem::walk(fr, ps, k + 1, c1) == (c1, Seq::<Event>::empty()));
        assert(ctcore::sem::walk(fr, ps.drop_last(), k, c0) == (c0, Seq::<Event>::empty()));
        assert(e1 + Seq::<Event>::empty() == e1);
        assert(Seq::<Event>::empty() + e1 == e1);
    } else {
        lemma_walk_snoc(fr, ps, k + 1, c1);
        assert(ps.drop_last()[k as int] == ps[k as int]);
        let (c3, e3) = ctcore::sem::walk(fr, ps.drop_last(), k + 1, c1);
        let (c4, e4) = ctcore::sem::step(fr, c3, ps.last());
        assert(e1 + (e3 + e4) == (e1 + e3) + e4);
    }
}

pub open spec fn projs_rel(ps: Seq<ProjectionElem>, qs: Seq<c::Proj>) -> bool {
    ps.len() == qs.len() && forall|k: int| 0 <= k < ps.len() ==> lowers_proj(#[trigger] ps[k], qs[k])
}

/// One projection: MIR's step (when it succeeds) and core's agree.
pub proof fn lemma_proj_step(fm: Frame, fc: Frame, p: PRes, q: Cur, e: ProjectionElem, cq: c::Proj)
    requires fr_rel(fm, fc), cur_rel(p, q), lowers_proj(e, cq), proj_step(fm, p, e) is Some,
    ensures cur_rel(proj_step(fm, p, e)->Some_0.0, ctcore::sem::step(fc, q, cq).0),
        proj_step(fm, p, e)->Some_0.1 == ctcore::sem::step(fc, q, cq).1,
{
    let cur = pres_val(fm, p)->Some_0;
    if let PRes::At(l) = p { lemma_load(fm, fc, l); }
    if let ProjectionElem::Index(x) = e {
        let i = root_val(fm, Root::Local(x as nat))->Some_0->Int_0;
        assert(fc.locals[x as int] == Val::Int(i));
        assert(ctcore::sem::read_loc(fc, ctcore::sem::local_loc(x as nat)) == Val::Int(i));
    }
}

/// The first `n` projections.
pub proof fn lemma_places(fm: Frame, fc: Frame, base: PRes, cbase: Cur, ps: Seq<ProjectionElem>, qs: Seq<c::Proj>, n: nat)
    requires fr_rel(fm, fc), cur_rel(base, cbase), projs_rel(ps, qs), n <= ps.len(), places(fm, base, ps, n) is Some,
    ensures cur_rel(places(fm, base, ps, n)->Some_0.0, ctcore::sem::walk(fc, qs.subrange(0, n as int), 0, cbase).0),
        places(fm, base, ps, n)->Some_0.1 == ctcore::sem::walk(fc, qs.subrange(0, n as int), 0, cbase).1,
    decreases n,
{
    if n == 0 {
    } else {
        lemma_places(fm, fc, base, cbase, ps, qs, (n - 1) as nat);
        let (p1, e1) = places(fm, base, ps, (n - 1) as nat)->Some_0;
        let qn = qs.subrange(0, n as int);
        assert(qn.drop_last() == qs.subrange(0, n - 1));
        lemma_walk_snoc(fc, qn, 0, cbase);
        let (c1, _) = ctcore::sem::walk(fc, qs.subrange(0, n - 1), 0, cbase);
        lemma_proj_step(fm, fc, p1, c1, ps[n - 1], qs[n - 1]);
    }
}

/// A lowered place: MIR's evaluation (when it succeeds) and core's walk agree, with the same events.
pub proof fn lemma_place(fm: Frame, fc: Frame, p: Place, q: c::Place)
    requires fr_rel(fm, fc), q.local == p.local, projs_rel(p.projection@, q.proj@), eval_place(fm, p) is Some,
    ensures cur_rel(eval_place(fm, p)->Some_0.0, ctcore::sem::place_walk(fc, q).0),
        eval_place(fm, p)->Some_0.1 == ctcore::sem::place_walk(fc, q).1,
{
    let base = PRes::At(Loc { root: Root::Local(p.local as nat), path: seq![] });
    assert(q.proj@.subrange(0, q.proj@.len() as int) == q.proj@);
    lemma_places(fm, fc, base, Cur::L(ctcore::sem::local_loc(q.local as nat)), p.projection@, q.proj@, p.projection@.len());
}

/// Reading a lowered place.
pub proof fn lemma_read_place(fm: Frame, fc: Frame, p: Place, q: c::Place)
    requires fr_rel(fm, fc), q.local == p.local, projs_rel(p.projection@, q.proj@), read_place(fm, p) is Some,
    ensures read_place(fm, p)->Some_0.0 == ctcore::sem::read_place(fc, q).0,
        read_place(fm, p)->Some_0.1 == ctcore::sem::read_place(fc, q).1,
{
    lemma_place(fm, fc, p, q);
    if let PRes::At(l) = eval_place(fm, p)->Some_0.0 { lemma_load(fm, fc, l); }
}

pub proof fn lemma_lowers_place(m: MirCrate, b: Body, p: Place, q: c::Place, mutating: bool)
    requires lowers_place(m, b, p, q, mutating),
    ensures q.local == p.local, projs_rel(p.projection@, q.proj@),
{
}

} // verus!
