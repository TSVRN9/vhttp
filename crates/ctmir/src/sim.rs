//! The simulation (Task 6), stage 1: the value relation. A MIR value `v` and a core value `c`
//! agree (`vr`) when they are equal, except that core may hold `Unit` where MIR holds a
//! unit-shaped value (`us`): `ZeroSized` constants, `GhostUnit` results and core's entry locals
//! are `Unit` in core, the type's `unit_like` value in MIR. The relation is not a function: an
//! aggregate `()` is `Tup([])` on both sides, a `ZeroSized` one is `Unit` in core.
//!
//! The shared navigation (`get`/`put`/`read_at`/`write_at`) preserves `vr`, except for a write
//! into the interior of a value that core holds as `Unit` (core's write is a no-op there) and a
//! write through a trailing `Variant` of a value core holds as `Unit`; `wsafe` names exactly those
//! cases, a typing fact the caller supplies.
#[allow(unused_imports)]
use crate::mir::*;
#[allow(unused_imports)]
use crate::rel::*;
#[allow(unused_imports)]
use crate::sem::*;
#[cfg(verus_keep_ghost)]
use ctcore::sem::{get, pad, put, read_at, write_at};
#[allow(unused_imports)]
use ctcore::sem::{Cur, Event, Frame, Loc, Root, Val, PE};
#[allow(unused_imports)]
use ctcore::syntax as c;
use vstd::prelude::*;

verus! {

/// Unit-shaped: built from `Unit` by tuples, ADTs (any variant) and arrays.
pub open spec fn us(v: Val) -> bool
    decreases v,
{
    match v {
        Val::Unit => true,
        Val::Tup(vs) => forall|i: int| 0 <= i < vs.len() ==> us(#[trigger] vs[i]),
        Val::Adt(_, vs) => forall|i: int| 0 <= i < vs.len() ==> us(#[trigger] vs[i]),
        Val::Arr(vs) => forall|i: int| 0 <= i < vs.len() ==> us(#[trigger] vs[i]),
        _ => false,
    }
}

/// MIR value `v` agrees with core value `c`.
pub open spec fn vr(v: Val, c: Val) -> bool
    decreases v,
{
    (c is Unit && us(v)) || match v {
        Val::Int(a) => c == Val::Int(a),
        Val::Unit => c is Unit,
        Val::Tup(vs) => c is Tup && vs.len() == c->Tup_0.len() && forall|i: int| 0 <= i < vs.len() ==> vr(#[trigger] vs[i], c->Tup_0[i]),
        Val::Adt(k, vs) => c is Adt && c->Adt_0 == k && vs.len() == c->Adt_1.len()
            && forall|i: int| 0 <= i < vs.len() ==> vr(#[trigger] vs[i], c->Adt_1[i]),
        Val::Arr(vs) => c is Arr && vs.len() == c->Arr_0.len() && forall|i: int| 0 <= i < vs.len() ==> vr(#[trigger] vs[i], c->Arr_0[i]),
        Val::Shr(b) => c is Shr && vr(*b, *c->Shr_0),
        Val::Mut(l) => c == Val::Mut(l),
    }
}

pub open spec fn vrs(vs: Seq<Val>, cs: Seq<Val>) -> bool {
    vs.len() == cs.len() && forall|i: int| 0 <= i < vs.len() ==> vr(#[trigger] vs[i], cs[i])
}

pub proof fn lemma_vr_refl(v: Val)
    ensures vr(v, v),
    decreases v,
{
    match v {
        Val::Tup(vs) => { assert forall|i: int| 0 <= i < vs.len() implies vr(#[trigger] vs[i], vs[i]) by { lemma_vr_refl(vs[i]); } },
        Val::Adt(_, vs) => { assert forall|i: int| 0 <= i < vs.len() implies vr(#[trigger] vs[i], vs[i]) by { lemma_vr_refl(vs[i]); } },
        Val::Arr(vs) => { assert forall|i: int| 0 <= i < vs.len() implies vr(#[trigger] vs[i], vs[i]) by { lemma_vr_refl(vs[i]); } },
        Val::Shr(b) => lemma_vr_refl(*b),
        _ => {},
    }
}

pub proof fn lemma_vrs_refl(vs: Seq<Val>)
    ensures vrs(vs, vs),
{
    assert forall|i: int| 0 <= i < vs.len() implies vr(#[trigger] vs[i], vs[i]) by { lemma_vr_refl(vs[i]); }
}

/// Only `Unit` agrees with core's `Unit`-free values... the converse: `vr(v, Unit)` is `us(v)`.
pub proof fn lemma_vr_unit(v: Val)
    ensures vr(v, Val::Unit) == us(v),
{
}

/// An int agrees only with itself.
pub proof fn lemma_vr_int(v: Val, c: Val)
    requires vr(v, c), v is Int || c is Int,
    ensures v == c,
{
}

pub proof fn lemma_us_get(v: Val, e: PE)
    requires us(v),
    ensures us(get(v, e)),
{
}

pub proof fn lemma_vr_get(v: Val, c: Val, e: PE)
    requires vr(v, c),
    ensures vr(get(v, e), get(c, e)),
{
    if c is Unit && us(v) {
        lemma_us_get(v, e);
    } else {
        match (v, e) {
            (Val::Adt(k, vs), PE::Variant(j)) => {
                assert(vr(Val::Adt(j, vs), Val::Adt(j, c->Adt_1)));
            },
            _ => {},
        }
    }
}

pub proof fn lemma_vr_read_at(v: Val, c: Val, p: Seq<PE>)
    requires vr(v, c),
    ensures vr(read_at(v, p), read_at(c, p)),
    decreases p.len(),
{
    if p.len() > 0 {
        lemma_vr_get(v, c, p[0]);
        lemma_vr_read_at(get(v, p[0]), get(c, p[0]), p.drop_first());
    }
}

proof fn lemma_us_pad(vs: Seq<Val>, n: nat)
    requires forall|i: int| 0 <= i < vs.len() ==> us(#[trigger] vs[i]),
    ensures forall|i: int| 0 <= i < pad(vs, n).len() ==> us(#[trigger] pad(vs, n)[i]), pad(vs, n).len() >= n,
{
    assert forall|i: int| 0 <= i < pad(vs, n).len() implies us(#[trigger] pad(vs, n)[i]) by {
        if i >= vs.len() { assert(pad(vs, n)[i] == Val::Unit); }
    }
}

proof fn lemma_vr_pad(vs: Seq<Val>, cs: Seq<Val>, n: nat)
    requires vrs(vs, cs),
    ensures vrs(pad(vs, n), pad(cs, n)), pad(vs, n).len() >= n,
{
    assert forall|i: int| 0 <= i < pad(vs, n).len() implies vr(#[trigger] pad(vs, n)[i], pad(cs, n)[i]) by {
        if i >= vs.len() { assert(pad(vs, n)[i] == Val::Unit && pad(cs, n)[i] == Val::Unit); }
    }
}

/// A unit-shaped value with a unit-shaped component written stays unit-shaped.
pub proof fn lemma_us_put(v: Val, e: PE, w: Val)
    requires us(v), us(w),
    ensures us(put(v, e, w)),
{
    match (v, e) {
        (Val::Tup(vs), PE::Field(i)) => {
            lemma_us_pad(vs, i + 1);
            let s = pad(vs, i + 1).update(i as int, w);
            assert forall|j: int| 0 <= j < s.len() implies us(#[trigger] s[j]) by { if j != i { assert(s[j] == pad(vs, i + 1)[j]); } }
        },
        (Val::Adt(k, vs), PE::Field(i)) => {
            lemma_us_pad(vs, i + 1);
            let s = pad(vs, i + 1).update(i as int, w);
            assert forall|j: int| 0 <= j < s.len() implies us(#[trigger] s[j]) by { if j != i { assert(s[j] == pad(vs, i + 1)[j]); } }
        },
        (Val::Arr(vs), PE::Index(i)) => {
            if i < vs.len() {
                let s = vs.update(i as int, w);
                assert forall|j: int| 0 <= j < s.len() implies us(#[trigger] s[j]) by { if j != i { assert(s[j] == vs[j]); } }
            }
        },
        _ => {},
    }
}

pub proof fn lemma_us_write_at(v: Val, p: Seq<PE>, w: Val)
    requires us(v), us(w),
    ensures us(write_at(v, p, w)),
    decreases p.len(),
{
    if p.len() > 0 {
        lemma_us_get(v, p[0]);
        lemma_us_write_at(get(v, p[0]), p.drop_first(), w);
        lemma_us_put(v, p[0], write_at(get(v, p[0]), p.drop_first(), w));
    }
}

/// One `put` keeps the agreement: a write into a value core holds as `Unit` must be unit-shaped,
/// and a `Variant` write of an ADT must not be core's `Unit`.
pub open spec fn put_ok(v: Val, c: Val, e: PE, w: Val, d: Val) -> bool {
    &&& (c is Unit && !(v is Unit) ==> us(w))
    &&& (e is Variant && c is Adt ==> !(d is Unit && w is Adt))
}

proof fn lemma_vr_upd(vs: Seq<Val>, cs: Seq<Val>, i: nat, w: Val, d: Val)
    requires vrs(vs, cs), i < vs.len(), vr(w, d),
    ensures vrs(vs.update(i as int, w), cs.update(i as int, d)),
{
    assert forall|j: int| 0 <= j < vs.len() implies vr(#[trigger] vs.update(i as int, w)[j], cs.update(i as int, d)[j]) by {
        if j != i { assert(vs.update(i as int, w)[j] == vs[j]); }
    }
}

pub proof fn lemma_vr_put(v: Val, c: Val, e: PE, w: Val, d: Val)
    requires vr(v, c), vr(w, d), put_ok(v, c, e, w, d),
    ensures vr(put(v, e, w), put(c, e, d)),
{
    if c is Unit && us(v) {
        if v is Unit {
        } else {
            lemma_us_put(v, e, w);
        }
    } else {
        match (v, e) {
            (Val::Tup(vs), PE::Field(i)) => {
                let cs = c->Tup_0;
                lemma_vr_pad(vs, cs, i + 1);
                lemma_vr_upd(pad(vs, i + 1), pad(cs, i + 1), i, w, d);
            },
            (Val::Adt(k, vs), PE::Field(i)) => {
                let cs = c->Adt_1;
                lemma_vr_pad(vs, cs, i + 1);
                lemma_vr_upd(pad(vs, i + 1), pad(cs, i + 1), i, w, d);
            },
            (Val::Arr(vs), PE::Index(i)) => {
                if i < vs.len() { lemma_vr_upd(vs, c->Arr_0, i, w, d); }
            },
            (Val::Adt(k, vs), PE::Variant(_)) => {
                match w {
                    Val::Adt(_, ws) => {
                        assert(d is Adt);
                        assert(vr(Val::Adt(k, ws), Val::Adt(k, d->Adt_1)));
                    },
                    _ => {
                        assert(!(d is Adt)) by { if d is Adt && !(w is Adt) { assert(!vr(w, d)); } }
                    },
                }
            },
            _ => {},
        }
    }
}

/// `write_at` keeps the agreement when every `put` along the path does.
pub open spec fn wsafe(v: Val, c: Val, p: Seq<PE>, w: Val, d: Val) -> bool
    decreases p.len(),
{
    p.len() == 0 || {
        let (v1, c1) = (get(v, p[0]), get(c, p[0]));
        &&& wsafe(v1, c1, p.drop_first(), w, d)
        &&& put_ok(v, c, p[0], write_at(v1, p.drop_first(), w), write_at(c1, p.drop_first(), d))
    }
}

pub proof fn lemma_vr_write_at(v: Val, c: Val, p: Seq<PE>, w: Val, d: Val)
    requires vr(v, c), vr(w, d), wsafe(v, c, p, w, d),
    ensures vr(write_at(v, p, w), write_at(c, p, d)),
    decreases p.len(),
{
    if p.len() > 0 {
        let (v1, c1) = (get(v, p[0]), get(c, p[0]));
        lemma_vr_get(v, c, p[0]);
        lemma_vr_write_at(v1, c1, p.drop_first(), w, d);
        lemma_vr_put(v, c, p[0], write_at(v1, p.drop_first(), w), write_at(c1, p.drop_first(), d));
    }
}

/// A MIR-side condition for `wsafe`: a write into the interior of a unit-shaped value (not `Unit`)
/// keeps it unit-shaped, and a write through a trailing `Variant` is not of a unit-shaped ADT.
pub open spec fn mws(v: Val, p: Seq<PE>, w: Val) -> bool
    decreases p.len(),
{
    p.len() == 0 || {
        let v1 = get(v, p[0]);
        &&& mws(v1, p.drop_first(), w)
        &&& (us(v) && !(v is Unit) ==> us(write_at(v1, p.drop_first(), w)))
        &&& (p[0] is Variant && p.len() == 1 ==> !(us(w) && w is Adt))
    }
}

/// `put` into an ADT gives an ADT.
proof fn lemma_put_adt(c: Val, e: PE, x: Val)
    requires c is Adt,
    ensures put(c, e, x) is Adt,
{
}

pub proof fn lemma_mws(v: Val, c: Val, p: Seq<PE>, w: Val, d: Val)
    requires vr(v, c), vr(w, d), mws(v, p, w),
    ensures wsafe(v, c, p, w, d),
    decreases p.len(),
{
    if p.len() > 0 {
        let (v1, c1) = (get(v, p[0]), get(c, p[0]));
        let rest = p.drop_first();
        lemma_vr_get(v, c, p[0]);
        lemma_mws(v1, c1, rest, w, d);
        if p[0] is Variant && c is Adt {
            if rest.len() > 0 {
                assert(c1 is Adt);
                lemma_put_adt(c1, rest[0], write_at(get(c1, rest[0]), rest.drop_first(), d));
            } else {
                if d is Unit && w is Adt { assert(us(w)); }
            }
        }
    }
}

// ------------------------------------------------------------------ purity and frames

/// Every `Shr` inside `v` holds a `Mut`-free snapshot (core's walk reads `Unit` through a `Mut` in
/// a snapshot; MIR's follows it).
pub open spec fn pure(v: Val) -> bool
    decreases v,
{
    match v {
        Val::Shr(b) => mut_free(*b),
        Val::Tup(vs) => forall|i: int| 0 <= i < vs.len() ==> pure(#[trigger] vs[i]),
        Val::Adt(_, vs) => forall|i: int| 0 <= i < vs.len() ==> pure(#[trigger] vs[i]),
        Val::Arr(vs) => forall|i: int| 0 <= i < vs.len() ==> pure(#[trigger] vs[i]),
        _ => true,
    }
}

pub open spec fn pure_fr(fr: Frame) -> bool {
    &&& forall|i: int| 0 <= i < fr.locals.len() ==> pure(#[trigger] fr.locals[i])
    &&& forall|i: int| 0 <= i < fr.slots.len() ==> pure(#[trigger] fr.slots[i])
}

/// The MIR frame against the core frame: the MIR locals and the slots agree; core's temps (after
/// the MIR locals) are ignored.
pub open spec fn fr_rel(fm: Frame, fc: Frame) -> bool {
    &&& fm.locals.len() <= fc.locals.len()
    &&& forall|i: int| 0 <= i < fm.locals.len() ==> vr(#[trigger] fm.locals[i], fc.locals[i])
    &&& vrs(fm.slots, fc.slots)
}

pub proof fn lemma_mf_get(v: Val, e: PE)
    requires mut_free(v),
    ensures mut_free(get(v, e)),
{
}

pub proof fn lemma_mf_read_at(v: Val, p: Seq<PE>)
    requires mut_free(v),
    ensures mut_free(read_at(v, p)),
    decreases p.len(),
{
    if p.len() > 0 { lemma_mf_get(v, p[0]); lemma_mf_read_at(get(v, p[0]), p.drop_first()); }
}

pub proof fn lemma_mf_pure(v: Val)
    requires mut_free(v),
    ensures pure(v),
    decreases v,
{
    match v {
        Val::Tup(vs) => { assert forall|i: int| 0 <= i < vs.len() implies pure(#[trigger] vs[i]) by { lemma_mf_pure(vs[i]); } },
        Val::Adt(_, vs) => { assert forall|i: int| 0 <= i < vs.len() implies pure(#[trigger] vs[i]) by { lemma_mf_pure(vs[i]); } },
        Val::Arr(vs) => { assert forall|i: int| 0 <= i < vs.len() implies pure(#[trigger] vs[i]) by { lemma_mf_pure(vs[i]); } },
        _ => {},
    }
}

pub proof fn lemma_pure_get(v: Val, e: PE)
    requires pure(v),
    ensures pure(get(v, e)),
{
}

pub proof fn lemma_pure_read_at(v: Val, p: Seq<PE>)
    requires pure(v),
    ensures pure(read_at(v, p)),
    decreases p.len(),
{
    if p.len() > 0 { lemma_pure_get(v, p[0]); lemma_pure_read_at(get(v, p[0]), p.drop_first()); }
}

/// A MIR load agrees with core's read of the same location.
pub proof fn lemma_load(fm: Frame, fc: Frame, l: Loc)
    requires fr_rel(fm, fc), load(fm, l) is Some,
    ensures vr(load(fm, l)->Some_0, ctcore::sem::read_loc(fc, l)), pure_fr(fm) ==> pure(load(fm, l)->Some_0),
{
    match l.root {
        Root::Local(i) => {
            lemma_vr_read_at(fm.locals[i as int], fc.locals[i as int], l.path);
            if pure_fr(fm) { lemma_pure_read_at(fm.locals[i as int], l.path); }
        },
        Root::Slot(j) => {
            lemma_vr_read_at(fm.slots[j as int], fc.slots[j as int], l.path);
            if pure_fr(fm) { lemma_pure_read_at(fm.slots[j as int], l.path); }
        },
    }
}

// ------------------------------------------------------------------ places

/// A MIR place cursor against core's: the same location, or agreeing `Mut`-free snapshots.
pub open spec fn cur_rel(p: PRes, q: Cur) -> bool {
    match (p, q) {
        (PRes::At(l), Cur::L(l2)) => l == l2,
        (PRes::Snap(v), Cur::V(c)) => vr(v, c) && mut_free(v),
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
    requires fr_rel(fm, fc), pure_fr(fm), cur_rel(p, q), lowers_proj(e, cq), proj_step(fm, p, e) is Some,
    ensures cur_rel(proj_step(fm, p, e)->Some_0.0, ctcore::sem::step(fc, q, cq).0),
        proj_step(fm, p, e)->Some_0.1 == ctcore::sem::step(fc, q, cq).1,
{
    let cur = pres_val(fm, p)->Some_0;
    let qv = match q { Cur::L(l) => ctcore::sem::read_loc(fc, l), Cur::V(v) => v };
    assert(vr(cur, qv) && pure(cur)) by {
        match p {
            PRes::At(l) => lemma_load(fm, fc, l),
            PRes::Snap(v) => lemma_mf_pure(v),
        }
    }
    match e {
        ProjectionElem::Deref => {
            match cur {
                Val::Mut(l) => { assert(p is At) by { if p is Snap { assert(!mut_free(cur)); } } },
                Val::Shr(b) => {},
                _ => {},
            }
        },
        ProjectionElem::Field(i, _) => {
            if let PRes::Snap(v) = p { lemma_vr_get(v, q->V_0, PE::Field(i as nat)); lemma_mf_get(v, PE::Field(i as nat)); }
        },
        ProjectionElem::Index(x) => {
            let i = root_val(fm, Root::Local(x as nat))->Some_0->Int_0;
            assert(fc.locals[x as int] == Val::Int(i));
            assert(ctcore::sem::read_loc(fc, ctcore::sem::local_loc(x as nat)) == Val::Int(i));
            if let PRes::Snap(v) = p { lemma_vr_get(v, q->V_0, PE::Index(i as nat)); lemma_mf_get(v, PE::Index(i as nat)); }
        },
        ProjectionElem::ConstantIndex { offset, min_length: _, from_end: _ } => {
            if let PRes::Snap(v) = p { lemma_vr_get(v, q->V_0, PE::Index(offset as nat)); lemma_mf_get(v, PE::Index(offset as nat)); }
        },
        ProjectionElem::Downcast(k) => {
            if let PRes::Snap(v) = p { lemma_vr_get(v, q->V_0, PE::Variant(k as nat)); lemma_mf_get(v, PE::Variant(k as nat)); }
        },
        _ => {},
    }
}

/// The first `n` projections.
pub proof fn lemma_places(fm: Frame, fc: Frame, base: PRes, cbase: Cur, ps: Seq<ProjectionElem>, qs: Seq<c::Proj>, n: nat)
    requires fr_rel(fm, fc), pure_fr(fm), cur_rel(base, cbase), projs_rel(ps, qs), n <= ps.len(), places(fm, base, ps, n) is Some,
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
    requires fr_rel(fm, fc), pure_fr(fm), q.local == p.local, projs_rel(p.projection@, q.proj@), eval_place(fm, p) is Some,
    ensures cur_rel(eval_place(fm, p)->Some_0.0, ctcore::sem::place_walk(fc, q).0),
        eval_place(fm, p)->Some_0.1 == ctcore::sem::place_walk(fc, q).1,
{
    let base = PRes::At(Loc { root: Root::Local(p.local as nat), path: seq![] });
    assert(q.proj@.subrange(0, q.proj@.len() as int) == q.proj@);
    lemma_places(fm, fc, base, Cur::L(ctcore::sem::local_loc(q.local as nat)), p.projection@, q.proj@, p.projection@.len());
}

/// Reading a lowered place.
pub proof fn lemma_read_place(fm: Frame, fc: Frame, p: Place, q: c::Place)
    requires fr_rel(fm, fc), pure_fr(fm), q.local == p.local, projs_rel(p.projection@, q.proj@), read_place(fm, p) is Some,
    ensures vr(read_place(fm, p)->Some_0.0, ctcore::sem::read_place(fc, q).0), pure(read_place(fm, p)->Some_0.0),
        read_place(fm, p)->Some_0.1 == ctcore::sem::read_place(fc, q).1,
{
    lemma_place(fm, fc, p, q);
    match eval_place(fm, p)->Some_0.0 {
        PRes::At(l) => lemma_load(fm, fc, l),
        PRes::Snap(v) => lemma_mf_pure(v),
    }
}

pub proof fn lemma_lowers_place(m: MirCrate, b: Body, p: Place, q: c::Place, mutating: bool)
    requires lowers_place(m, b, p, q, mutating),
    ensures q.local == p.local, projs_rel(p.projection@, q.proj@),
{
}

} // verus!
