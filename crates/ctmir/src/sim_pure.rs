//! The simulation, frame purity (no `Mut` inside a snapshot) and stores. MIR values the semantics
//! builds are pure, except a snapshot `&place` of a value that holds a `Mut`: that is a typing
//! fact (`ty_free` forbids `&mut` under a reference), a hypothesis of the statement lemma.
#[allow(unused_imports)]
use crate::mir::*;
#[allow(unused_imports)]
use crate::sem::*;
#[allow(unused_imports)]
use crate::sim::*;
#[cfg(verus_keep_ghost)]
use ctcore::sem::{get, pad, put, read_at, write_at};
#[allow(unused_imports)]
use ctcore::sem::{Event, Frame, Loc, Root, Val, PE};
use vstd::prelude::*;

verus! {

pub proof fn lemma_us_mf(v: Val)
    requires us(v),
    ensures mut_free(v),
    decreases v,
{
    match v {
        Val::Tup(vs) => { assert forall|i: int| 0 <= i < vs.len() implies mut_free(#[trigger] vs[i]) by { lemma_us_mf(vs[i]); } },
        Val::Adt(_, vs) => { assert forall|i: int| 0 <= i < vs.len() implies mut_free(#[trigger] vs[i]) by { lemma_us_mf(vs[i]); } },
        Val::Arr(vs) => { assert forall|i: int| 0 <= i < vs.len() implies mut_free(#[trigger] vs[i]) by { lemma_us_mf(vs[i]); } },
        _ => {},
    }
}

pub proof fn lemma_ul_mf(m: MirCrate, t: Ty, fuel: nat, clos: bool)
    ensures unit_like(m, t, fuel, clos) matches Some((v, _)) ==> mut_free(v),
{
    crate::sim_const::lemma_ul_us(m, t, fuel, clos);
    if let Some((v, _)) = unit_like(m, t, fuel, clos) { lemma_us_mf(v); }
}

pub open spec fn mfs(vs: Seq<Val>) -> bool { forall|i: int| 0 <= i < vs.len() ==> mut_free(#[trigger] vs[i]) }

/// Decoded constants hold no `Mut`.
pub proof fn lemma_dec_mf(m: MirCrate, t: Ty, a: Allocation, off: nat, fuel: nat)
    ensures dec(m, t, a, off, fuel) matches Some((v, _)) ==> mut_free(v),
    decreases fuel, 0nat, 0nat,
{
    if fuel > 0 {
        let f = (fuel - 1) as nat;
        if let Some(r) = rigid(m, t) {
            if int_of(r) is None {
                match r {
                    RigidTy::Pat(base, _) => lemma_dec_mf(m, base, a, off, f),
                    RigidTy::Tuple(ts) => lemma_dec_tuple_mf(m, t, ts@, a, off, f),
                    RigidTy::Array(e, c) => lemma_dec_array_mf(m, t, e, c.id, a, off, f),
                    RigidTy::Adt(_, _) => lemma_dec_adt_mf(m, t, a, off, f),
                    RigidTy::Ref(_, p, _) => lemma_dec_ref_mf(m, p, a, off, f),
                    _ => {},
                }
            }
        }
    }
}

proof fn lemma_dec_tuple_mf(m: MirCrate, t: Ty, ts: Seq<Ty>, a: Allocation, off: nat, fuel: nat)
    ensures dec_tuple(m, t, ts, a, off, fuel) matches Some((v, _)) ==> mut_free(v),
    decreases fuel, 2nat, 0nat,
{
    if let Some(l) = layout(m, t) { if let Some(o) = offs_of(l.fields) { lemma_dec_fields_mf(m, ts, o, a, off, fuel, ts.len()); } }
}

proof fn lemma_dec_array_mf(m: MirCrate, t: Ty, e: Ty, c: TyConstId, a: Allocation, off: nat, fuel: nat)
    ensures dec_array(m, t, e, c, a, off, fuel) matches Some((v, _)) ==> mut_free(v),
    decreases fuel, 2nat, 0nat,
{
    if let (Some(n), Some(l)) = (const_usize(m, c), layout(m, t)) { if let FieldsShape::Array { stride, count: _ } = l.fields {
        lemma_dec_elems_mf(m, e, stride.num_bits as nat / 8, a, off, fuel, n as nat);
    } }
}

proof fn lemma_dec_adt_mf(m: MirCrate, t: Ty, a: Allocation, off: nat, fuel: nat)
    ensures dec_adt(m, t, a, off, fuel) matches Some((v, _)) ==> mut_free(v),
    decreases fuel, 2nat, 0nat,
{
    if let (Some(row), Some(l)) = (adt_row(m, t), layout(m, t)) { if let Some((k, o)) = adt_sel(row, l, a, off) {
        if k < row.variants@.len() { lemma_dec_fields_mf(m, row.variants@[k as int].fields@, o, a, off, fuel, o.len()); }
    } }
}

proof fn lemma_dec_ref_mf(m: MirCrate, p: Ty, a: Allocation, off: nat, fuel: nat)
    ensures dec_ref(m, p, a, off, fuel) matches Some((v, _)) ==> mut_free(v),
    decreases fuel, 2nat, 0nat,
{
    lemma_ul_mf(m, p, tfuel(m), true);
    if let (Some(id), Some(addr)) = (prov_at(a, off), le(a, off, 8)) {
        if let Some(a2) = alloc_mem(m, id) { lemma_dec_mf(m, p, a2, addr, fuel); }
    }
}

pub proof fn lemma_dec_fields_mf(m: MirCrate, ts: Seq<Ty>, os: Seq<MachineSize>, a: Allocation, base: nat, fuel: nat, n: nat)
    ensures dec_fields(m, ts, os, a, base, fuel, n) matches Some((vs, _)) ==> mfs(vs),
    decreases fuel, 1nat, n,
{
    if n > 0 && n <= ts.len() && n <= os.len() {
        lemma_dec_fields_mf(m, ts, os, a, base, fuel, (n - 1) as nat);
        lemma_dec_mf(m, ts[n - 1], a, (base + os[n - 1].num_bits / 8) as nat, fuel);
    }
}

pub proof fn lemma_dec_elems_mf(m: MirCrate, e: Ty, stride: nat, a: Allocation, base: nat, fuel: nat, n: nat)
    ensures dec_elems(m, e, stride, a, base, fuel, n) matches Some((vs, _)) ==> mfs(vs),
    decreases fuel, 1nat, n,
{
    if n > 0 {
        lemma_dec_elems_mf(m, e, stride, a, base, fuel, (n - 1) as nat);
        lemma_dec_mf(m, e, a, (base + (n - 1) * stride) as nat, fuel);
    }
}

pub proof fn lemma_const_mf(m: MirCrate, k: ConstOperand)
    ensures const_val(m, k) matches Some((v, _)) ==> mut_free(v),
{
    match k.const_.kind {
        ConstantKind::Allocated(a) => lemma_dec_mf(m, k.const_.ty, a, 0, dfuel(m)),
        _ => lemma_ul_mf(m, k.const_.ty, tfuel(m), true),
    }
}

// ------------------------------------------------------------------ reads of a pure frame are pure

pub open spec fn pres_pure(p: PRes) -> bool { match p { PRes::Snap(v) => mut_free(v), _ => true } }

proof fn lemma_places_pure(fr: Frame, base: PRes, ps: Seq<ProjectionElem>, n: nat)
    requires pure_fr(fr), pres_pure(base), places(fr, base, ps, n) is Some,
    ensures pres_pure(places(fr, base, ps, n)->Some_0.0),
    decreases n,
{
    if n > 0 {
        lemma_places_pure(fr, base, ps, (n - 1) as nat);
        let p = places(fr, base, ps, (n - 1) as nat)->Some_0.0;
        let cur = pres_val(fr, p)->Some_0;
        match p {
            PRes::At(l) => { lemma_load_pure(fr, l); },
            PRes::Snap(v) => { lemma_mf_pure(v); },
        }
        match (ps[n - 1], p) {
            (ProjectionElem::Field(i, _), PRes::Snap(v)) => lemma_mf_get(v, PE::Field(i as nat)),
            (ProjectionElem::Downcast(i), PRes::Snap(v)) => lemma_mf_get(v, PE::Variant(i as nat)),
            (ProjectionElem::Index(_), PRes::Snap(v)) => {
                let i = root_val(fr, Root::Local(ps[n - 1]->Index_0 as nat))->Some_0->Int_0;
                lemma_mf_get(v, PE::Index(i as nat));
            },
            (ProjectionElem::ConstantIndex { offset, min_length: _, from_end }, PRes::Snap(v)) => {
                let vs = v->Arr_0;
                lemma_mf_get(v, PE::Index(if from_end { (vs.len() - offset) as nat } else { offset as nat }));
            },
            _ => {},
        }
    }
}

pub proof fn lemma_load_pure(fr: Frame, l: Loc)
    requires pure_fr(fr), load(fr, l) is Some,
    ensures pure(load(fr, l)->Some_0),
{
    match l.root {
        Root::Local(i) => lemma_pure_read_at(fr.locals[i as int], l.path),
        Root::Slot(j) => lemma_pure_read_at(fr.slots[j as int], l.path),
    }
}

pub proof fn lemma_read_pure(fr: Frame, p: Place)
    requires pure_fr(fr), read_place(fr, p) is Some,
    ensures pure(read_place(fr, p)->Some_0.0),
{
    let base = PRes::At(Loc { root: Root::Local(p.local as nat), path: seq![] });
    lemma_places_pure(fr, base, p.projection@, p.projection@.len());
    match eval_place(fr, p)->Some_0.0 {
        PRes::At(l) => lemma_load_pure(fr, l),
        PRes::Snap(v) => lemma_mf_pure(v),
    }
}

pub proof fn lemma_op_pure(m: MirCrate, fr: Frame, x: Operand)
    requires pure_fr(fr), eval_op(m, fr, x) is Some,
    ensures pure(eval_op(m, fr, x)->Some_0.0),
{
    match x {
        Operand::Copy(p) => lemma_read_pure(fr, p),
        Operand::Move(p) => lemma_read_pure(fr, p),
        Operand::Constant(k) => { lemma_const_mf(m, k); lemma_mf_pure(const_val(m, k)->Some_0.0); },
        _ => {},
    }
}

pub proof fn lemma_ops_pure(m: MirCrate, fr: Frame, xs: Seq<Operand>, n: nat)
    requires pure_fr(fr), eval_ops(m, fr, xs, n) is Some,
    ensures forall|i: int| 0 <= i < eval_ops(m, fr, xs, n)->Some_0.0.len() ==> pure(#[trigger] eval_ops(m, fr, xs, n)->Some_0.0[i]),
        eval_ops(m, fr, xs, n)->Some_0.0.len() == n,
    decreases n,
{
    if n > 0 {
        lemma_ops_pure(m, fr, xs, (n - 1) as nat);
        lemma_op_pure(m, fr, xs[n - 1]);
        let vs = eval_ops(m, fr, xs, (n - 1) as nat)->Some_0.0;
        let v = eval_op(m, fr, xs[n - 1])->Some_0.0;
        assert forall|i: int| 0 <= i < n implies pure(#[trigger] vs.push(v)[i]) by { if i < n - 1 { assert(vs.push(v)[i] == vs[i]); } }
    }
}

/// The one typing fact purity needs: a shared borrow snapshots a `Mut`-free value.
pub open spec fn shr_tf(fr: Frame, rv: Rvalue) -> bool {
    rv matches Rvalue::Ref(_, BorrowKind::Shared, p) ==> (read_place(fr, p) matches Some((v, _)) ==> mut_free(v))
}

pub proof fn lemma_rv_pure(m: MirCrate, b: Body, fr: Frame, rv: Rvalue)
    requires pure_fr(fr), eval_rv(m, b, fr, rv) is Some, shr_tf(fr, rv),
    ensures pure(eval_rv(m, b, fr, rv)->Some_0.0),
{
    hide(eval_op);
    hide(eval_ops);
    hide(rv_bin);
    hide(rv_checked);
    hide(rv_discr);
    hide(rv_un);
    match rv {
        Rvalue::Use(x, _) => { lemma_op_pure(m, fr, x); assert(eval_rv(m, b, fr, rv) == eval_op(m, fr, x)); },
        Rvalue::Cast(ck, x, to) => {
            lemma_op_pure(m, fr, x);
            reveal(eval_op);
            assert(pure(eval_rv(m, b, fr, rv)->Some_0.0));
        },
        Rvalue::BinaryOp(op, x, y) => { reveal(rv_bin); assert(pure(eval_rv(m, b, fr, rv)->Some_0.0)); },
        Rvalue::CheckedBinaryOp(op, x, y) => {
            reveal(rv_checked);
            let t = eval_rv(m, b, fr, rv)->Some_0.0->Tup_0;
            assert(t.len() == 2 && t[0] is Int && t[1] is Int);
            assert forall|i: int| 0 <= i < t.len() implies pure(#[trigger] t[i]) by {}
            assert(pure(eval_rv(m, b, fr, rv)->Some_0.0)); },
        Rvalue::UnaryOp(op, x) => { reveal(rv_un); assert(pure(eval_rv(m, b, fr, rv)->Some_0.0)); },
        Rvalue::Discriminant(p) => { reveal(rv_discr); assert(pure(eval_rv(m, b, fr, rv)->Some_0.0)); },
        Rvalue::Ref(_, bk, p) => {
            match bk {
                BorrowKind::Shared => {
                    let v = read_place(fr, p)->Some_0.0;
                    assert(eval_rv(m, b, fr, rv)->Some_0.0 == Val::Shr(Box::new(v)));
                },
                _ => { assert(pure(eval_rv(m, b, fr, rv)->Some_0.0)); },
            }
        },
        Rvalue::Len(p) => { assert(pure(eval_rv(m, b, fr, rv)->Some_0.0)); },
        Rvalue::CopyForDeref(p) => { lemma_read_pure(fr, p); assert(pure(eval_rv(m, b, fr, rv)->Some_0.0)); },
        Rvalue::Aggregate(ak, ops) => {
            lemma_ops_pure(m, fr, ops@, ops@.len());
            let vs = eval_ops(m, fr, ops@, ops@.len())->Some_0.0;
            assert(pure(Val::Arr(vs)) && pure(Val::Tup(vs)));
            match ak { AggregateKind::Adt(_, var, _, _, _) => { assert(pure(Val::Adt(var as nat, vs))); }, _ => { assert(pure(eval_rv(m, b, fr, rv)->Some_0.0)); } }
        },
        Rvalue::Repeat(x, _) => {
            lemma_op_pure(m, fr, x);
            let v = eval_op(m, fr, x)->Some_0.0;
            let n = const_usize(m, rv->Repeat_1.id)->Some_0 as nat;
            let s = Seq::new(n, |_i: int| v);
            assert forall|i: int| 0 <= i < s.len() implies pure(#[trigger] s[i]) by {}
            assert(eval_rv(m, b, fr, rv)->Some_0.0->Arr_0 =~= s);
        },
        _ => { assert(pure(eval_rv(m, b, fr, rv)->Some_0.0)); },
    }
}

// ------------------------------------------------------------------ stores

pub proof fn lemma_pure_put(v: Val, e: PE, w: Val)
    requires pure(v), pure(w),
    ensures pure(put(v, e, w)),
{
    match (v, e) {
        (Val::Tup(vs), PE::Field(i)) => {
            let s = pad(vs, i + 1).update(i as int, w);
            assert forall|j: int| 0 <= j < s.len() implies pure(#[trigger] s[j]) by { if j != i && j >= vs.len() { assert(s[j] == Val::Unit); } }
        },
        (Val::Adt(k, vs), PE::Field(i)) => {
            let s = pad(vs, i + 1).update(i as int, w);
            assert forall|j: int| 0 <= j < s.len() implies pure(#[trigger] s[j]) by { if j != i && j >= vs.len() { assert(s[j] == Val::Unit); } }
        },
        (Val::Arr(vs), PE::Index(i)) => {
            if i < vs.len() {
                let s = vs.update(i as int, w);
                assert forall|j: int| 0 <= j < s.len() implies pure(#[trigger] s[j]) by { if j != i { assert(s[j] == vs[j]); } }
            }
        },
        _ => {},
    }
}

pub proof fn lemma_pure_write_at(v: Val, p: Seq<PE>, w: Val)
    requires pure(v), pure(w),
    ensures pure(write_at(v, p, w)),
    decreases p.len(),
{
    if p.len() > 0 {
        lemma_pure_get(v, p[0]);
        lemma_pure_write_at(get(v, p[0]), p.drop_first(), w);
        lemma_pure_put(v, p[0], write_at(get(v, p[0]), p.drop_first(), w));
    }
}

/// A MIR store and core's write of the same location keep the frames related (and pure).
pub proof fn lemma_store(fm: Frame, fc: Frame, l: Loc, w: Val, d: Val)
    requires fr_rel(fm, fc), store(fm, l, w) is Some, vr(w, d), mws(root_val(fm, l.root)->Some_0, l.path, w),
    ensures fr_rel(store(fm, l, w)->Some_0, ctcore::sem::write_loc(fc, l, d)),
        pure_fr(fm) && pure(w) ==> pure_fr(store(fm, l, w)->Some_0),
        ctcore::sem::write_loc(fc, l, d).locals.len() == fc.locals.len(),
{
    let fm2 = store(fm, l, w)->Some_0;
    let fc2 = ctcore::sem::write_loc(fc, l, d);
    match l.root {
        Root::Local(i) => {
            lemma_mws(fm.locals[i as int], fc.locals[i as int], l.path, w, d);
            lemma_vr_write_at(fm.locals[i as int], fc.locals[i as int], l.path, w, d);
            assert forall|k: int| 0 <= k < fm2.locals.len() implies vr(#[trigger] fm2.locals[k], fc2.locals[k]) by {}
            if pure_fr(fm) && pure(w) {
                lemma_pure_write_at(fm.locals[i as int], l.path, w);
                assert forall|k: int| 0 <= k < fm2.locals.len() implies pure(#[trigger] fm2.locals[k]) by {}
            }
        },
        Root::Slot(j) => {
            lemma_mws(fm.slots[j as int], fc.slots[j as int], l.path, w, d);
            lemma_vr_write_at(fm.slots[j as int], fc.slots[j as int], l.path, w, d);
            assert forall|k: int| 0 <= k < fm2.slots.len() implies vr(#[trigger] fm2.slots[k], fc2.slots[k]) by {}
            if pure_fr(fm) && pure(w) {
                lemma_pure_write_at(fm.slots[j as int], l.path, w);
                assert forall|k: int| 0 <= k < fm2.slots.len() implies pure(#[trigger] fm2.slots[k]) by {}
            }
        },
    }
}

} // verus!
