//! The MIR semantics (trusted; written clean-room from rustc_public's types, MiniRust and the
//! rustc dev guide, per spec §MIR semantics). A fuelled big-step run over a body's blocks gives
//! the final frame, the leakage event trace and the step count, or `None` for fuel exhaustion,
//! UB, a panic (failed `Assert`, a std precondition), `Unreachable`/`Resume`/`Abort`, an unwind
//! edge, or anything outside the subset (decisions 1, 2). Values, frames, events and integer
//! arithmetic are `ctcore::sem`'s shared vocabulary:
//! - an int or `bool` is `Int(bit pattern)`; a tuple `Tup`, an ADT `Adt(variant, fields)`, an array
//!   or slice `Arr`; a `Vec<E>` is `Arr` of its elements (the value model has no heap);
//! - `&place` is `Shr(snapshot)`, `&mut place` is `Mut(location)` (decision 3);
//! - fn items, closures and fn pointers are the opaque `Unit`;
//! - a value of a unit-like (single-inhabitant) type has two forms, chosen by its producer: the
//!   canonical `Unit` from a `ZeroSized` constant, an entry local, a ghost result, a `()`-returning
//!   std row and a decoded `()`; the structural `Tup`/`Adt`/`Arr` from aggregates, `Repeat`, decoded
//!   structs and arrays and `&ZST` constants; a root argument may be either (`wt_val`). A unit-like
//!   type holding an array (`ul_arr`) is structural from every producer, since an `Arr`'s length is
//!   read. Every consumer
//!   treats the two forms alike (`Discriminant` reads a one-variant enum's `Unit` as its variant;
//!   navigation and writes go through `ctcore::sem`'s `get`/`put`, which give and keep `Unit`), except
//!   that a `Declass(v)` event carries the form.
//!
//! The AST is read only through views (`@`): `Vec`-holding values are never compared with `==`.
#[allow(unused_imports)]
use crate::mir::*;
// The shared vocabulary from `ctcore::sem` (spec §MIR semantics), and nothing else from it.
#[cfg(verus_keep_ghost)]
use ctcore::sem::{bits, binop, cast, get, ival, read_at, signed, unop, write_at, Res, Root, PE};
use ctcore::sem::{Event, Frame, Loc, Val};
#[allow(unused_imports)]
use ctcore::syntax::{BinOp as COp, IntTy as CTy, UnOp as CUn};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

verus! {

pub spec const USZ: nat = 0xffff_ffff_ffff_ffff;

/// The manifest's policy calls, by `ct_key`: `declassify` keys are the identity emitting
/// `Declass(v)`; `ghost_unit` keys (manifest `ghost` lines) give the destination type's
/// unit-like value with no events.
pub struct CallPolicy { pub declassify: Set<Seq<u8>>, pub ghost_unit: Set<Seq<u8>> }

// ------------------------------------------------------------------ table lookups (first match)

pub open spec fn find_from<T>(s: Seq<T>, p: spec_fn(T) -> bool, k: nat) -> Option<nat>
    decreases s.len() - k,
{
    if k >= s.len() { None } else if p(s[k as int]) { Some(k) } else { find_from(s, p, k + 1) }
}

pub open spec fn find<T>(s: Seq<T>, p: spec_fn(T) -> bool) -> Option<nat> { find_from(s, p, 0) }

pub open spec fn ty_kind(m: MirCrate, t: Ty) -> Option<TyKind> {
    match find(m.tys@, |r: TyRow| r.id == t) { Some(k) => Some(m.tys@[k as int].kind), None => None }
}

pub open spec fn rigid(m: MirCrate, t: Ty) -> Option<RigidTy> {
    match ty_kind(m, t) { Some(TyKind::RigidTy(r)) => Some(r), _ => None }
}

pub open spec fn adt_row(m: MirCrate, t: Ty) -> Option<Adt> {
    match find(m.adts@, |r: Adt| r.ty == t) { Some(k) => Some(m.adts@[k as int]), None => None }
}

pub open spec fn layout(m: MirCrate, t: Ty) -> Option<LayoutShape> {
    match find(m.layouts@, |r: LayoutRow| r.ty == t) { Some(k) => Some(m.layouts@[k as int].shape), None => None }
}

pub open spec fn const_usize(m: MirCrate, id: TyConstId) -> Option<u64> {
    match find(m.consts@, |r: ConstRow| r.id == id) { Some(k) => m.consts@[k as int].usize, None => None }
}

/// `GlobalAlloc::Memory` only: `Function`, `Static`, `VTable` and `TypeId` are outside the subset.
pub open spec fn alloc_mem(m: MirCrate, id: AllocId) -> Option<Allocation> {
    match find(m.allocs@, |r: AllocRow| r.id == id) {
        Some(k) => match m.allocs@[k as int].alloc { GlobalAlloc::Memory(a) => Some(a), _ => None },
        None => None,
    }
}

pub open spec fn inst_idx(m: MirCrate, id: InstanceDef) -> Option<nat> { find(m.insts@, |x: Inst| x.id == id) }

/// The body of `insts[i]`, run only for `Item` and `Shim` instances: an `Intrinsic` may carry a
/// fallback body, which is not what it does.
pub open spec fn inst_body(m: MirCrate, i: nat) -> Option<Body> {
    if i < m.insts@.len() && (m.insts@[i as int].kind is Item || m.insts@[i as int].kind is Shim) {
        m.insts@[i as int].body
    } else {
        None
    }
}

/// Depth bounds for recursion through type ids (no structural measure): a non-pointer type
/// cannot contain itself, and each provenance hop enters another allocation.
pub open spec fn tfuel(m: MirCrate) -> nat { m.tys@.len() + 1 }
pub open spec fn dfuel(m: MirCrate) -> nat { (m.tys@.len() + 1) * (m.allocs@.len() + 1) }

// ------------------------------------------------------------------ types

pub open spec fn int_of(r: RigidTy) -> Option<CTy> {
    match r {
        RigidTy::Bool => Some(CTy::Bool),
        RigidTy::Int(i) => match i {
            IntTy::Isize => Some(CTy::Isize), IntTy::I8 => Some(CTy::I8), IntTy::I16 => Some(CTy::I16),
            IntTy::I32 => Some(CTy::I32), IntTy::I64 => Some(CTy::I64), IntTy::I128 => Some(CTy::I128),
            IntTy::Unknown(_) => None,
        },
        RigidTy::Uint(u) => match u {
            UintTy::Usize => Some(CTy::Usize), UintTy::U8 => Some(CTy::U8), UintTy::U16 => Some(CTy::U16),
            UintTy::U32 => Some(CTy::U32), UintTy::U64 => Some(CTy::U64), UintTy::U128 => Some(CTy::U128),
            UintTy::Unknown(_) => None,
        },
        _ => None,
    }
}

pub open spec fn int_ty(m: MirCrate, t: Ty) -> Option<CTy> {
    match rigid(m, t) { Some(r) => int_of(r), None => None }
}

/// Bytes an int or `bool` occupies (x86-64).
pub open spec fn ibytes(it: CTy) -> nat { if it is Bool { 1 } else { bits(it) / 8 } }

pub open spec fn is_mut_ref(m: MirCrate, t: Ty) -> bool { rigid(m, t) matches Some(RigidTy::Ref(_, _, Mutability::Mut)) }

/// Not `str`, a slice or a trait object (the dump gives these a size-0 layout).
pub open spec fn sized(m: MirCrate, t: Ty) -> bool {
    rigid(m, t) matches Some(r) && !(r is Str || r is Slice || r is Dynamic)
}

pub open spec fn is_zst(m: MirCrate, t: Ty) -> bool { sized(m, t) && (layout(m, t) matches Some(l) && l.size.num_bits == 0) }

/// A ghost result's type: sized, unit-like without closures, and size 0 if its layout is dumped
/// (most `Ghost<_>` destinations have no layout row).
pub open spec fn zst_dest(m: MirCrate, t: Ty) -> bool {
    sized(m, t) && unit_like(m, t, tfuel(m), false) is Some
        && match layout(m, t) { Some(l) => l.size.num_bits == 0, None => true }
}

/// `Vec<E, _>`: its element type `E`.
pub open spec fn vec_elem(m: MirCrate, t: Ty) -> Option<Ty> {
    match (adt_row(m, t), rigid(m, t)) {
        (Some(a), Some(RigidTy::Adt(_, ga))) =>
            if a.name@ == b"std::vec::Vec"@ && ga.0@.len() >= 1 && ga.0@[0] is Type { Some(ga.0@[0]->Type_0) } else { None },
        _ => None,
    }
}

/// `Vec<E>` with integer `E`: its drop glue is a std-model leaf (decision 4).
pub open spec fn vec_int(m: MirCrate, t: Ty) -> bool {
    vec_elem(m, t) matches Some(e) && int_ty(m, e) matches Some(it) && !(it is Bool)
}

pub open spec fn proj_ty(m: MirCrate, t: Ty, e: ProjectionElem) -> Option<Ty> {
    match e {
        ProjectionElem::Deref => match rigid(m, t) { Some(RigidTy::Ref(_, p, _)) => Some(p), _ => None },
        ProjectionElem::Field(_, ft) => Some(ft),
        ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => match rigid(m, t) {
            Some(RigidTy::Array(el, _)) => Some(el),
            Some(RigidTy::Slice(el)) => Some(el),
            _ => None,
        },
        ProjectionElem::Downcast(_) => Some(t),
        _ => None,
    }
}

pub open spec fn tys_along(m: MirCrate, t: Ty, ps: Seq<ProjectionElem>, n: nat) -> Option<Ty>
    decreases n,
{
    if n == 0 { Some(t) } else if n > ps.len() { None } else {
        match tys_along(m, t, ps, (n - 1) as nat) { Some(u) => proj_ty(m, u, ps[n - 1]), None => None }
    }
}

/// `Place::ty` (mir/body.rs): the local's declared type through the projections.
pub open spec fn place_ty(m: MirCrate, b: Body, p: Place) -> Option<Ty> {
    if p.local < b.locals@.len() { tys_along(m, b.locals@[p.local as int].ty, p.projection@, p.projection@.len()) } else { None }
}

pub open spec fn op_ty(m: MirCrate, b: Body, op: Operand) -> Option<Ty> {
    match op {
        Operand::Copy(p) => place_ty(m, b, p),
        Operand::Move(p) => place_ty(m, b, p),
        Operand::Constant(c) => Some(c.const_.ty),
        _ => None,
    }
}

/// No `Mut` anywhere inside `v`: a location is meaningful only in its own frame.
pub open spec fn mut_free(v: Val) -> bool
    decreases v,
{
    match v {
        Val::Mut(_) => false,
        Val::Tup(vs) => forall|i: int| 0 <= i < vs.len() ==> mut_free(#[trigger] vs[i]),
        Val::Adt(_, vs) => forall|i: int| 0 <= i < vs.len() ==> mut_free(#[trigger] vs[i]),
        Val::Arr(vs) => forall|i: int| 0 <= i < vs.len() ==> mut_free(#[trigger] vs[i]),
        Val::Shr(b) => mut_free(*b),
        _ => true,
    }
}

pub open spec fn unit_val() -> Val { Val::Unit }

/// A tuple's value; `()` is the canonical `Unit` (a single-inhabitant value: its representation
/// carries no meaning, and `Unit` is what core's images build for it).
pub open spec fn tup_val(vs: Seq<Val>) -> Val { if vs.len() == 0 { Val::Unit } else { Val::Tup(vs) } }

/// The value of a zero-sized type, with its count of ADT and reference nodes (for decision 7):
/// tuples, single-variant structs, arrays of them and empty arrays (`[T; 0]`, of any `T`); fn
/// items are `Unit`, and so are closures
/// when `clos` (a `ZeroSized` constant or a ZST-layout pointee: a closure without captures).
pub open spec fn unit_like(m: MirCrate, t: Ty, fuel: nat, clos: bool) -> Option<(Val, nat)>
    decreases fuel, 0nat,
{
    if fuel == 0 { None } else {
        let f = (fuel - 1) as nat;
        match rigid(m, t) {
            Some(RigidTy::Tuple(ts)) => match unit_likes(m, ts@, f, ts@.len(), clos) {
                Some((vs, c)) => Some((tup_val(vs), c)),
                None => None,
            },
            Some(RigidTy::Adt(_, _)) => match adt_row(m, t) {
                Some(a) => if !a.is_box && !(a.kind is Union) && a.variants@.len() == 1 {
                    match unit_likes(m, a.variants@[0].fields@, f, a.variants@[0].fields@.len(), clos) {
                        Some((vs, c)) => Some((Val::Adt(0, vs), c + 1)),
                        None => None,
                    }
                } else { None },
                None => None,
            },
            Some(RigidTy::Array(e, c)) => match const_usize(m, c.id) {
                Some(n) => if n == 0 { Some((Val::Arr(seq![]), 0)) } else {
                    match unit_like(m, e, f, clos) {
                        Some((v, k)) => Some((Val::Arr(Seq::new(n as nat, |_i: int| v)), (n as nat) * k)),
                        None => None,
                    }
                },
                None => None,
            },
            Some(RigidTy::FnDef(_, _)) => Some((Val::Unit, 0)),
            Some(RigidTy::Closure(_, _)) => if clos { Some((Val::Unit, 0)) } else { None },
            _ => None,
        }
    }
}

pub open spec fn unit_likes(m: MirCrate, ts: Seq<Ty>, fuel: nat, n: nat, clos: bool) -> Option<(Seq<Val>, nat)>
    decreases fuel, n,
{
    if n == 0 { Some((seq![], 0)) } else if n > ts.len() { None } else {
        match (unit_likes(m, ts, fuel, (n - 1) as nat, clos), unit_like(m, ts[n - 1], fuel, clos)) {
            (Some((vs, c)), Some((v, k))) => Some((vs.push(v), c + k)),
            _ => None,
        }
    }
}

/// An array among a type's tuple, one-variant ADT and array components (`unit_like`'s arms).
pub open spec fn has_arr(m: MirCrate, t: Ty, fuel: nat) -> bool
    decreases fuel,
{
    if fuel == 0 { false } else {
        let f = (fuel - 1) as nat;
        match rigid(m, t) {
            Some(RigidTy::Tuple(ts)) => exists|k: int| 0 <= k < ts@.len() && has_arr(m, #[trigger] ts@[k], f),
            Some(RigidTy::Adt(_, _)) => match adt_row(m, t) {
                Some(a) => a.variants@.len() == 1
                    && exists|k: int| 0 <= k < a.variants@[0].fields@.len() && has_arr(m, #[trigger] a.variants@[0].fields@[k], f),
                None => false,
            },
            Some(RigidTy::Array(_, _)) => true,
            _ => false,
        }
    }
}

/// A unit-like type holding an array (`[T; 0]`, or `[Z; n]` of a unit-like `Z`, at any depth): its
/// value's `Arr` nodes carry lengths that `Len`, `PtrMetadata`, `Index`, `ConstantIndex` and the
/// std rows read, so its producers keep `unit_like`'s structural value.
pub open spec fn ul_arr(m: MirCrate, t: Ty) -> bool { unit_like(m, t, tfuel(m), true) is Some && has_arr(m, t, tfuel(m)) }

/// The value a producer gives a unit-like type: the canonical `Unit`, or, for a type holding an
/// array, `unit_like`'s structural value (closures without captures `Unit`).
pub open spec fn ul_val(m: MirCrate, t: Ty) -> Val {
    if ul_arr(m, t) { unit_like(m, t, tfuel(m), true)->Some_0.0 } else { Val::Unit }
}

/// `ty` with any pattern type (`u8 is 1..`) replaced by its base.
pub open spec fn strip_pat(m: MirCrate, t: Ty) -> Ty {
    match rigid(m, t) { Some(RigidTy::Pat(base, _)) => base, _ => t }
}

/// `v` is a well-typed value of `ty`, a type the subset admits (patterns are not checked).
pub open spec fn wt_val(m: MirCrate, ty: Ty, v: Val) -> bool { ty_free(m, ty, tfuel(m), true) && wt_rec(m, ty, v) }

pub open spec fn wt_rec(m: MirCrate, ty: Ty, v: Val) -> bool
    decreases v,
{
    let t = strip_pat(m, ty);
    match rigid(m, t) {
        None => false,
        Some(r) => match int_of(r) {
            Some(it) => v matches Val::Int(n) && (n as int) < pow2(bits(it)),
            None => match v {
                Val::Tup(vs) => match r {
                    RigidTy::Tuple(ts) => vs.len() == ts@.len() && forall|i: int| 0 <= i < vs.len() ==> wt_rec(m, ts@[i], #[trigger] vs[i]),
                    _ => false,
                },
                Val::Arr(vs) => match r {
                    RigidTy::Array(e, c) => const_usize(m, c.id) == Some(vs.len() as u64) && vs.len() <= USZ
                        && forall|i: int| 0 <= i < vs.len() ==> wt_rec(m, e, #[trigger] vs[i]),
                    RigidTy::Slice(e) => vs.len() <= USZ && forall|i: int| 0 <= i < vs.len() ==> wt_rec(m, e, #[trigger] vs[i]),
                    RigidTy::Adt(_, _) => vec_elem(m, t) matches Some(e) && vs.len() <= USZ
                        && forall|i: int| 0 <= i < vs.len() ==> wt_rec(m, e, #[trigger] vs[i]),
                    _ => false,
                },
                Val::Adt(k, vs) => match (r, adt_row(m, t)) {
                    (RigidTy::Adt(_, _), Some(a)) => vec_elem(m, t) is None && !a.is_box && !(a.kind is Union)
                        && k < a.variants@.len() && vs.len() == a.variants@[k as int].fields@.len()
                        && forall|i: int| 0 <= i < vs.len() ==> wt_rec(m, a.variants@[k as int].fields@[i], #[trigger] vs[i]),
                    _ => false,
                },
                Val::Shr(b) => match r { RigidTy::Ref(_, p, Mutability::Not) => wt_rec(m, p, *b), _ => false },
                Val::Mut(_) => r matches RigidTy::Ref(_, _, Mutability::Mut),
                // a unit-like type without an array has two forms: structural and the canonical `Unit`
                Val::Unit => r is FnDef || r is Closure || r is FnPtr
                    || (r matches RigidTy::Ref(_, p, Mutability::Not) && rigid(m, p) matches Some(RigidTy::Str))
                    || (unit_like(m, t, tfuel(m), true) is Some && !ul_arr(m, t)),
                _ => false,
            },
        },
    }
}

// ------------------------------------------------------------------ constants (decision 5)

pub open spec fn byte_at(a: Allocation, i: nat) -> Option<u8> { if i < a.bytes@.len() { a.bytes@[i as int] } else { None } }

/// The `n` bytes at `off`, little-endian; `None` if any is uninitialized.
pub open spec fn le(a: Allocation, off: nat, n: nat) -> Option<nat>
    decreases n,
{
    if n == 0 { Some(0) } else {
        match (byte_at(a, off), le(a, off + 1, (n - 1) as nat)) { (Some(x), Some(r)) => Some(x as nat + 256 * r), _ => None }
    }
}

/// No pointer (8 bytes from each provenance entry) overlaps `[off, off + n)`.
pub open spec fn no_prov(a: Allocation, off: nat, n: nat) -> bool {
    forall|k: int| 0 <= k < a.provenance.ptrs@.len() ==>
        !(off < #[trigger] a.provenance.ptrs@[k].0 + 8 && a.provenance.ptrs@[k].0 < off + n)
}

pub open spec fn prov_at(a: Allocation, off: nat) -> Option<AllocId> {
    match find(a.provenance.ptrs@, |e: (usize, AllocId)| e.0 as nat == off) {
        Some(k) => Some(a.provenance.ptrs@[k as int].1),
        None => None,
    }
}

/// An int or `bool` at `off`: initialized, pointer-free, and a `bool` is 0 or 1.
pub open spec fn rd_int(a: Allocation, off: nat, it: CTy) -> Option<u128> {
    if no_prov(a, off, ibytes(it)) {
        match le(a, off, ibytes(it)) {
            Some(v) => if it is Bool && v > 1 { None } else { Some(v as u128) },
            None => None,
        }
    } else { None }
}

pub open spec fn offs_of(f: FieldsShape) -> Option<Seq<MachineSize>> {
    match f { FieldsShape::Arbitrary { offsets } => Some(offsets@), _ => None }
}

pub open spec fn len_bytes(l: IntegerLength) -> nat {
    match l { IntegerLength::I8 => 1, IntegerLength::I16 => 2, IntegerLength::I32 => 4, IntegerLength::I64 => 8, _ => 16 }
}

/// A tag's width in bytes: an int of its length, or a pointer (8 bytes on x86-64, e.g. the null
/// niche of `Option<&T>`). Its bytes must carry no provenance (`adt_sel`'s `no_prov`), so a tag
/// holding a real pointer is outside the subset.
pub open spec fn tag_bytes(p: Primitive) -> Option<nat> {
    match p { Primitive::Int { length, signed: _ } => Some(len_bytes(length)), Primitive::Pointer(_) => Some(8), _ => None }
}

/// The variant a tag selects (rustc_abi `TagEncoding`): `Direct` stores the discriminant truncated
/// to the tag; `Niche` maps tag `t` to `start + (t - niche_start) mod 2^bits` when that lies in
/// `niche_variants`, else to the untagged variant.
pub open spec fn tag_variant(row: Adt, enc: TagEncoding, t: nat, tbits: nat) -> Option<nat> {
    match enc {
        TagEncoding::Direct => find(row.variants@, |v: AdtVariant|
            v.discr is Some && (v.discr->Some_0 as int) % (pow2(tbits) as int) == t as int),
        TagEncoding::Niche { untagged_variant, niche_variants, niche_start } => {
            let rel = (t as int - niche_start as int) % (pow2(tbits) as int);
            if niche_variants.start <= niche_variants.end && rel <= niche_variants.end - niche_variants.start {
                Some((niche_variants.start + rel) as nat)
            } else { Some(untagged_variant as nat) }
        },
        _ => None,
    }
}

/// The variant of an ADT value at `off` and its fields' offsets, from the layout.
pub open spec fn adt_sel(row: Adt, l: LayoutShape, a: Allocation, off: nat) -> Option<(nat, Seq<MachineSize>)> {
    match l.variants {
        VariantsShape::Single { index } => match offs_of(l.fields) { Some(o) => Some((index as nat, o)), None => None },
        VariantsShape::Multiple { tag, tag_encoding, tag_field, variants } => match (tag, offs_of(l.fields)) {
            (Scalar::Initialized { value, valid_range: _ }, Some(o)) =>
                if tag_field < o.len() && o[tag_field as int].num_bits % 8 == 0 && tag_bytes(value) is Some {
                    let n = tag_bytes(value)->Some_0;
                    let toff = (off + o[tag_field as int].num_bits / 8) as nat;
                    match (no_prov(a, toff, n), le(a, toff, n)) {
                        (true, Some(t)) => match tag_variant(row, tag_encoding, t, 8 * n) {
                            Some(k) => if k < variants@.len() { Some((k, variants@[k as int].offsets@)) } else { None },
                            None => None,
                        },
                        _ => None,
                    }
                } else { None },
            _ => None,
        },
        _ => None,
    }
}

/// Decodes the value of type `t` at byte `off` of `a`, with its count of ADT and reference nodes.
pub open spec fn dec(m: MirCrate, t: Ty, a: Allocation, off: nat, fuel: nat) -> Option<(Val, nat)>
    decreases fuel, 0nat, 0nat,
{
    if fuel == 0 { None } else {
        let f = (fuel - 1) as nat;
        match rigid(m, t) {
            Some(r) => match int_of(r) {
                Some(it) => match rd_int(a, off, it) { Some(v) => Some((Val::Int(v), 0)), None => None },
                None => match r {
                    RigidTy::Pat(base, _) => dec(m, base, a, off, f),
                    RigidTy::Tuple(ts) => dec_tuple(m, t, ts@, a, off, f),
                    RigidTy::Array(e, c) => dec_array(m, t, e, c.id, a, off, f),
                    RigidTy::Adt(_, _) => dec_adt(m, t, a, off, f),
                    RigidTy::Ref(_, p, Mutability::Not) => dec_ref(m, p, a, off, f),
                    _ => None,
                },
            },
            None => None,
        }
    }
}

pub open spec fn dec_fields(m: MirCrate, ts: Seq<Ty>, os: Seq<MachineSize>, a: Allocation, base: nat, fuel: nat, n: nat)
    -> Option<(Seq<Val>, nat)>
    decreases fuel, 1nat, n,
{
    if n == 0 { Some((seq![], 0)) } else if n > ts.len() || n > os.len() || os[n - 1].num_bits % 8 != 0 { None } else {
        match (dec_fields(m, ts, os, a, base, fuel, (n - 1) as nat), dec(m, ts[n - 1], a, (base + os[n - 1].num_bits / 8) as nat, fuel)) {
            (Some((vs, c)), Some((v, k))) => Some((vs.push(v), c + k)),
            _ => None,
        }
    }
}

pub open spec fn dec_elems(m: MirCrate, e: Ty, stride: nat, a: Allocation, base: nat, fuel: nat, n: nat) -> Option<(Seq<Val>, nat)>
    decreases fuel, 1nat, n,
{
    if n == 0 { Some((seq![], 0)) } else {
        match (dec_elems(m, e, stride, a, base, fuel, (n - 1) as nat), dec(m, e, a, (base + (n - 1) * stride) as nat, fuel)) {
            (Some((vs, c)), Some((v, k))) => Some((vs.push(v), c + k)),
            _ => None,
        }
    }
}

pub open spec fn dec_tuple(m: MirCrate, t: Ty, ts: Seq<Ty>, a: Allocation, off: nat, fuel: nat) -> Option<(Val, nat)>
    decreases fuel, 2nat, 0nat,
{
    match layout(m, t) {
        Some(l) => match offs_of(l.fields) {
            Some(o) => if o.len() == ts.len() {
                match dec_fields(m, ts, o, a, off, fuel, ts.len()) { Some((vs, c)) => Some((tup_val(vs), c)), None => None }
            } else { None },
            None => None,
        },
        None => None,
    }
}

/// Arrays element by element at the layout's stride.
pub open spec fn dec_array(m: MirCrate, t: Ty, e: Ty, c: TyConstId, a: Allocation, off: nat, fuel: nat) -> Option<(Val, nat)>
    decreases fuel, 2nat, 0nat,
{
    match (const_usize(m, c), layout(m, t)) {
        (Some(n), Some(l)) => match l.fields {
            FieldsShape::Array { stride, count } => if count == n && stride.num_bits % 8 == 0 {
                match dec_elems(m, e, stride.num_bits as nat / 8, a, off, fuel, n as nat) {
                    Some((vs, k)) => Some((Val::Arr(vs), k)),
                    None => None,
                }
            } else { None },
            _ => None,
        },
        _ => None,
    }
}

/// ADTs by the layout's variant rule; `Box`, unions and `Vec` (no layout of its own fields here
/// decodes, since they hold pointers) are outside the subset.
pub open spec fn dec_adt(m: MirCrate, t: Ty, a: Allocation, off: nat, fuel: nat) -> Option<(Val, nat)>
    decreases fuel, 2nat, 0nat,
{
    match (adt_row(m, t), layout(m, t)) {
        (Some(row), Some(l)) => if row.is_box || row.kind is Union { None } else {
            match adt_sel(row, l, a, off) {
                Some((k, o)) => if k < row.variants@.len() && o.len() == row.variants@[k as int].fields@.len() {
                    match dec_fields(m, row.variants@[k as int].fields@, o, a, off, fuel, o.len()) {
                        Some((vs, c)) => Some((Val::Adt(k, vs), c + 1)),
                        None => None,
                    }
                } else { None },
                None => None,
            }
        },
        _ => None,
    }
}

/// `&ZST`: `Shr` of the ZST's value, whatever the address.
pub open spec fn dec_zst_ref(m: MirCrate, p: Ty) -> Option<(Val, nat)> {
    match unit_like(m, p, tfuel(m), true) { Some((v, c)) => Some((Val::Shr(Box::new(v)), c + 1)), None => None }
}

/// A shared reference: `&str` is the opaque `Unit` (its contents are never read in the subset);
/// to a ZST, `Shr` of its value (rustc gives such a pointer either no provenance or provenance
/// into a zero-size `GlobalAlloc::Memory`); to an array through its provenance into a
/// `GlobalAlloc::Memory`, the pointer's bytes being the offset there.
pub open spec fn dec_ref(m: MirCrate, p: Ty, a: Allocation, off: nat, fuel: nat) -> Option<(Val, nat)>
    decreases fuel, 2nat, 0nat,
{
    if rigid(m, p) matches Some(RigidTy::Str) {
        match prov_at(a, off) { Some(id) => if alloc_mem(m, id) is Some { Some((Val::Unit, 0)) } else { None }, None => Some((Val::Unit, 0)) }
    } else {
    match (prov_at(a, off), le(a, off, 8)) {
        (Some(id), Some(addr)) => match (alloc_mem(m, id), rigid(m, p)) {
            (Some(a2), Some(r)) => if is_zst(m, p) { dec_zst_ref(m, p) } else if r is Array {
                match dec(m, p, a2, addr, fuel) { Some((v, c)) => Some((Val::Shr(Box::new(v)), c + 1)), None => None }
            } else { None },
            _ => None,
        },
        (None, Some(_)) => if no_prov(a, off, 8) && is_zst(m, p) { dec_zst_ref(m, p) } else { None },
        _ => None,
    }
    }
}

pub open spec fn decode_const(m: MirCrate, ty: Ty, a: Allocation, off: nat) -> Option<Val> {
    match dec(m, ty, a, off, dfuel(m)) { Some((v, _)) => Some(v), None => None }
}

/// Decision 7's constant charge applies to ADT-typed constants and to `&ZST`.
pub open spec fn charged(m: MirCrate, t: Ty) -> bool {
    match rigid(m, t) {
        Some(RigidTy::Adt(_, _)) => true,
        Some(RigidTy::Ref(_, p, _)) => is_zst(m, p),
        _ => false,
    }
}

/// A constant operand's value and its step charge.
pub open spec fn const_val(m: MirCrate, c: ConstOperand) -> Option<(Val, nat)> {
    let t = c.const_.ty;
    match c.const_.kind {
        ConstantKind::Allocated(a) => match dec(m, t, a, 0, dfuel(m)) {
            Some((v, k)) => Some((v, if charged(m, t) { k } else { 0 })),
            None => None,
        },
        ConstantKind::ZeroSized => match unit_like(m, t, tfuel(m), true) { Some(_) => Some((ul_val(m, t), 0)), None => None },
        _ => None,
    }
}

// ------------------------------------------------------------------ frames and places

pub open spec fn root_val(fr: Frame, r: Root) -> Option<Val> {
    match r {
        Root::Local(n) => if n < fr.locals.len() { Some(fr.locals[n as int]) } else { None },
        Root::Slot(n) => if n < fr.slots.len() { Some(fr.slots[n as int]) } else { None },
    }
}

pub open spec fn set_root(fr: Frame, r: Root, v: Val) -> Frame {
    match r {
        Root::Local(n) => Frame { locals: fr.locals.update(n as int, v), slots: fr.slots },
        Root::Slot(n) => Frame { locals: fr.locals, slots: fr.slots.update(n as int, v) },
    }
}

pub open spec fn load(fr: Frame, l: Loc) -> Option<Val> {
    match root_val(fr, l.root) { Some(v) => Some(read_at(v, l.path)), None => None }
}

pub open spec fn store(fr: Frame, l: Loc, w: Val) -> Option<Frame> {
    match root_val(fr, l.root) { Some(v) => Some(set_root(fr, l.root, write_at(v, l.path, w))), None => None }
}

/// An evaluated place: a location in the frame, or a read-only snapshot reached through a `Shr`.
pub enum PRes { At(Loc), Snap(Val) }

pub open spec fn pres_val(fr: Frame, p: PRes) -> Option<Val> {
    match p { PRes::At(l) => load(fr, l), PRes::Snap(v) => Some(v) }
}

pub open spec fn extend(p: PRes, e: PE) -> PRes {
    match p { PRes::At(l) => PRes::At(Loc { root: l.root, path: l.path.push(e) }), PRes::Snap(v) => PRes::Snap(get(v, e)) }
}

/// One projection. `Deref` follows a `&mut` location only from a location: a `&mut` met inside a
/// `&` snapshot is not followed (rustc's MIR does not do it in the subset: `ty_free` forbids `&mut`
/// under `&`), so the run gives `None`. `Index` reads its local, is bounds-checked (out of bounds is UB: MiniRust
/// expressions.md `Index`) and emits `Idx(i)`; `ConstantIndex` checks `min_length` and the bound.
pub open spec fn proj_step(fr: Frame, p: PRes, e: ProjectionElem) -> Option<(PRes, Seq<Event>)> {
    match pres_val(fr, p) {
        None => None,
        Some(cur) => match e {
            ProjectionElem::Deref => match cur {
                Val::Mut(l) => if p is At { Some((PRes::At(l), seq![])) } else { None },
                Val::Shr(b) => Some((PRes::Snap(*b), seq![])),
                _ => None,
            },
            ProjectionElem::Field(i, _) => Some((extend(p, PE::Field(i as nat)), seq![])),
            ProjectionElem::Index(x) => match (root_val(fr, Root::Local(x as nat)), cur) {
                (Some(Val::Int(i)), Val::Arr(vs)) =>
                    if (i as nat) < vs.len() { Some((extend(p, PE::Index(i as nat)), seq![Event::Idx(i)])) } else { None },
                _ => None,
            },
            ProjectionElem::ConstantIndex { offset, min_length, from_end } => match cur {
                Val::Arr(vs) => if vs.len() >= min_length && (if from_end { 1 <= offset <= vs.len() } else { offset < vs.len() }) {
                    Some((extend(p, PE::Index(if from_end { (vs.len() - offset) as nat } else { offset as nat })), seq![]))
                } else { None },
                _ => None,
            },
            ProjectionElem::Downcast(k) => Some((extend(p, PE::Variant(k as nat)), seq![])),
            _ => None,
        },
    }
}

pub open spec fn places(fr: Frame, base: PRes, ps: Seq<ProjectionElem>, n: nat) -> Option<(PRes, Seq<Event>)>
    decreases n,
{
    if n == 0 { Some((base, seq![])) } else if n > ps.len() { None } else {
        match places(fr, base, ps, (n - 1) as nat) {
            Some((p, e)) => match proj_step(fr, p, ps[n - 1]) { Some((q, e2)) => Some((q, e + e2)), None => None },
            None => None,
        }
    }
}

/// A place's projections left to right, with their events in that order.
pub open spec fn eval_place(fr: Frame, p: Place) -> Option<(PRes, Seq<Event>)> {
    places(fr, PRes::At(Loc { root: Root::Local(p.local as nat), path: seq![] }), p.projection@, p.projection@.len())
}

pub open spec fn read_place(fr: Frame, p: Place) -> Option<(Val, Seq<Event>)> {
    match eval_place(fr, p) {
        Some((q, e)) => match pres_val(fr, q) { Some(v) => Some((v, e)), None => None },
        None => None,
    }
}

// ------------------------------------------------------------------ operands and rvalues

/// An operand's value, events and step charge. `Copy` and `Move` both read the place.
pub open spec fn eval_op(m: MirCrate, fr: Frame, op: Operand) -> Option<(Val, Seq<Event>, nat)> {
    match op {
        Operand::Copy(p) => match read_place(fr, p) { Some((v, e)) => Some((v, e, 0)), None => None },
        Operand::Move(p) => match read_place(fr, p) { Some((v, e)) => Some((v, e, 0)), None => None },
        Operand::Constant(c) => match const_val(m, c) { Some((v, k)) => Some((v, seq![], k)), None => None },
        _ => None,
    }
}

/// The first `n` operands, left to right.
pub open spec fn eval_ops(m: MirCrate, fr: Frame, ops: Seq<Operand>, n: nat) -> Option<(Seq<Val>, Seq<Event>, nat)>
    decreases n,
{
    if n == 0 { Some((seq![], seq![], 0)) } else if n > ops.len() { None } else {
        match (eval_ops(m, fr, ops, (n - 1) as nat), eval_op(m, fr, ops[n - 1])) {
            (Some((vs, e, k)), Some((v, e2, k2))) => Some((vs.push(v), e + e2, k + k2)),
            _ => None,
        }
    }
}

pub open spec fn core_bin(op: BinOp) -> Option<COp> {
    match op {
        BinOp::Add | BinOp::AddUnchecked => Some(COp::Add),
        BinOp::Sub | BinOp::SubUnchecked => Some(COp::Sub),
        BinOp::Mul | BinOp::MulUnchecked => Some(COp::Mul),
        BinOp::Div => Some(COp::Div),
        BinOp::Rem => Some(COp::Rem),
        BinOp::BitXor => Some(COp::BitXor),
        BinOp::BitAnd => Some(COp::BitAnd),
        BinOp::BitOr => Some(COp::BitOr),
        BinOp::Shl | BinOp::ShlUnchecked => Some(COp::Shl),
        BinOp::Shr | BinOp::ShrUnchecked => Some(COp::Shr),
        BinOp::Eq => Some(COp::Eq),
        BinOp::Lt => Some(COp::Lt),
        BinOp::Le => Some(COp::Le),
        BinOp::Ne => Some(COp::Ne),
        BinOp::Ge => Some(COp::Ge),
        BinOp::Gt => Some(COp::Gt),
        _ => None,
    }
}

pub open spec fn in_range(it: CTy, x: int) -> bool {
    if signed(it) { -pow2((bits(it) - 1) as nat) <= x < pow2((bits(it) - 1) as nat) } else { 0 <= x < pow2(bits(it)) }
}

/// MIR's UB conditions (MiniRust operators.md): unchecked ops must not overflow or over-shift;
/// `/` and `%` need a nonzero divisor and not `MIN / -1`. Plain `+ - *` wrap; `<< >>` mask.
pub open spec fn bin_ok(op: BinOp, it: CTy, rt: CTy, a: u128, c: u128) -> bool {
    let (x, y) = (ival(it, a), ival(it, c));
    match op {
        BinOp::AddUnchecked => in_range(it, x + y),
        BinOp::SubUnchecked => in_range(it, x - y),
        BinOp::MulUnchecked => in_range(it, x * y),
        BinOp::Div | BinOp::Rem => y != 0 && !(signed(it) && x == -pow2((bits(it) - 1) as nat) && y == -1),
        BinOp::ShlUnchecked | BinOp::ShrUnchecked => 0 <= ival(rt, c) < bits(it),
        _ => true,
    }
}

pub open spec fn bin_ev(op: BinOp, a: u128, c: u128) -> Seq<Event> {
    match op {
        BinOp::Div | BinOp::Rem => seq![Event::DivOps(a, c)],
        BinOp::Shl | BinOp::ShlUnchecked | BinOp::Shr | BinOp::ShrUnchecked => seq![Event::Shamt(c)],
        _ => seq![],
    }
}

/// `BinaryOp` on ints and `bool`s at the left operand's type: operands' events, then its own.
pub open spec fn rv_bin(m: MirCrate, b: Body, fr: Frame, op: BinOp, x: Operand, y: Operand) -> Option<(Val, Seq<Event>, nat)> {
    match (eval_op(m, fr, x), eval_op(m, fr, y), op_ty(m, b, x), op_ty(m, b, y), core_bin(op)) {
        (Some((Val::Int(a), ex, kx)), Some((Val::Int(c), ey, ky)), Some(tx), Some(ty), Some(cop)) =>
            match (int_ty(m, tx), int_ty(m, ty)) {
                (Some(it), Some(rt)) => if bin_ok(op, it, rt, a, c) {
                    Some((Val::Int(binop(cop, it, a, c)), ex + ey + bin_ev(op, a, c), kx + ky))
                } else { None },
                _ => None,
            },
        _ => None,
    }
}

/// `CheckedBinaryOp` (`+ - *`): the wrapped result and whether the exact result differs.
pub open spec fn rv_checked(m: MirCrate, b: Body, fr: Frame, op: BinOp, x: Operand, y: Operand) -> Option<(Val, Seq<Event>, nat)> {
    match (eval_op(m, fr, x), eval_op(m, fr, y), op_ty(m, b, x)) {
        (Some((Val::Int(a), ex, kx)), Some((Val::Int(c), ey, ky)), Some(tx)) => match int_ty(m, tx) {
            Some(it) => {
                let (u, w) = (ival(it, a), ival(it, c));
                let r: Option<(COp, int)> = match op {
                    BinOp::Add => Some((COp::Add, u + w)),
                    BinOp::Sub => Some((COp::Sub, u - w)),
                    BinOp::Mul => Some((COp::Mul, u * w)),
                    _ => None,
                };
                match r {
                    Some((cop, exact)) => Some((
                        Val::Tup(seq![Val::Int(binop(cop, it, a, c)), Val::Int(if in_range(it, exact) { 0 } else { 1 })]),
                        ex + ey, kx + ky)),
                    None => None,
                }
            },
            None => None,
        },
        _ => None,
    }
}

/// `UnaryOp`: `!` and wrapping `-` on ints, and `PtrMetadata` of a slice reference (its length).
pub open spec fn rv_un(m: MirCrate, b: Body, fr: Frame, op: UnOp, x: Operand) -> Option<(Val, Seq<Event>, nat)> {
    match (eval_op(m, fr, x), op_ty(m, b, x)) {
        (Some((v, e, k)), Some(tx)) => match op {
            UnOp::Not => match (v, int_ty(m, tx)) { (Val::Int(a), Some(it)) => Some((Val::Int(unop(CUn::Not, it, a)), e, k)), _ => None },
            UnOp::Neg => match (v, int_ty(m, tx)) {
                (Val::Int(a), Some(it)) => if signed(it) { Some((Val::Int(unop(CUn::Neg, it, a)), e, k)) } else { None },
                _ => None,
            },
            UnOp::PtrMetadata => match rigid(m, tx) {
                Some(RigidTy::Ref(_, p, _)) => if rigid(m, p) matches Some(RigidTy::Slice(_)) {
                    let pointee = match v { Val::Shr(bx) => Some(*bx), Val::Mut(l) => load(fr, l), _ => None };
                    match pointee { Some(Val::Arr(vs)) => Some((Val::Int(vs.len() as u128), e, k)), _ => None }
                } else { None },
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

/// `Cast`: int-to-int `as`; `Unsize` of a reference to an array into one to a slice keeps the
/// value (the `Arr` carries its length, MiniRust's slice metadata); fn-pointer reifications keep
/// the opaque `Unit`; `Subtype` is the identity. Pointer and transmute casts are outside.
pub open spec fn rv_cast(m: MirCrate, b: Body, fr: Frame, ck: CastKind, x: Operand, to: Ty) -> Option<(Val, Seq<Event>, nat)> {
    match (eval_op(m, fr, x), op_ty(m, b, x)) {
        (Some((v, e, k)), Some(tx)) => match ck {
            CastKind::IntToInt => match (v, int_ty(m, tx), int_ty(m, to)) {
                (Val::Int(a), Some(f), Some(t)) => Some((Val::Int(cast(f, t, a)), e, k)),
                _ => None,
            },
            CastKind::PointerCoercion(PointerCoercion::Unsize) => match (rigid(m, tx), rigid(m, to)) {
                (Some(RigidTy::Ref(_, p, _)), Some(RigidTy::Ref(_, q, _))) =>
                    if rigid(m, p) is Some && rigid(m, p)->Some_0 is Array && rigid(m, q) is Some && rigid(m, q)->Some_0 is Slice {
                        Some((v, e, k))
                    } else { None },
                _ => None,
            },
            CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_)) => if v is Unit { Some((Val::Unit, e, k)) } else { None },
            CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer(_)) => if v is Unit { Some((Val::Unit, e, k)) } else { None },
            CastKind::Subtype => Some((v, e, k)),
            _ => None,
        },
        _ => None,
    }
}

pub open spec fn rv_agg(m: MirCrate, fr: Frame, ak: AggregateKind, ops: Seq<Operand>) -> Option<(Val, Seq<Event>, nat)> {
    match eval_ops(m, fr, ops, ops.len()) {
        Some((vs, e, k)) => match ak {
            AggregateKind::Array(_) => Some((Val::Arr(vs), e, k)),
            AggregateKind::Tuple => Some((Val::Tup(vs), e, k)),
            AggregateKind::Adt(_, var, _, _, active) => if active is None { Some((Val::Adt(var as nat, vs), e, k)) } else { None },
            _ => None,
        },
        None => None,
    }
}

/// `Discriminant`: the discriminant (a bit pattern) of the stored variant (a one-variant enum's
/// canonical `Unit` is its variant); 0 for a struct.
pub open spec fn rv_discr(m: MirCrate, b: Body, fr: Frame, p: Place) -> Option<(Val, Seq<Event>, nat)> {
    match (read_place(fr, p), place_ty(m, b, p)) {
        (Some((v, e)), Some(t)) => match adt_row(m, t) {
            Some(a) => match a.kind {
                AdtKind::Enum => match v {
                    Val::Adt(k, _) => if k < a.variants@.len() && a.variants@[k as int].discr is Some {
                        Some((Val::Int(a.variants@[k as int].discr->Some_0), e, 0))
                    } else { None },
                    // the canonical `Unit` of a unit-like one-variant enum
                    Val::Unit => if a.variants@.len() == 1 && a.variants@[0].discr is Some && unit_like(m, t, tfuel(m), true) is Some {
                        Some((Val::Int(a.variants@[0].discr->Some_0), e, 0))
                    } else { None },
                    _ => None,
                },
                AdtKind::Struct => Some((Val::Int(0), e, 0)),
                _ => None,
            },
            None => None,
        },
        _ => None,
    }
}

pub open spec fn rv_ref(fr: Frame, bk: BorrowKind, p: Place) -> Option<(Val, Seq<Event>, nat)> {
    match bk {
        BorrowKind::Shared => match read_place(fr, p) { Some((v, e)) => Some((Val::Shr(Box::new(v)), e, 0)), None => None },
        BorrowKind::Mut { .. } => match eval_place(fr, p) { Some((PRes::At(l), e)) => Some((Val::Mut(l), e, 0)), _ => None },
        _ => None,
    }
}

/// An rvalue's value, its events (operands left to right, then its own) and constant charges.
pub open spec fn eval_rv(m: MirCrate, b: Body, fr: Frame, rv: Rvalue) -> Option<(Val, Seq<Event>, nat)> {
    match rv {
        Rvalue::Use(x, _) => eval_op(m, fr, x),
        Rvalue::BinaryOp(op, x, y) => rv_bin(m, b, fr, op, x, y),
        Rvalue::CheckedBinaryOp(op, x, y) => rv_checked(m, b, fr, op, x, y),
        Rvalue::UnaryOp(op, x) => rv_un(m, b, fr, op, x),
        Rvalue::Cast(ck, x, to) => rv_cast(m, b, fr, ck, x, to),
        Rvalue::Aggregate(ak, ops) => rv_agg(m, fr, ak, ops@),
        Rvalue::Repeat(x, c) => match (eval_op(m, fr, x), const_usize(m, c.id)) {
            (Some((v, e, k)), Some(n)) => Some((Val::Arr(Seq::new(n as nat, |_i: int| v)), e, k)),
            _ => None,
        },
        Rvalue::Ref(_, bk, p) => rv_ref(fr, bk, p),
        Rvalue::Len(p) => match read_place(fr, p) { Some((Val::Arr(vs), e)) => Some((Val::Int(vs.len() as u128), e, 0)), _ => None },
        Rvalue::Discriminant(p) => rv_discr(m, b, fr, p),
        Rvalue::CopyForDeref(p) => match read_place(fr, p) { Some((v, e)) => Some((v, e, 0)), None => None },
        _ => None,
    }
}

// ------------------------------------------------------------------ statements (decisions 6, 7)

/// A statement's new frame, events and steps. `Assign`: the rvalue, then the destination's
/// projections (decision 6), cost 1 plus constant charges. Statements that generate no code cost
/// 0 and evaluate nothing (MiniRust evaluates `PlaceMention`'s place; here it emits nothing).
#[verifier::opaque]
pub open spec fn exec_stmt(m: MirCrate, b: Body, fr: Frame, s: Statement) -> Option<(Frame, Seq<Event>, nat)> {
    match s.kind {
        StatementKind::Assign(p, rv) => match (eval_rv(m, b, fr, rv), eval_place(fr, p)) {
            (Some((v, e1, k)), Some((PRes::At(l), e2))) => match store(fr, l, v) {
                Some(fr2) => Some((fr2, e1 + e2, 1 + k)),
                None => None,
            },
            _ => None,
        },
        StatementKind::SetDiscriminant { place, variant_index } => match eval_place(fr, place) {
            Some((PRes::At(l), e)) => match load(fr, l) {
                Some(Val::Adt(_, vs)) => match store(fr, l, Val::Adt(variant_index as nat, vs)) {
                    Some(fr2) => Some((fr2, e, 1)),
                    None => None,
                },
                _ => None,
            },
            _ => None,
        },
        StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop | StatementKind::FakeRead(_, _)
        | StatementKind::PlaceMention(_) | StatementKind::AscribeUserType { .. } | StatementKind::Coverage(_)
        | StatementKind::ConstEvalCounter => Some((fr, seq![], 0)),
        _ => None,
    }
}

pub open spec fn exec_stmts(m: MirCrate, b: Body, fr: Frame, ss: Seq<Statement>, n: nat) -> Option<(Frame, Seq<Event>, nat)>
    decreases n,
{
    if n == 0 { Some((fr, seq![], 0)) } else if n > ss.len() { None } else {
        match exec_stmts(m, b, fr, ss, (n - 1) as nat) {
            Some((f1, e1, s1)) => match exec_stmt(m, b, f1, ss[n - 1]) {
                Some((f2, e2, s2)) => Some((f2, e1 + e2, s1 + s2)),
                None => None,
            },
            None => None,
        }
    }
}

// ------------------------------------------------------------------ the std model (decision 8)

pub enum StdFn {
    VecNew, VecWithCapacity, VecPush, VecExtendFromSlice, VecAsSlice, ArrayAsSlice, VecLen, VecSet, VecIndex,
    SliceSubrange, SliceToVec, Wrapping(COp, CTy), GhostNew,
}

pub open spec fn garg0(m: MirCrate, g: GenericArgs) -> Option<RigidTy> {
    if g.0@.len() > 0 { match g.0@[0] { GenericArgKind::Type(t) => rigid(m, t), _ => None } } else { None }
}

pub open spec fn is_u8(r: Option<RigidTy>) -> bool { r matches Some(RigidTy::Uint(UintTy::U8)) }

pub open spec fn is_u64_pair(m: MirCrate, r: Option<RigidTy>) -> bool {
    match r {
        Some(RigidTy::Tuple(ts)) => ts@.len() == 2 && (rigid(m, ts@[0]) matches Some(RigidTy::Uint(UintTy::U64)))
            && (rigid(m, ts@[1]) matches Some(RigidTy::Uint(UintTy::U64))),
        _ => false,
    }
}

/// The std-model rows (spec §MIR semantics "Std-model rows"), by `ct_key` and the first generic
/// argument where the row admits element types. Effects mirror vstd 0.0.0-2026-10-04-0306:
/// - `Vec::new` std_specs/vec.rs:100, `with_capacity` vec.rs:115, `push` vec.rs:141,
///   `extend_from_slice` vec.rs:163, `as_slice` vec.rs:236, `len` vec.rs:93, `Index::index`
///   vec.rs:184 (and `vec_index`, vec.rs:53, `requires i < len`);
/// - `<[T; N]>::as_slice` array.rs:123;
/// - `VecAdditionalExecFns::set` pervasive.rs:390 (`requires i < len`);
/// - `slice_subrange` slice.rs:108 (`requires i <= j <= len`), `slice_to_vec` slice.rs:100;
/// - `wrapping_add`/`wrapping_sub` std_specs/num.rs:98/112;
/// - `Ghost::assume_new_fallback` verus_builtin lib.rs:517 (a ghost value: unit-like at run time).
pub open spec fn std_model(m: MirCrate, key: Seq<u8>, gargs: GenericArgs) -> Option<StdFn> {
    let e = garg0(m, gargs);
    let u8_or_pair = is_u8(e) || is_u64_pair(m, e);
    if key == b"std::vec::Vec::new"@ && u8_or_pair { Some(StdFn::VecNew) }
    else if key == b"std::vec::Vec::with_capacity"@ && is_u8(e) { Some(StdFn::VecWithCapacity) }
    else if key == b"std::vec::Vec::push"@ && u8_or_pair { Some(StdFn::VecPush) }
    else if key == b"std::vec::Vec::extend_from_slice"@ && is_u8(e) { Some(StdFn::VecExtendFromSlice) }
    else if key == b"std::vec::Vec::as_slice"@ && is_u8(e) { Some(StdFn::VecAsSlice) }
    else if key == b"std::array::<impl [u8; 16]>::as_slice"@ || key == b"std::array::<impl [u8; 32]>::as_slice"@
        || key == b"std::array::<impl [u8; 64]>::as_slice"@ || key == b"std::array::<impl [u8; 128]>::as_slice"@ { Some(StdFn::ArrayAsSlice) }
    else if key == b"std::vec::Vec::len"@ && u8_or_pair { Some(StdFn::VecLen) }
    else if key == b"<std::vec::Vec<u8> as vstd::pervasive::VecAdditionalExecFns<u8>>::set"@ { Some(StdFn::VecSet) }
    else if key == b"<std::vec::Vec<(u64, u64)> as std::ops::Index<usize>>::index"@ { Some(StdFn::VecIndex) }
    else if key == b"vstd::slice::slice_subrange"@ && is_u8(e) { Some(StdFn::SliceSubrange) }
    else if key == b"vstd::slice::slice_to_vec"@ && is_u8(e) { Some(StdFn::SliceToVec) }
    else if key == b"core::num::<impl u32>::wrapping_add"@ { Some(StdFn::Wrapping(COp::Add, CTy::U32)) }
    else if key == b"core::num::<impl u64>::wrapping_sub"@ { Some(StdFn::Wrapping(COp::Sub, CTy::U64)) }
    else if key == b"vstd::prelude::Ghost::assume_new_fallback"@ { Some(StdFn::GhostNew) }
    else { None }
}

/// The elements behind a shared reference argument.
pub open spec fn shr_arr(v: Val) -> Option<Seq<Val>> {
    match v { Val::Shr(b) => match *b { Val::Arr(xs) => Some(xs), _ => None }, _ => None }
}

/// The `Vec` behind a `&mut` argument: its location and elements.
pub open spec fn mut_arr(fr: Frame, v: Val) -> Option<(Loc, Seq<Val>)> {
    match v { Val::Mut(l) => match load(fr, l) { Some(Val::Arr(xs)) => Some((l, xs)), _ => None }, _ => None }
}

pub open spec fn int_arg(v: Val) -> Option<u128> { match v { Val::Int(n) => Some(n), _ => None } }

/// A std row's result, new frame, events and extra cost. A vstd precondition that fails, or a
/// length past `usize::MAX`, is a panic: `None`.
pub open spec fn std_apply(m: MirCrate, f: StdFn, dty: Option<Ty>, vs: Seq<Val>, fr: Frame) -> Option<(Val, Frame, Seq<Event>, nat)> {
    match f {
        StdFn::VecNew => if vs.len() == 0 { Some((Val::Arr(seq![]), fr, seq![], 0)) } else { None },
        StdFn::VecWithCapacity => if vs.len() == 1 && vs[0] is Int { Some((Val::Arr(seq![]), fr, seq![Event::Alloc(vs[0]->Int_0)], 0)) } else { None },
        StdFn::VecPush => if vs.len() == 2 {
            match mut_arr(fr, vs[0]) {
                Some((l, xs)) => if xs.len() + 1 <= USZ {
                    match store(fr, l, Val::Arr(xs.push(vs[1]))) { Some(fr2) => Some((unit_val(), fr2, seq![], 0)), None => None }
                } else { None },
                None => None,
            }
        } else { None },
        StdFn::VecExtendFromSlice => if vs.len() == 2 {
            match (mut_arr(fr, vs[0]), shr_arr(vs[1])) {
                (Some((l, xs)), Some(ys)) => if xs.len() + ys.len() <= USZ {
                    match store(fr, l, Val::Arr(xs + ys)) { Some(fr2) => Some((unit_val(), fr2, seq![], ys.len())), None => None }
                } else { None },
                _ => None,
            }
        } else { None },
        StdFn::VecAsSlice | StdFn::ArrayAsSlice => if vs.len() == 1 && shr_arr(vs[0]) is Some { Some((vs[0], fr, seq![], 0)) } else { None },
        StdFn::VecLen => if vs.len() == 1 {
            match shr_arr(vs[0]) { Some(xs) => Some((Val::Int(xs.len() as u128), fr, seq![], 0)), None => None }
        } else { None },
        StdFn::VecSet => if vs.len() == 3 {
            match (mut_arr(fr, vs[0]), int_arg(vs[1])) {
                (Some((l, xs)), Some(i)) => if (i as nat) < xs.len() {
                    match store(fr, l, Val::Arr(xs.update(i as int, vs[2]))) {
                        Some(fr2) => Some((unit_val(), fr2, seq![Event::Idx(i)], 0)),
                        None => None,
                    }
                } else { None },
                _ => None,
            }
        } else { None },
        StdFn::VecIndex => if vs.len() == 2 {
            match (shr_arr(vs[0]), int_arg(vs[1])) {
                (Some(xs), Some(i)) => if (i as nat) < xs.len() {
                    Some((Val::Shr(Box::new(xs[i as int])), fr, seq![Event::Idx(i)], 0))
                } else { None },
                _ => None,
            }
        } else { None },
        StdFn::SliceSubrange => if vs.len() == 3 {
            match (shr_arr(vs[0]), int_arg(vs[1]), int_arg(vs[2])) {
                (Some(xs), Some(lo), Some(hi)) => if lo <= hi && (hi as nat) <= xs.len() {
                    Some((Val::Shr(Box::new(Val::Arr(xs.subrange(lo as int, hi as int)))), fr, seq![Event::Range(lo, hi)], 0))
                } else { None },
                _ => None,
            }
        } else { None },
        StdFn::SliceToVec => if vs.len() == 1 {
            match shr_arr(vs[0]) { Some(xs) => if xs.len() <= USZ { Some((Val::Arr(xs), fr, seq![], xs.len())) } else { None }, None => None }
        } else { None },
        StdFn::Wrapping(op, it) => if vs.len() == 2 {
            match (int_arg(vs[0]), int_arg(vs[1])) { (Some(a), Some(c)) => Some((Val::Int(binop(op, it, a, c)), fr, seq![], 0)), _ => None }
        } else { None },
        StdFn::GhostNew => match dty {
            Some(t) => if zst_dest(m, t) { Some((ul_val(m, t), fr, seq![], 0)) } else { None },
            None => None,
        },
    }
}

/// A leaf call (policy or std model): result, frame, events, extra cost; `None` if not a leaf.
pub open spec fn leaf_call(m: MirCrate, pol: CallPolicy, key: Seq<u8>, gargs: GenericArgs, dty: Option<Ty>, vs: Seq<Val>, fr: Frame)
    -> Option<(Val, Frame, Seq<Event>, nat)>
{
    if pol.declassify.contains(key) {
        if vs.len() == 1 { Some((vs[0], fr, seq![Event::Declass(vs[0])], 0)) } else { None }
    } else if pol.ghost_unit.contains(key) {
        match dty {
            Some(t) => if zst_dest(m, t) { Some((ul_val(m, t), fr, seq![], 0)) } else { None },
            None => None,
        }
    } else {
        match std_model(m, key, gargs) { Some(f) => std_apply(m, f, dty, vs, fr), None => None }
    }
}

pub open spec fn is_leaf(m: MirCrate, pol: CallPolicy, key: Seq<u8>, gargs: GenericArgs) -> bool {
    pol.declassify.contains(key) || pol.ghost_unit.contains(key) || std_model(m, key, gargs) is Some
}

// ------------------------------------------------------------------ calls (decision 3)

/// The frame a body starts in: parameter `1 + j` is `args[j]`, or `Mut(Slot(j))` when its type is
/// `&mut` (slot `j` holds the pointee). Local 0 and the other locals are `Unit` (uninitialized),
/// except that a local of unit-like type holds its one value, `ul_val` (a ZST read never fails,
/// MiniRust; rustc's `RemoveZsts` removes assignments to ZST places, so a run reads this value):
/// the canonical `Unit`, or the structural value of a type holding an array.
pub open spec fn mir_entry(m: MirCrate, i: nat, args: Seq<Val>, slots: Seq<Val>) -> Frame {
    match inst_body(m, i) {
        Some(b) => Frame { locals: Seq::new(b.locals@.len(), |k: int| entry_local(m, b, args, k)), slots },
        None => Frame { locals: seq![], slots },
    }
}

pub open spec fn entry_local(m: MirCrate, b: Body, args: Seq<Val>, k: int) -> Val {
    if 1 <= k <= b.arg_count && k - 1 < args.len() && k < b.locals@.len() {
        if is_mut_ref(m, b.locals@[k].ty) { Val::Mut(Loc { root: Root::Slot((k - 1) as nat), path: seq![] }) } else { args[k - 1] }
    } else if 0 <= k < b.locals@.len() { ul_val(m, b.locals@[k].ty) } else { Val::Unit }
}

/// Argument `j` can be passed: a `&mut` parameter gets a location whose (mut-free) pointee is
/// copied in; any other argument must hold no location.
pub open spec fn arg_ok(m: MirCrate, cb: Body, fr: Frame, vs: Seq<Val>, j: int) -> bool {
    if is_mut_ref(m, cb.locals@[j + 1].ty) {
        vs[j] is Mut && (load(fr, vs[j]->Mut_0) matches Some(x) && mut_free(x))
    } else { mut_free(vs[j]) }
}

pub open spec fn args_ok(m: MirCrate, cb: Body, fr: Frame, vs: Seq<Val>) -> bool {
    vs.len() == cb.arg_count && cb.arg_count < cb.locals@.len() && forall|j: int| 0 <= j < vs.len() ==> arg_ok(m, cb, fr, vs, j)
}

pub open spec fn call_slots(m: MirCrate, cb: Body, fr: Frame, vs: Seq<Val>) -> Seq<Val> {
    Seq::new(vs.len(), |j: int| if is_mut_ref(m, cb.locals@[j + 1].ty) { load(fr, vs[j]->Mut_0)->Some_0 } else { Val::Unit })
}

/// Writes the callee's final slots back to the caller's locations, parameter order.
pub open spec fn write_back(m: MirCrate, cb: Body, fr: Frame, vs: Seq<Val>, cs: Seq<Val>, n: nat) -> Option<Frame>
    decreases n,
{
    if n == 0 { Some(fr) } else if n > vs.len() { None } else {
        match write_back(m, cb, fr, vs, cs, (n - 1) as nat) {
            Some(f) => if is_mut_ref(m, cb.locals@[n as int].ty) {
                if n - 1 < cs.len() && mut_free(cs[n - 1]) && vs[n - 1] is Mut { store(f, vs[n - 1]->Mut_0, cs[n - 1]) } else { None }
            } else { Some(f) },
            None => None,
        }
    }
}

/// The callee's return value (mut-free) and the caller's frame after write-back.
pub open spec fn return_to(m: MirCrate, cb: Body, fr: Frame, vs: Seq<Val>, cf: Frame) -> Option<(Val, Frame)> {
    if cf.locals.len() > 0 && mut_free(cf.locals[0]) {
        match write_back(m, cb, fr, vs, cf.slots, vs.len()) { Some(f) => Some((cf.locals[0], f)), None => None }
    } else { None }
}

/// The callee of a `Call` whose function operand is a constant of `FnDef` type: its `insts`
/// index (through `calls`) and generic args.
pub open spec fn callee_of(m: MirCrate, func: Operand) -> Option<(nat, GenericArgs)> {
    match func {
        Operand::Constant(c) => match find(m.calls@, |r: Call| r.fn_ty == c.const_.ty) {
            Some(k) => match m.calls@[k as int].resolved {
                Some(id) => match inst_idx(m, id) { Some(j) => Some((j, m.calls@[k as int].args)), None => None },
                None => None,
            },
            None => None,
        },
        _ => None,
    }
}

/// A run's outcome. `Panic` is a failed `Assert`, `Unreachable`/`Abort`, UB guarded by rustc's
/// checks (an index out of bounds, `/ 0`, unchecked overflow), a std precondition, or a value of
/// the wrong shape for its construct (not proved unreachable: sem is untyped; that rustc-typed MIR
/// in the subset never meets one is trusted: TRUSTED.md, the "CT semantics" row).
/// `Unsup` is a construct outside the subset, decided statically (`block_ok`, `inst_body`).
pub enum Out { Done(Frame, Seq<Event>, nat), Panic, Unsup, Fuel }

/// A block's terminator outcome: jump to a block with events and steps, or stop with an outcome.
pub enum Step { Jump(nat, Frame, Seq<Event>, nat), Stop(Out) }

/// `SwitchInt`: the operand's bit pattern against the branch values, emitting `Cond(d)`.
pub open spec fn switch_step(m: MirCrate, fr: Frame, x: Operand, tg: SwitchTargets) -> Step {
    match eval_op(m, fr, x) {
        Some((Val::Int(d), e, k)) => {
            let t = match find(tg.branches@, |br: (u128, BasicBlockIdx)| br.0 == d) {
                Some(j) => tg.branches@[j as int].1 as nat,
                None => tg.otherwise as nat,
            };
            Step::Jump(t, fr, e + seq![Event::Cond(d)], 1 + k)
        },
        _ => Step::Stop(Out::Panic),
    }
}

/// `Assert`: emits `Cond(c)`; a condition other than `expected` panics.
pub open spec fn assert_step(m: MirCrate, fr: Frame, x: Operand, expected: bool, target: BasicBlockIdx) -> Step {
    match eval_op(m, fr, x) {
        Some((Val::Int(c), e, k)) => if (c == 0 || c == 1) && (c == 1) == expected {
            Step::Jump(target as nat, fr, e + seq![Event::Cond(c)], 1 + k)
        } else { Step::Stop(Out::Panic) },
        _ => Step::Stop(Out::Panic),
    }
}

// ------------------------------------------------------------------ runs (decisions 1, 2, 4)

/// A run of `insts[i]` from `fr`: `Some` exactly when it returns.
pub open spec fn mir_run_fn(m: MirCrate, pol: CallPolicy, i: nat, fr: Frame, fuel: nat) -> Res {
    match mir_run(m, pol, i, fr, fuel) { Out::Done(f, e, s) => Some((f, e, s)), _ => None }
}

/// Fuel: each block entered and each call to a body takes 1.
pub open spec fn mir_run(m: MirCrate, pol: CallPolicy, i: nat, fr: Frame, fuel: nat) -> Out
    decreases fuel, 4nat,
{
    match inst_body(m, i) { Some(b) => run_block(m, pol, b, 0, fr, fuel), None => Out::Unsup }
}

pub open spec fn run_block(m: MirCrate, pol: CallPolicy, b: Body, bb: nat, fr: Frame, fuel: nat) -> Out
    decreases fuel, 3nat,
{
    if fuel == 0 { Out::Fuel } else if bb >= b.blocks@.len() || !block_ok(m, pol, b, b.blocks@[bb as int]) { Out::Unsup } else {
        let blk = b.blocks@[bb as int];
        match exec_stmts(m, b, fr, blk.statements@, blk.statements@.len()) {
            Some((f1, e1, s1)) => match step_term(m, pol, b, blk.terminator.kind, f1, fuel) {
                Step::Stop(Out::Done(f2, e2, s2)) => Out::Done(f2, e1 + e2, s1 + s2),
                Step::Stop(o) => o,
                Step::Jump(t, f2, e2, s2) => match run_block(m, pol, b, t, f2, (fuel - 1) as nat) {
                    Out::Done(f3, e3, s3) => Out::Done(f3, e1 + e2 + e3, s1 + s2 + s3),
                    o => o,
                },
            },
            None => Out::Panic,
        }
    }
}

/// Terminators, each costing 1. Only normal successors are followed (`Resume`, inline asm and
/// unknown terminators are outside the subset; `block_ok` stops them first). A call with no
/// return target diverges (a panic), so the run never completes: `Panic`.
pub open spec fn step_term(m: MirCrate, pol: CallPolicy, b: Body, t: TerminatorKind, fr: Frame, fuel: nat) -> Step
    decreases fuel, 2nat,
{
    match t {
        TerminatorKind::Goto { target } => Step::Jump(target as nat, fr, seq![], 1),
        TerminatorKind::SwitchInt { discr, targets } => switch_step(m, fr, discr, targets),
        TerminatorKind::Assert { cond, expected, msg: _, target, unwind: _ } => assert_step(m, fr, cond, expected, target),
        TerminatorKind::Return => Step::Stop(Out::Done(fr, seq![], 1)),
        TerminatorKind::Unreachable | TerminatorKind::Abort => Step::Stop(Out::Panic),
        TerminatorKind::Drop { place, target, unwind: _ } => drop_step(m, pol, b, place, target as nat, fr, fuel),
        TerminatorKind::Call { func, args, destination, target, unwind: _ } => match target {
            Some(tb) => call_step(m, pol, b, func, args@, destination, tb as nat, fr, fuel),
            None => Step::Stop(Out::Panic),
        },
        _ => Step::Stop(Out::Unsup),
    }
}

/// A body call: enter with the `&mut` slots, run on 1 less fuel, return and write back.
pub open spec fn body_call(m: MirCrate, pol: CallPolicy, j: nat, cb: Body, vs: Seq<Val>, fr: Frame, fuel: nat)
    -> Result<(Val, Frame, Seq<Event>, nat), Out>
    decreases fuel, 0nat,
{
    if fuel == 0 { Err(Out::Fuel) } else if !args_ok(m, cb, fr, vs) { Err(Out::Panic) } else {
        match mir_run(m, pol, j, mir_entry(m, j, vs, call_slots(m, cb, fr, vs)), (fuel - 1) as nat) {
            Out::Done(cf, e, s) => match return_to(m, cb, fr, vs, cf) {
                Some((r, f2)) => Ok((r, f2, e, s)),
                None => Err(Out::Panic),
            },
            o => Err(o),
        }
    }
}

/// `Call` (decision 6, amended): the arguments' events left to right, then the callee's (a body's
/// trace, or the policy or std row's events), then the destination place's events. The place is
/// evaluated before the call (MiniRust terminators.md), its events listed last. A leaf costs 1
/// plus constant charges plus its table cost; a body call 1 plus charges plus the callee's steps.
/// Policy calls first, then the std model, then an `Item`/`Shim` instance with a body.
pub open spec fn call_step(m: MirCrate, pol: CallPolicy, b: Body, func: Operand, args: Seq<Operand>, dest: Place, tb: nat, fr: Frame, fuel: nat)
    -> Step
    decreases fuel, 1nat,
{
    match callee_of(m, func) {
        None => Step::Stop(Out::Unsup),
        Some((j, gargs)) => if j >= m.insts@.len() { Step::Stop(Out::Unsup) } else { match (eval_ops(m, fr, args, args.len()), eval_place(fr, dest)) {
            (Some((vs, e1, k1)), Some((PRes::At(l), e2))) => {
                let key = m.insts@[j as int].key@;
                let r: Result<(Val, Frame, Seq<Event>, nat), Out> = if is_leaf(m, pol, key, gargs) {
                    match leaf_call(m, pol, key, gargs, place_ty(m, b, dest), vs, fr) {
                        Some(x) => Ok(x),
                        None => Err(Out::Panic),
                    }
                } else {
                    match inst_body(m, j) { Some(cb) => body_call(m, pol, j, cb, vs, fr, fuel), None => Err(Out::Unsup) }
                };
                match r {
                    Ok((v, f2, e3, x)) => match store(f2, l, v) {
                        Some(f3) => Step::Jump(tb, f3, e1 + e3 + e2, 1 + k1 + x),
                        None => Step::Stop(Out::Panic),
                    },
                    Err(o) => Step::Stop(o),
                }
            },
            _ => Step::Stop(Out::Panic),
        } },
    }
}

/// `Drop` (decision 4): `drop_in_place::<T>` through the `drops` row for the place's type. An empty
/// shim and the `Vec<int>` leaf are no-ops costing 1; otherwise the glue body runs on `&mut place`
/// (slot 0, written back), costing 2 plus its steps. Events: the place's, then the glue's.
pub open spec fn drop_step(m: MirCrate, pol: CallPolicy, b: Body, place: Place, tb: nat, fr: Frame, fuel: nat) -> Step
    decreases fuel, 1nat,
{
    match (place_ty(m, b, place), eval_place(fr, place)) {
        (Some(t), Some((PRes::At(l), e))) => match drop_row(m, t) {
            Some(d) => if d.empty || vec_int(m, t) { Step::Jump(tb, fr, e, 1) } else {
                match glue_of(m, d.glue) {
                    Some((j, gb)) => match body_call(m, pol, j, gb, seq![Val::Mut(l)], fr, fuel) {
                        Ok((_, f2, e2, s2)) => Step::Jump(tb, f2, e + e2, 2 + s2),
                        Err(o) => Step::Stop(o),
                    },
                    None => Step::Stop(Out::Unsup),
                }
            },
            None => Step::Stop(Out::Unsup),
        },
        (None, _) => Step::Stop(Out::Unsup),
        _ => Step::Stop(Out::Panic),
    }
}

pub open spec fn drop_row(m: MirCrate, t: Ty) -> Option<DropRow> {
    match find(m.drops@, |d: DropRow| d.ty == t) { Some(k) => Some(m.drops@[k as int]), None => None }
}

/// A drop glue instance: its `insts` index and body.
pub open spec fn glue_of(m: MirCrate, g: InstanceDef) -> Option<(nat, Body)> {
    match inst_idx(m, g) { Some(j) => match inst_body(m, j) { Some(gb) => Some((j, gb)), None => None }, None => None }
}

// ------------------------------------------------------------------ the subset (static)
//
// Each predicate mirrors the static `None` arms of the evaluation functions above: a construct
// passes exactly when its evaluation can fail only on values (a panic, or a mis-shaped value).

/// No `Box`, union, `UnsafeCell`, raw pointer, float, `char`, trait object or unresolved type
/// anywhere in `t`; `&mut` only where `mut_ok` (not inside any reference's pointee).
pub open spec fn ty_free(m: MirCrate, t: Ty, fuel: nat, mut_ok: bool) -> bool
    decreases fuel,
{
    if fuel == 0 { false } else {
        let f = (fuel - 1) as nat;
        match rigid(m, t) {
            Some(r) => match r {
                RigidTy::Bool | RigidTy::Int(_) | RigidTy::Uint(_) => int_of(r) is Some,
                RigidTy::Str | RigidTy::Never | RigidTy::FnDef(_, _) | RigidTy::FnPtr(_) | RigidTy::Closure(_, _) => true,
                RigidTy::Pat(base, _) => ty_free(m, base, f, mut_ok),
                RigidTy::Tuple(ts) => forall|k: int| 0 <= k < ts@.len() ==> ty_free(m, #[trigger] ts@[k], f, mut_ok),
                RigidTy::Array(e, _) => ty_free(m, e, f, mut_ok),
                RigidTy::Slice(e) => ty_free(m, e, f, mut_ok),
                RigidTy::Ref(_, p, mu) => (mu is Not || mut_ok) && !(mu is Unknown) && ty_free(m, p, f, false),
                RigidTy::Adt(_, _) => match vec_elem(m, t) {
                    Some(e) => ty_free(m, e, f, false),
                    None => match adt_row(m, t) {
                        Some(a) => !a.is_box && !(a.kind is Union) && !(a.kind is Unknown) && a.name@ != b"std::cell::UnsafeCell"@
                            && forall|k: int, i: int| 0 <= k < a.variants@.len() && 0 <= i < a.variants@[k].fields@.len()
                                ==> ty_free(m, #[trigger] a.variants@[k].fields@[i], f, mut_ok),
                        None => false,
                    },
                },
                _ => false,
            },
            None => false,
        }
    }
}

/// A callee's signature: no `&mut` in the return type; a parameter is `&mut T` with `T` free of
/// `&mut`, or free of `&mut` itself (decision 3's slots).
pub open spec fn sig_ok(m: MirCrate, b: Body) -> bool {
    b.arg_count < b.locals@.len() && ty_free(m, b.locals@[0].ty, tfuel(m), false)
    && forall|k: int| 1 <= k <= b.arg_count ==> match rigid(m, #[trigger] b.locals@[k].ty) {
        Some(RigidTy::Ref(_, p, Mutability::Mut)) => ty_free(m, p, tfuel(m), false),
        _ => ty_free(m, b.locals@[k].ty, tfuel(m), false),
    }
}

pub open spec fn locals_ok(m: MirCrate, b: Body) -> bool {
    forall|k: int| 0 <= k < b.locals@.len() ==> ty_free(m, #[trigger] b.locals@[k].ty, tfuel(m), true)
}

/// One projection at type `t`: `Deref` of a reference, not onto `str` (whose contents are never
/// read) and, when `mutating`, not through a shared reference; `Index` of a local.
pub open spec fn proj_ok(m: MirCrate, b: Body, t: Ty, e: ProjectionElem, mutating: bool) -> bool {
    proj_ty(m, t, e) is Some && match e {
        ProjectionElem::Deref => match rigid(m, t) {
            Some(RigidTy::Ref(_, p, mu)) => !(rigid(m, p) matches Some(RigidTy::Str)) && !(mutating && !(mu is Mut)),
            _ => false,
        },
        ProjectionElem::Index(x) => x < b.locals@.len(),
        _ => true,
    }
}

pub open spec fn path_ok(m: MirCrate, b: Body, t: Ty, ps: Seq<ProjectionElem>, n: nat, mutating: bool) -> bool
    decreases n,
{
    if n == 0 { true } else if n > ps.len() { false } else {
        path_ok(m, b, t, ps, (n - 1) as nat, mutating)
            && match tys_along(m, t, ps, (n - 1) as nat) { Some(u) => proj_ok(m, b, u, ps[n - 1], mutating), None => false }
    }
}

/// A place the subset evaluates; `mutating` for a write, a `&mut` borrow or a drop.
pub open spec fn place_ok(m: MirCrate, b: Body, p: Place, mutating: bool) -> bool {
    p.local < b.locals@.len() && path_ok(m, b, b.locals@[p.local as int].ty, p.projection@, p.projection@.len(), mutating)
}

pub open spec fn op_ok(m: MirCrate, b: Body, x: Operand) -> bool {
    match x {
        Operand::Copy(p) => place_ok(m, b, p, false),
        Operand::Move(p) => place_ok(m, b, p, false),
        Operand::Constant(c) => const_val(m, c) is Some,
        _ => false,
    }
}

pub open spec fn ops_ok(m: MirCrate, b: Body, xs: Seq<Operand>) -> bool {
    forall|k: int| 0 <= k < xs.len() ==> op_ok(m, b, #[trigger] xs[k])
}

/// An operand of int or `bool` type.
pub open spec fn int_op(m: MirCrate, b: Body, x: Operand) -> bool {
    op_ok(m, b, x) && (op_ty(m, b, x) matches Some(t) && int_ty(m, t) is Some)
}

pub open spec fn cast_ok(m: MirCrate, b: Body, ck: CastKind, x: Operand, to: Ty) -> bool {
    op_ok(m, b, x) && match op_ty(m, b, x) {
        Some(tx) => match ck {
            CastKind::IntToInt => int_ty(m, tx) is Some && int_ty(m, to) is Some,
            CastKind::PointerCoercion(PointerCoercion::Unsize) => match (rigid(m, tx), rigid(m, to)) {
                (Some(RigidTy::Ref(_, p, _)), Some(RigidTy::Ref(_, q, _))) =>
                    (rigid(m, p) matches Some(RigidTy::Array(_, _))) && (rigid(m, q) matches Some(RigidTy::Slice(_))),
                _ => false,
            },
            CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_)) | CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer(_)) =>
                rigid(m, tx) matches Some(r) && (r is Closure || r is FnDef),
            CastKind::Subtype => true,
            _ => false,
        },
        None => false,
    }
}

pub open spec fn rv_ok(m: MirCrate, b: Body, rv: Rvalue) -> bool {
    match rv {
        Rvalue::Use(x, _) => op_ok(m, b, x),
        Rvalue::BinaryOp(op, x, y) => core_bin(op) is Some && int_op(m, b, x) && int_op(m, b, y),
        Rvalue::CheckedBinaryOp(op, x, y) => (op is Add || op is Sub || op is Mul) && int_op(m, b, x) && int_op(m, b, y),
        Rvalue::UnaryOp(op, x) => match op {
            UnOp::Not => int_op(m, b, x),
            UnOp::Neg => int_op(m, b, x) && signed(int_ty(m, op_ty(m, b, x)->Some_0)->Some_0),
            UnOp::PtrMetadata => op_ok(m, b, x) && (op_ty(m, b, x) matches Some(tx)
                && (rigid(m, tx) matches Some(RigidTy::Ref(_, p, _)) && rigid(m, p) matches Some(RigidTy::Slice(_)))),
            _ => false,
        },
        Rvalue::Cast(ck, x, to) => cast_ok(m, b, ck, x, to),
        Rvalue::Aggregate(ak, ops) => ops_ok(m, b, ops@) && match ak {
            AggregateKind::Array(_) | AggregateKind::Tuple => true,
            AggregateKind::Adt(_, _, _, _, active) => active is None,
            _ => false,
        },
        Rvalue::Repeat(x, c) => op_ok(m, b, x) && const_usize(m, c.id) is Some,
        Rvalue::Ref(_, bk, p) => match bk {
            BorrowKind::Shared => place_ok(m, b, p, false),
            BorrowKind::Mut { .. } => place_ok(m, b, p, true),
            _ => false,
        },
        Rvalue::Len(p) => place_ok(m, b, p, false)
            && (place_ty(m, b, p) matches Some(t) && rigid(m, t) matches Some(r) && (r is Array || r is Slice)),
        Rvalue::Discriminant(p) => place_ok(m, b, p, false) && (place_ty(m, b, p) matches Some(t) && adt_row(m, t) matches Some(a)
            && (a.kind is Struct || (a.kind is Enum && forall|k: int| 0 <= k < a.variants@.len() ==> (#[trigger] a.variants@[k]).discr is Some))),
        Rvalue::CopyForDeref(p) => place_ok(m, b, p, false),
        _ => false,
    }
}

pub open spec fn stmt_ok(m: MirCrate, b: Body, s: Statement) -> bool {
    match s.kind {
        StatementKind::Assign(p, rv) => place_ok(m, b, p, true) && rv_ok(m, b, rv),
        StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop | StatementKind::FakeRead(_, _)
        | StatementKind::PlaceMention(_) | StatementKind::AscribeUserType { .. } | StatementKind::Coverage(_)
        | StatementKind::ConstEvalCounter => true,
        _ => false,
    }
}

pub open spec fn std_arity(f: StdFn) -> Option<nat> {
    match f {
        StdFn::VecNew => Some(0),
        StdFn::VecWithCapacity | StdFn::VecAsSlice | StdFn::ArrayAsSlice | StdFn::VecLen | StdFn::SliceToVec => Some(1),
        StdFn::VecPush | StdFn::VecExtendFromSlice | StdFn::VecIndex | StdFn::Wrapping(_, _) => Some(2),
        StdFn::VecSet | StdFn::SliceSubrange => Some(3),
        StdFn::GhostNew => None,
    }
}

/// A leaf call's static shape: arity, and a ghost result's type.
pub open spec fn leaf_ok(m: MirCrate, pol: CallPolicy, key: Seq<u8>, gargs: GenericArgs, n: nat, dty: Option<Ty>) -> bool {
    if pol.declassify.contains(key) { n == 1 }
    else if pol.ghost_unit.contains(key) { dty matches Some(t) && zst_dest(m, t) }
    else {
        match std_model(m, key, gargs) {
            Some(f) => match std_arity(f) { Some(a) => a == n, None => dty matches Some(t) && zst_dest(m, t) },
            None => false,
        }
    }
}

/// Each argument has its parameter's type (type ids are interned). A closure reached through
/// `Fn::call` resolves to the closure body but is passed its arguments as one tuple (the rust-call
/// ABI): an arity check alone does not see that, and `mir_entry` would bind the tuple to the first
/// parameter.
pub open spec fn args_typed(m: MirCrate, b: Body, args: Seq<Operand>, cb: Body) -> bool {
    forall|k: int| 0 <= k < args.len() ==> op_ty(m, b, #[trigger] args[k]) == Some(cb.locals@[k + 1].ty)
}

pub open spec fn call_ok(m: MirCrate, pol: CallPolicy, b: Body, func: Operand, args: Seq<Operand>, dest: Place) -> bool {
    match callee_of(m, func) {
        Some((j, g)) => ops_ok(m, b, args) && place_ok(m, b, dest, true) && j < m.insts@.len()
            && if is_leaf(m, pol, m.insts@[j as int].key@, g) { leaf_ok(m, pol, m.insts@[j as int].key@, g, args.len(), place_ty(m, b, dest)) }
               else {
                   inst_body(m, j) matches Some(cb) && args.len() == cb.arg_count && sig_ok(m, cb)
                       && cb.spread_arg is None && args_typed(m, b, args, cb)
               },
        None => false,
    }
}

pub open spec fn drop_ok(m: MirCrate, b: Body, place: Place) -> bool {
    place_ok(m, b, place, true) && (place_ty(m, b, place) matches Some(t) && drop_row(m, t) matches Some(d)
        && (d.empty || vec_int(m, t) || (glue_of(m, d.glue) matches Some((_, gb)) && gb.arg_count == 1 && sig_ok(m, gb)
            && is_mut_ref(m, gb.locals@[1].ty))))
}

pub open spec fn term_ok(m: MirCrate, pol: CallPolicy, b: Body, t: TerminatorKind) -> bool {
    match t {
        TerminatorKind::Goto { .. } | TerminatorKind::Return | TerminatorKind::Unreachable | TerminatorKind::Abort => true,
        TerminatorKind::SwitchInt { discr, .. } => int_op(m, b, discr),
        TerminatorKind::Assert { cond, .. } => int_op(m, b, cond),
        TerminatorKind::Drop { place, .. } => drop_ok(m, b, place),
        TerminatorKind::Call { func, args, destination, target, .. } => target is None || call_ok(m, pol, b, func, args@, destination),
        _ => false,
    }
}

/// The static gate `run_block` applies before running a block.
#[verifier::opaque]
pub open spec fn block_ok(m: MirCrate, pol: CallPolicy, b: Body, blk: BasicBlock) -> bool {
    (forall|k: int| 0 <= k < blk.statements@.len() ==> stmt_ok(m, b, #[trigger] blk.statements@[k]))
    && term_ok(m, pol, b, blk.terminator.kind)
}

/// The normal successors of a terminator are in `r`.
pub open spec fn succs_in(t: TerminatorKind, r: Set<nat>) -> bool {
    match t {
        TerminatorKind::Goto { target } => r.contains(target as nat),
        TerminatorKind::SwitchInt { discr: _, targets } => r.contains(targets.otherwise as nat)
            && forall|k: int| 0 <= k < targets.branches@.len() ==> r.contains((#[trigger] targets.branches@[k]).1 as nat),
        TerminatorKind::Assert { target, .. } => r.contains(target as nat),
        TerminatorKind::Drop { target, .. } => r.contains(target as nat),
        TerminatorKind::Call { target, .. } => match target { Some(x) => r.contains(x as nat), None => true },
        _ => true,
    }
}

/// The body callees and drop glue a terminator runs are in `s`.
pub open spec fn callees_in(m: MirCrate, pol: CallPolicy, b: Body, t: TerminatorKind, s: Set<nat>) -> bool {
    match t {
        TerminatorKind::Call { func, target, .. } => target is None || match callee_of(m, func) {
            Some((j, g)) => is_leaf(m, pol, m.insts@[j as int].key@, g) || s.contains(j),
            None => true,
        },
        TerminatorKind::Drop { place, .. } => match place_ty(m, b, place) {
            Some(t) => match drop_row(m, t) {
                Some(d) => d.empty || vec_int(m, t) || (glue_of(m, d.glue) matches Some((j, _)) && s.contains(j)),
                None => true,
            },
            None => true,
        },
        _ => true,
    }
}

/// Instance `j`'s body, its signature and local types are in the subset, and `rs(j)` (closed under
/// normal successors, holding the entry block) holds only `block_ok` blocks whose callees are in `s`.
pub open spec fn body_in(m: MirCrate, pol: CallPolicy, s: Set<nat>, rs: spec_fn(nat) -> Set<nat>, j: nat) -> bool {
    inst_body(m, j) matches Some(b) && sig_ok(m, b) && locals_ok(m, b) && rs(j).contains(0)
    && forall|bb: nat| #[trigger] rs(j).contains(bb) ==> bb < b.blocks@.len() && block_ok(m, pol, b, b.blocks@[bb as int])
        && succs_in(b.blocks@[bb as int].terminator.kind, rs(j)) && callees_in(m, pol, b, b.blocks@[bb as int].terminator.kind, s)
}

pub open spec fn closed(m: MirCrate, pol: CallPolicy, s: Set<nat>, rs: spec_fn(nat) -> Set<nat>) -> bool {
    forall|j: nat| #[trigger] s.contains(j) ==> body_in(m, pol, s, rs, j)
}

/// `insts[i]` is in the subset: some set of instances holding it, closed under body calls and drop
/// glue, whose normal-edge reachable blocks (any closed superset of them) are all in the subset.
/// The least such sets are the closure and its reachable blocks.
pub open spec fn in_subset(m: MirCrate, pol: CallPolicy, i: nat) -> bool {
    exists|s: Set<nat>, rs: spec_fn(nat) -> Set<nat>| #[trigger] closed(m, pol, s, rs) && s.contains(i)
}

} // verus!
