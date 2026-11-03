//! `lowers`: the relation between a dump and the core program the translator gives for one root
//! (spec; Task 6 proves the simulation from it). Per construct, each `lowers_*` says what the core
//! image of a MIR item is, through views (core values hold `Vec`s, which spec code cannot build).
//!
//! Temps. A core body has the MIR locals `0..nloc` and then fresh temps. A constant's image is an
//! operand plus `pre`, the temp assignments it needs, run just before the statement (or, for a
//! terminator, at the end of the block's statements): `pre[i]` assigns temp `base + i`, so the
//! temps of one image are distinct and none is a MIR local. A constant takes as many temps as
//! decision 7 charges it steps (`const_val`'s count). A drop through glue takes two: the `&mut`
//! argument (assigned in `pre`) and the unit destination (never read).
#[allow(unused_imports)]
use crate::lower::FnInfo;
#[allow(unused_imports)]
use crate::mir::*;
#[allow(unused_imports)]
use crate::policy::*;
#[allow(unused_imports)]
use crate::sem::*;
#[allow(unused_imports)]
use ctcore::syntax as c;
use vstd::prelude::*;

verus! {

pub open spec fn core_cv(cv: c::ConstVal) -> ctcore::sem::Val { ctcore::sem::const_val(cv) }

/// The type-depth bound of `lowers_ty`.
pub open spec fn tyf() -> nat { 17 }

// ------------------------------------------------------------------ types

/// Types map structurally. The one fact the semantics needs: the core type is `Mut` exactly
/// when the MIR type is `&mut` (both entry frames put a slot location there).
pub open spec fn lowers_ty(m: MirCrate, t: Ty, ct: c::Ty, fuel: nat) -> bool
    decreases fuel, 1nat,
{
    if fuel == 0 { false } else {
        let f = (fuel - 1) as nat;
        match rigid(m, t) {
            Some(r) => match r {
                RigidTy::Bool | RigidTy::Int(_) | RigidTy::Uint(_) => int_of(r) matches Some(it) && ct is Int && ct->Int_0 == it,
                RigidTy::Tuple(ts) => if ts@.len() == 0 { ct is Unit } else {
                    ct is Tuple && ct->Tuple_0@.len() == ts@.len()
                        && forall|i: int| 0 <= i < ts@.len() ==> lowers_ty(m, #[trigger] ts@[i], ct->Tuple_0@[i], f)
                },
                RigidTy::Adt(_, _) => lowers_adt_ty(m, t, ct, f),
                RigidTy::Array(e, n) => ct is Array && const_usize(m, n.id) == Some(ct->Array_1) && lowers_ty(m, e, *ct->Array_0, f),
                RigidTy::Slice(e) => ct is Slice && lowers_ty(m, e, *ct->Slice_0, f),
                RigidTy::Str => ct is Unit,
                RigidTy::Ref(_, p, mu) => if rigid(m, p) matches Some(RigidTy::Str) { mu is Not && ct is Unit } else {
                    match mu {
                        Mutability::Not => ct is Shr && lowers_ty(m, p, *ct->Shr_0, f),
                        Mutability::Mut => ct is Mut && lowers_ty(m, p, *ct->Mut_0, f),
                        _ => false,
                    }
                },
                RigidTy::FnDef(_, _) | RigidTy::Closure(_, _) | RigidTy::FnPtr(_) => ct is Unit,
                _ => false,
            },
            None => false,
        }
    }
}

/// `vstd`'s `Ghost`/`Tracked` are `Unit`, `Vec<E>` is `Vec`, a struct or enum its variants' fields.
pub open spec fn lowers_adt_ty(m: MirCrate, t: Ty, ct: c::Ty, f: nat) -> bool
    decreases f, 2nat,
{
    match adt_row(m, t) {
        Some(a) => if a.name@ == b"vstd::prelude::Ghost"@ || a.name@ == b"vstd::prelude::Tracked"@ { ct is Unit }
            else if vec_elem(m, t) is Some { ct is Vec && lowers_ty(m, vec_elem(m, t)->Some_0, *ct->Vec_0, f) }
            else {
                !a.is_box && (a.kind is Struct || a.kind is Enum) && ct is Adt && ct->Adt_0@.len() == a.variants@.len()
                && forall|k: int| 0 <= k < a.variants@.len() ==> {
                    &&& (#[trigger] ct->Adt_0@[k])@.len() == a.variants@[k].fields@.len()
                    &&& forall|i: int| 0 <= i < a.variants@[k].fields@.len() ==> lowers_ty(m, #[trigger] a.variants@[k].fields@[i], ct->Adt_0@[k]@[i], f)
                }
            },
        None => false,
    }
}

// ------------------------------------------------------------------ places

pub open spec fn lowers_proj(e: ProjectionElem, q: c::Proj) -> bool {
    match e {
        ProjectionElem::Deref => q is Deref,
        ProjectionElem::Field(i, _) => q is Field && q->Field_0 == i,
        ProjectionElem::Index(l) => q is Index && q->Index_0 == l,
        ProjectionElem::ConstantIndex { offset, min_length: _, from_end } => !from_end && q is ConstIndex && q->ConstIndex_0 == offset,
        ProjectionElem::Downcast(v) => q is Downcast && q->Downcast_0 == v,
        _ => false,
    }
}

/// Some `Deref` among the first `n` projections goes through a shared reference (the walk is in
/// a snapshot from there on).
pub open spec fn snap(m: MirCrate, t: Ty, ps: Seq<ProjectionElem>, n: nat) -> bool
    decreases n,
{
    if n == 0 || n > ps.len() { false } else {
        snap(m, t, ps, (n - 1) as nat) || (ps[n - 1] is Deref && shr_at(m, tys_along(m, t, ps, (n - 1) as nat)))
    }
}

pub open spec fn shr_at(m: MirCrate, u: Option<Ty>) -> bool {
    match u { Some(u) => rigid(m, u) matches Some(RigidTy::Ref(_, _, Mutability::Not)), None => false }
}

/// No `Deref` of a `&mut` inside a snapshot (core's walk reads `Unit` there; MIR's follows it).
pub open spec fn no_mut_in_snap(m: MirCrate, t: Ty, ps: Seq<ProjectionElem>) -> bool {
    forall|k: int| 0 <= k < ps.len() && (#[trigger] ps[k]) is Deref && snap(m, t, ps, k as nat)
        ==> !(tys_along(m, t, ps, k as nat) matches Some(u) && is_mut_ref(m, u))
}

/// A place: in the subset (`place_ok`), projection by projection the same, no `&mut` deref in a
/// snapshot.
pub open spec fn lowers_place(m: MirCrate, b: Body, p: Place, q: c::Place, mutating: bool) -> bool {
    &&& place_ok(m, b, p, mutating)
    &&& q.local == p.local && q.proj@.len() == p.projection@.len()
    &&& forall|k: int| 0 <= k < p.projection@.len() ==> lowers_proj(#[trigger] p.projection@[k], q.proj@[k])
    &&& no_mut_in_snap(m, b.locals@[p.local as int].ty, p.projection@)
}

// ------------------------------------------------------------------ temps and constants

/// `pre[i]` assigns temp `base + i`.
pub open spec fn temps_at(pre: Seq<c::Stmt>, base: nat) -> bool {
    forall|i: int| 0 <= i < pre.len() ==> (#[trigger] pre[i]) is Assign && pre[i]->Assign_0.local == base + i
        && pre[i]->Assign_0.proj@.len() == 0
}

pub open spec fn tmp_rv(pre: Seq<c::Stmt>, i: int) -> c::Rvalue { pre[i]->Assign_1 }

/// `y` reads temp `x` whole.
pub open spec fn is_tmp(y: c::Operand, x: nat) -> bool { y is Copy && y->Copy_0.local == x && y->Copy_0.proj@.len() == 0 }

/// A literal image of the value `dec` gives at `off`: an int `Const`, or a `Lit` whose value it is
/// (`Unit` also stands for `()`, a value representation Task 6 relates).
pub open spec fn lit_img(m: MirCrate, t: Ty, a: Allocation, off: nat, fuel: nat, y: c::Operand) -> bool {
    dec(m, t, a, off, fuel) matches Some((v, _)) && (
        (int_ty(m, t) matches Some(it) && y is Const && y->Const_0 == it && v == ctcore::sem::Val::Int(y->Const_1))
        || (y is Lit && (core_cv(y->Lit_0) == v || (y->Lit_0 is Unit && v == unit_val()))))
}

/// The prefix node counts of `dec_fields`.
pub open spec fn fcount(m: MirCrate, ts: Seq<Ty>, os: Seq<MachineSize>, a: Allocation, base: nat, fuel: nat, n: nat) -> nat {
    match dec_fields(m, ts, os, a, base, fuel, n) { Some((_, c)) => c, None => 0 }
}

/// A value nested in an ADT constant (or a charged constant): as many temps as `dec` counts
/// nodes. A literal takes none, a `&[T; N]` or `&ZST` literal one (`Use(Lit(..))`), an ADT its
/// fields' and then one `Aggregate`, a `&` of a unit-like ADT that ADT's and then one `RefShr`.
pub open spec fn lowers_cv(m: MirCrate, t: Ty, a: Allocation, off: nat, fuel: nat, y: c::Operand, pre: Seq<c::Stmt>, base: nat) -> bool
    decreases fuel, 1nat,
{
    if fuel == 0 { false } else {
        &&& temps_at(pre, base)
        &&& dec(m, t, a, off, fuel) matches Some((v, k))
        &&& pre.len() == k
        &&& {
            ||| k == 0 && lit_img(m, t, a, off, fuel, y)
            ||| k == 1 && is_tmp(y, base) && tmp_rv(pre, 0) is Use && tmp_rv(pre, 0)->Use_0 is Lit && core_cv(tmp_rv(pre, 0)->Use_0->Lit_0) == v
            ||| adt_img(m, t, a, off, (fuel - 1) as nat, y, pre, base)
            ||| zref_img(m, t, y, pre, base)
        }
    }
}

/// `dec_adt` at fuel `f`, node by node.
pub open spec fn adt_img(m: MirCrate, t: Ty, a: Allocation, off: nat, f: nat, y: c::Operand, pre: Seq<c::Stmt>, base: nat) -> bool
    decreases f, 2nat,
{
    rigid(m, t) is Some && rigid(m, t)->Some_0 is Adt && match (adt_row(m, t), layout(m, t)) {
        (Some(row), Some(l)) => !row.is_box && !(row.kind is Union) && match adt_sel(row, l, a, off) {
            Some((kv, o)) => kv < row.variants@.len() && o.len() == row.variants@[kv as int].fields@.len() && {
                let fs = row.variants@[kv as int].fields@;
                let n = fs.len();
                &&& dec_fields(m, fs, o, a, off, f, n) is Some
                &&& {
                    let c = fcount(m, fs, o, a, off, f, n);
                    &&& pre.len() == c + 1 && is_tmp(y, base + c)
                    &&& tmp_rv(pre, c as int) is Aggregate && tmp_rv(pre, c as int)->Aggregate_0 == c::AggKind::Adt(kv as usize)
                    &&& tmp_rv(pre, c as int)->Aggregate_1@.len() == n
                    &&& forall|i: int| 0 <= i < n ==> lowers_cv(m, #[trigger] fs[i], a, (off + o[i].num_bits / 8) as nat, f, tmp_rv(pre, c as int)->Aggregate_1@[i],
                            pre.subrange(fcount(m, fs, o, a, off, f, i as nat) as int, fcount(m, fs, o, a, off, f, (i + 1) as nat) as int),
                            base + fcount(m, fs, o, a, off, f, i as nat))
                }
            },
            None => false,
        },
        _ => false,
    }
}

/// A `&` of a unit-like ADT: the ADT's temps (`ul_img`), then `RefShr` of the last.
pub open spec fn zref_img(m: MirCrate, t: Ty, y: c::Operand, pre: Seq<c::Stmt>, base: nat) -> bool {
    rigid(m, t) matches Some(RigidTy::Ref(_, p, Mutability::Not)) && pre.len() >= 1 && {
        let c = (pre.len() - 1) as nat;
        &&& is_tmp(y, base + c)
        &&& tmp_rv(pre, c as int) is RefShr
        &&& ul_img(m, p, tfuel(m), c::Operand::Copy(tmp_rv(pre, c as int)->RefShr_0), pre.subrange(0, c as int), base)
    }
}

pub open spec fn ucount(m: MirCrate, ts: Seq<Ty>, fuel: nat, n: nat) -> nat {
    match unit_likes(m, ts, fuel, n, true) { Some((_, c)) => c, None => 0 }
}

/// A unit-like value (`unit_like` with closures): a literal, or an ADT's fields and then one
/// `Aggregate` of variant 0.
pub open spec fn ul_img(m: MirCrate, t: Ty, fuel: nat, y: c::Operand, pre: Seq<c::Stmt>, base: nat) -> bool
    decreases fuel,
{
    if fuel == 0 { false } else {
        &&& temps_at(pre, base)
        &&& unit_like(m, t, fuel, true) matches Some((v, k))
        &&& pre.len() == k
        &&& {
            ||| k == 0 && y is Lit && (core_cv(y->Lit_0) == v || (y->Lit_0 is Unit && v == unit_val()))
            ||| rigid(m, t) matches Some(RigidTy::Adt(_, _)) && adt_row(m, t) matches Some(row) && row.variants@.len() == 1 && {
                let fs = row.variants@[0].fields@;
                let f = (fuel - 1) as nat;
                let c = ucount(m, fs, f, fs.len());
                &&& k == c + 1 && is_tmp(y, base + c)
                &&& tmp_rv(pre, c as int) is Aggregate && tmp_rv(pre, c as int)->Aggregate_0 == c::AggKind::Adt(0)
                &&& tmp_rv(pre, c as int)->Aggregate_1@.len() == fs.len()
                &&& forall|i: int| 0 <= i < fs.len() ==> ul_img(m, #[trigger] fs[i], f, tmp_rv(pre, c as int)->Aggregate_1@[i],
                        pre.subrange(ucount(m, fs, f, i as nat) as int, ucount(m, fs, f, (i + 1) as nat) as int), base + ucount(m, fs, f, i as nat))
            }
        }
    }
}

/// A constant operand (decision 5): its value's image, with its charge in temps.
pub open spec fn lowers_const(m: MirCrate, k: ConstOperand, y: c::Operand, pre: Seq<c::Stmt>, base: nat) -> bool {
    let t = k.const_.ty;
    &&& const_val(m, k) matches Some((_, ch)) && pre.len() == ch
    &&& match k.const_.kind {
        ConstantKind::ZeroSized => y is Lit && y->Lit_0 is Unit,
        ConstantKind::Allocated(a) => if charged(m, t) { lowers_cv(m, t, a, 0, dfuel(m), y, pre, base) }
            else { lit_img(m, t, a, 0, dfuel(m), y) },
        _ => false,
    }
}

// ------------------------------------------------------------------ operands and rvalues

pub open spec fn op_charge(m: MirCrate, x: Operand) -> nat {
    match x { Operand::Constant(k) => match const_val(m, k) { Some((_, ch)) => ch, None => 0 }, _ => 0 }
}

pub open spec fn ops_charge(m: MirCrate, xs: Seq<Operand>, n: nat) -> nat
    decreases n,
{
    if n == 0 || n > xs.len() { 0 } else { ops_charge(m, xs, (n - 1) as nat) + op_charge(m, xs[n - 1]) }
}

pub open spec fn lowers_op(m: MirCrate, b: Body, x: Operand, y: c::Operand, pre: Seq<c::Stmt>, base: nat) -> bool {
    match x {
        Operand::Copy(p) => pre.len() == 0 && y is Copy && lowers_place(m, b, p, y->Copy_0, false),
        Operand::Move(p) => pre.len() == 0 && y is Copy && lowers_place(m, b, p, y->Copy_0, false),
        Operand::Constant(k) => lowers_const(m, k, y, pre, base),
        _ => false,
    }
}

/// Operands left to right, their temps one after another.
pub open spec fn lowers_ops(m: MirCrate, b: Body, xs: Seq<Operand>, ys: Seq<c::Operand>, pre: Seq<c::Stmt>, base: nat) -> bool {
    &&& ys.len() == xs.len() && pre.len() == ops_charge(m, xs, xs.len())
    &&& forall|k: int| 0 <= k < xs.len() ==> lowers_op(m, b, #[trigger] xs[k], ys[k],
            pre.subrange(ops_charge(m, xs, k as nat) as int, ops_charge(m, xs, (k + 1) as nat) as int), base + ops_charge(m, xs, k as nat))
}

/// `x`'s type is an int or `bool`, `it`.
pub open spec fn int_at(m: MirCrate, b: Body, x: Operand, it: c::IntTy) -> bool {
    op_ty(m, b, x) matches Some(t) && int_ty(m, t) == Some(it)
}

pub open spec fn two_ops(m: MirCrate, b: Body, x: Operand, y: Operand, cx: c::Operand, cy: c::Operand, pre: Seq<c::Stmt>, base: nat) -> bool {
    let n = op_charge(m, x);
    pre.len() == n + op_charge(m, y) && lowers_op(m, b, x, cx, pre.subrange(0, n as int), base)
        && lowers_op(m, b, y, cy, pre.subrange(n as int, pre.len() as int), base + n)
}

/// Core `Discr` reads the variant index: the place is a struct, or an enum whose discriminants
/// are the indices.
pub open spec fn discr_index(m: MirCrate, b: Body, p: Place) -> bool {
    place_ty(m, b, p) matches Some(t) && adt_row(m, t) matches Some(a) && (a.kind is Struct
        || (a.kind is Enum && forall|k: int| 0 <= k < a.variants@.len() ==> (#[trigger] a.variants@[k]).discr == Some(k as u128)))
}

pub open spec fn lowers_rv(m: MirCrate, b: Body, rv: Rvalue, cr: c::Rvalue, pre: Seq<c::Stmt>, base: nat) -> bool {
    match rv {
        Rvalue::Use(x, _) => cr is Use && lowers_op(m, b, x, cr->Use_0, pre, base),
        Rvalue::BinaryOp(op, x, y) => cr is Bin && core_bin(op) == Some(cr->Bin_0) && int_at(m, b, x, cr->Bin_1)
            && two_ops(m, b, x, y, cr->Bin_2, cr->Bin_3, pre, base),
        Rvalue::UnaryOp(UnOp::Not, x) => cr is Un && cr->Un_0 is Not && int_at(m, b, x, cr->Un_1) && lowers_op(m, b, x, cr->Un_2, pre, base),
        Rvalue::UnaryOp(UnOp::Neg, x) => cr is Un && cr->Un_0 is Neg && int_at(m, b, x, cr->Un_1) && lowers_op(m, b, x, cr->Un_2, pre, base),
        Rvalue::UnaryOp(UnOp::PtrMetadata, x) => cr is Len && pre.len() == 0 && match x {
            Operand::Copy(p) => lowers_place(m, b, p, cr->Len_0, false),
            Operand::Move(p) => lowers_place(m, b, p, cr->Len_0, false),
            _ => false,
        },
        Rvalue::Cast(CastKind::IntToInt, x, to) => cr is Cast && int_at(m, b, x, cr->Cast_0) && int_ty(m, to) == Some(cr->Cast_1)
            && lowers_op(m, b, x, cr->Cast_2, pre, base),
        Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), x, _) => cr is Use && lowers_op(m, b, x, cr->Use_0, pre, base),
        Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_)), x, _) => cr is Use && lowers_op(m, b, x, cr->Use_0, pre, base),
        Rvalue::Aggregate(ak, xs) => cr is Aggregate && lowers_ops(m, b, xs@, cr->Aggregate_1@, pre, base) && match ak {
            AggregateKind::Array(_) => cr->Aggregate_0 is Array,
            AggregateKind::Tuple => cr->Aggregate_0 is Tuple,
            AggregateKind::Adt(_, v, _, _, None) => cr->Aggregate_0 == c::AggKind::Adt(v),
            _ => false,
        },
        Rvalue::Repeat(x, n) => cr is Repeat && const_usize(m, n.id) == Some(cr->Repeat_1) && lowers_op(m, b, x, cr->Repeat_0, pre, base),
        Rvalue::Ref(_, BorrowKind::Shared, p) => cr is RefShr && pre.len() == 0 && lowers_place(m, b, p, cr->RefShr_0, false),
        Rvalue::Ref(_, BorrowKind::Mut { .. }, p) => cr is RefMut && pre.len() == 0 && lowers_place(m, b, p, cr->RefMut_0, true),
        Rvalue::Len(p) => cr is Len && pre.len() == 0 && lowers_place(m, b, p, cr->Len_0, false),
        Rvalue::Discriminant(p) => cr is Discr && pre.len() == 0 && lowers_place(m, b, p, cr->Discr_0, false) && discr_index(m, b, p),
        Rvalue::CopyForDeref(p) => cr is Use && cr->Use_0 is Copy && pre.len() == 0 && lowers_place(m, b, p, cr->Use_0->Copy_0, false),
        _ => false,
    }
}

// ------------------------------------------------------------------ statements and blocks

/// Temps `base..base + n` lie after the MIR locals and inside the core body.
pub open spec fn tmps_in(base: nat, n: nat, nloc: nat, ncore: nat) -> bool { nloc <= base && base + n <= ncore }

/// A statement's image: its temps, then the assignment (`stmt_ok` holds); none for the
/// statements that generate no code.
pub open spec fn lowers_stmt(m: MirCrate, b: Body, nloc: nat, ncore: nat, s: Statement, cs: Seq<c::Stmt>) -> bool {
    match s.kind {
        StatementKind::Assign(p, rv) => cs.len() >= 1 && cs.last() is Assign && rv_ok(m, b, rv)
            && lowers_place(m, b, p, cs.last()->Assign_0, true)
            && exists|base: nat| tmps_in(base, (cs.len() - 1) as nat, nloc, ncore) && #[trigger] lowers_rv(m, b, rv, cs.last()->Assign_1, cs.drop_last(), base),
        StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop | StatementKind::FakeRead(_, _)
        | StatementKind::PlaceMention(_) | StatementKind::AscribeUserType { .. } | StatementKind::Coverage(_)
        | StatementKind::ConstEvalCounter => cs.len() == 0,
        _ => false,
    }
}

/// The core statements of a MIR statement (its charge plus 1 for an assignment).
pub open spec fn slen(m: MirCrate, s: Statement) -> nat {
    match s.kind { StatementKind::Assign(_, rv) => rv_charge(m, rv) + 1, _ => 0 }
}

pub open spec fn rv_charge(m: MirCrate, rv: Rvalue) -> nat {
    match rv {
        Rvalue::Use(x, _) => op_charge(m, x),
        Rvalue::BinaryOp(_, x, y) => op_charge(m, x) + op_charge(m, y),
        Rvalue::UnaryOp(_, x) => op_charge(m, x),
        Rvalue::Cast(_, x, _) => op_charge(m, x),
        Rvalue::Aggregate(_, xs) => ops_charge(m, xs@, xs@.len()),
        Rvalue::Repeat(x, _) => op_charge(m, x),
        _ => 0,
    }
}

/// Where statement `i`'s image starts.
pub open spec fn soff(m: MirCrate, ss: Seq<Statement>, i: nat) -> nat
    decreases i,
{
    if i == 0 || i > ss.len() { 0 } else { soff(m, ss, (i - 1) as nat) + slen(m, ss[i - 1]) }
}

pub open spec fn is_declassify(pol: Policy, m: MirCrate, func: Operand) -> bool {
    callee_of(m, func) matches Some((j, _)) && j < m.insts@.len() && has(pol.declassify@, m.insts@[j as int].key@)
}

/// The core intrinsic of a leaf: policy calls first, then the std model (as `leaf_call`).
pub open spec fn intr_of(m: MirCrate, pol: CallPolicy, key: Seq<u8>, g: GenericArgs) -> Option<c::Intrinsic> {
    if pol.declassify.contains(key) { Some(c::Intrinsic::Declassify) }
    else if pol.ghost_unit.contains(key) { Some(c::Intrinsic::GhostUnit) }
    else {
        match std_model(m, key, g) {
            Some(f) => Some(match f {
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
            }),
            None => None,
        }
    }
}

/// A callee entered as a core fn: an `Item` with a body in the dump's crate or a policy crate.
pub open spec fn internal(m: MirCrate, pol: Policy, j: nat) -> bool {
    j < m.insts@.len() && {
        let x = m.insts@[j as int];
        x.kind is Item && x.body is Some
            && (x.krate@ == m.crate_name@ || has(pol.internal_crates@, x.krate@) || has(pol.translate_crates@, x.krate@))
    }
}

/// Core fn `h` is the image of `insts[j]` (`ord`: each fn's `insts` index).
pub open spec fn fn_of(ord: Seq<usize>, h: usize, j: nat) -> bool { (h as nat) < ord.len() && ord[h as int] as nat == j }

/// `Call`: the callee resolved through `calls`; a leaf is its intrinsic, a body call the core fn
/// of an internal instance.
pub open spec fn lowers_call(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, func: Operand, args: Seq<Operand>, dest: Place,
    tb: BasicBlockIdx, pre: Seq<c::Stmt>, base: nat, ct: c::Term) -> bool
{
    callee_of(m, func) matches Some((j, g)) && j < m.insts@.len() && ct is Call && ct->Call_3 == tb
    && lowers_place(m, b, dest, ct->Call_2, true) && lowers_ops(m, b, args, ct->Call_1@, pre, base)
    && if is_leaf(m, cpol(pol), m.insts@[j as int].key@, g) {
        ct->Call_0 is Intr && intr_of(m, cpol(pol), m.insts@[j as int].key@, g) == Some(ct->Call_0->Intr_0)
    } else {
        ct->Call_0 is Fn && fn_of(ord, ct->Call_0->Fn_0, j) && internal(m, pol, j)
    }
}

pub open spec fn no_index(p: Place) -> bool { forall|k: int| 0 <= k < p.projection@.len() ==> !(#[trigger] p.projection@[k] is Index) }

/// `Drop` through its `drops` row: an empty shim or the `Vec<int>` leaf is a `Goto`; other glue is
/// `x = &mut place` (in `pre`) and a call of the glue's core fn on `x` into a fresh unit temp.
pub open spec fn lowers_drop(m: MirCrate, ord: Seq<usize>, b: Body, nloc: nat, ncore: nat, place: Place, target: BasicBlockIdx,
    pre: Seq<c::Stmt>, ct: c::Term) -> bool
{
    place_ty(m, b, place) matches Some(t) && drop_row(m, t) matches Some(d) && no_index(place)
    && if d.empty || vec_int(m, t) { pre.len() == 0 && ct is Goto && ct->Goto_0 == target } else {
        glue_of(m, d.glue) matches Some((j, _)) && pre.len() == 1 && pre[0] is Assign && pre[0]->Assign_0.proj@.len() == 0
        && pre[0]->Assign_1 is RefMut && lowers_place(m, b, place, pre[0]->Assign_1->RefMut_0, true) && {
            let x = pre[0]->Assign_0.local as nat;
            &&& nloc <= x < ncore
            &&& ct is Call && ct->Call_0 is Fn && fn_of(ord, ct->Call_0->Fn_0, j) && ct->Call_3 == target
            &&& ct->Call_1@.len() == 1 && is_tmp(ct->Call_1@[0], x)
            &&& ct->Call_2.proj@.len() == 0 && nloc <= ct->Call_2.local < ncore && ct->Call_2.local != x
        }
    }
}

pub open spec fn lowers_term(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, nloc: nat, ncore: nat, t: TerminatorKind,
    pre: Seq<c::Stmt>, ct: c::Term) -> bool
{
    exists|base: nat| tmps_in(base, pre.len(), nloc, ncore) && #[trigger] lowers_term_at(m, pol, ord, b, nloc, ncore, t, pre, ct, base)
}

/// `lowers_term` with the terminator's temps from `base`.
pub open spec fn lowers_term_at(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, nloc: nat, ncore: nat, t: TerminatorKind,
    pre: Seq<c::Stmt>, ct: c::Term, base: nat) -> bool
{
    match t {
        TerminatorKind::Goto { target } => pre.len() == 0 && ct is Goto && ct->Goto_0 == target,
        TerminatorKind::SwitchInt { discr, targets } => ct is Switch && lowers_op(m, b, discr, ct->Switch_0, pre, base)
            && ct->Switch_1@ == targets.branches@ && ct->Switch_2 == targets.otherwise,
        TerminatorKind::Assert { cond, expected, msg: _, target, unwind: _ } => ct is Assert && lowers_op(m, b, cond, ct->Assert_0, pre, base)
            && ct->Assert_1 == expected && ct->Assert_2 == target,
        TerminatorKind::Return => pre.len() == 0 && ct is Return,
        TerminatorKind::Unreachable => pre.len() == 0 && ct is Abort,
        TerminatorKind::Drop { place, target, unwind: _ } => lowers_drop(m, ord, b, nloc, ncore, place, target, pre, ct),
        TerminatorKind::Call { func, args, destination, target: Some(tb), unwind: _ } =>
            lowers_call(m, pol, ord, b, func, args@, destination, tb, pre, base, ct),
        _ => false,
    }
}

/// A reachable block: its statements' images one after another, then its terminator's temps and
/// the terminator.
pub open spec fn lowers_block(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, nloc: nat, ncore: nat, blk: BasicBlock, cb: c::Block) -> bool {
    let ss = blk.statements@;
    let n = ss.len();
    let cs = cb.stmts@;
    &&& soff(m, ss, n) <= cs.len()
    &&& forall|i: int| 0 <= i < n ==> lowers_stmt(m, b, nloc, ncore, #[trigger] ss[i], cs.subrange(soff(m, ss, i as nat) as int, soff(m, ss, (i + 1) as nat) as int))
    &&& lowers_term(m, pol, ord, b, nloc, ncore, blk.terminator.kind, cs.subrange(soff(m, ss, n) as int, cs.len() as int), cb.term)
}

// ------------------------------------------------------------------ fns and the program

/// The instances the program's fns are images of.
pub open spec fn ord_set(ord: Seq<usize>) -> Set<nat> { ord.map_values(|j: usize| j as nat).to_set() }

/// Core body `cb` is the image of `insts[j]` with reachable blocks `r` (marks): that body is in
/// the subset (`body_in`'s conditions, block by block), locals map 1:1 by `lowers_ty`, a reachable
/// block by `lowers_block`, an unreachable one is an empty `Abort` block.
pub open spec fn lowers_body(m: MirCrate, pol: Policy, ord: Seq<usize>, j: nat, cb: c::Body, r: Seq<bool>) -> bool {
    inst_body(m, j) matches Some(b) && {
        let nloc = b.locals@.len();
        let ncore = cb.locals@.len();
        &&& b.spread_arg is None && sig_ok(m, b) && locals_ok(m, b)
        &&& cb.nargs == b.arg_count && nloc <= ncore && cb.blocks@.len() == b.blocks@.len() && r.len() == b.blocks@.len()
        &&& forall|k: int| 0 <= k < nloc ==> lowers_ty(m, #[trigger] b.locals@[k].ty, cb.locals@[k], tyf())
        &&& r.len() > 0 && r[0]
        &&& forall|bb: int| 0 <= bb < r.len() ==> #[trigger] block_rel(m, pol, ord, b, nloc, ncore, r, b.blocks@[bb], cb.blocks@[bb], r[bb])
    }
}

/// One block of `lowers_body`.
pub open spec fn block_rel(m: MirCrate, pol: Policy, ord: Seq<usize>, b: Body, nloc: nat, ncore: nat, r: Seq<bool>,
    blk: BasicBlock, cblk: c::Block, reached: bool) -> bool
{
    if reached {
        &&& block_ok(m, cpol(pol), b, blk)
        &&& succs_in(blk.terminator.kind, marks(r))
        &&& callees_in(m, cpol(pol), b, blk.terminator.kind, ord_set(ord))
        &&& lowers_block(m, pol, ord, b, nloc, ncore, blk, cblk)
    } else {
        cblk.stmts@.len() == 0 && cblk.term is Abort
    }
}

/// The `insts` index of each fn.
pub open spec fn ords(infos: Seq<FnInfo>) -> Seq<usize> { infos.map_values(|i: FnInfo| i.inst) }

/// The blocks a mark sequence holds.
pub open spec fn marks(r: Seq<bool>) -> Set<nat> {
    Seq::new(r.len(), |i: int| i as nat).filter(|i: nat| i < r.len() && r[i as int]).to_set()
}

/// Item `k` may be root `root`: its instance's key is `root`, or it is generic and its name is
/// `root` (or holds `::<`, so its key could be anything).
pub open spec fn item_may_be(m: MirCrate, k: int, root: Seq<u8>) -> bool {
    match m.items@[k].inst {
        Some(id) => inst_idx(m, id) matches Some(j) && m.insts@[j as int].key@ == root,
        None => m.items@[k].name@ == root || has_lt(m.items@[k].name@),
    }
}

pub open spec fn has_lt(s: Seq<u8>) -> bool { exists|i: int| 0 <= i && i + 2 < s.len() && #[trigger] s[i] == 58u8 && s[i + 1] == 58u8 && s[i + 2] == 60u8 }

/// The `insts` index of item `k`'s instance.
pub open spec fn item_inst(m: MirCrate, k: int) -> Option<nat> {
    match m.items@[k].inst { Some(id) => inst_idx(m, id), None => None }
}

/// `insts[j]` is root `root`: the one item that may be it, and monomorphic.
pub open spec fn root_of(m: MirCrate, root: Seq<u8>, j: nat) -> bool {
    exists|k: int| 0 <= k < m.items@.len() && #[trigger] item_may_be(m, k, root) && item_inst(m, k) == Some(j)
        && forall|k2: int| 0 <= k2 < m.items@.len() && #[trigger] item_may_be(m, k2, root) ==> k2 == k
}

pub open spec fn lowers_rs(m: MirCrate, pol: Policy, root: Seq<u8>, p: c::Program, infos: Seq<FnInfo>, rs: Seq<Seq<bool>>) -> bool {
    &&& p.fns@.len() == infos.len() && rs.len() == infos.len() && infos.len() >= 1
    &&& root_of(m, root, infos[0].inst as nat) && infos[0].is_root
    &&& forall|g: int, h: int| 0 <= g < infos.len() && 0 <= h < infos.len() && g != h ==> (#[trigger] infos[g]).inst != (#[trigger] infos[h]).inst
    &&& forall|g: int| 0 <= g < infos.len() ==> lowers_body(m, pol, ords(infos), infos[g].inst as nat, p.fns@[g], #[trigger] rs[g])
}

/// The translator's contract: some reachable-block marks per fn make every fn the image of its
/// instance.
pub open spec fn lowers(m: MirCrate, pol: Policy, root: Seq<u8>, p: c::Program, infos: Seq<FnInfo>) -> bool {
    exists|rs: Seq<Seq<bool>>| lowers_rs(m, pol, root, p, infos, rs)
}

} // verus!
