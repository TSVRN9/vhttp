//! The translator, construct by construct (verified against `rel::lowers_*`): places, operands,
//! rvalues, statements and terminators. Bodies, the closure and `lower` are in `lower_fn`. Each
//! lowering also proves the semantics' static gate for its construct (`rv_ok`, `stmt_ok`,
//! `term_ok`, `callees_in`), which `lowers` requires of every reachable block.
use crate::look::*;
use crate::lower_const::*;
use crate::mir::*;
#[cfg(verus_keep_ghost)]
use crate::rel::*;
#[cfg(verus_keep_ghost)]
use crate::sem::*;
use ctcore::syntax as c;
use vstd::prelude::*;

verus! {

/// What the report needs about one translated fn (index = its core fn index).
pub struct FnInfo {
    /// `ct_key` of the instance; for drop glue (whose key `std::ptr::drop_glue` all glue shares)
    /// the instance name.
    pub path: Vec<u8>,
    pub is_root: bool,
    /// The fn item's `#[ct::..]` tool attributes, trimmed.
    pub attrs: Vec<Vec<u8>>,
    /// One per MIR argument, from `var_debug_info`; empty when it has no plain name.
    pub param_names: Vec<Vec<u8>>,
    /// Per block, the terminator's `<file>:<line>`.
    pub block_sites: Vec<Vec<u8>>,
    /// `<file>:<line>` of each declassify call, in block order.
    pub declassify_sites: Vec<Vec<u8>>,
    /// Per block, per core statement, its `<file>:<line>`.
    pub stmt_sites: Vec<Vec<Vec<u8>>>,
    /// The `insts` index this fn is the image of.
    pub inst: usize,
}

pub enum Reject {
    Unsupported { path: Vec<u8>, what: Vec<u8>, site: Vec<u8> },
    Unresolved { path: Vec<u8>, callee: Vec<u8>, site: Vec<u8> },
    Attr { path: Vec<u8>, msg: Vec<u8> },
    Root { path: Vec<u8>, msg: Vec<u8> },
}

pub fn copy_bytes(s: &Vec<u8>) -> (v: Vec<u8>)
    ensures v@ == s@,
{
    msg(s.as_slice())
}

// ------------------------------------------------------------------ places and operands

pub fn x_proj_ty(m: &MirCrate, t: Ty, e: &ProjectionElem) -> (r: Option<Ty>)
    ensures r == proj_ty(*m, t, *e),
{
    match e {
        ProjectionElem::Deref => match x_rigid(m, t) { Some(RigidTy::Ref(_, p, _)) => Some(*p), _ => None },
        ProjectionElem::Field(_, ft) => Some(*ft),
        ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => match x_rigid(m, t) {
            Some(RigidTy::Array(el, _)) => Some(*el),
            Some(RigidTy::Slice(el)) => Some(*el),
            _ => None,
        },
        ProjectionElem::Downcast(_) => Some(t),
        _ => None,
    }
}

proof fn lemma_tys_none(m: MirCrate, t: Ty, ps: Seq<ProjectionElem>, k: nat, n: nat)
    requires k <= n, tys_along(m, t, ps, k) is None,
    ensures tys_along(m, t, ps, n) is None,
    decreases n - k,
{
    if k < n { lemma_tys_none(m, t, ps, k, (n - 1) as nat); }
}

pub fn x_place_ty(m: &MirCrate, b: &Body, p: &Place) -> (r: Option<Ty>)
    ensures r == place_ty(*m, *b, *p),
{
    if p.local >= b.locals.len() { return None; }
    let mut u = b.locals[p.local].ty;
    let mut k: usize = 0;
    while k < p.projection.len()
        invariant k <= p.projection@.len(), p.local < b.locals@.len(),
            tys_along(*m, b.locals@[p.local as int].ty, p.projection@, k as nat) == Some(u),
        decreases p.projection.len() - k,
    {
        u = match x_proj_ty(m, u, &p.projection[k]) {
            Some(v) => v,
            None => {
                proof { lemma_tys_none(*m, b.locals@[p.local as int].ty, p.projection@, (k + 1) as nat, p.projection@.len()); }
                return None;
            },
        };
        k += 1;
    }
    Some(u)
}

pub fn x_op_ty(m: &MirCrate, b: &Body, x: &Operand) -> (r: Option<Ty>)
    ensures r == op_ty(*m, *b, *x),
{
    match x {
        Operand::Copy(p) | Operand::Move(p) => x_place_ty(m, b, p),
        Operand::Constant(k) => Some(k.const_.ty),
        _ => None,
    }
}

/// A place: its projections at their types (`place_ok`), no `Deref` of a `&mut` once a shared
/// `Deref` has entered a snapshot (core reads `Unit` there), no `ConstantIndex` from the end.
pub fn lower_place(m: &MirCrate, b: &Body, p: &Place, mutating: bool) -> (r: Result<c::Place, Vec<u8>>)
    ensures r matches Ok(q) ==> lowers_place(*m, *b, *p, q, mutating),
{
    if p.local >= b.locals.len() { return Err(msg(b"place of an unknown local")); }
    let ghost t0 = b.locals@[p.local as int].ty;
    let ghost ps = p.projection@;
    let mut u = b.locals[p.local].ty;
    let mut sn = false;
    let mut proj: Vec<c::Proj> = Vec::new();
    let mut k: usize = 0;
    while k < p.projection.len()
        invariant
            k <= ps.len(), ps == p.projection@, p.local < b.locals@.len(), t0 == b.locals@[p.local as int].ty,
            tys_along(*m, t0, ps, k as nat) == Some(u), path_ok(*m, *b, t0, ps, k as nat, mutating), sn == snap(*m, t0, ps, k as nat),
            proj@.len() == k, forall|i: int| 0 <= i < k ==> lowers_proj(#[trigger] ps[i], proj@[i]),
            forall|i: int| 0 <= i < k && (#[trigger] ps[i]) is Deref && snap(*m, t0, ps, i as nat)
                ==> !(tys_along(*m, t0, ps, i as nat) matches Some(v) && is_mut_ref(*m, v)),
        decreases p.projection.len() - k,
    {
        let e = &p.projection[k];
        let q = match e {
            ProjectionElem::Deref => {
                match x_rigid(m, u) {
                    Some(RigidTy::Ref(_, pt, mu)) => {
                        if matches!(x_rigid(m, *pt), Some(RigidTy::Str)) { return Err(msg(b"a deref of &str")); }
                        match mu {
                            Mutability::Mut => if sn { return Err(msg(b"a deref of a &mut under a shared reference")); },
                            Mutability::Not => {
                                if mutating { return Err(msg(b"a write through a shared reference")); }
                                sn = true;
                            },
                            Mutability::Unknown(_) => return Err(msg(b"unknown mutability")),
                        }
                    },
                    _ => return Err(msg(b"a deref of a non-reference")),
                }
                c::Proj::Deref
            },
            ProjectionElem::Field(i, _) => c::Proj::Field(*i),
            ProjectionElem::Index(l) => {
                if *l >= b.locals.len() { return Err(msg(b"an index by an unknown local")); }
                c::Proj::Index(*l)
            },
            ProjectionElem::ConstantIndex { offset, min_length: _, from_end } => {
                if *from_end { return Err(msg(b"projection ConstantIndex from the end")); }
                c::Proj::ConstIndex(*offset)
            },
            ProjectionElem::Downcast(v) => c::Proj::Downcast(*v),
            _ => return Err(msg(b"projection outside the subset (Subslice, OpaqueCast, ..)")),
        };
        let u2 = match x_proj_ty(m, u, e) { Some(v) => v, None => return Err(msg(b"a projection at the wrong type")) };
        proof {
            assert(tys_along(*m, t0, ps, (k + 1) as nat) == Some(u2));
            assert(path_ok(*m, *b, t0, ps, (k + 1) as nat, mutating));
        }
        u = u2;
        proj.push(q);
        k += 1;
    }
    Ok(c::Place { local: p.local, proj })
}

/// An operand's image: its temps have the operand's charge and start at `base`; it is `op_ok`.
pub proof fn lemma_op_shape(m: MirCrate, b: Body, x: Operand, y: c::Operand, pre: Seq<c::Stmt>, base: nat)
    requires lowers_op(m, b, x, y, pre, base),
    ensures pre.len() == op_charge(m, x), temps_at(pre, base), op_ok(m, b, x),
{
}

pub fn lower_op(m: &MirCrate, b: &Body, x: &Operand, tmp: &mut Tmp) -> (r: Result<c::Operand, Vec<u8>>)
    ensures r matches Ok(y) ==> grew(*old(tmp), *final(tmp)) && lowers_op(*m, *b, *x, y, seg(*old(tmp), *final(tmp)), tbase(*old(tmp))),
{
    proof { lemma_no_temps(*tmp); }
    match x {
        Operand::Copy(p) | Operand::Move(p) => Ok(c::Operand::Copy(lower_place(m, b, p, false)?)),
        Operand::Constant(k) => x_const(m, k, tmp),
        Operand::RuntimeChecks(_) => Err(msg(b"a RuntimeChecks operand")),
        Operand::Unknown(_) => Err(msg(b"an unknown operand")),
    }
}

/// An operand of int or `bool` type, with that type.
pub fn lower_int_op(m: &MirCrate, b: &Body, x: &Operand, tmp: &mut Tmp) -> (r: Result<(c::Operand, c::IntTy), Vec<u8>>)
    ensures r matches Ok((y, it)) ==> grew(*old(tmp), *final(tmp)) && int_at(*m, *b, *x, it) && int_op(*m, *b, *x)
        && lowers_op(*m, *b, *x, y, seg(*old(tmp), *final(tmp)), tbase(*old(tmp))),
{
    let it = match x_op_ty(m, b, x) {
        Some(t) => match x_int_ty(m, t) { Some(it) => it, None => return Err(msg(b"non-integer operand type")) },
        None => return Err(msg(b"operand type")),
    };
    let y = lower_op(m, b, x, tmp)?;
    proof { lemma_op_shape(*m, *b, *x, y, seg(*old(tmp), *tmp), tbase(*old(tmp))); }
    Ok((y, it))
}

proof fn lemma_oc_mono(m: MirCrate, xs: Seq<Operand>, j: nat, n: nat)
    requires j <= n <= xs.len(),
    ensures ops_charge(m, xs, j) <= ops_charge(m, xs, n),
    decreases n - j,
{
    if j < n { lemma_oc_mono(m, xs, j, (n - 1) as nat); }
}

/// Operands left to right, their temps one after another.
#[verifier::loop_isolation(false)]
pub fn lower_ops(m: &MirCrate, b: &Body, xs: &Vec<Operand>, tmp: &mut Tmp) -> (r: Result<Vec<c::Operand>, Vec<u8>>)
    ensures r matches Ok(ys) ==> grew(*old(tmp), *final(tmp)) && temps_at(seg(*old(tmp), *final(tmp)), tbase(*old(tmp)))
        && lowers_ops(*m, *b, xs@, ys@, seg(*old(tmp), *final(tmp)), tbase(*old(tmp))) && ops_ok(*m, *b, xs@),
{
    let ghost t0 = *old(tmp);
    let ghost base = tbase(t0);
    proof { lemma_no_temps(*tmp); }
    let mut ys: Vec<c::Operand> = Vec::new();
    let mut k: usize = 0;
    while k < xs.len()
        invariant
            k <= xs@.len(), t0 == *old(tmp), base == tbase(t0),
            grew(t0, *tmp), temps_at(seg(t0, *tmp), base), ys@.len() == k, seg(t0, *tmp).len() == ops_charge(*m, xs@, k as nat),
            forall|i: int| 0 <= i < k ==> lowers_op(*m, *b, #[trigger] xs@[i], ys@[i],
                seg(t0, *tmp).subrange(ops_charge(*m, xs@, i as nat) as int, ops_charge(*m, xs@, (i + 1) as nat) as int),
                base + ops_charge(*m, xs@, i as nat)),
            forall|i: int| 0 <= i < k ==> op_ok(*m, *b, #[trigger] xs@[i]),
        decreases xs.len() - k,
    {
        let ghost t1 = *tmp;
        let y = lower_op(m, b, &xs[k], tmp)?;
        proof { lemma_ops_step(*m, *b, xs@, k as nat, t0, t1, *tmp, ys@, y); }
        ys.push(y);
        k += 1;
    }
    Ok(ys)
}

proof fn lemma_ops_step(m: MirCrate, b: Body, xs: Seq<Operand>, k: nat, t0: Tmp, t1: Tmp, t2: Tmp, ys: Seq<c::Operand>, y: c::Operand)
    requires
        k < xs.len(), ys.len() == k, grew(t0, t1), temps_at(seg(t0, t1), tbase(t0)), seg(t0, t1).len() == ops_charge(m, xs, k),
        forall|i: int| 0 <= i < k ==> lowers_op(m, b, #[trigger] xs[i], ys[i],
            seg(t0, t1).subrange(ops_charge(m, xs, i as nat) as int, ops_charge(m, xs, (i + 1) as nat) as int), tbase(t0) + ops_charge(m, xs, i as nat)),
        forall|i: int| 0 <= i < k ==> op_ok(m, b, #[trigger] xs[i]),
        grew(t1, t2), lowers_op(m, b, xs[k as int], y, seg(t1, t2), tbase(t1)),
    ensures
        grew(t0, t2), temps_at(seg(t0, t2), tbase(t0)), seg(t0, t2).len() == ops_charge(m, xs, k + 1),
        forall|i: int| 0 <= i < k + 1 ==> lowers_op(m, b, #[trigger] xs[i], ys.push(y)[i],
            seg(t0, t2).subrange(ops_charge(m, xs, i as nat) as int, ops_charge(m, xs, (i + 1) as nat) as int), tbase(t0) + ops_charge(m, xs, i as nat)),
        forall|i: int| 0 <= i < k + 1 ==> op_ok(m, b, #[trigger] xs[i]),
{
    lemma_op_shape(m, b, xs[k as int], y, seg(t1, t2), tbase(t1));
    lemma_seg_trans(t0, t1, t2);
    assert forall|i: int| 0 <= i < k + 1 implies lowers_op(m, b, #[trigger] xs[i], ys.push(y)[i],
        seg(t0, t2).subrange(ops_charge(m, xs, i as nat) as int, ops_charge(m, xs, (i + 1) as nat) as int), tbase(t0) + ops_charge(m, xs, i as nat)) by {
        if i < k {
            lemma_oc_mono(m, xs, (i + 1) as nat, k);
            lemma_oc_mono(m, xs, i as nat, (i + 1) as nat);
            assert(seg(t0, t2).subrange(ops_charge(m, xs, i as nat) as int, ops_charge(m, xs, (i + 1) as nat) as int)
                =~= seg(t0, t1).subrange(ops_charge(m, xs, i as nat) as int, ops_charge(m, xs, (i + 1) as nat) as int));
        } else {
            assert(ys.push(y)[i] == y);
            assert(seg(t0, t2).subrange(ops_charge(m, xs, i as nat) as int, ops_charge(m, xs, (i + 1) as nat) as int) =~= seg(t1, t2));
        }
    };
}

// ------------------------------------------------------------------ rvalues and statements

/// The wrapping binary operators (no `*Unchecked`, `Cmp` or `Offset`, as the old translator).
pub fn lower_binop(op: &BinOp) -> (r: Option<c::BinOp>)
    ensures r matches Some(o) ==> core_bin(*op) == Some(o),
{
    match op {
        BinOp::Add => Some(c::BinOp::Add), BinOp::Sub => Some(c::BinOp::Sub), BinOp::Mul => Some(c::BinOp::Mul),
        BinOp::Div => Some(c::BinOp::Div), BinOp::Rem => Some(c::BinOp::Rem), BinOp::BitXor => Some(c::BinOp::BitXor),
        BinOp::BitAnd => Some(c::BinOp::BitAnd), BinOp::BitOr => Some(c::BinOp::BitOr), BinOp::Shl => Some(c::BinOp::Shl),
        BinOp::Shr => Some(c::BinOp::Shr), BinOp::Eq => Some(c::BinOp::Eq), BinOp::Ne => Some(c::BinOp::Ne),
        BinOp::Lt => Some(c::BinOp::Lt), BinOp::Le => Some(c::BinOp::Le), BinOp::Gt => Some(c::BinOp::Gt),
        BinOp::Ge => Some(c::BinOp::Ge),
        _ => None,
    }
}

fn is_signed(it: &c::IntTy) -> (r: bool)
    ensures r == ctcore::sem::signed(*it),
{
    matches!(it, c::IntTy::I8 | c::IntTy::I16 | c::IntTy::I32 | c::IntTy::I64 | c::IntTy::I128 | c::IntTy::Isize)
}

/// The postcondition every rvalue lowering shares.
pub open spec fn rv_post(m: MirCrate, b: Body, rv: Rvalue, cr: c::Rvalue, t0: Tmp, t1: Tmp) -> bool {
    grew(t0, t1) && rv_ok(m, b, rv) && lowers_rv(m, b, rv, cr, seg(t0, t1), tbase(t0))
}

pub fn lower_rv(m: &MirCrate, b: &Body, rv: &Rvalue, tmp: &mut Tmp) -> (r: Result<c::Rvalue, Vec<u8>>)
    ensures r matches Ok(cr) ==> rv_post(*m, *b, *rv, cr, *old(tmp), *final(tmp)),
{
    match rv {
        Rvalue::Use(x, _) => {
            let y = lower_op(m, b, x, tmp)?;
            proof { lemma_op_shape(*m, *b, *x, y, seg(*old(tmp), *tmp), tbase(*old(tmp))); }
            Ok(c::Rvalue::Use(y))
        },
        Rvalue::BinaryOp(_, _, _) => lower_rv_bin(m, b, rv, tmp),
        Rvalue::UnaryOp(_, _) => lower_rv_un(m, b, rv, tmp),
        Rvalue::Cast(_, _, _) => lower_rv_cast(m, b, rv, tmp),
        Rvalue::Aggregate(ak, xs) => {
            let kind = match ak {
                AggregateKind::Array(_) => c::AggKind::Array,
                AggregateKind::Tuple => c::AggKind::Tuple,
                AggregateKind::Adt(_, v, _, _, None) => c::AggKind::Adt(*v),
                _ => return Err(msg(b"an aggregate outside the subset (closure, union, raw pointer)")),
            };
            Ok(c::Rvalue::Aggregate(kind, lower_ops(m, b, xs, tmp)?))
        },
        Rvalue::Repeat(x, n) => match x_const_usize(m, n.id) {
            Some(k) => {
                let y = lower_op(m, b, x, tmp)?;
                proof { lemma_op_shape(*m, *b, *x, y, seg(*old(tmp), *tmp), tbase(*old(tmp))); }
                Ok(c::Rvalue::Repeat(y, k))
            },
            None => Err(msg(b"repeat count")),
        },
        _ => {
            proof { lemma_no_temps(*tmp); }
            lower_rv_place(m, b, rv)
        },
    }
}

pub fn lower_rv_bin(m: &MirCrate, b: &Body, rv: &Rvalue, tmp: &mut Tmp) -> (r: Result<c::Rvalue, Vec<u8>>)
    requires rv is BinaryOp,
    ensures r matches Ok(cr) ==> rv_post(*m, *b, *rv, cr, *old(tmp), *final(tmp)),
{
    let (op, x, y) = match rv { Rvalue::BinaryOp(op, x, y) => (op, x, y), _ => return Err(msg(b"?")) };
    let cop = match lower_binop(op) { Some(o) => o, None => return Err(msg(b"binary operator outside the subset")) };
    let ghost t0 = *old(tmp);
    let (cx, it) = lower_int_op(m, b, x, tmp)?;
    let ghost t1 = *tmp;
    let (cy, _) = lower_int_op(m, b, y, tmp)?;
    proof {
        lemma_op_shape(*m, *b, *x, cx, seg(t0, t1), tbase(t0));
        lemma_op_shape(*m, *b, *y, cy, seg(t1, *tmp), tbase(t1));
        lemma_seg_trans(t0, t1, *tmp);
    }
    Ok(c::Rvalue::Bin(cop, it, cx, cy))
}

pub fn lower_rv_un(m: &MirCrate, b: &Body, rv: &Rvalue, tmp: &mut Tmp) -> (r: Result<c::Rvalue, Vec<u8>>)
    requires rv is UnaryOp,
    ensures r matches Ok(cr) ==> rv_post(*m, *b, *rv, cr, *old(tmp), *final(tmp)),
{
    let (op, x) = match rv { Rvalue::UnaryOp(op, x) => (op, x), _ => return Err(msg(b"?")) };
    match op {
        UnOp::Not => { let (cx, it) = lower_int_op(m, b, x, tmp)?; Ok(c::Rvalue::Un(c::UnOp::Not, it, cx)) },
        UnOp::Neg => {
            let (cx, it) = lower_int_op(m, b, x, tmp)?;
            if !is_signed(&it) { return Err(msg(b"negation of an unsigned int")); }
            Ok(c::Rvalue::Un(c::UnOp::Neg, it, cx))
        },
        UnOp::PtrMetadata => {
            proof { lemma_no_temps(*tmp); }
            let slice_ref = match x_op_ty(m, b, x) {
                Some(t) => match x_rigid(m, t) {
                    Some(RigidTy::Ref(_, p, _)) => matches!(x_rigid(m, *p), Some(RigidTy::Slice(_))),
                    _ => false,
                },
                None => false,
            };
            match x {
                Operand::Copy(p) | Operand::Move(p) => if slice_ref { Ok(c::Rvalue::Len(lower_place(m, b, p, false)?)) } else {
                    Err(msg(b"PtrMetadata of a non-slice reference"))
                },
                _ => Err(msg(b"PtrMetadata of a constant")),
            }
        },
        UnOp::Unknown(_) => Err(msg(b"an unknown unary operator")),
    }
}

pub fn lower_rv_cast(m: &MirCrate, b: &Body, rv: &Rvalue, tmp: &mut Tmp) -> (r: Result<c::Rvalue, Vec<u8>>)
    requires rv is Cast,
    ensures r matches Ok(cr) ==> rv_post(*m, *b, *rv, cr, *old(tmp), *final(tmp)),
{
    let (ck, x, to) = match rv { Rvalue::Cast(ck, x, to) => (ck, x, to), _ => return Err(msg(b"?")) };
    match ck {
        CastKind::IntToInt => {
            let it = match x_int_ty(m, *to) { Some(it) => it, None => return Err(msg(b"cast to a non-integer type")) };
            let (cx, from) = lower_int_op(m, b, x, tmp)?;
            Ok(c::Rvalue::Cast(from, it, cx))
        },
        CastKind::PointerCoercion(PointerCoercion::Unsize) => {
            let ok = match x_op_ty(m, b, x) {
                Some(tx) => match (x_rigid(m, tx), x_rigid(m, *to)) {
                    (Some(RigidTy::Ref(_, p, _)), Some(RigidTy::Ref(_, q, _))) =>
                        matches!(x_rigid(m, *p), Some(RigidTy::Array(_, _))) && matches!(x_rigid(m, *q), Some(RigidTy::Slice(_))),
                    _ => false,
                },
                None => false,
            };
            if !ok { return Err(msg(b"an unsize cast other than array to slice")); }
            let y = lower_op(m, b, x, tmp)?;
            proof { lemma_op_shape(*m, *b, *x, y, seg(*old(tmp), *tmp), tbase(*old(tmp))); }
            Ok(c::Rvalue::Use(y))
        },
        CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_)) => {
            // the erased `Ghost(..)` argument: a closure constant, the opaque `Unit`
            let ok = match x {
                Operand::Constant(k) => matches!(k.const_.kind, ConstantKind::ZeroSized)
                    && matches!(x_rigid(m, k.const_.ty), Some(RigidTy::Closure(_, _))),
                _ => false,
            };
            if !ok { return Err(msg(b"a fn-pointer cast of a non-constant closure")); }
            let y = lower_op(m, b, x, tmp)?;
            proof { lemma_op_shape(*m, *b, *x, y, seg(*old(tmp), *tmp), tbase(*old(tmp))); }
            Ok(c::Rvalue::Use(y))
        },
        _ => Err(msg(b"a cast outside the subset")),
    }
}

/// Rvalues over a place (no temps): borrows, `Len`, `Discriminant`, `CopyForDeref`.
pub fn lower_rv_place(m: &MirCrate, b: &Body, rv: &Rvalue) -> (r: Result<c::Rvalue, Vec<u8>>)
    ensures r matches Ok(cr) ==> rv_ok(*m, *b, *rv) && lowers_rv(*m, *b, *rv, cr, Seq::<c::Stmt>::empty(), 0),
            r matches Ok(cr) ==> forall|base: nat| lowers_rv(*m, *b, *rv, cr, Seq::<c::Stmt>::empty(), base),
{
    match rv {
        Rvalue::Ref(_, bk, p) => match bk {
            BorrowKind::Shared => Ok(c::Rvalue::RefShr(lower_place(m, b, p, false)?)),
            BorrowKind::Mut { .. } => Ok(c::Rvalue::RefMut(lower_place(m, b, p, true)?)),
            _ => Err(msg(b"a fake borrow")),
        },
        Rvalue::Len(p) => {
            let ok = match x_place_ty(m, b, p) {
                Some(t) => matches!(x_rigid(m, t), Some(RigidTy::Array(_, _))) || matches!(x_rigid(m, t), Some(RigidTy::Slice(_))),
                None => false,
            };
            if ok { Ok(c::Rvalue::Len(lower_place(m, b, p, false)?)) } else { Err(msg(b"Len of a non-array")) }
        },
        Rvalue::Discriminant(p) => {
            // core `Discr` reads the variant index; MIR's discriminant is the variant's `discr`
            let ok = match x_place_ty(m, b, p) {
                Some(t) => match x_adt_row(m, t) {
                    Some(a) => match a.kind {
                        AdtKind::Struct => true,
                        AdtKind::Enum => discr_is_index(a),
                        _ => false,
                    },
                    None => false,
                },
                None => false,
            };
            if ok { Ok(c::Rvalue::Discr(lower_place(m, b, p, false)?)) } else {
                Err(msg(b"discriminant of an enum with explicit discriminants (or a non-ADT)"))
            }
        },
        Rvalue::CopyForDeref(p) => Ok(c::Rvalue::Use(c::Operand::Copy(lower_place(m, b, p, false)?))),
        _ => Err(msg(b"rvalue outside the subset")),
    }
}

/// Every variant's discriminant is its index.
pub fn discr_is_index(a: &Adt) -> (r: bool)
    ensures r ==> forall|k: int| 0 <= k < a.variants@.len() ==> (#[trigger] a.variants@[k]).discr == Some(k as u128),
{
    let mut k: usize = 0;
    while k < a.variants.len()
        invariant k <= a.variants@.len(), forall|i: int| 0 <= i < k ==> (#[trigger] a.variants@[i]).discr == Some(i as u128),
        decreases a.variants.len() - k,
    {
        match a.variants[k].discr { Some(d) => if d != k as u128 { return false; }, None => return false }
        k += 1;
    }
    true
}

/// `tys` grew by at least as many temps as `pre` (a drop's destination temp has no assignment).
pub open spec fn grew2(old: Tmp, new: Tmp) -> bool {
    &&& new.nloc == old.nloc && new.pre@.len() >= old.pre@.len() && new.pre@.subrange(0, old.pre@.len() as int) == old.pre@
    &&& new.tys@.len() - old.tys@.len() >= new.pre@.len() - old.pre@.len()
}

/// A statement's image is `pre` then `st` (none for a no-op statement).
pub fn lower_stmt(m: &MirCrate, b: &Body, s: &Statement, tmp: &mut Tmp) -> (r: Result<Option<c::Stmt>, Vec<u8>>)
    requires old(tmp).nloc == b.locals@.len(), old(tmp).pre@.len() == 0,
    ensures r matches Ok(o) ==> grew2(*old(tmp), *final(tmp)) && match o {
        Some(st) => lowers_stmt(*m, *b, b.locals@.len(), tbase(*final(tmp)), *s, final(tmp).pre@.push(st)),
        None => final(tmp).pre@.len() == 0 && lowers_stmt(*m, *b, b.locals@.len(), tbase(*final(tmp)), *s, Seq::<c::Stmt>::empty()),
    },
{
    match &s.kind {
        StatementKind::Assign(p, rv) => {
            let cp = lower_place(m, b, p, true)?;
            let ghost t0 = *tmp;
            let cr = lower_rv(m, b, rv, tmp)?;
            let st = c::Stmt::Assign(cp, cr);
            proof {
                let cs = tmp.pre@.push(st);
                assert(cs.drop_last() =~= seg(t0, *tmp));
                assert(tmps_in(tbase(t0), (cs.len() - 1) as nat, b.locals@.len(), tbase(*tmp)));
                assert(lowers_rv(*m, *b, *rv, cs.last()->Assign_1, cs.drop_last(), tbase(t0)));
            }
            Ok(Some(st))
        },
        StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop | StatementKind::FakeRead(_, _)
        | StatementKind::PlaceMention(_) | StatementKind::AscribeUserType { .. } | StatementKind::Coverage(_)
        | StatementKind::ConstEvalCounter => {
            proof { lemma_no_temps(*tmp); }
            Ok(None)
        },
        StatementKind::SetDiscriminant { .. } => Err(msg(b"statement SetDiscriminant")),
        StatementKind::Intrinsic(_) => Err(msg(b"statement Intrinsic")),
        StatementKind::Unknown(_) => Err(msg(b"an unknown statement")),
    }
}

} // verus!
