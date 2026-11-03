//! The MIR → core translator (verified against `rel::lowers`). It lowers the closure of one root:
//! internal callees (by the policy's crate rules) and drop glue as core fns, leaves (policy and
//! std-model calls) as intrinsics, anything else `Unresolved`. MIR locals and blocks map 1:1;
//! blocks off the normal-edge reachable set become empty `Abort` blocks, and fresh temps (after
//! the MIR locals) hold constants and drop-glue arguments.
use crate::json::bytes_eq;
use crate::look::*;
use crate::lower_const::*;
use crate::mir::*;
use crate::policy::*;
#[cfg(verus_keep_ghost)]
use crate::sem::*;
use crate::sem::StdFn;
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

fn copy_bytes(s: &Vec<u8>) -> (v: Vec<u8>)
    ensures v@ == s@,
{
    msg(s.as_slice())
}

fn push_dec(v: &mut Vec<u8>, n: usize)
    decreases n,
{
    if n >= 10 { push_dec(v, n / 10); }
    v.push((b'0' as usize + n % 10) as u8);
}

/// `<file>:<line>` of a span, or `?`.
pub fn site(m: &MirCrate, sp: Span) -> Vec<u8> {
    match x_span(m, sp) {
        Some(r) => {
            let mut v = copy_bytes(&r.file);
            v.push(b':');
            push_dec(&mut v, r.line);
            v
        },
        None => msg(b"?"),
    }
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

pub fn x_place_ty(m: &MirCrate, b: &Body, p: &Place) -> (r: Option<Ty>)
    ensures r == place_ty(*m, *b, *p),
{
    if p.local >= b.locals.len() { return None; }
    let mut u = b.locals[p.local].ty;
    let mut k: usize = 0;
    while k < p.projection.len()
        invariant k <= p.projection@.len(), tys_along(*m, b.locals@[p.local as int].ty, p.projection@, k as nat) == Some(u),
        decreases p.projection.len() - k,
    {
        u = match x_proj_ty(m, u, &p.projection[k]) { Some(v) => v, None => return None };
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
pub fn lower_place(m: &MirCrate, b: &Body, p: &Place, mutating: bool) -> (r: Result<c::Place, Vec<u8>>) {
    if p.local >= b.locals.len() { return Err(msg(b"place of an unknown local")); }
    let mut u = b.locals[p.local].ty;
    let mut snap = false;
    let mut proj: Vec<c::Proj> = Vec::new();
    let mut k: usize = 0;
    while k < p.projection.len()
        invariant k <= p.projection@.len(),
        decreases p.projection.len() - k,
    {
        let e = &p.projection[k];
        let q = match e {
            ProjectionElem::Deref => {
                match x_rigid(m, u) {
                    Some(RigidTy::Ref(_, pt, mu)) => {
                        if matches!(x_rigid(m, *pt), Some(RigidTy::Str)) { return Err(msg(b"a deref of &str")); }
                        match mu {
                            Mutability::Mut => if snap { return Err(msg(b"a deref of a &mut under a shared reference")); },
                            Mutability::Not => {
                                if mutating { return Err(msg(b"a write through a shared reference")); }
                                snap = true;
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
        u = match x_proj_ty(m, u, e) { Some(v) => v, None => return Err(msg(b"a projection at the wrong type")) };
        proj.push(q);
        k += 1;
    }
    Ok(c::Place { local: p.local, proj })
}

pub fn lower_op(m: &MirCrate, b: &Body, x: &Operand, tmp: &mut Tmp) -> (r: Result<c::Operand, Vec<u8>>) {
    match x {
        Operand::Copy(p) | Operand::Move(p) => Ok(c::Operand::Copy(lower_place(m, b, p, false)?)),
        Operand::Constant(k) => x_const(m, k, tmp),
        Operand::RuntimeChecks(_) => Err(msg(b"a RuntimeChecks operand")),
        Operand::Unknown(_) => Err(msg(b"an unknown operand")),
    }
}

/// An operand of int or `bool` type, with that type.
pub fn lower_int_op(m: &MirCrate, b: &Body, x: &Operand, tmp: &mut Tmp) -> (r: Result<(c::Operand, c::IntTy), Vec<u8>>) {
    let it = match x_op_ty(m, b, x) {
        Some(t) => match x_int_ty(m, t) { Some(it) => it, None => return Err(msg(b"non-integer operand type")) },
        None => return Err(msg(b"operand type")),
    };
    Ok((lower_op(m, b, x, tmp)?, it))
}

pub fn lower_ops(m: &MirCrate, b: &Body, xs: &Vec<Operand>, tmp: &mut Tmp) -> (r: Result<Vec<c::Operand>, Vec<u8>>) {
    let mut ys: Vec<c::Operand> = Vec::new();
    let mut k: usize = 0;
    while k < xs.len()
        invariant k <= xs@.len(),
        decreases xs.len() - k,
    {
        ys.push(lower_op(m, b, &xs[k], tmp)?);
        k += 1;
    }
    Ok(ys)
}

// ------------------------------------------------------------------ rvalues and statements

/// The wrapping binary operators (no `*Unchecked`, `Cmp` or `Offset`, as the old translator).
pub fn lower_binop(op: &BinOp) -> (r: Option<c::BinOp>) {
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

fn is_signed(it: &c::IntTy) -> bool {
    matches!(it, c::IntTy::I8 | c::IntTy::I16 | c::IntTy::I32 | c::IntTy::I64 | c::IntTy::I128 | c::IntTy::Isize)
}

pub fn lower_rv(m: &MirCrate, b: &Body, rv: &Rvalue, tmp: &mut Tmp) -> (r: Result<c::Rvalue, Vec<u8>>) {
    match rv {
        Rvalue::Use(x, _) => Ok(c::Rvalue::Use(lower_op(m, b, x, tmp)?)),
        Rvalue::BinaryOp(op, x, y) => {
            let cop = match lower_binop(op) { Some(o) => o, None => return Err(msg(b"binary operator outside the subset")) };
            let (cx, it) = lower_int_op(m, b, x, tmp)?;
            let (cy, _) = lower_int_op(m, b, y, tmp)?;
            Ok(c::Rvalue::Bin(cop, it, cx, cy))
        },
        Rvalue::UnaryOp(op, x) => match op {
            UnOp::Not => { let (cx, it) = lower_int_op(m, b, x, tmp)?; Ok(c::Rvalue::Un(c::UnOp::Not, it, cx)) },
            UnOp::Neg => {
                let (cx, it) = lower_int_op(m, b, x, tmp)?;
                if !is_signed(&it) { return Err(msg(b"negation of an unsigned int")); }
                Ok(c::Rvalue::Un(c::UnOp::Neg, it, cx))
            },
            UnOp::PtrMetadata => {
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
        },
        Rvalue::Cast(ck, x, to) => match ck {
            CastKind::IntToInt => {
                let (cx, from) = lower_int_op(m, b, x, tmp)?;
                match x_int_ty(m, *to) { Some(it) => Ok(c::Rvalue::Cast(from, it, cx)), None => Err(msg(b"cast to a non-integer type")) }
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
                if ok { Ok(c::Rvalue::Use(lower_op(m, b, x, tmp)?)) } else { Err(msg(b"an unsize cast other than array to slice")) }
            },
            CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_)) => {
                // the erased `Ghost(..)` argument: a closure constant, the opaque `Unit`
                let ok = match x {
                    Operand::Constant(k) => matches!(k.const_.kind, ConstantKind::ZeroSized)
                        && matches!(x_rigid(m, k.const_.ty), Some(RigidTy::Closure(_, _))),
                    _ => false,
                };
                if ok { Ok(c::Rvalue::Use(lower_op(m, b, x, tmp)?)) } else { Err(msg(b"a fn-pointer cast of a non-constant closure")) }
            },
            _ => Err(msg(b"a cast outside the subset")),
        },
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
            Some(k) => Ok(c::Rvalue::Repeat(lower_op(m, b, x, tmp)?, k)),
            None => Err(msg(b"repeat count")),
        },
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
        if a.variants[k].discr != Some(k as u128) { return false; }
        k += 1;
    }
    true
}

pub fn lower_stmt(m: &MirCrate, b: &Body, s: &Statement, tmp: &mut Tmp) -> (r: Result<Option<c::Stmt>, Vec<u8>>) {
    match &s.kind {
        StatementKind::Assign(p, rv) => {
            let cp = lower_place(m, b, p, true)?;
            Ok(Some(c::Stmt::Assign(cp, lower_rv(m, b, rv, tmp)?)))
        },
        StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop | StatementKind::FakeRead(_, _)
        | StatementKind::PlaceMention(_) | StatementKind::AscribeUserType { .. } | StatementKind::Coverage(_)
        | StatementKind::ConstEvalCounter => Ok(None),
        StatementKind::SetDiscriminant { .. } => Err(msg(b"statement SetDiscriminant")),
        StatementKind::Intrinsic(_) => Err(msg(b"statement Intrinsic")),
        StatementKind::Unknown(_) => Err(msg(b"an unknown statement")),
    }
}

// ------------------------------------------------------------------ the closure

/// The closure being lowered: the `insts` index of each core fn, and the keys bound so far
/// (key, def, the instance for an internal fn or root, `None` for a leaf).
pub struct Tr { pub order: Vec<usize>, pub keys: Vec<(Vec<u8>, DefId, Option<usize>)> }

pub fn fn_index(tr: &mut Tr, j: usize) -> (g: usize) {
    let mut g: usize = 0;
    while g < tr.order.len()
        invariant g <= tr.order@.len(),
        decreases tr.order.len() - g,
    {
        if tr.order[g] == j { return g; }
        g += 1;
    }
    tr.order.push(j);
    g
}

/// Binds `key` to `(def, inst)`; `false` when it names something else already (`ct_key` drops
/// generic args, so distinct fns can share one).
pub fn bind(tr: &mut Tr, key: &[u8], def: DefId, inst: Option<usize>) -> bool {
    let mut k: usize = 0;
    while k < tr.keys.len()
        invariant k <= tr.keys@.len(),
        decreases tr.keys.len() - k,
    {
        if bytes_eq(tr.keys[k].0.as_slice(), key) { return tr.keys[k].1 == def && tr.keys[k].2 == inst; }
        k += 1;
    }
    tr.keys.push((msg(key), def, inst));
    true
}

/// A callee entered as a core fn: an `Item` with a body, in the dump's crate or a policy crate.
pub fn is_internal(m: &MirCrate, pol: &Policy, j: usize) -> (r: bool) {
    if j >= m.insts.len() { return false; }
    let x = &m.insts[j];
    matches!(x.kind, InstanceKind::Item) && x.body.is_some()
        && (bytes_eq(x.krate.as_slice(), m.crate_name.as_slice()) || has_exec(&pol.internal_crates, x.krate.as_slice())
            || has_exec(&pol.translate_crates, x.krate.as_slice()))
}

pub fn x_intr_of(m: &MirCrate, pol: &Policy, key: &[u8], g: &GenericArgs) -> (r: Option<c::Intrinsic>) {
    if has_exec(&pol.declassify, key) { return Some(c::Intrinsic::Declassify); }
    if has_exec(&pol.ghost_unit, key) { return Some(c::Intrinsic::GhostUnit); }
    match x_std_model(m, key, g) {
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

/// `leaf_ok`: arity, and a ghost result's type.
pub fn x_leaf_ok(m: &MirCrate, pol: &Policy, key: &[u8], g: &GenericArgs, n: usize, dty: Option<Ty>) -> (r: bool) {
    let ghost_dest = match dty { Some(t) => x_zst_dest(m, t), None => false };
    if has_exec(&pol.declassify, key) { return n == 1; }
    if has_exec(&pol.ghost_unit, key) { return ghost_dest; }
    match x_std_model(m, key, g) {
        Some(f) => match f {
            StdFn::VecNew => n == 0,
            StdFn::VecWithCapacity | StdFn::VecAsSlice | StdFn::ArrayAsSlice | StdFn::VecLen | StdFn::SliceToVec => n == 1,
            StdFn::VecPush | StdFn::VecExtendFromSlice | StdFn::VecIndex | StdFn::Wrapping(_, _) => n == 2,
            StdFn::VecSet | StdFn::SliceSubrange => n == 3,
            StdFn::GhostNew => ghost_dest,
        },
        None => false,
    }
}

/// One body's lowering state: its path, MIR body, temps and the current site.
pub struct Bx<'a> { pub path: Vec<u8>, pub b: &'a Body, pub tmp: Tmp, pub site: Vec<u8> }

fn uns(bx: &Bx, what: Vec<u8>) -> Reject {
    Reject::Unsupported { path: copy_bytes(&bx.path), what, site: copy_bytes(&bx.site) }
}

/// A terminator, and whether it is a declassify call.
pub fn lower_term(m: &MirCrate, pol: &Policy, tr: &mut Tr, bx: &mut Bx, t: &Terminator) -> (r: Result<(c::Term, bool), Reject>) {
    let b = bx.b;
    match &t.kind {
        TerminatorKind::Goto { target } => Ok((c::Term::Goto(*target), false)),
        TerminatorKind::SwitchInt { discr, targets } => {
            let (op, _) = match lower_int_op(m, b, discr, &mut bx.tmp) { Ok(x) => x, Err(e) => return Err(uns(bx, e)) };
            let mut brs: Vec<(u128, usize)> = Vec::new();
            let mut k: usize = 0;
            while k < targets.branches.len()
                invariant k <= targets.branches@.len(),
                decreases targets.branches.len() - k,
            {
                brs.push(targets.branches[k]);
                k += 1;
            }
            Ok((c::Term::Switch(op, brs, targets.otherwise), false))
        },
        TerminatorKind::Assert { cond, expected, msg: _, target, unwind: _ } => {
            let (op, _) = match lower_int_op(m, b, cond, &mut bx.tmp) { Ok(x) => x, Err(e) => return Err(uns(bx, e)) };
            Ok((c::Term::Assert(op, *expected, *target), false))
        },
        TerminatorKind::Return => Ok((c::Term::Return, false)),
        TerminatorKind::Unreachable => Ok((c::Term::Abort, false)),
        TerminatorKind::Drop { place, target, unwind: _ } => lower_drop(m, pol, tr, bx, place, *target),
        TerminatorKind::Call { func, args, destination, target, unwind: _ } => {
            let tb = match target { Some(tb) => *tb, None => return Err(uns(bx, msg(b"a diverging call"))) };
            lower_call(m, pol, tr, bx, func, args, destination, tb)
        },
        _ => Err(uns(bx, msg(b"terminator outside the subset (Resume, Abort, InlineAsm, ..)"))),
    }
}

/// `Drop` through its `drops` row: an empty shim or the `Vec<int>` leaf is a `Goto`; any other
/// glue is a `Call` of the glue fn on a fresh `&mut place` temp, into a fresh `Unit` temp.
pub fn lower_drop(m: &MirCrate, pol: &Policy, tr: &mut Tr, bx: &mut Bx, place: &Place, target: usize) -> (r: Result<(c::Term, bool), Reject>) {
    let b = bx.b;
    let t = match x_place_ty(m, b, place) { Some(t) => t, None => return Err(uns(bx, msg(b"drop place type"))) };
    let cp = match lower_place(m, b, place, true) { Ok(p) => p, Err(e) => return Err(uns(bx, e)) };
    let mut k: usize = 0;
    while k < place.projection.len()
        invariant k <= place.projection@.len(),
        decreases place.projection.len() - k,
    {
        if matches!(place.projection[k], ProjectionElem::Index(_)) { return Err(uns(bx, msg(b"a drop of an indexed place"))); }
        k += 1;
    }
    let d = match x_drop_row(m, t) { Some(d) => d, None => return Err(uns(bx, msg(b"a drop with no drops row"))) };
    if d.empty || x_vec_int(m, t) { return Ok((c::Term::Goto(target), false)); }
    let j = match x_inst_idx(m, d.glue) { Some(j) => j, None => return Err(uns(bx, msg(b"drop glue with no insts row"))) };
    let ok = match x_inst_body(m, j) {
        Some(gb) => gb.arg_count == 1 && gb.locals.len() > 1 && x_sig_ok(m, gb) && x_is_mut_ref(m, gb.locals[1].ty)
            && matches!(x_rigid(m, gb.locals[1].ty), Some(RigidTy::Ref(_, pt, _)) if *pt == t),
        None => false,
    };
    if !ok { return Err(uns(bx, msg(b"drop glue without a body of one &mut parameter"))); }
    let ct = match lower_ty(m, t, TYF) { Ok(ct) => ct, Err(e) => return Err(uns(bx, e)) };
    let x = match fresh(&mut bx.tmp, c::Ty::Mut(Box::new(ct)), c::Rvalue::RefMut(cp)) { Ok(x) => x, Err(e) => return Err(uns(bx, e)) };
    let y = match fresh_local(&mut bx.tmp, c::Ty::Unit) { Ok(y) => y, Err(e) => return Err(uns(bx, e)) };
    let g = fn_index(tr, j);
    let mut args: Vec<c::Operand> = Vec::new();
    args.push(c::Operand::Copy(pl(x)));
    Ok((c::Term::Call(c::Callee::Fn(g), args, pl(y), target), false))
}

pub fn lower_call(m: &MirCrate, pol: &Policy, tr: &mut Tr, bx: &mut Bx, func: &Operand, args: &Vec<Operand>, dest: &Place, tb: usize)
    -> (r: Result<(c::Term, bool), Reject>)
{
    let b = bx.b;
    let fty = match func {
        Operand::Constant(k) => k.const_.ty,
        _ => return Err(uns(bx, msg(b"a call through a fn pointer or closure value"))),
    };
    let (j, k) = match x_callee_of(m, func) {
        Some(x) => x,
        None => {
            let callee = match x_call_row(m, fty) { Some(k) => copy_bytes(&m.calls[k].def_name), None => msg(b"?") };
            return Err(Reject::Unresolved { path: copy_bytes(&bx.path), callee, site: copy_bytes(&bx.site) });
        },
    };
    let key = m.insts[j].key.as_slice();
    let ga = &m.calls[k].args;
    let leaf = x_is_leaf(m, pol, key, ga);
    let internal = !leaf && is_internal(m, pol, j);
    if !bind(tr, key, m.insts[j].def, if internal { Some(j) } else { None }) {
        let mut w = msg(b"ambiguous key ");
        let mut i: usize = 0;
        while i < key.len()
            invariant i <= key@.len(),
            decreases key.len() - i,
        {
            w.push(key[i]);
            i += 1;
        }
        return Err(uns(bx, w));
    }
    if leaf {
        if !x_leaf_ok(m, pol, key, ga, args.len(), x_place_ty(m, b, dest)) {
            return Err(uns(bx, msg(b"a std or policy call at an unexpected arity or result type")));
        }
        let k = match x_intr_of(m, pol, key, ga) { Some(k) => k, None => return Err(uns(bx, msg(b"a leaf without an intrinsic"))) };
        let declass = matches!(k, c::Intrinsic::Declassify);
        let ops = match lower_ops(m, b, args, &mut bx.tmp) { Ok(o) => o, Err(e) => return Err(uns(bx, e)) };
        let dst = match lower_place(m, b, dest, true) { Ok(p) => p, Err(e) => return Err(uns(bx, e)) };
        return Ok((c::Term::Call(c::Callee::Intr(k), ops, dst, tb), declass));
    }
    if internal {
        let ok = match x_inst_body(m, j) {
            Some(cb) => {
                if cb.spread_arg.is_some() { return Err(uns(bx, msg(b"a call to a closure (rust-call body)"))); }
                if !(args.len() == cb.arg_count && x_sig_ok(m, cb)) { false } else if !args_match(m, b, args, cb) {
                    // a closure called through `Fn::call` takes its arguments tupled (rust-call)
                    return Err(uns(bx, msg(b"a call whose argument types are not the callee's parameter types (a closure call)")));
                } else { true }
            },
            None => false,
        };
        if !ok { return Err(uns(bx, msg(b"a call to a fn whose signature is outside the subset"))); }
        let ops = match lower_ops(m, b, args, &mut bx.tmp) { Ok(o) => o, Err(e) => return Err(uns(bx, e)) };
        let dst = match lower_place(m, b, dest, true) { Ok(p) => p, Err(e) => return Err(uns(bx, e)) };
        let g = fn_index(tr, j);
        return Ok((c::Term::Call(c::Callee::Fn(g), ops, dst, tb), false));
    }
    if std_key(key) { return Err(uns(bx, msg(b"a std fn at generic args the std model does not admit"))); }
    Err(Reject::Unresolved { path: copy_bytes(&bx.path), callee: msg(key), site: copy_bytes(&bx.site) })
}

/// Each argument's type is the callee's parameter type (ids are interned types).
fn args_match(m: &MirCrate, b: &Body, args: &Vec<Operand>, cb: &Body) -> bool {
    let mut k: usize = 0;
    while k < args.len()
        invariant k <= args@.len(),
        decreases args.len() - k,
    {
        if k + 1 >= cb.locals.len() { return false; }
        match x_op_ty(m, b, &args[k]) { Some(t) => if t != cb.locals[k + 1].ty { return false; }, None => return false }
        k += 1;
    }
    true
}

// ------------------------------------------------------------------ bodies

/// Blocks reachable from block 0 along normal edges; `None` if a target is out of range.
pub fn reach(b: &Body) -> (r: Option<Vec<bool>>) {
    let n = b.blocks.len();
    if n == 0 { return None; }
    let mut seen: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n, seen@.len() == i,
        decreases n - i,
    {
        seen.push(false);
        i += 1;
    }
    let mut work: Vec<usize> = Vec::new();
    seen.set(0, true);
    work.push(0);
    while work.len() > 0
        invariant seen@.len() == n,
        decreases n - count_true(seen@), work@.len(),
    {
        let bb = work.pop().unwrap();
        if bb >= n { return None; }
        let mut succ: Vec<usize> = Vec::new();
        match &b.blocks[bb].terminator.kind {
            TerminatorKind::Goto { target } | TerminatorKind::Drop { target, .. } | TerminatorKind::Assert { target, .. } => succ.push(*target),
            TerminatorKind::Call { target, .. } => if let Some(t) = target { succ.push(*t); },
            TerminatorKind::SwitchInt { targets, .. } => {
                let mut k: usize = 0;
                while k < targets.branches.len()
                    invariant k <= targets.branches@.len(),
                    decreases targets.branches.len() - k,
                {
                    succ.push(targets.branches[k].1);
                    k += 1;
                }
                succ.push(targets.otherwise);
            },
            _ => {},
        }
        let mut k: usize = 0;
        while k < succ.len()
            invariant k <= succ@.len(), seen@.len() == n,
            decreases succ.len() - k,
        {
            let s = succ[k];
            if s >= n { return None; }
            if !seen[s] {
                seen.set(s, true);
                work.push(s);
            }
            k += 1;
        }
    }
    Some(seen)
}

pub open spec fn count_true(s: Seq<bool>) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { count_true(s.drop_last()) + if s.last() { 1nat } else { 0nat } }
}

fn trim(s: &Vec<u8>) -> Vec<u8> {
    let mut lo: usize = 0;
    let mut hi: usize = s.len();
    while lo < hi && (s[lo] == b' ' || s[lo] == b'\n' || s[lo] == b'\t' || s[lo] == b'\r')
        invariant lo <= hi <= s@.len(),
        decreases hi - lo,
    { lo += 1; }
    while hi > lo && (s[hi - 1] == b' ' || s[hi - 1] == b'\n' || s[hi - 1] == b'\t' || s[hi - 1] == b'\r')
        invariant lo <= hi <= s@.len(),
        decreases hi - lo,
    { hi -= 1; }
    let mut v = Vec::new();
    let mut i = lo;
    while i < hi
        invariant lo <= i <= hi <= s@.len(),
        decreases hi - i,
    {
        v.push(s[i]);
        i += 1;
    }
    v
}

fn starts_with(s: &Vec<u8>, p: &[u8]) -> bool {
    if s.len() < p.len() { return false; }
    let mut i: usize = 0;
    while i < p.len()
        invariant i <= p@.len() <= s@.len(),
        decreases p.len() - i,
    {
        if s[i] != p[i] { return false; }
        i += 1;
    }
    true
}

/// The `#[ct::..]` attributes of the item of `def`, trimmed.
fn attrs_of(m: &MirCrate, def: DefId) -> Vec<Vec<u8>> {
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut k: usize = 0;
    while k < m.items.len()
        invariant k <= m.items@.len(),
        decreases m.items.len() - k,
    {
        if m.items[k].def == def {
            let a = &m.items[k].attrs;
            let mut i: usize = 0;
            while i < a.len()
                invariant i <= a@.len(),
                decreases a.len() - i,
            {
                let t = trim(&a[i]);
                if starts_with(&t, b"#[ct::") { out.push(t); }
                i += 1;
            }
            return out;
        }
        k += 1;
    }
    out
}

/// Parameter names from the argument locals' debug info (`argument_index` is 1-based).
fn param_names(b: &Body) -> Vec<Vec<u8>> {
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut j: usize = 1;
    while j <= b.arg_count && j < 0x1_0000
        invariant 1 <= j,
        decreases b.arg_count + 1 - j,
    {
        let mut name = Vec::new();
        let mut k: usize = 0;
        while k < b.var_debug_info.len()
            invariant k <= b.var_debug_info@.len(),
            decreases b.var_debug_info.len() - k,
        {
            let v = &b.var_debug_info[k];
            let here = match &v.value {
                VarDebugInfoContents::Place(p) => p.local == j && p.projection.len() == 0,
                _ => false,
            };
            if v.argument_index == Some(j as u16) && here { name = copy_bytes(&v.name); break; }
            k += 1;
        }
        out.push(name);
        j += 1;
    }
    out
}

fn ty_err(path: &Vec<u8>, what: Vec<u8>, site: Vec<u8>) -> Reject {
    Reject::Unsupported { path: copy_bytes(path), what, site }
}

/// One fn of the closure: `insts[j]`'s body.
pub fn lower_body(m: &MirCrate, pol: &Policy, tr: &mut Tr, j: usize, is_root: bool, errs: &mut Vec<Reject>) -> Option<(c::Body, FnInfo)> {
    let n0 = errs.len();
    let x = &m.insts[j];
    let is_shim = matches!(x.kind, InstanceKind::Shim);
    let path = if is_shim { copy_bytes(&x.name) } else { copy_bytes(&x.key) };
    let b = match x_inst_body(m, j) {
        Some(b) => b,
        None => { errs.push(ty_err(&path, msg(b"no MIR body"), msg(b"?"))); return None; },
    };
    let bsite = site(m, b.span);
    if b.spread_arg.is_some() { errs.push(ty_err(&path, msg(b"a rust-call (closure) body"), copy_bytes(&bsite))); }
    if !x_sig_ok(m, b) || !x_locals_ok(m, b) {
        errs.push(ty_err(&path, msg(b"a local type outside the subset"), copy_bytes(&bsite)));
    }
    let mut locals: Vec<c::Ty> = Vec::new();
    let mut k: usize = 0;
    while k < b.locals.len()
        invariant k <= b.locals@.len(),
        decreases b.locals.len() - k,
    {
        match lower_ty(m, b.locals[k].ty, TYF) {
            Ok(t) => locals.push(t),
            Err(e) => errs.push(ty_err(&path, e, site(m, b.locals[k].span))),
        }
        k += 1;
    }
    let seen = match reach(b) {
        Some(s) => s,
        None => { errs.push(ty_err(&path, msg(b"a block target out of range"), copy_bytes(&bsite))); return None; },
    };
    let mut bx = Bx { path: copy_bytes(&path), b, tmp: Tmp { nloc: b.locals.len(), tys: Vec::new(), pre: Vec::new() }, site: msg(b"?") };
    let mut blocks: Vec<c::Block> = Vec::new();
    let mut block_sites: Vec<Vec<u8>> = Vec::new();
    let mut stmt_sites: Vec<Vec<Vec<u8>>> = Vec::new();
    let mut declassify_sites: Vec<Vec<u8>> = Vec::new();
    let mut bb: usize = 0;
    while bb < b.blocks.len()
        invariant bb <= b.blocks@.len(), seen@.len() == b.blocks@.len(),
        decreases b.blocks.len() - bb,
    {
        let blk = &b.blocks[bb];
        block_sites.push(site(m, blk.terminator.span));
        let mut stmts: Vec<c::Stmt> = Vec::new();
        let mut sites: Vec<Vec<u8>> = Vec::new();
        if !seen[bb] {
            blocks.push(c::Block { stmts, term: c::Term::Abort });
            stmt_sites.push(sites);
            bb += 1;
            continue;
        }
        let mut i: usize = 0;
        while i < blk.statements.len()
            invariant i <= blk.statements@.len(),
            decreases blk.statements.len() - i,
        {
            let s = &blk.statements[i];
            bx.site = site(m, s.span);
            let r = lower_stmt(m, b, s, &mut bx.tmp);
            flush(&mut bx, &mut stmts, &mut sites);
            match r {
                Ok(Some(st)) => { stmts.push(st); sites.push(copy_bytes(&bx.site)); },
                Ok(None) => {},
                Err(e) => errs.push(uns(&bx, e)),
            }
            i += 1;
        }
        bx.site = site(m, blk.terminator.span);
        let r = lower_term(m, pol, tr, &mut bx, &blk.terminator);
        flush(&mut bx, &mut stmts, &mut sites);
        match r {
            Ok((term, declass)) => {
                if declass { declassify_sites.push(copy_bytes(&bx.site)); }
                blocks.push(c::Block { stmts, term });
            },
            Err(e) => { errs.push(e); blocks.push(c::Block { stmts, term: c::Term::Abort }); },
        }
        stmt_sites.push(sites);
        bb += 1;
    }
    if errs.len() > n0 { return None; }
    let mut t: usize = 0;
    while t < bx.tmp.tys.len()
        invariant t <= bx.tmp.tys@.len(),
        decreases bx.tmp.tys.len() - t,
    {
        let ty = bx.tmp.tys.remove(0);
        locals.push(ty);
    }
    let info = FnInfo {
        path, is_root, attrs: attrs_of(m, x.def), param_names: param_names(b), block_sites, declassify_sites, stmt_sites, inst: j,
    };
    Some((c::Body { nargs: b.arg_count, locals, blocks }, info))
}

/// Moves the pending temp assignments to the end of `stmts`, at the current site.
fn flush(bx: &mut Bx, stmts: &mut Vec<c::Stmt>, sites: &mut Vec<Vec<u8>>) {
    while bx.tmp.pre.len() > 0
        invariant true,
        decreases bx.tmp.pre@.len(),
    {
        let s = bx.tmp.pre.remove(0);
        stmts.push(s);
        sites.push(copy_bytes(&bx.site));
    }
}

fn has_lt(s: &Vec<u8>) -> bool {
    let mut i: usize = 0;
    while i + 2 < s.len()
        invariant i <= s@.len(),
        decreases s.len() - i,
    {
        if s[i] == b':' && s[i + 1] == b':' && s[i + 2] == b'<' { return true; }
        i += 1;
    }
    false
}

/// The root: exactly one local fn item whose key is `root`, and it is monomorphic. A generic
/// item's key is its name (a name holding `::<` might strip to anything, so it matches).
pub fn root_inst(m: &MirCrate, root: &[u8]) -> Result<usize, Vec<u8>> {
    let mut hit: Option<Option<usize>> = None;
    let mut n: usize = 0;
    let mut k: usize = 0;
    while k < m.items.len()
        invariant k <= m.items@.len(), n <= k,
        decreases m.items.len() - k,
    {
        let it = &m.items[k];
        let here = match it.inst {
            Some(id) => match x_inst_idx(m, id) {
                Some(j) => if bytes_eq(m.insts[j].key.as_slice(), root) { Some(Some(j)) } else { None },
                None => None,
            },
            None => if bytes_eq(it.name.as_slice(), root) || has_lt(&it.name) { Some(None) } else { None },
        };
        if let Some(h) = here { hit = Some(h); n += 1; }
        k += 1;
    }
    if n > 1 { return Err(msg(b"root is ambiguous: several fns of the crate share its key")); }
    match hit { Some(Some(j)) => Ok(j), _ => Err(msg(b"root matches no monomorphic fn of the crate")) }
}

/// Lowers the closure of manifest root `root` (a `ct_key`) to a core program, fn 0 the root.
pub fn lower(m: &MirCrate, pol: &Policy, root: &[u8]) -> (r: Result<(c::Program, Vec<FnInfo>), Vec<Reject>>) {
    let j = match root_inst(m, root) {
        Ok(j) => j,
        Err(e) => { let mut es = Vec::new(); es.push(Reject::Root { path: msg(root), msg: e }); return Err(es); },
    };
    let mut tr = Tr { order: Vec::new(), keys: Vec::new() };
    tr.order.push(j);
    bind(&mut tr, root, m.insts[j].def, Some(j));
    let mut errs: Vec<Reject> = Vec::new();
    let mut fns: Vec<c::Body> = Vec::new();
    let mut infos: Vec<FnInfo> = Vec::new();
    let mut i: usize = 0;
    while i < tr.order.len()
        invariant i <= tr.order@.len(),
        decreases m.insts@.len() + 1 - i,
    {
        let jj = tr.order[i];
        if let Some((cb, info)) = lower_body(m, pol, &mut tr, jj, i == 0, &mut errs) {
            fns.push(cb);
            infos.push(info);
        }
        i += 1;
    }
    if errs.len() > 0 { return Err(errs); }
    let p = c::Program { fns };
    if !ctcore::check::check_wf(&p) {
        let mut es = Vec::new();
        es.push(Reject::Unsupported { path: msg(root), what: msg(b"the core program is not well-formed (a &mut inside a type, ..)"), site: msg(b"?") });
        return Err(es);
    }
    Ok((p, infos))
}

fn fresh_local(tmp: &mut Tmp, ty: c::Ty) -> (r: Result<usize, Vec<u8>>) {
    if tmp.tys.len() >= usize::MAX - tmp.nloc { return Err(msg(b"too many temps")); }
    let local = tmp.nloc + tmp.tys.len();
    tmp.tys.push(ty);
    Ok(local)
}

} // verus!
