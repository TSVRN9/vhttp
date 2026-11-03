//! Exec mirrors of `sem`'s table lookups and static type predicates. A lookup returns exactly
//! what its spec returns (first match); a predicate only implies its spec (`r ==> spec`), since
//! rejecting more is sound.
use crate::json::bytes_eq;
use crate::mir::*;
use crate::policy::*;
#[cfg(verus_keep_ghost)]
use crate::sem::*;
use crate::sem::StdFn;
use ctcore::syntax::{BinOp as COp, IntTy as CTy};
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ first match

proof fn lemma_find_from<T>(s: Seq<T>, p: spec_fn(T) -> bool, k: nat, i: nat)
    requires k <= i <= s.len(), forall|l: int| k <= l < i ==> !p(#[trigger] s[l]), i < s.len() ==> p(s[i as int]),
    ensures find_from(s, p, k) == if i < s.len() { Some(i) } else { None::<nat> },
    decreases i - k,
{
    if k < i { lemma_find_from(s, p, k + 1, i); }
}

/// `find` returns `i` (in range, `p` holds there, nowhere before) or `None` (`p` holds nowhere).
pub proof fn lemma_find<T>(s: Seq<T>, p: spec_fn(T) -> bool, i: nat)
    requires i <= s.len(), forall|l: int| 0 <= l < i ==> !p(#[trigger] s[l]), i < s.len() ==> p(s[i as int]),
    ensures find(s, p) == if i < s.len() { Some(i) } else { None::<nat> },
{
    lemma_find_from(s, p, 0, i);
}

proof fn lemma_find_from_spec<T>(s: Seq<T>, p: spec_fn(T) -> bool, k: nat)
    ensures match find_from(s, p, k) {
        Some(i) => k <= i < s.len() && p(s[i as int]) && forall|l: int| k <= l < i ==> !p(#[trigger] s[l]),
        None => forall|l: int| k <= l < s.len() ==> !p(#[trigger] s[l]),
    },
    decreases s.len() - k,
{
    if k < s.len() && !p(s[k as int]) { lemma_find_from_spec(s, p, k + 1); }
}

/// What `find` returns, for any predicate (a broadcast: it fires on the closures inside `sem`'s
/// lookups, which a lemma call cannot name).
pub broadcast proof fn lemma_find_spec<T>(s: Seq<T>, p: spec_fn(T) -> bool)
    ensures #![trigger find(s, p)] match find(s, p) {
        Some(i) => i < s.len() && p(s[i as int]) && forall|l: int| 0 <= l < i ==> !p(#[trigger] s[l]),
        None => forall|l: int| 0 <= l < s.len() ==> !p(#[trigger] s[l]),
    },
{
    lemma_find_from_spec(s, p, 0);
}

pub fn x_ty_kind(m: &MirCrate, t: Ty) -> (r: Option<&TyKind>)
    ensures match r { Some(x) => ty_kind(*m, t) == Some(*x), None => ty_kind(*m, t) is None },
{
    let mut i: usize = 0;
    while i < m.tys.len()
        invariant i <= m.tys@.len(), forall|l: int| 0 <= l < i ==> (#[trigger] m.tys@[l]).id != t,
        decreases m.tys.len() - i,
    {
        if m.tys[i].id == t {
            proof { lemma_find(m.tys@, |r: TyRow| r.id == t, i as nat); }
            return Some(&m.tys[i].kind);
        }
        i += 1;
    }
    proof { lemma_find(m.tys@, |r: TyRow| r.id == t, i as nat); }
    None
}

pub fn x_rigid(m: &MirCrate, t: Ty) -> (r: Option<&RigidTy>)
    ensures match r { Some(x) => rigid(*m, t) == Some(*x), None => rigid(*m, t) is None },
{
    match x_ty_kind(m, t) { Some(TyKind::RigidTy(r)) => Some(r), _ => None }
}

pub fn x_adt_row(m: &MirCrate, t: Ty) -> (r: Option<&Adt>)
    ensures match r { Some(x) => adt_row(*m, t) == Some(*x), None => adt_row(*m, t) is None },
{
    let mut i: usize = 0;
    while i < m.adts.len()
        invariant i <= m.adts@.len(), forall|l: int| 0 <= l < i ==> (#[trigger] m.adts@[l]).ty != t,
        decreases m.adts.len() - i,
    {
        if m.adts[i].ty == t {
            proof { lemma_find(m.adts@, |r: Adt| r.ty == t, i as nat); }
            return Some(&m.adts[i]);
        }
        i += 1;
    }
    proof { lemma_find(m.adts@, |r: Adt| r.ty == t, i as nat); }
    None
}

pub fn x_layout(m: &MirCrate, t: Ty) -> (r: Option<&LayoutShape>)
    ensures match r { Some(x) => layout(*m, t) == Some(*x), None => layout(*m, t) is None },
{
    let mut i: usize = 0;
    while i < m.layouts.len()
        invariant i <= m.layouts@.len(), forall|l: int| 0 <= l < i ==> (#[trigger] m.layouts@[l]).ty != t,
        decreases m.layouts.len() - i,
    {
        if m.layouts[i].ty == t {
            proof { lemma_find(m.layouts@, |r: LayoutRow| r.ty == t, i as nat); }
            return Some(&m.layouts[i].shape);
        }
        i += 1;
    }
    proof { lemma_find(m.layouts@, |r: LayoutRow| r.ty == t, i as nat); }
    None
}

pub fn x_const_usize(m: &MirCrate, id: TyConstId) -> (r: Option<u64>)
    ensures r == const_usize(*m, id),
{
    let mut i: usize = 0;
    while i < m.consts.len()
        invariant i <= m.consts@.len(), forall|l: int| 0 <= l < i ==> (#[trigger] m.consts@[l]).id != id,
        decreases m.consts.len() - i,
    {
        if m.consts[i].id == id {
            proof { lemma_find(m.consts@, |r: ConstRow| r.id == id, i as nat); }
            return m.consts[i].usize;
        }
        i += 1;
    }
    proof { lemma_find(m.consts@, |r: ConstRow| r.id == id, i as nat); }
    None
}

pub fn x_alloc_mem(m: &MirCrate, id: AllocId) -> (r: Option<&Allocation>)
    ensures match r { Some(x) => alloc_mem(*m, id) == Some(*x), None => alloc_mem(*m, id) is None },
{
    let mut i: usize = 0;
    while i < m.allocs.len()
        invariant i <= m.allocs@.len(), forall|l: int| 0 <= l < i ==> (#[trigger] m.allocs@[l]).id != id,
        decreases m.allocs.len() - i,
    {
        if m.allocs[i].id == id {
            proof { lemma_find(m.allocs@, |r: AllocRow| r.id == id, i as nat); }
            return match &m.allocs[i].alloc { GlobalAlloc::Memory(a) => Some(a), _ => None };
        }
        i += 1;
    }
    proof { lemma_find(m.allocs@, |r: AllocRow| r.id == id, i as nat); }
    None
}

pub fn x_inst_idx(m: &MirCrate, id: InstanceDef) -> (r: Option<usize>)
    ensures match r { Some(j) => inst_idx(*m, id) == Some(j as nat) && j < m.insts@.len(), None => inst_idx(*m, id) is None },
{
    let mut i: usize = 0;
    while i < m.insts.len()
        invariant i <= m.insts@.len(), forall|l: int| 0 <= l < i ==> (#[trigger] m.insts@[l]).id != id,
        decreases m.insts.len() - i,
    {
        if m.insts[i].id == id {
            proof { lemma_find(m.insts@, |x: Inst| x.id == id, i as nat); }
            return Some(i);
        }
        i += 1;
    }
    proof { lemma_find(m.insts@, |x: Inst| x.id == id, i as nat); }
    None
}

pub fn x_drop_row(m: &MirCrate, t: Ty) -> (r: Option<&DropRow>)
    ensures match r { Some(x) => drop_row(*m, t) == Some(*x), None => drop_row(*m, t) is None },
{
    let mut i: usize = 0;
    while i < m.drops.len()
        invariant i <= m.drops@.len(), forall|l: int| 0 <= l < i ==> (#[trigger] m.drops@[l]).ty != t,
        decreases m.drops.len() - i,
    {
        if m.drops[i].ty == t {
            proof { lemma_find(m.drops@, |d: DropRow| d.ty == t, i as nat); }
            return Some(&m.drops[i]);
        }
        i += 1;
    }
    proof { lemma_find(m.drops@, |d: DropRow| d.ty == t, i as nat); }
    None
}

/// The `calls` row of a callee of type `fn_ty` (first match), by index.
pub fn x_call_row(m: &MirCrate, fn_ty: Ty) -> (r: Option<usize>)
    ensures match r {
        Some(k) => find(m.calls@, |r: Call| r.fn_ty == fn_ty) == Some(k as nat) && k < m.calls@.len(),
        None => find(m.calls@, |r: Call| r.fn_ty == fn_ty) is None,
    },
{
    let mut i: usize = 0;
    while i < m.calls.len()
        invariant i <= m.calls@.len(), forall|l: int| 0 <= l < i ==> (#[trigger] m.calls@[l]).fn_ty != fn_ty,
        decreases m.calls.len() - i,
    {
        if m.calls[i].fn_ty == fn_ty {
            proof { lemma_find(m.calls@, |r: Call| r.fn_ty == fn_ty, i as nat); }
            return Some(i);
        }
        i += 1;
    }
    proof { lemma_find(m.calls@, |r: Call| r.fn_ty == fn_ty, i as nat); }
    None
}

/// The `spans` row of `sp` (no spec: sites are report metadata).
pub fn x_span(m: &MirCrate, sp: Span) -> Option<&SpanRow> {
    let mut i: usize = 0;
    while i < m.spans.len()
        invariant i <= m.spans@.len(),
        decreases m.spans.len() - i,
    {
        if m.spans[i].id == sp { return Some(&m.spans[i]); }
        i += 1;
    }
    None
}

/// `callee_of`: the `insts` index and `calls` row of a constant `FnDef` callee.
pub fn x_callee_of(m: &MirCrate, func: &Operand) -> (r: Option<(usize, usize)>)
    ensures match r {
        Some((j, k)) => k < m.calls@.len() && callee_of(*m, *func) == Some((j as nat, m.calls@[k as int].args)),
        None => callee_of(*m, *func) is None,
    },
{
    match func {
        Operand::Constant(c) => match x_call_row(m, c.const_.ty) {
            Some(k) => match m.calls[k].resolved {
                Some(id) => match x_inst_idx(m, id) { Some(j) => Some((j, k)), None => None },
                None => None,
            },
            None => None,
        },
        _ => None,
    }
}

pub fn x_inst_body(m: &MirCrate, i: usize) -> (r: Option<&Body>)
    ensures match r { Some(b) => inst_body(*m, i as nat) == Some(*b), None => inst_body(*m, i as nat) is None },
{
    if i < m.insts.len() && (matches!(m.insts[i].kind, InstanceKind::Item) || matches!(m.insts[i].kind, InstanceKind::Shim)) {
        match &m.insts[i].body { Some(b) => Some(b), None => None }
    } else { None }
}

// ------------------------------------------------------------------ copies (the core enums derive nothing)

pub fn cp_ity(t: &CTy) -> (r: CTy) ensures r == *t {
    match t {
        CTy::U8 => CTy::U8, CTy::U16 => CTy::U16, CTy::U32 => CTy::U32, CTy::U64 => CTy::U64, CTy::U128 => CTy::U128,
        CTy::Usize => CTy::Usize, CTy::I8 => CTy::I8, CTy::I16 => CTy::I16, CTy::I32 => CTy::I32, CTy::I64 => CTy::I64,
        CTy::I128 => CTy::I128, CTy::Isize => CTy::Isize, CTy::Bool => CTy::Bool,
    }
}

pub fn cp_op(o: &COp) -> (r: COp) ensures r == *o {
    match o {
        COp::Add => COp::Add, COp::Sub => COp::Sub, COp::Mul => COp::Mul, COp::Div => COp::Div, COp::Rem => COp::Rem,
        COp::BitXor => COp::BitXor, COp::BitAnd => COp::BitAnd, COp::BitOr => COp::BitOr, COp::Shl => COp::Shl,
        COp::Shr => COp::Shr, COp::Eq => COp::Eq, COp::Ne => COp::Ne, COp::Lt => COp::Lt, COp::Le => COp::Le,
        COp::Gt => COp::Gt, COp::Ge => COp::Ge,
    }
}

// ------------------------------------------------------------------ types

pub fn x_int_of(r: &RigidTy) -> (o: Option<CTy>)
    ensures o == int_of(*r),
{
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

pub fn x_int_ty(m: &MirCrate, t: Ty) -> (o: Option<CTy>)
    ensures o == int_ty(*m, t),
{
    match x_rigid(m, t) { Some(r) => x_int_of(r), None => None }
}

pub fn x_is_mut_ref(m: &MirCrate, t: Ty) -> (r: bool)
    ensures r == is_mut_ref(*m, t),
{
    matches!(x_rigid(m, t), Some(RigidTy::Ref(_, _, Mutability::Mut)))
}

pub fn x_sized(m: &MirCrate, t: Ty) -> (r: bool)
    ensures r == sized(*m, t),
{
    match x_rigid(m, t) {
        Some(r) => !(matches!(r, RigidTy::Str) || matches!(r, RigidTy::Slice(_)) || matches!(r, RigidTy::Dynamic(_, _))),
        None => false,
    }
}

pub fn x_is_zst(m: &MirCrate, t: Ty) -> (r: bool)
    ensures r == is_zst(*m, t),
{
    x_sized(m, t) && match x_layout(m, t) { Some(l) => l.size.num_bits == 0, None => false }
}

pub fn x_vec_elem(m: &MirCrate, t: Ty) -> (r: Option<Ty>)
    ensures r == vec_elem(*m, t),
{
    match (x_adt_row(m, t), x_rigid(m, t)) {
        (Some(a), Some(RigidTy::Adt(_, ga))) => {
            if bytes_eq(a.name.as_slice(), b"std::vec::Vec") && ga.0.len() >= 1 {
                match &ga.0[0] { GenericArgKind::Type(e) => Some(*e), _ => None }
            } else { None }
        },
        _ => None,
    }
}

pub fn x_vec_int(m: &MirCrate, t: Ty) -> (r: bool)
    ensures r == vec_int(*m, t),
{
    match x_vec_elem(m, t) {
        Some(e) => match x_int_ty(m, e) { Some(it) => !matches!(it, CTy::Bool), None => false },
        None => false,
    }
}

/// `ty_free` at the given fuel.
#[verifier::loop_isolation(false)]
pub fn x_ty_free(m: &MirCrate, t: Ty, fuel: usize, mut_ok: bool) -> (r: bool)
    ensures r ==> ty_free(*m, t, fuel as nat, mut_ok),
    decreases fuel,
{
    if fuel == 0 { return false; }
    let f = fuel - 1;
    let r = match x_rigid(m, t) { Some(r) => r, None => return false };
    match r {
        RigidTy::Bool | RigidTy::Int(_) | RigidTy::Uint(_) => x_int_of(r).is_some(),
        RigidTy::Str | RigidTy::Never | RigidTy::FnDef(_, _) | RigidTy::FnPtr(_) | RigidTy::Closure(_, _) => true,
        RigidTy::Pat(base, _) => x_ty_free(m, *base, f, mut_ok),
        RigidTy::Tuple(ts) => {
            let mut k: usize = 0;
            while k < ts.len()
                invariant k <= ts@.len(), forall|i: int| 0 <= i < k ==> ty_free(*m, #[trigger] ts@[i], f as nat, mut_ok),
                decreases ts.len() - k,
            {
                if !x_ty_free(m, ts[k], f, mut_ok) { return false; }
                k += 1;
            }
            true
        },
        RigidTy::Array(e, _) => x_ty_free(m, *e, f, mut_ok),
        RigidTy::Slice(e) => x_ty_free(m, *e, f, mut_ok),
        RigidTy::Ref(_, p, mu) => (matches!(mu, Mutability::Not) || mut_ok) && !matches!(mu, Mutability::Unknown(_))
            && x_ty_free(m, *p, f, false),
        RigidTy::Adt(_, _) => match x_vec_elem(m, t) {
            Some(e) => x_ty_free(m, e, f, false),
            None => match x_adt_row(m, t) {
                Some(a) => {
                    if a.is_box || matches!(a.kind, AdtKind::Union) || matches!(a.kind, AdtKind::Unknown(_))
                        || bytes_eq(a.name.as_slice(), b"std::cell::UnsafeCell") { return false; }
                    let mut k: usize = 0;
                    while k < a.variants.len()
                        invariant
                            k <= a.variants@.len(),
                            forall|kk: int, i: int| 0 <= kk < k && 0 <= i < a.variants@[kk].fields@.len()
                                ==> ty_free(*m, #[trigger] a.variants@[kk].fields@[i], f as nat, mut_ok),
                        decreases a.variants.len() - k,
                    {
                        let fs = &a.variants[k].fields;
                        let mut i: usize = 0;
                        while i < fs.len()
                            invariant
                                k < a.variants@.len(), *fs == a.variants@[k as int].fields, i <= fs@.len(),
                                forall|kk: int, ii: int| 0 <= kk < k && 0 <= ii < a.variants@[kk].fields@.len()
                                    ==> ty_free(*m, #[trigger] a.variants@[kk].fields@[ii], f as nat, mut_ok),
                                forall|ii: int| 0 <= ii < i ==> ty_free(*m, #[trigger] fs@[ii], f as nat, mut_ok),
                            decreases fs.len() - i,
                        {
                            if !x_ty_free(m, fs[i], f, mut_ok) { return false; }
                            i += 1;
                        }
                        k += 1;
                    }
                    true
                },
                None => false,
            },
        },
        _ => false,
    }
}

/// `tfuel(m)` (`None` past usize).
pub fn x_tfuel(m: &MirCrate) -> (r: Option<usize>)
    ensures r matches Some(f) ==> f as nat == tfuel(*m),
{
    if m.tys.len() < usize::MAX { Some(m.tys.len() + 1) } else { None }
}

pub fn x_sig_ok(m: &MirCrate, b: &Body) -> (r: bool)
    ensures r ==> sig_ok(*m, *b),
{
    let tf = match x_tfuel(m) { Some(f) => f, None => return false };
    if !(b.arg_count < b.locals.len() && x_ty_free(m, b.locals[0].ty, tf, false)) { return false; }
    let mut k: usize = 1;
    while k <= b.arg_count && k < b.locals.len()
        invariant
            1 <= k <= b.arg_count + 1, b.arg_count < b.locals@.len(), tf as nat == tfuel(*m),
            forall|i: int| 1 <= i < k ==> match rigid(*m, #[trigger] b.locals@[i].ty) {
                Some(RigidTy::Ref(_, p, Mutability::Mut)) => ty_free(*m, p, tfuel(*m), false),
                _ => ty_free(*m, b.locals@[i].ty, tfuel(*m), false),
            },
        decreases b.arg_count + 1 - k,
    {
        let t = b.locals[k].ty;
        let ok = match x_rigid(m, t) {
            Some(RigidTy::Ref(_, p, Mutability::Mut)) => x_ty_free(m, *p, tf, false),
            _ => x_ty_free(m, t, tf, false),
        };
        if !ok { return false; }
        k += 1;
    }
    true
}

pub fn x_locals_ok(m: &MirCrate, b: &Body) -> (r: bool)
    ensures r ==> locals_ok(*m, *b),
{
    let tf = match x_tfuel(m) { Some(f) => f, None => return false };
    let mut k: usize = 0;
    while k < b.locals.len()
        invariant k <= b.locals@.len(), tf as nat == tfuel(*m),
            forall|i: int| 0 <= i < k ==> ty_free(*m, #[trigger] b.locals@[i].ty, tfuel(*m), true),
        decreases b.locals.len() - k,
    {
        if !x_ty_free(m, b.locals[k].ty, tf, true) { return false; }
        k += 1;
    }
    true
}

/// `unit_like(m, t, fuel, clos) is Some`.
pub fn x_unit_like(m: &MirCrate, t: Ty, fuel: usize, clos: bool) -> (r: bool)
    ensures r == unit_like(*m, t, fuel as nat, clos) is Some,
    decreases fuel, 0nat,
{
    if fuel == 0 { return false; }
    let f = fuel - 1;
    match x_rigid(m, t) {
        Some(RigidTy::Tuple(ts)) => x_unit_likes(m, ts, f, clos),
        Some(RigidTy::Adt(_, _)) => match x_adt_row(m, t) {
            Some(a) => !a.is_box && !matches!(a.kind, AdtKind::Union) && a.variants.len() == 1
                && x_unit_likes(m, &a.variants[0].fields, f, clos),
            None => false,
        },
        Some(RigidTy::Array(e, c)) => match x_const_usize(m, c.id) {
            Some(n) => n == 0 || x_unit_like(m, *e, f, clos),
            None => false,
        },
        Some(RigidTy::FnDef(_, _)) => true,
        Some(RigidTy::Closure(_, _)) => clos,
        _ => false,
    }
}

pub fn x_unit_likes(m: &MirCrate, ts: &Vec<Ty>, fuel: usize, clos: bool) -> (r: bool)
    ensures r == unit_likes(*m, ts@, fuel as nat, ts@.len(), clos) is Some,
    decreases fuel, 1nat,
{
    let mut k: usize = 0;
    while k < ts.len()
        invariant k <= ts@.len(), unit_likes(*m, ts@, fuel as nat, k as nat, clos) is Some,
        decreases ts.len() - k,
    {
        if !x_unit_like(m, ts[k], fuel, clos) {
            proof { lemma_unit_likes_none(*m, ts@, fuel as nat, (k + 1) as nat, ts@.len(), clos); }
            return false;
        }
        k += 1;
    }
    true
}

/// A failed prefix of `unit_likes` stays failed.
pub proof fn lemma_unit_likes_none(m: MirCrate, ts: Seq<Ty>, fuel: nat, k: nat, n: nat, clos: bool)
    requires 0 < k <= n <= ts.len(), unit_likes(m, ts, fuel, k, clos) is None,
    ensures unit_likes(m, ts, fuel, n, clos) is None,
    decreases n - k,
{
    if k < n { lemma_unit_likes_none(m, ts, fuel, k, (n - 1) as nat, clos); }
}

pub fn x_zst_dest(m: &MirCrate, t: Ty) -> (r: bool)
    ensures r ==> zst_dest(*m, t),
{
    let tf = match x_tfuel(m) { Some(f) => f, None => return false };
    x_sized(m, t) && x_unit_like(m, t, tf, false) && match x_layout(m, t) { Some(l) => l.size.num_bits == 0, None => true }
}

// ------------------------------------------------------------------ the std model and leaves

pub fn x_garg0<'a>(m: &'a MirCrate, g: &GenericArgs) -> (r: Option<&'a RigidTy>)
    ensures match r { Some(x) => garg0(*m, *g) == Some(*x), None => garg0(*m, *g) is None },
{
    if g.0.len() > 0 { match &g.0[0] { GenericArgKind::Type(t) => x_rigid(m, *t), _ => None } } else { None }
}

pub fn x_std_model(m: &MirCrate, key: &[u8], g: &GenericArgs) -> (r: Option<StdFn>)
    ensures r == std_model(*m, key@, *g),
{
    let e = x_garg0(m, g);
    let u8_ = matches!(e, Some(RigidTy::Uint(UintTy::U8)));
    let pair = match e {
        Some(RigidTy::Tuple(ts)) => ts.len() == 2 && matches!(x_rigid(m, ts[0]), Some(RigidTy::Uint(UintTy::U64)))
            && matches!(x_rigid(m, ts[1]), Some(RigidTy::Uint(UintTy::U64))),
        _ => false,
    };
    proof {
        assert(u8_ == is_u8(garg0(*m, *g)));
        assert(pair == is_u64_pair(*m, garg0(*m, *g)));
    }
    let u8_or_pair = u8_ || pair;
    if bytes_eq(key, b"std::vec::Vec::new") && u8_or_pair { Some(StdFn::VecNew) }
    else if bytes_eq(key, b"std::vec::Vec::with_capacity") && u8_ { Some(StdFn::VecWithCapacity) }
    else if bytes_eq(key, b"std::vec::Vec::push") && u8_or_pair { Some(StdFn::VecPush) }
    else if bytes_eq(key, b"std::vec::Vec::extend_from_slice") && u8_ { Some(StdFn::VecExtendFromSlice) }
    else if bytes_eq(key, b"std::vec::Vec::as_slice") && u8_ { Some(StdFn::VecAsSlice) }
    else if bytes_eq(key, b"std::array::<impl [u8; 16]>::as_slice") || bytes_eq(key, b"std::array::<impl [u8; 32]>::as_slice")
        || bytes_eq(key, b"std::array::<impl [u8; 64]>::as_slice") || bytes_eq(key, b"std::array::<impl [u8; 128]>::as_slice") { Some(StdFn::ArrayAsSlice) }
    else if bytes_eq(key, b"std::vec::Vec::len") && u8_or_pair { Some(StdFn::VecLen) }
    else if bytes_eq(key, b"<std::vec::Vec<u8> as vstd::pervasive::VecAdditionalExecFns<u8>>::set") { Some(StdFn::VecSet) }
    else if bytes_eq(key, b"<std::vec::Vec<(u64, u64)> as std::ops::Index<usize>>::index") { Some(StdFn::VecIndex) }
    else if bytes_eq(key, b"vstd::slice::slice_subrange") && u8_ { Some(StdFn::SliceSubrange) }
    else if bytes_eq(key, b"vstd::slice::slice_to_vec") && u8_ { Some(StdFn::SliceToVec) }
    else if bytes_eq(key, b"core::num::<impl u32>::wrapping_add") { Some(StdFn::Wrapping(COp::Add, CTy::U32)) }
    else if bytes_eq(key, b"core::num::<impl u64>::wrapping_sub") { Some(StdFn::Wrapping(COp::Sub, CTy::U64)) }
    else if bytes_eq(key, b"vstd::prelude::Ghost::assume_new_fallback") { Some(StdFn::GhostNew) }
    else { None }
}

/// A std-model key at any generic args (an error message only: admitted at others, it is
/// `Unsupported`, as the old type-arg guard said, rather than `Unresolved`).
pub fn std_key(key: &[u8]) -> bool {
    bytes_eq(key, b"std::vec::Vec::new") || bytes_eq(key, b"std::vec::Vec::with_capacity") || bytes_eq(key, b"std::vec::Vec::push")
    || bytes_eq(key, b"std::vec::Vec::extend_from_slice") || bytes_eq(key, b"std::vec::Vec::as_slice")
    || bytes_eq(key, b"std::vec::Vec::len") || bytes_eq(key, b"vstd::slice::slice_subrange") || bytes_eq(key, b"vstd::slice::slice_to_vec")
}

pub fn x_is_leaf(m: &MirCrate, pol: &Policy, key: &[u8], g: &GenericArgs) -> (r: bool)
    ensures r == is_leaf(*m, cpol(*pol), key@, *g),
{
    proof { lemma_set_of(pol.declassify@, key@); lemma_set_of(pol.ghost_unit@, key@); }
    has_exec(&pol.declassify, key) || has_exec(&pol.ghost_unit, key) || x_std_model(m, key, g).is_some()
}

} // verus!
