//! The evaluator's constants and unit-like values: exec mirrors of `sem`'s `unit_like`, `has_arr`,
//! `ul_val`, `dec` (with its `dec_*` companions) and `const_val`, with lookups through `Tabs`.
//! - `e_unit_like` is exact (its `Panic` is `unit_like`'s `None`), since `ul_val` branches on it.
//! - The decoders claim only their `Ok` results: a failed decode is `GaveUp`, because `look.rs` and
//!   `lower_const.rs`'s byte readers they reuse are one-way, and in-subset constants decode
//!   (`op_ok` requires `const_val is Some`).
//! - An allocation past `CAP` elements, or a count past `u64`, is `GaveUp`.
use crate::eval::{Halt, R};
use crate::eval_tab::*;
use crate::interp_val::*;
#[cfg(verus_keep_ghost)]
use crate::look::lemma_unit_likes_none;
use crate::look::{x_int_of, x_tfuel};
use crate::lower_const::{x_adt_sel, x_dfuel, x_le, x_no_prov, x_prov_at, x_rd_int};
use crate::mir::*;
#[cfg(verus_keep_ghost)]
use crate::sem::*;
use vstd::prelude::*;

verus! {

/// The largest `Vec` the evaluator builds from a count.
pub const CAP: u64 = 0x100_0000; // 1 << 24

/// `n` copies of `x`.
pub fn repeat(x: &CVal, n: u64) -> (vs: Vec<CVal>)
    ensures cvs(vs@) == Seq::new(n as nat, |_i: int| cv(*x)),
{
    let mut vs: Vec<CVal> = Vec::new();
    let mut i: u64 = 0;
    while i < n
        invariant i <= n, vs@.len() == i, forall|q: int| 0 <= q < i ==> cv(#[trigger] vs@[q]) == cv(*x),
        decreases n - i,
    {
        vs.push(cclone(x));
        i += 1;
    }
    proof { assert(cvs(vs@) =~= Seq::new(n as nat, |_i: int| cv(*x))); }
    vs
}

/// `tup_val`: `()` is `Unit`.
pub fn tup_cval(vs: Vec<CVal>) -> (r: CVal)
    ensures cv(r) == tup_val(cvs(vs@)),
{
    if vs.len() == 0 {
        CVal::Unit
    } else {
        let r = CVal::Tup(vs);
        proof { lemma_cv(r); }
        r
    }
}

// ------------------------------------------------------------------ unit-like values

pub fn t_has_arr(m: &MirCrate, tb: &Tabs, t: Ty, fuel: usize) -> (r: bool)
    requires tabs_ok(*m, *tb),
    ensures r == has_arr(*m, t, fuel as nat),
    decreases fuel, 0nat,
{
    if fuel == 0 { return false; }
    let f = fuel - 1;
    match t_rigid(m, tb, t) {
        Some(RigidTy::Tuple(ts)) => t_has_arrs(m, tb, ts, f),
        Some(RigidTy::Adt(_, _)) => match t_adt_row(m, tb, t) {
            Some(a) => a.variants.len() == 1 && t_has_arrs(m, tb, &a.variants[0].fields, f),
            None => false,
        },
        Some(RigidTy::Array(_, _)) => true,
        _ => false,
    }
}

fn t_has_arrs(m: &MirCrate, tb: &Tabs, ts: &Vec<Ty>, fuel: usize) -> (r: bool)
    requires tabs_ok(*m, *tb),
    ensures r == exists|k: int| 0 <= k < ts@.len() && has_arr(*m, #[trigger] ts@[k], fuel as nat),
    decreases fuel, 1nat,
{
    let mut k: usize = 0;
    while k < ts.len()
        invariant k <= ts@.len(), tabs_ok(*m, *tb), forall|i: int| 0 <= i < k ==> !has_arr(*m, #[trigger] ts@[i], fuel as nat),
        decreases ts.len() - k,
    {
        if t_has_arr(m, tb, ts[k], fuel) { return true; }
        k += 1;
    }
    false
}

/// `unit_like(m, t, fuel, clos)`: its value and node count.
pub fn e_unit_like(m: &MirCrate, tb: &Tabs, t: Ty, fuel: usize, clos: bool) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures
        r matches Ok((v, c)) ==> unit_like(*m, t, fuel as nat, clos) == Some((cv(v), c as nat)),
        r matches Err(Halt::Panic) ==> unit_like(*m, t, fuel as nat, clos) is None,
    decreases fuel, 0nat,
{
    if fuel == 0 { return Err(Halt::Panic); }
    let f = fuel - 1;
    match t_rigid(m, tb, t) {
        Some(RigidTy::Tuple(ts)) => {
            let (vs, c) = e_unit_likes(m, tb, ts, f, clos)?;
            Ok((tup_cval(vs), c))
        },
        Some(RigidTy::Adt(_, _)) => match t_adt_row(m, tb, t) {
            Some(a) => if !a.is_box && !matches!(a.kind, AdtKind::Union) && a.variants.len() == 1 {
                let (vs, c) = e_unit_likes(m, tb, &a.variants[0].fields, f, clos)?;
                if c == u64::MAX { return Err(Halt::GaveUp); }
                let v = CVal::Adt(0, vs);
                proof { lemma_cv(v); }
                Ok((v, c + 1))
            } else { Err(Halt::Panic) },
            None => Err(Halt::Panic),
        },
        Some(RigidTy::Array(e, c)) => match t_const_usize(m, tb, c.id) {
            Some(n) => if n == 0 {
                let v = CVal::Arr(Vec::new());
                proof { lemma_cv(v); assert(cvs(Seq::<CVal>::empty()) =~= Seq::<ctcore::sem::Val>::empty()); }
                Ok((v, 0))
            } else {
                let (x, k) = e_unit_like(m, tb, *e, f, clos)?;
                if n > CAP || k > 0x1_0000_0000 { return Err(Halt::GaveUp); }
                let v = CVal::Arr(repeat(&x, n));
                proof { lemma_cv(v); assert(n * k <= 0x100_0000 * 0x1_0000_0000) by (nonlinear_arith) requires n <= 0x100_0000, k <= 0x1_0000_0000; }
                Ok((v, n * k))
            },
            None => Err(Halt::Panic),
        },
        Some(RigidTy::FnDef(_, _)) => Ok((CVal::Unit, 0)),
        Some(RigidTy::Closure(_, _)) => if clos { Ok((CVal::Unit, 0)) } else { Err(Halt::Panic) },
        _ => Err(Halt::Panic),
    }
}

fn e_unit_likes(m: &MirCrate, tb: &Tabs, ts: &Vec<Ty>, fuel: usize, clos: bool) -> (r: R<(Vec<CVal>, u64)>)
    requires tabs_ok(*m, *tb),
    ensures
        r matches Ok((vs, c)) ==> unit_likes(*m, ts@, fuel as nat, ts@.len(), clos) == Some((cvs(vs@), c as nat)),
        r matches Err(Halt::Panic) ==> unit_likes(*m, ts@, fuel as nat, ts@.len(), clos) is None,
    decreases fuel, 1nat,
{
    let mut vs: Vec<CVal> = Vec::new();
    let mut c: u64 = 0;
    let mut k: usize = 0;
    proof { assert(cvs(vs@) =~= Seq::<ctcore::sem::Val>::empty()); }
    while k < ts.len()
        invariant k <= ts@.len(), tabs_ok(*m, *tb), unit_likes(*m, ts@, fuel as nat, k as nat, clos) == Some((cvs(vs@), c as nat)),
        decreases ts.len() - k,
    {
        match e_unit_like(m, tb, ts[k], fuel, clos) {
            Ok((v, x)) => {
                if c > u64::MAX - x { return Err(Halt::GaveUp); }
                proof { lemma_cvs_push(vs@, v); }
                vs.push(v);
                c = c + x;
            },
            Err(Halt::Panic) => {
                proof { lemma_unit_likes_none(*m, ts@, fuel as nat, (k + 1) as nat, ts@.len(), clos); }
                return Err(Halt::Panic);
            },
            Err(Halt::GaveUp) => return Err(Halt::GaveUp),
        }
        k += 1;
    }
    Ok((vs, c))
}

/// `ul_val(m, t)`: the structural value of a unit-like type holding an array, else `Unit`.
pub fn e_ul_val(m: &MirCrate, tb: &Tabs, t: Ty) -> (r: R<CVal>)
    requires tabs_ok(*m, *tb),
    ensures r matches Ok(v) ==> cv(v) == ul_val(*m, t),
{
    let tf = match x_tfuel(m) { Some(f) => f, None => return Err(Halt::GaveUp) };
    if !t_has_arr(m, tb, t, tf) { return Ok(CVal::Unit); }
    match e_unit_like(m, tb, t, tf, true) {
        Ok((v, _)) => Ok(v),
        Err(Halt::Panic) => Ok(CVal::Unit),
        Err(Halt::GaveUp) => Err(Halt::GaveUp),
    }
}

// ------------------------------------------------------------------ decoding (claims `Ok` only)

pub fn e_dec(m: &MirCrate, tb: &Tabs, t: Ty, a: &Allocation, off: usize, fuel: usize) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures
        r matches Ok((v, k)) ==> dec(*m, t, *a, off as nat, fuel as nat) == Some((cv(v), k as nat)),
        !(r matches Err(Halt::Panic)),
    decreases fuel, 0nat,
{
    if fuel == 0 { return Err(Halt::GaveUp); }
    let f = fuel - 1;
    let r = match t_rigid(m, tb, t) { Some(r) => r, None => return Err(Halt::GaveUp) };
    match x_int_of(r) {
        Some(it) => match x_rd_int(a, off, &it) { Some(v) => Ok((CVal::Int(v), 0)), None => Err(Halt::GaveUp) },
        None => match r {
            RigidTy::Pat(base, _) => e_dec(m, tb, *base, a, off, f),
            RigidTy::Tuple(ts) => e_dec_tuple(m, tb, t, ts, a, off, f),
            RigidTy::Array(e, c) => e_dec_array(m, tb, t, *e, c.id, a, off, f),
            RigidTy::Adt(_, _) => e_dec_adt(m, tb, t, a, off, f),
            RigidTy::Ref(_, p, Mutability::Not) => e_dec_ref(m, tb, *p, a, off, f),
            _ => Err(Halt::GaveUp),
        },
    }
}

#[verifier::loop_isolation(false)]
fn e_dec_fields(m: &MirCrate, tb: &Tabs, ts: &Vec<Ty>, os: &Vec<MachineSize>, a: &Allocation, base: usize, fuel: usize)
    -> (r: R<(Vec<CVal>, u64)>)
    requires tabs_ok(*m, *tb), os@.len() == ts@.len(),
    ensures
        r matches Ok((vs, c)) ==> dec_fields(*m, ts@, os@, *a, base as nat, fuel as nat, ts@.len()) == Some((cvs(vs@), c as nat)),
        !(r matches Err(Halt::Panic)),
    decreases fuel, 1nat,
{
    let mut vs: Vec<CVal> = Vec::new();
    let mut c: u64 = 0;
    let mut i: usize = 0;
    proof { assert(cvs(vs@) =~= Seq::<ctcore::sem::Val>::empty()); }
    while i < ts.len()
        invariant i <= ts@.len(), dec_fields(*m, ts@, os@, *a, base as nat, fuel as nat, i as nat) == Some((cvs(vs@), c as nat)),
        decreases ts.len() - i,
    {
        if os[i].num_bits % 8 != 0 { return Err(Halt::GaveUp); }
        let rel = os[i].num_bits / 8;
        if base > usize::MAX - rel { return Err(Halt::GaveUp); }
        let (v, k) = match e_dec(m, tb, ts[i], a, base + rel, fuel) { Ok(x) => x, Err(_) => return Err(Halt::GaveUp) };
        if c > u64::MAX - k { return Err(Halt::GaveUp); }
        proof { lemma_cvs_push(vs@, v); }
        vs.push(v);
        c = c + k;
        i += 1;
    }
    Ok((vs, c))
}

#[verifier::loop_isolation(false)]
fn e_dec_elems(m: &MirCrate, tb: &Tabs, e: Ty, stride: usize, a: &Allocation, base: usize, fuel: usize, n: u64)
    -> (r: R<(Vec<CVal>, u64)>)
    requires tabs_ok(*m, *tb),
    ensures
        r matches Ok((vs, c)) ==> dec_elems(*m, e, stride as nat, *a, base as nat, fuel as nat, n as nat) == Some((cvs(vs@), c as nat)),
        !(r matches Err(Halt::Panic)),
    decreases fuel, 1nat,
{
    if n > CAP { return Err(Halt::GaveUp); }
    let mut vs: Vec<CVal> = Vec::new();
    let mut c: u64 = 0;
    let mut i: u64 = 0;
    let mut at: usize = base;
    proof { assert(cvs(vs@) =~= Seq::<ctcore::sem::Val>::empty()); }
    while i < n
        invariant i <= n, at as int == base + i * stride,
            dec_elems(*m, e, stride as nat, *a, base as nat, fuel as nat, i as nat) == Some((cvs(vs@), c as nat)),
        decreases n - i,
    {
        let (v, k) = match e_dec(m, tb, e, a, at, fuel) { Ok(x) => x, Err(_) => return Err(Halt::GaveUp) };
        if c > u64::MAX - k || at > usize::MAX - stride { return Err(Halt::GaveUp); }
        proof { lemma_cvs_push(vs@, v); }
        vs.push(v);
        c = c + k;
        at = at + stride;
        proof { assert(at as int == base + (i + 1) * stride) by (nonlinear_arith) requires at as int == base + i * stride + stride; }
        i += 1;
    }
    Ok((vs, c))
}

fn e_dec_tuple(m: &MirCrate, tb: &Tabs, t: Ty, ts: &Vec<Ty>, a: &Allocation, off: usize, fuel: usize) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures
        r matches Ok((v, k)) ==> dec_tuple(*m, t, ts@, *a, off as nat, fuel as nat) == Some((cv(v), k as nat)),
        !(r matches Err(Halt::Panic)),
    decreases fuel, 2nat,
{
    let o = match t_layout(m, tb, t) {
        Some(l) => match &l.fields { FieldsShape::Arbitrary { offsets } => offsets, _ => return Err(Halt::GaveUp) },
        None => return Err(Halt::GaveUp),
    };
    if o.len() != ts.len() { return Err(Halt::GaveUp); }
    let (vs, c) = e_dec_fields(m, tb, ts, o, a, off, fuel)?;
    Ok((tup_cval(vs), c))
}

fn e_dec_array(m: &MirCrate, tb: &Tabs, t: Ty, e: Ty, cid: TyConstId, a: &Allocation, off: usize, fuel: usize) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures
        r matches Ok((v, k)) ==> dec_array(*m, t, e, cid, *a, off as nat, fuel as nat) == Some((cv(v), k as nat)),
        !(r matches Err(Halt::Panic)),
    decreases fuel, 2nat,
{
    let n = match t_const_usize(m, tb, cid) { Some(n) => n, None => return Err(Halt::GaveUp) };
    let stride = match t_layout(m, tb, t) {
        Some(l) => match &l.fields {
            FieldsShape::Array { stride, count } => if *count == n && stride.num_bits % 8 == 0 { stride.num_bits / 8 } else {
                return Err(Halt::GaveUp);
            },
            _ => return Err(Halt::GaveUp),
        },
        None => return Err(Halt::GaveUp),
    };
    let (vs, c) = e_dec_elems(m, tb, e, stride, a, off, fuel, n)?;
    let v = CVal::Arr(vs);
    proof { lemma_cv(v); }
    Ok((v, c))
}

fn e_dec_adt(m: &MirCrate, tb: &Tabs, t: Ty, a: &Allocation, off: usize, fuel: usize) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures
        r matches Ok((v, k)) ==> dec_adt(*m, t, *a, off as nat, fuel as nat) == Some((cv(v), k as nat)),
        !(r matches Err(Halt::Panic)),
    decreases fuel, 2nat,
{
    let row = match t_adt_row(m, tb, t) { Some(r) => r, None => return Err(Halt::GaveUp) };
    let l = match t_layout(m, tb, t) { Some(l) => l, None => return Err(Halt::GaveUp) };
    if row.is_box || matches!(row.kind, AdtKind::Union) { return Err(Halt::GaveUp); }
    let (k, o) = match x_adt_sel(row, l, a, off) { Some(x) => x, None => return Err(Halt::GaveUp) };
    if !(k < row.variants.len() && o.len() == row.variants[k].fields.len()) { return Err(Halt::GaveUp); }
    let (vs, c) = e_dec_fields(m, tb, &row.variants[k].fields, o, a, off, fuel)?;
    if c == u64::MAX { return Err(Halt::GaveUp); }
    let v = CVal::Adt(k, vs);
    proof { lemma_cv(v); }
    Ok((v, c + 1))
}

fn e_dec_zst_ref(m: &MirCrate, tb: &Tabs, p: Ty) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures
        r matches Ok((v, k)) ==> dec_zst_ref(*m, p) == Some((cv(v), k as nat)),
        !(r matches Err(Halt::Panic)),
{
    let tf = match x_tfuel(m) { Some(f) => f, None => return Err(Halt::GaveUp) };
    match e_unit_like(m, tb, p, tf, true) {
        Ok((v, c)) => if c == u64::MAX { Err(Halt::GaveUp) } else { Ok((CVal::Shr(Box::new(v)), c + 1)) },
        Err(_) => Err(Halt::GaveUp),
    }
}

fn e_dec_ref(m: &MirCrate, tb: &Tabs, p: Ty, a: &Allocation, off: usize, fuel: usize) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures
        r matches Ok((v, k)) ==> dec_ref(*m, p, *a, off as nat, fuel as nat) == Some((cv(v), k as nat)),
        !(r matches Err(Halt::Panic)),
    decreases fuel, 2nat,
{
    let rp = t_rigid(m, tb, p);
    if matches!(rp, Some(RigidTy::Str)) {
        return match x_prov_at(a, off) {
            Some(id) => if t_alloc_mem(m, tb, id).is_some() { Ok((CVal::Unit, 0)) } else { Err(Halt::GaveUp) },
            None => Ok((CVal::Unit, 0)),
        };
    }
    let addr = match x_le(a, off, 8) { Some(x) => x, None => return Err(Halt::GaveUp) };
    match x_prov_at(a, off) {
        Some(id) => match (t_alloc_mem(m, tb, id), rp) {
            (Some(a2), Some(r)) => if t_is_zst(m, tb, p) { e_dec_zst_ref(m, tb, p) } else if matches!(r, RigidTy::Array(_, _)) {
                if addr > usize::MAX as u128 { return Err(Halt::GaveUp); }
                let (v, c) = e_dec(m, tb, p, a2, addr as usize, fuel)?;
                if c == u64::MAX { return Err(Halt::GaveUp); }
                Ok((CVal::Shr(Box::new(v)), c + 1))
            } else { Err(Halt::GaveUp) },
            _ => Err(Halt::GaveUp),
        },
        None => if x_no_prov(a, off, 8) && t_is_zst(m, tb, p) { e_dec_zst_ref(m, tb, p) } else { Err(Halt::GaveUp) },
    }
}

// ------------------------------------------------------------------ constant operands

/// `charged(m, t)`.
fn t_charged(m: &MirCrate, tb: &Tabs, t: Ty) -> (r: bool)
    requires tabs_ok(*m, *tb),
    ensures r == charged(*m, t),
{
    match t_rigid(m, tb, t) {
        Some(RigidTy::Adt(_, _)) => true,
        Some(RigidTy::Ref(_, p, _)) => t_is_zst(m, tb, *p),
        _ => false,
    }
}

/// `const_val(m, c)`: a constant operand's value and its step charge.
pub fn e_const_val(m: &MirCrate, tb: &Tabs, c: &ConstOperand) -> (r: R<(CVal, u64)>)
    requires tabs_ok(*m, *tb),
    ensures
        r matches Ok((v, k)) ==> const_val(*m, *c) == Some((cv(v), k as nat)),
        r matches Err(Halt::Panic) ==> const_val(*m, *c) is None,
{
    let t = c.const_.ty;
    match &c.const_.kind {
        ConstantKind::Allocated(a) => {
            let df = match x_dfuel(m) { Some(f) => f, None => return Err(Halt::GaveUp) };
            let (v, k) = e_dec(m, tb, t, a, 0, df)?;
            Ok((v, if t_charged(m, tb, t) { k } else { 0 }))
        },
        ConstantKind::ZeroSized => {
            let tf = match x_tfuel(m) { Some(f) => f, None => return Err(Halt::GaveUp) };
            let (v, _) = e_unit_like(m, tb, t, tf, true)?;
            if t_has_arr(m, tb, t, tf) { Ok((v, 0)) } else { Ok((CVal::Unit, 0)) }
        },
        _ => Err(Halt::Panic),
    }
}

} // verus!
