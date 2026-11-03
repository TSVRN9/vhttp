//! The translator's types and constants. A type lowers structurally (`lower_ty`, `lowers_ty`). A
//! constant lowers to a core operand plus the temps it needs (`Tmp`): ints are `Const`, int
//! arrays and shared references to them `Lit`, and each ADT or reference node that decision 7
//! charges one temp, assigned in post-order before the statement that reads it (`lowers_const`).
use crate::json::bytes_eq;
use crate::look::*;
use crate::mir::*;
#[cfg(verus_keep_ghost)]
use crate::rel::*;
#[cfg(verus_keep_ghost)]
use crate::sem::*;
use ctcore::syntax as c;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_vanish, lemma_small_mod};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{lemma2_to64, pow2};
use vstd::prelude::*;

verus! {

pub fn msg(s: &[u8]) -> (v: Vec<u8>)
    ensures v@ == s@,
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant i <= s@.len(), v@ == s@.subrange(0, i as int),
        decreases s.len() - i,
    {
        v.push(s[i]);
        i += 1;
    }
    v
}

/// The type-depth bound (`struct T { v: Vec<T> }` recurses).
pub const TYF: usize = 17;

// ------------------------------------------------------------------ types

#[verifier::loop_isolation(false)]
pub fn lower_ty(m: &MirCrate, t: Ty, fuel: usize) -> (r: Result<c::Ty, Vec<u8>>)
    ensures r matches Ok(ct) ==> lowers_ty(*m, t, ct, fuel as nat),
    decreases fuel, 1nat,
{
    if fuel == 0 { return Err(msg(b"type nested too deeply (recursive?)")); }
    let f = fuel - 1;
    let r = match x_rigid(m, t) { Some(r) => r, None => return Err(msg(b"non-rigid type")) };
    match r {
        RigidTy::Bool | RigidTy::Int(_) | RigidTy::Uint(_) => match x_int_of(r) {
            Some(it) => Ok(c::Ty::Int(it)),
            None => Err(msg(b"unknown integer type")),
        },
        RigidTy::Tuple(ts) => {
            if ts.len() == 0 { return Ok(c::Ty::Unit); }
            let mut v: Vec<c::Ty> = Vec::new();
            let mut k: usize = 0;
            while k < ts.len()
                invariant k <= ts@.len(), v@.len() == k, forall|i: int| 0 <= i < k ==> lowers_ty(*m, #[trigger] ts@[i], v@[i], f as nat),
                decreases ts.len() - k,
            {
                let e = lower_ty(m, ts[k], f)?;
                v.push(e);
                k += 1;
            }
            Ok(c::Ty::Tuple(v))
        },
        RigidTy::Adt(_, _) => lower_adt_ty(m, t, f),
        RigidTy::Array(e, n) => match x_const_usize(m, n.id) {
            Some(k) => Ok(c::Ty::Array(Box::new(lower_ty(m, *e, f)?), k)),
            None => Err(msg(b"array length")),
        },
        RigidTy::Slice(e) => Ok(c::Ty::Slice(Box::new(lower_ty(m, *e, f)?))),
        // `str` is opaque: nothing in the subset reads one
        RigidTy::Str => Ok(c::Ty::Unit),
        RigidTy::Ref(_, p, mu) => {
            let is_str = matches!(x_rigid(m, *p), Some(RigidTy::Str));
            match mu {
                Mutability::Not => if is_str { Ok(c::Ty::Unit) } else { Ok(c::Ty::Shr(Box::new(lower_ty(m, *p, f)?))) },
                Mutability::Mut => if is_str { Err(msg(b"type &mut str")) } else { Ok(c::Ty::Mut(Box::new(lower_ty(m, *p, f)?))) },
                Mutability::Unknown(_) => Err(msg(b"unknown mutability")),
            }
        },
        // ZST fn items, closures, and fn pointers (code values are the opaque `Unit`)
        RigidTy::FnDef(_, _) | RigidTy::Closure(_, _) | RigidTy::FnPtr(_) => Ok(c::Ty::Unit),
        _ => Err(msg(b"type outside the subset (float, char, raw pointer, dyn, never, pattern, ..)")),
    }
}

#[verifier::loop_isolation(false)]
pub fn lower_adt_ty(m: &MirCrate, t: Ty, f: usize) -> (r: Result<c::Ty, Vec<u8>>)
    ensures r matches Ok(ct) ==> lowers_adt_ty(*m, t, ct, f as nat),
    decreases f, 2nat,
{
    let a = match x_adt_row(m, t) { Some(a) => a, None => return Err(msg(b"type with no adts row")) };
    if bytes_eq(a.name.as_slice(), b"vstd::prelude::Ghost") || bytes_eq(a.name.as_slice(), b"vstd::prelude::Tracked") {
        return Ok(c::Ty::Unit);
    }
    if let Some(e) = x_vec_elem(m, t) { return Ok(c::Ty::Vec(Box::new(lower_ty(m, e, f)?))); }
    if bytes_eq(a.name.as_slice(), b"std::cell::UnsafeCell") || bytes_eq(a.name.as_slice(), b"core::cell::UnsafeCell") {
        return Err(msg(b"interior mutability (UnsafeCell)"));
    }
    if a.is_box || !(matches!(a.kind, AdtKind::Struct) || matches!(a.kind, AdtKind::Enum)) {
        return Err(msg(b"Box or union type"));
    }
    let mut vs: Vec<Vec<c::Ty>> = Vec::new();
    let mut k: usize = 0;
    while k < a.variants.len()
        invariant
            k <= a.variants@.len(), vs@.len() == k,
            forall|kk: int| 0 <= kk < k ==> {
                &&& (#[trigger] vs@[kk])@.len() == a.variants@[kk].fields@.len()
                &&& forall|i: int| 0 <= i < a.variants@[kk].fields@.len() ==> lowers_ty(*m, #[trigger] a.variants@[kk].fields@[i], vs@[kk]@[i], f as nat)
            },
        decreases a.variants.len() - k,
    {
        let fs = &a.variants[k].fields;
        let mut v: Vec<c::Ty> = Vec::new();
        let mut i: usize = 0;
        while i < fs.len()
            invariant
                k < a.variants@.len(), *fs == a.variants@[k as int].fields, i <= fs@.len(), v@.len() == i,
                forall|ii: int| 0 <= ii < i ==> lowers_ty(*m, #[trigger] fs@[ii], v@[ii], f as nat),
            decreases fs.len() - i,
        {
            v.push(lower_ty(m, fs[i], f)?);
            i += 1;
        }
        vs.push(v);
        k += 1;
    }
    Ok(c::Ty::Adt(vs))
}

// ------------------------------------------------------------------ allocation bytes

/// `le(a, off, n)`.
pub fn x_le(a: &Allocation, off: usize, n: usize) -> (r: Option<u128>)
    requires n <= 16,
    ensures r matches Some(v) ==> le(*a, off as nat, n as nat) == Some(v as nat),
    decreases n,
{
    if n == 0 { return Some(0); }
    if off >= a.bytes.len() { return None; }
    let x = match a.bytes[off] { Some(x) => x, None => return None };
    let r = match x_le(a, off + 1, n - 1) { Some(r) => r, None => return None };
    if r > 0xff_ffff_ffff_ffff_ffff_ffff_ffff_ffff { return None; }
    Some(x as u128 + 256 * r)
}

/// `no_prov(a, off, n)`.
pub fn x_no_prov(a: &Allocation, off: usize, n: usize) -> (r: bool)
    ensures r == no_prov(*a, off as nat, n as nat),
{
    let ps = &a.provenance.ptrs;
    let mut k: usize = 0;
    while k < ps.len()
        invariant k <= ps@.len(), *ps == a.provenance.ptrs,
            forall|i: int| 0 <= i < k ==> !(off < #[trigger] ps@[i].0 + 8 && ps@[i].0 < off + n),
        decreases ps.len() - k,
    {
        let o = ps[k].0 as u128;
        if (off as u128) < o + 8 && o < off as u128 + n as u128 { return false; }
        k += 1;
    }
    true
}

/// `prov_at(a, off)`.
pub fn x_prov_at(a: &Allocation, off: usize) -> (r: Option<AllocId>)
    ensures r == prov_at(*a, off as nat),
{
    let ps = &a.provenance.ptrs;
    let mut k: usize = 0;
    while k < ps.len()
        invariant k <= ps@.len(), *ps == a.provenance.ptrs, forall|i: int| 0 <= i < k ==> (#[trigger] ps@[i]).0 as nat != off as nat,
        decreases ps.len() - k,
    {
        if ps[k].0 == off {
            proof { lemma_prov_at(*a, off as nat, k as nat); }
            return Some(ps[k].1);
        }
        k += 1;
    }
    proof { lemma_prov_at(*a, off as nat, k as nat); }
    None
}

proof fn lemma_prov_at(a: Allocation, off: nat, k: nat)
    requires k <= a.provenance.ptrs@.len(), forall|i: int| 0 <= i < k ==> (#[trigger] a.provenance.ptrs@[i]).0 as nat != off,
        k < a.provenance.ptrs@.len() ==> a.provenance.ptrs@[k as int].0 as nat == off,
    ensures prov_at(a, off) == if k < a.provenance.ptrs@.len() { Some(a.provenance.ptrs@[k as int].1) } else { None },
{
    broadcast use lemma_find_spec;
}

pub fn x_ibytes(it: &c::IntTy) -> (n: usize)
    ensures n as nat == ibytes(*it), n <= 16,
{
    match it {
        c::IntTy::Bool | c::IntTy::U8 | c::IntTy::I8 => 1,
        c::IntTy::U16 | c::IntTy::I16 => 2,
        c::IntTy::U32 | c::IntTy::I32 => 4,
        c::IntTy::U64 | c::IntTy::I64 | c::IntTy::Usize | c::IntTy::Isize => 8,
        c::IntTy::U128 | c::IntTy::I128 => 16,
    }
}

/// `rd_int(a, off, it)`.
pub fn x_rd_int(a: &Allocation, off: usize, it: &c::IntTy) -> (r: Option<u128>)
    ensures r matches Some(v) ==> rd_int(*a, off as nat, *it) == Some(v),
{
    let n = x_ibytes(it);
    if !x_no_prov(a, off, n) { return None; }
    match x_le(a, off, n) {
        Some(v) => if matches!(it, c::IntTy::Bool) && v > 1 { None } else { Some(v) },
        None => None,
    }
}

/// `2^bits` for a tag width below 128 bits.
fn tag_mod(bits: usize) -> (r: Option<u128>)
    ensures r matches Some(md) ==> md as int == pow2(bits as nat) && 0 < md <= 0x1_0000_0000_0000_0000,
{
    proof { lemma2_to64(); }
    if bits == 8 { Some(0x100) } else if bits == 16 { Some(0x1_0000) } else if bits == 32 { Some(0x1_0000_0000) }
    else if bits == 64 { Some(0x1_0000_0000_0000_0000) } else { None }
}

/// `(t - ns) mod md`, for `t < md`.
proof fn lemma_niche_rel(t: int, ns: int, md: int)
    requires 0 <= t < md, 0 <= ns, md > 0,
    ensures ({ let nsm = ns % md; (t - ns) % md == if t >= nsm { t - nsm } else { t + (md - nsm) } }),
{
    let nsm = ns % md;
    lemma_fundamental_div_mod(ns, md);
    let q = ns / md;
    assert(ns == md * q + nsm);
    assert(0 <= nsm < md) by { vstd::arithmetic::div_mod::lemma_mod_bound(ns, md); }
    lemma_mod_multiples_vanish(-q, t - nsm, md);
    assert(md * (-q) + (t - nsm) == t - ns) by (nonlinear_arith) requires ns == md * q + nsm;
    if t >= nsm {
        lemma_small_mod((t - nsm) as nat, md as nat);
    } else {
        lemma_mod_multiples_vanish(1, t - nsm, md);
        lemma_small_mod((t + (md - nsm)) as nat, md as nat);
    }
}

pub open spec fn direct_hit(v: AdtVariant, t: nat, tbits: nat) -> bool {
    v.discr is Some && (v.discr->Some_0 as int) % (pow2(tbits) as int) == t as int
}

proof fn lemma_direct(row: Adt, t: nat, tbits: nat, k: nat)
    requires k < row.variants@.len(), forall|i: int| 0 <= i < k ==> !direct_hit(#[trigger] row.variants@[i], t, tbits),
        direct_hit(row.variants@[k as int], t, tbits),
    ensures tag_variant(row, TagEncoding::Direct, t, tbits) == Some(k),
{
    broadcast use lemma_find_spec;
}

/// `tag_variant(row, enc, t, tbits)`; 128-bit tags are rejected.
pub fn x_tag_variant(row: &Adt, enc: &TagEncoding, t: u128, tbits: usize) -> (r: Option<usize>)
    ensures r matches Some(k) ==> tag_variant(*row, *enc, t as nat, tbits as nat) == Some(k as nat),
{
    let md = match tag_mod(tbits) { Some(md) => md, None => return None };
    match enc {
        TagEncoding::Direct => {
            let mut k: usize = 0;
            while k < row.variants.len()
                invariant k <= row.variants@.len(), md as int == pow2(tbits as nat), md > 0, *enc == TagEncoding::Direct,
                    forall|i: int| 0 <= i < k ==> !direct_hit(#[trigger] row.variants@[i], t as nat, tbits as nat),
                decreases row.variants.len() - k,
            {
                if let Some(d) = row.variants[k].discr {
                    if d % md == t {
                        proof { lemma_direct(*row, t as nat, tbits as nat, k as nat); }
                        return Some(k);
                    }
                }
                k += 1;
            }
            None
        },
        TagEncoding::Niche { untagged_variant, niche_variants, niche_start } => {
            if t >= md { return None; }
            let ns = *niche_start % md;
            let rel = if t >= ns { t - ns } else { t + (md - ns) };
            proof { lemma_niche_rel(t as int, *niche_start as int, md as int); }
            let (lo, hi) = (niche_variants.start, niche_variants.end);
            if lo <= hi && rel <= (hi - lo) as u128 { Some(lo + rel as usize) } else { Some(*untagged_variant) }
        },
        _ => None,
    }
}

pub fn x_tag_bytes(p: &Primitive) -> (r: Option<usize>)
    ensures r matches Some(n) ==> tag_bytes(*p) == Some(n as nat) && n <= 16,
{
    match p {
        Primitive::Int { length, signed: _ } => match length {
            IntegerLength::I8 => Some(1), IntegerLength::I16 => Some(2), IntegerLength::I32 => Some(4),
            IntegerLength::I64 => Some(8), _ => Some(16),
        },
        Primitive::Pointer(_) => Some(8),
        _ => None,
    }
}

/// `adt_sel(row, l, a, off)`: the variant and its field offsets.
pub fn x_adt_sel<'a>(row: &Adt, l: &'a LayoutShape, a: &Allocation, off: usize) -> (r: Option<(usize, &'a Vec<MachineSize>)>)
    ensures r matches Some((k, o)) ==> adt_sel(*row, *l, *a, off as nat) == Some((k as nat, o@)),
{
    match &l.variants {
        VariantsShape::Single { index } => match &l.fields {
            FieldsShape::Arbitrary { offsets } => Some((*index, offsets)),
            _ => None,
        },
        VariantsShape::Multiple { tag, tag_encoding, tag_field, variants } => match (tag, &l.fields) {
            (Scalar::Initialized { value, valid_range: _ }, FieldsShape::Arbitrary { offsets: o }) => {
                if !(*tag_field < o.len() && o[*tag_field].num_bits % 8 == 0) { return None; }
                let n = match x_tag_bytes(value) { Some(n) => n, None => return None };
                let rel = o[*tag_field].num_bits / 8;
                if off > usize::MAX - rel { return None; }
                let toff = off + rel;
                if !x_no_prov(a, toff, n) { return None; }
                let t = match x_le(a, toff, n) { Some(t) => t, None => return None };
                match x_tag_variant(row, tag_encoding, t, 8 * n) {
                    Some(k) => if k < variants.len() { Some((k, &variants[k].offsets)) } else { None },
                    None => None,
                }
            },
            _ => None,
        },
        _ => None,
    }
}

// ------------------------------------------------------------------ temps

/// The temps of one body: fresh locals after the MIR ones (`nloc`), their types, and the
/// pending assignments of the statement or terminator being lowered.
pub struct Tmp { pub nloc: usize, pub tys: Vec<c::Ty>, pub pre: Vec<c::Stmt> }

/// The next temp's local.
pub open spec fn tbase(t: Tmp) -> nat { (t.nloc + t.tys@.len()) as nat }

/// `new` is `old` with assignments appended, one fresh temp each.
pub open spec fn grew(old: Tmp, new: Tmp) -> bool {
    &&& new.nloc == old.nloc && new.pre@.len() >= old.pre@.len() && new.pre@.subrange(0, old.pre@.len() as int) == old.pre@
    &&& new.tys@.len() - old.tys@.len() == new.pre@.len() - old.pre@.len()
}

/// The assignments appended since `old`.
pub open spec fn seg(old: Tmp, new: Tmp) -> Seq<c::Stmt> { new.pre@.subrange(old.pre@.len() as int, new.pre@.len() as int) }

pub fn pl(local: usize) -> (p: c::Place)
    ensures p.local == local, p.proj@.len() == 0,
{
    c::Place { local, proj: Vec::new() }
}

/// A fresh temp of type `ty`, assigned `rv` in `tmp.pre`.
pub fn fresh(tmp: &mut Tmp, ty: c::Ty, rv: c::Rvalue) -> (r: Result<usize, Vec<u8>>)
    ensures r matches Ok(x) ==> {
        &&& x as nat == tbase(*old(tmp)) && grew(*old(tmp), *final(tmp)) && final(tmp).pre@.len() == old(tmp).pre@.len() + 1
        &&& final(tmp).pre@.last() is Assign && final(tmp).pre@.last()->Assign_0.local == x && final(tmp).pre@.last()->Assign_0.proj@.len() == 0
        &&& final(tmp).pre@.last()->Assign_1 == rv
    },
{
    if tmp.tys.len() >= usize::MAX - tmp.nloc { return Err(msg(b"too many temps")); }
    let local = tmp.nloc + tmp.tys.len();
    tmp.tys.push(ty);
    tmp.pre.push(c::Stmt::Assign(pl(local), rv));
    proof { assert(tmp.pre@.subrange(0, old(tmp).pre@.len() as int) =~= old(tmp).pre@); }
    Ok(local)
}

/// One temp's segment satisfies `temps_at`.
proof fn lemma_one_temp(old: Tmp, new: Tmp, x: nat)
    requires grew(old, new), new.pre@.len() == old.pre@.len() + 1, x == tbase(old),
        new.pre@.last() is Assign, new.pre@.last()->Assign_0.local == x, new.pre@.last()->Assign_0.proj@.len() == 0,
    ensures temps_at(seg(old, new), tbase(old)), seg(old, new).len() == 1, seg(old, new)[0] == new.pre@.last(),
{
    assert(seg(old, new)[0] == new.pre@.last());
}

/// Appending a segment after a segment: both are segments of the whole, `temps_at` composes.
proof fn lemma_seg_trans(t0: Tmp, t1: Tmp, t2: Tmp)
    requires grew(t0, t1), grew(t1, t2), temps_at(seg(t0, t1), tbase(t0)), temps_at(seg(t1, t2), tbase(t1)),
    ensures grew(t0, t2), temps_at(seg(t0, t2), tbase(t0)), tbase(t1) == tbase(t0) + seg(t0, t1).len(),
        seg(t0, t2).subrange(0, seg(t0, t1).len() as int) == seg(t0, t1),
        seg(t0, t2).subrange(seg(t0, t1).len() as int, seg(t0, t2).len() as int) == seg(t1, t2),
{
    let (n0, n1, n2) = (t0.pre@.len() as int, t1.pre@.len() as int, t2.pre@.len() as int);
    assert(t2.pre@.subrange(0, n0) =~= t2.pre@.subrange(0, n1).subrange(0, n0));
    assert(seg(t0, t2).subrange(0, n1 - n0) =~= seg(t0, t1));
    assert(seg(t0, t2).subrange(n1 - n0, n2 - n0) =~= seg(t1, t2));
    assert forall|i: int| 0 <= i < seg(t0, t2).len() implies (#[trigger] seg(t0, t2)[i]) is Assign
        && seg(t0, t2)[i]->Assign_0.local == tbase(t0) + i && seg(t0, t2)[i]->Assign_0.proj@.len() == 0 by {
        if i < n1 - n0 { assert(seg(t0, t2)[i] == seg(t0, t1)[i]); } else { assert(seg(t0, t2)[i] == seg(t1, t2)[i - (n1 - n0)]); }
    };
}

// ------------------------------------------------------------------ constant values

/// The value of a "literal" type (ints, arrays of literals, `&str`, `&ZST` with a literal value,
/// `&[T; N]`) at `off`, and its ADT/reference node count, mirroring `dec`.
pub fn x_lit(m: &MirCrate, t: Ty, a: &Allocation, off: usize, fuel: usize) -> (r: Result<(c::ConstVal, usize), Vec<u8>>)
    ensures r matches Ok((cv, k)) ==> dec(*m, t, *a, off as nat, fuel as nat) == Some((core_cv(cv), k as nat)),
    decreases fuel, 1nat,
{
    if fuel == 0 { return Err(msg(b"constant nested too deeply")); }
    let f = fuel - 1;
    let r = match x_rigid(m, t) { Some(r) => r, None => return Err(msg(b"constant of a non-rigid type")) };
    if let Some(it) = x_int_of(r) {
        return match x_rd_int(a, off, &it) {
            Some(v) => Ok((c::ConstVal::Int(v), 0)),
            None => Err(msg(b"an integer constant with an uninitialized byte or a pointer")),
        };
    }
    match r {
        RigidTy::Array(e, cn) => x_lit_array(m, t, *e, cn.id, a, off, f),
        RigidTy::Ref(_, p, Mutability::Not) => x_lit_ref(m, *p, a, off, f),
        _ => Err(msg(b"constant of a type outside the subset (a tuple, ..)")),
    }
}

/// `dec_array` at fuel `f`.
#[verifier::loop_isolation(false)]
pub fn x_lit_array(m: &MirCrate, t: Ty, e: Ty, cid: TyConstId, a: &Allocation, off: usize, f: usize) -> (r: Result<(c::ConstVal, usize), Vec<u8>>)
    ensures r matches Ok((cv, k)) ==> dec_array(*m, t, e, cid, *a, off as nat, f as nat) == Some((core_cv(cv), k as nat)),
    decreases f, 2nat,
{
    let n = match x_const_usize(m, cid) { Some(n) => n, None => return Err(msg(b"array length")) };
    let l = match x_layout(m, t) { Some(l) => l, None => return Err(msg(b"constant array without a layout")) };
    let stride = match &l.fields {
        FieldsShape::Array { stride, count } => if *count == n && stride.num_bits % 8 == 0 { stride.num_bits / 8 } else {
            return Err(msg(b"constant array layout"));
        },
        _ => return Err(msg(b"constant array layout")),
    };
    let mut vs: Vec<c::ConstVal> = Vec::new();
    let mut cnt: usize = 0;
    let mut i: u64 = 0;
    let mut at: usize = off;
    while i < n
        invariant
            i <= n, vs@.len() == i, at as int == off + i * stride,
            dec_elems(*m, e, stride as nat, *a, off as nat, f as nat, i as nat) matches Some((ws, k))
                && k == cnt && ws.len() == i && forall|j: int| 0 <= j < i ==> ws[j] == core_cv(#[trigger] vs@[j]),
        decreases n - i,
    {
        let (v, k) = x_lit(m, e, a, at, f)?;
        proof {
            let ws = dec_elems(*m, e, stride as nat, *a, off as nat, f as nat, i as nat)->Some_0.0;
            assert(dec_elems(*m, e, stride as nat, *a, off as nat, f as nat, (i + 1) as nat)
                == Some((ws.push(core_cv(v)), cnt as nat + k as nat)));
        }
        vs.push(v);
        if cnt > usize::MAX - k || at > usize::MAX - stride { return Err(msg(b"constant too large")); }
        cnt = cnt + k;
        at = at + stride;
        proof { assert(at as int == off + (i + 1) * stride) by (nonlinear_arith) requires at as int == off + i * stride + stride; }
        i += 1;
    }
    proof {
        let ws = dec_elems(*m, e, stride as nat, *a, off as nat, f as nat, n as nat)->Some_0.0;
        let w = core_cv(c::ConstVal::Arr(vs));
        assert(w->Arr_0.len() == vs@.len());
        assert forall|j: int| 0 <= j < ws.len() implies w->Arr_0[j] == ws[j] by { assert(w->Arr_0[j] == core_cv(vs@[j])); };
        assert(w->Arr_0 =~= ws);
    }
    Ok((c::ConstVal::Arr(vs), cnt))
}

/// `dec_ref` at fuel `f`: `&str` (opaque), `&ZST` with a literal value, `&[T; N]` through its
/// provenance.
pub fn x_lit_ref(m: &MirCrate, p: Ty, a: &Allocation, off: usize, f: usize) -> (r: Result<(c::ConstVal, usize), Vec<u8>>)
    ensures r matches Ok((cv, k)) ==> dec_ref(*m, p, *a, off as nat, f as nat) == Some((core_cv(cv), k as nat)),
    decreases f, 2nat,
{
    if matches!(x_rigid(m, p), Some(RigidTy::Str)) {
        return match x_prov_at(a, off) {
            Some(id) => if x_alloc_mem(m, id).is_some() { Ok((c::ConstVal::Unit, 0)) } else { Err(msg(b"&str constant into a non-memory allocation")) },
            None => Ok((c::ConstVal::Unit, 0)),
        };
    }
    let addr = match x_le(a, off, 8) { Some(x) => x, None => return Err(msg(b"a constant reference with uninitialized bytes")) };
    let target = match x_prov_at(a, off) {
        Some(id) => match x_alloc_mem(m, id) { Some(a2) => Some(a2), None => return Err(msg(b"a constant reference to a non-memory allocation")) },
        None => if x_no_prov(a, off, 8) { None } else { return Err(msg(b"a constant reference with a partial pointer")) },
    };
    if x_is_zst(m, p) {
        let tf = match x_tfuel(m) { Some(tf) => tf, None => return Err(msg(b"too many types")) };
        let (v, k) = x_ul_lit(m, p, tf)?;
        return Ok((c::ConstVal::Shr(Box::new(v)), k + 1));
    }
    match (target, x_rigid(m, p)) {
        (Some(a2), Some(RigidTy::Array(_, _))) => {
            if addr > usize::MAX as u128 { return Err(msg(b"constant reference address")); }
            let (v, k) = x_lit(m, p, a2, addr as usize, f)?;
            if k == usize::MAX { return Err(msg(b"constant too large")); }
            Ok((c::ConstVal::Shr(Box::new(v)), k + 1))
        },
        _ => Err(msg(b"a constant reference to a non-zero-sized value")),
    }
}

/// A literal unit-like value (`unit_like` with closures allowed): fn items, closures, `[T; 0]`.
pub fn x_ul_lit(m: &MirCrate, t: Ty, fuel: usize) -> (r: Result<(c::ConstVal, usize), Vec<u8>>)
    ensures r matches Ok((cv, k)) ==> unit_like(*m, t, fuel as nat, true) == Some((core_cv(cv), k as nat)) && k == 0,
{
    if fuel == 0 { return Err(msg(b"constant nested too deeply")); }
    match x_rigid(m, t) {
        Some(RigidTy::FnDef(_, _)) | Some(RigidTy::Closure(_, _)) => Ok((c::ConstVal::Unit, 0)),
        Some(RigidTy::Array(_, cn)) => match x_const_usize(m, cn.id) {
            Some(0) => {
                let v: Vec<c::ConstVal> = Vec::new();
                proof {
                    let w = core_cv(c::ConstVal::Arr(v));
                    assert(w->Arr_0.len() == 0);
                    assert(w->Arr_0 =~= Seq::<ctcore::sem::Val>::empty());
                }
                Ok((c::ConstVal::Arr(v), 0))
            },
            _ => Err(msg(b"a constant reference to a non-empty array of zero-sized values")),
        },
        _ => Err(msg(b"a constant reference to a zero-sized value that is not a literal")),
    }
}

/// The ADT node at `off` (`dec_adt` at `fuel - 1`): its fields, then one temp.
pub fn x_adt(m: &MirCrate, t: Ty, a: &Allocation, off: usize, fuel: usize, tmp: &mut Tmp) -> (r: Result<c::Operand, Vec<u8>>)
    requires fuel > 0, rigid(*m, t) matches Some(RigidTy::Adt(_, _)),
    ensures r matches Ok(y) ==> grew(*old(tmp), *final(tmp)) && lowers_cv(*m, t, *a, off as nat, fuel as nat, y, seg(*old(tmp), *final(tmp)), tbase(*old(tmp))),
    decreases fuel, 1nat,
{
    let f = fuel - 1;
    let ct = lower_ty(m, t, TYF)?;
    if !matches!(ct, c::Ty::Adt(_)) { return Err(msg(b"constant of a unit-mapped ADT (Ghost, Tracked, Vec)")); }
    let row = match x_adt_row(m, t) { Some(r) => r, None => return Err(msg(b"constant of a type with no adts row")) };
    let l = match x_layout(m, t) { Some(l) => l, None => return Err(msg(b"constant without a layout")) };
    if row.is_box || matches!(row.kind, AdtKind::Union) { return Err(msg(b"Box or union constant")); }
    if let VariantsShape::Multiple { tag: Scalar::Initialized { value: Primitive::Int { signed: true, .. }, .. }, tag_encoding: TagEncoding::Direct, .. } = &l.variants {
        return Err(msg(b"constant with a signed tag"));
    }
    let (k, o) = match x_adt_sel(row, l, a, off) { Some(x) => x, None => return Err(msg(b"constant whose variant does not decode (a pointer tag, ..)")) };
    if !(k < row.variants.len() && o.len() == row.variants[k].fields.len()) { return Err(msg(b"constant variant layout")); }
    let fs = &row.variants[k].fields;
    let ghost t0 = *old(tmp);
    let ops = x_fields(m, fs, o, a, off, f, tmp)?;
    let ghost t2 = *tmp;
    let x = fresh(tmp, ct, c::Rvalue::Aggregate(c::AggKind::Adt(k), ops))?;
    let y = c::Operand::Copy(pl(x));
    proof { lemma_adt_close(*m, t, *a, off as nat, fuel as nat, k as nat, o@, t0, t2, *tmp, x as nat); assert(is_tmp(y, x as nat)); }
    Ok(y)
}

/// The fields of an ADT constant, left to right, their temps one after another.
#[verifier::loop_isolation(false)]
pub fn x_fields(m: &MirCrate, fs: &Vec<Ty>, o: &Vec<MachineSize>, a: &Allocation, off: usize, f: usize, tmp: &mut Tmp)
    -> (r: Result<Vec<c::Operand>, Vec<u8>>)
    requires fs@.len() == o@.len(),
    ensures r matches Ok(ops) ==> {
        let (t0, t2) = (*old(tmp), *final(tmp));
        &&& grew(t0, t2) && temps_at(seg(t0, t2), tbase(t0)) && ops@.len() == fs@.len()
        &&& dec_fields(*m, fs@, o@, *a, off as nat, f as nat, fs@.len()) is Some
        &&& fcount(*m, fs@, o@, *a, off as nat, f as nat, fs@.len()) == seg(t0, t2).len()
        &&& forall|j: int| 0 <= j < fs@.len() ==> lowers_cv(*m, #[trigger] fs@[j], *a, (off + o@[j].num_bits / 8) as nat, f as nat, ops@[j],
                seg(t0, t2).subrange(fcount(*m, fs@, o@, *a, off as nat, f as nat, j as nat) as int, fcount(*m, fs@, o@, *a, off as nat, f as nat, (j + 1) as nat) as int),
                tbase(t0) + fcount(*m, fs@, o@, *a, off as nat, f as nat, j as nat))
    },
    decreases f, 3nat,
{
    let ghost t0 = *old(tmp);
    let ghost base = tbase(t0);
    proof { assert(tmp.pre@.subrange(0, tmp.pre@.len() as int) =~= tmp.pre@); assert(seg(t0, *tmp) =~= Seq::<c::Stmt>::empty()); }
    let mut ops: Vec<c::Operand> = Vec::new();
    let mut i: usize = 0;
    while i < fs.len()
        invariant
            i <= fs@.len(), fs@.len() == o@.len(), t0 == *old(tmp), base == tbase(t0),
            grew(t0, *tmp), temps_at(seg(t0, *tmp), base), ops@.len() == i,
            dec_fields(*m, fs@, o@, *a, off as nat, f as nat, i as nat) is Some,
            fcount(*m, fs@, o@, *a, off as nat, f as nat, i as nat) == seg(t0, *tmp).len(),
            forall|j: int| 0 <= j < i ==> lowers_cv(*m, #[trigger] fs@[j], *a, (off + o@[j].num_bits / 8) as nat, f as nat, ops@[j],
                seg(t0, *tmp).subrange(fcount(*m, fs@, o@, *a, off as nat, f as nat, j as nat) as int, fcount(*m, fs@, o@, *a, off as nat, f as nat, (j + 1) as nat) as int),
                base + fcount(*m, fs@, o@, *a, off as nat, f as nat, j as nat)),
        decreases fs.len() - i,
    {
        if o[i].num_bits % 8 != 0 { return Err(msg(b"constant field offset")); }
        let rel = o[i].num_bits / 8;
        if off > usize::MAX - rel { return Err(msg(b"constant too large")); }
        let ghost t1 = *tmp;
        let y = x_cv(m, fs[i], a, off + rel, f, tmp)?;
        proof { lemma_field_step(*m, fs@, o@, *a, off as nat, f as nat, i as nat, t0, t1, *tmp, ops@, y); }
        ops.push(y);
        i += 1;
    }
    Ok(ops)
}
/// One field step of `x_fields`'s loop.
proof fn lemma_field_step(m: MirCrate, fs: Seq<Ty>, o: Seq<MachineSize>, a: Allocation, off: nat, f: nat, i: nat,
    t0: Tmp, t1: Tmp, t2: Tmp, ops: Seq<c::Operand>, y: c::Operand)
    requires
        i < fs.len(), fs.len() == o.len(), o[i as int].num_bits % 8 == 0, ops.len() == i,
        grew(t0, t1), temps_at(seg(t0, t1), tbase(t0)), dec_fields(m, fs, o, a, off, f, i) is Some,
        fcount(m, fs, o, a, off, f, i) == seg(t0, t1).len(),
        forall|j: int| 0 <= j < i ==> lowers_cv(m, #[trigger] fs[j], a, (off + o[j].num_bits / 8) as nat, f, ops[j],
            seg(t0, t1).subrange(fcount(m, fs, o, a, off, f, j as nat) as int, fcount(m, fs, o, a, off, f, (j + 1) as nat) as int),
            tbase(t0) + fcount(m, fs, o, a, off, f, j as nat)),
        grew(t1, t2), lowers_cv(m, fs[i as int], a, (off + o[i as int].num_bits / 8) as nat, f, y, seg(t1, t2), tbase(t1)),
    ensures
        grew(t0, t2), temps_at(seg(t0, t2), tbase(t0)), dec_fields(m, fs, o, a, off, f, i + 1) is Some,
        fcount(m, fs, o, a, off, f, i + 1) == seg(t0, t2).len(),
        forall|j: int| 0 <= j < i + 1 ==> lowers_cv(m, #[trigger] fs[j], a, (off + o[j].num_bits / 8) as nat, f, ops.push(y)[j],
            seg(t0, t2).subrange(fcount(m, fs, o, a, off, f, j as nat) as int, fcount(m, fs, o, a, off, f, (j + 1) as nat) as int),
            tbase(t0) + fcount(m, fs, o, a, off, f, j as nat)),
{
    lemma_seg_trans(t0, t1, t2);
    assert(dec_fields(m, fs, o, a, off, f, i + 1) is Some);
    assert forall|j: int| 0 <= j < i + 1 implies lowers_cv(m, #[trigger] fs[j], a, (off + o[j].num_bits / 8) as nat, f, ops.push(y)[j],
        seg(t0, t2).subrange(fcount(m, fs, o, a, off, f, j as nat) as int, fcount(m, fs, o, a, off, f, (j + 1) as nat) as int),
        tbase(t0) + fcount(m, fs, o, a, off, f, j as nat)) by {
        if j < i {
            lemma_fcount_mono(m, fs, o, a, off, f, (j + 1) as nat, i);
            lemma_fcount_mono(m, fs, o, a, off, f, j as nat, (j + 1) as nat);
            assert(seg(t0, t2).subrange(fcount(m, fs, o, a, off, f, j as nat) as int, fcount(m, fs, o, a, off, f, (j + 1) as nat) as int)
                =~= seg(t0, t1).subrange(fcount(m, fs, o, a, off, f, j as nat) as int, fcount(m, fs, o, a, off, f, (j + 1) as nat) as int));
        } else {
            assert(ops.push(y)[j] == y);
            assert(seg(t0, t2).subrange(fcount(m, fs, o, a, off, f, j as nat) as int, fcount(m, fs, o, a, off, f, (j + 1) as nat) as int) =~= seg(t1, t2));
        }
    };
}

/// `fcount` grows with `n` while `dec_fields` succeeds.
proof fn lemma_fcount_mono(m: MirCrate, fs: Seq<Ty>, o: Seq<MachineSize>, a: Allocation, off: nat, f: nat, j: nat, n: nat)
    requires j <= n, dec_fields(m, fs, o, a, off, f, n) is Some,
    ensures dec_fields(m, fs, o, a, off, f, j) is Some, fcount(m, fs, o, a, off, f, j) <= fcount(m, fs, o, a, off, f, n),
    decreases n - j,
{
    if j < n { lemma_fcount_mono(m, fs, o, a, off, f, j, (n - 1) as nat); }
}

/// The ADT node's own temp closes `x_adt`.
proof fn lemma_adt_close(m: MirCrate, t: Ty, a: Allocation, off: nat, fuel: nat, k: nat, o: Seq<MachineSize>, t0: Tmp, t2: Tmp, t3: Tmp, x: nat)
    requires
        fuel > 0, rigid(m, t) matches Some(RigidTy::Adt(_, _)),
        adt_row(m, t) matches Some(row) && layout(m, t) matches Some(l) && !row.is_box && !(row.kind is Union)
            && adt_sel(row, l, a, off) == Some((k, o)) && k < row.variants@.len() && o.len() == row.variants@[k as int].fields@.len() && {
            let fs = row.variants@[k as int].fields@;
            let f = (fuel - 1) as nat;
            &&& grew(t0, t2) && temps_at(seg(t0, t2), tbase(t0))
            &&& dec_fields(m, fs, o, a, off, f, fs.len()) is Some && fcount(m, fs, o, a, off, f, fs.len()) == seg(t0, t2).len()
            &&& t3.pre@.last() is Assign && t3.pre@.last()->Assign_1 is Aggregate && t3.pre@.last()->Assign_1->Aggregate_0 == c::AggKind::Adt(k as usize)
            &&& t3.pre@.last()->Assign_1->Aggregate_1@.len() == fs.len()
            &&& forall|j: int| 0 <= j < fs.len() ==> lowers_cv(m, #[trigger] fs[j], a, (off + o[j].num_bits / 8) as nat, f, t3.pre@.last()->Assign_1->Aggregate_1@[j],
                    seg(t0, t2).subrange(fcount(m, fs, o, a, off, f, j as nat) as int, fcount(m, fs, o, a, off, f, (j + 1) as nat) as int),
                    tbase(t0) + fcount(m, fs, o, a, off, f, j as nat))
        },
        x == tbase(t2), grew(t2, t3), t3.pre@.len() == t2.pre@.len() + 1,
        t3.pre@.last()->Assign_0.local == x, t3.pre@.last()->Assign_0.proj@.len() == 0,
    ensures grew(t0, t3), forall|y: c::Operand| is_tmp(y, x) ==> lowers_cv(m, t, a, off, fuel, y, seg(t0, t3), tbase(t0)),
{
    let row = adt_row(m, t)->Some_0;
    let l = layout(m, t)->Some_0;
    let fs = row.variants@[k as int].fields@;
    let f = (fuel - 1) as nat;
    let c = fcount(m, fs, o, a, off, f, fs.len());
    lemma_one_temp(t2, t3, x);
    lemma_seg_trans(t0, t2, t3);
    let pre = seg(t0, t3);
    assert(pre[c as int] == t3.pre@.last()) by { assert(seg(t2, t3)[0] == pre[c as int]); };
    assert(dec_adt(m, t, a, off, f) == Some((ctcore::sem::Val::Adt(k, dec_fields(m, fs, o, a, off, f, fs.len())->Some_0.0), c + 1)));
    assert(int_of(rigid(m, t)->Some_0) is None);
    assert(dec(m, t, a, off, fuel) == Some((ctcore::sem::Val::Adt(k, dec_fields(m, fs, o, a, off, f, fs.len())->Some_0.0), c + 1)));
    assert forall|j: int| 0 <= j < fs.len() implies lowers_cv(m, #[trigger] fs[j], a, (off + o[j].num_bits / 8) as nat, f, tmp_rv(pre, c as int)->Aggregate_1@[j],
        pre.subrange(fcount(m, fs, o, a, off, f, j as nat) as int, fcount(m, fs, o, a, off, f, (j + 1) as nat) as int),
        tbase(t0) + fcount(m, fs, o, a, off, f, j as nat)) by {
        lemma_fcount_mono(m, fs, o, a, off, f, (j + 1) as nat, fs.len());
        lemma_fcount_mono(m, fs, o, a, off, f, j as nat, (j + 1) as nat);
        assert(pre.subrange(fcount(m, fs, o, a, off, f, j as nat) as int, fcount(m, fs, o, a, off, f, (j + 1) as nat) as int)
            =~= seg(t0, t2).subrange(fcount(m, fs, o, a, off, f, j as nat) as int, fcount(m, fs, o, a, off, f, (j + 1) as nat) as int));
    };
    assert forall|y: c::Operand| is_tmp(y, x) implies lowers_cv(m, t, a, off, fuel, y, pre, tbase(t0)) by {
        assert(adt_img(m, t, a, off, f, y, pre, tbase(t0)));
    };
}

/// A unit-like ADT value (`unit_like` with closures allowed): its fields, then one temp.
pub fn x_ul(m: &MirCrate, t: Ty, fuel: usize, tmp: &mut Tmp) -> (r: Result<c::Operand, Vec<u8>>)
    ensures r matches Ok(y) ==> grew(*old(tmp), *final(tmp)) && seg(*old(tmp), *final(tmp)).len() >= 1
        && is_tmp(y, (tbase(*old(tmp)) + seg(*old(tmp), *final(tmp)).len() - 1) as nat)
        && ul_img(*m, t, fuel as nat, y, seg(*old(tmp), *final(tmp)), tbase(*old(tmp))),
    decreases fuel, 1nat,
{
    if fuel == 0 { return Err(msg(b"constant nested too deeply")); }
    let f = fuel - 1;
    let ct = lower_ty(m, t, TYF)?;
    if !matches!(ct, c::Ty::Adt(_)) { return Err(msg(b"constant of a unit-mapped ADT (Ghost, Tracked)")); }
    if !matches!(x_rigid(m, t), Some(RigidTy::Adt(_, _))) { return Err(msg(b"a zero-sized constant that is not a struct")); }
    let row = match x_adt_row(m, t) { Some(r) => r, None => return Err(msg(b"constant of a type with no adts row")) };
    if row.is_box || matches!(row.kind, AdtKind::Union) || row.variants.len() != 1 { return Err(msg(b"a zero-sized constant that is not a struct")); }
    let fs = &row.variants[0].fields;
    let ghost t0 = *old(tmp);
    let ops = x_ul_fields(m, fs, f, tmp)?;
    let ghost t2 = *tmp;
    let x = fresh(tmp, ct, c::Rvalue::Aggregate(c::AggKind::Adt(0), ops))?;
    let y = c::Operand::Copy(pl(x));
    proof { lemma_ul_close(*m, t, fuel as nat, t0, t2, *tmp, x as nat); assert(is_tmp(y, x as nat)); }
    Ok(y)
}

/// A unit-like struct's fields: nested unit-like structs, `()`, and literal unit-like values.
#[verifier::loop_isolation(false)]
pub fn x_ul_fields(m: &MirCrate, fs: &Vec<Ty>, f: usize, tmp: &mut Tmp) -> (r: Result<Vec<c::Operand>, Vec<u8>>)
    ensures r matches Ok(ops) ==> {
        let (t0, t2) = (*old(tmp), *final(tmp));
        &&& grew(t0, t2) && temps_at(seg(t0, t2), tbase(t0)) && ops@.len() == fs@.len()
        &&& unit_likes(*m, fs@, f as nat, fs@.len(), true) is Some && ucount(*m, fs@, f as nat, fs@.len()) == seg(t0, t2).len()
        &&& forall|j: int| 0 <= j < fs@.len() ==> ul_img(*m, #[trigger] fs@[j], f as nat, ops@[j],
                seg(t0, t2).subrange(ucount(*m, fs@, f as nat, j as nat) as int, ucount(*m, fs@, f as nat, (j + 1) as nat) as int),
                tbase(t0) + ucount(*m, fs@, f as nat, j as nat))
    },
    decreases f, 2nat,
{
    let ghost t0 = *old(tmp);
    proof { assert(tmp.pre@.subrange(0, tmp.pre@.len() as int) =~= tmp.pre@); assert(seg(t0, *tmp) =~= Seq::<c::Stmt>::empty()); }
    let mut ops: Vec<c::Operand> = Vec::new();
    let mut i: usize = 0;
    while i < fs.len()
        invariant
            i <= fs@.len(), t0 == *old(tmp),
            grew(t0, *tmp), temps_at(seg(t0, *tmp), tbase(t0)), ops@.len() == i,
            unit_likes(*m, fs@, f as nat, i as nat, true) is Some, ucount(*m, fs@, f as nat, i as nat) == seg(t0, *tmp).len(),
            forall|j: int| 0 <= j < i ==> ul_img(*m, #[trigger] fs@[j], f as nat, ops@[j],
                seg(t0, *tmp).subrange(ucount(*m, fs@, f as nat, j as nat) as int, ucount(*m, fs@, f as nat, (j + 1) as nat) as int),
                tbase(t0) + ucount(*m, fs@, f as nat, j as nat)),
        decreases fs.len() - i,
    {
        let ghost t1 = *tmp;
        let y = match x_rigid(m, fs[i]) {
            Some(RigidTy::Adt(_, _)) => x_ul(m, fs[i], f, tmp)?,
            Some(RigidTy::Tuple(ts)) => if ts.len() == 0 && f > 0 {
                proof { lemma_unit_tuple_ul(*m, fs@[i as int], f as nat, *tmp); }
                c::Operand::Lit(c::ConstVal::Unit)
            } else {
                return Err(msg(b"a zero-sized constant with a tuple field"));
            },
            _ => {
                let (v, _) = x_ul_lit(m, fs[i], f)?;
                proof { lemma_lit_ul(*m, fs@[i as int], f as nat, v, *tmp); }
                c::Operand::Lit(v)
            },
        };
        proof { lemma_ul_step(*m, fs@, f as nat, i as nat, t0, t1, *tmp, ops@, y); }
        ops.push(y);
        i += 1;
    }
    Ok(ops)
}

proof fn lemma_unit_tuple_ul(m: MirCrate, t: Ty, f: nat, t1: Tmp)
    requires f > 0, rigid(m, t) matches Some(RigidTy::Tuple(ts)) && ts@.len() == 0,
    ensures ul_img(m, t, f, c::Operand::Lit(c::ConstVal::Unit), seg(t1, t1), tbase(t1)), grew(t1, t1),
{
    assert(t1.pre@.subrange(0, t1.pre@.len() as int) =~= t1.pre@);
    assert(seg(t1, t1) =~= Seq::<c::Stmt>::empty());
    let ts = rigid(m, t)->Some_0->Tuple_0;
    assert(unit_likes(m, ts@, (f - 1) as nat, 0, true) == Some((Seq::<ctcore::sem::Val>::empty(), 0nat)));
    assert(unit_like(m, t, f, true) == Some((unit_val(), 0nat)));
}

proof fn lemma_lit_ul(m: MirCrate, t: Ty, f: nat, v: c::ConstVal, t1: Tmp)
    requires f > 0, unit_like(m, t, f, true) == Some((core_cv(v), 0nat)),
    ensures ul_img(m, t, f, c::Operand::Lit(v), seg(t1, t1), tbase(t1)), grew(t1, t1),
{
    assert(t1.pre@.subrange(0, t1.pre@.len() as int) =~= t1.pre@);
    assert(seg(t1, t1) =~= Seq::<c::Stmt>::empty());
}

/// One field step of `x_ul_fields`'s loop.
proof fn lemma_ul_step(m: MirCrate, fs: Seq<Ty>, f: nat, i: nat, t0: Tmp, t1: Tmp, t2: Tmp, ops: Seq<c::Operand>, y: c::Operand)
    requires
        i < fs.len(), ops.len() == i,
        grew(t0, t1), temps_at(seg(t0, t1), tbase(t0)), unit_likes(m, fs, f, i, true) is Some,
        ucount(m, fs, f, i) == seg(t0, t1).len(),
        forall|j: int| 0 <= j < i ==> ul_img(m, #[trigger] fs[j], f, ops[j],
            seg(t0, t1).subrange(ucount(m, fs, f, j as nat) as int, ucount(m, fs, f, (j + 1) as nat) as int), tbase(t0) + ucount(m, fs, f, j as nat)),
        grew(t1, t2), ul_img(m, fs[i as int], f, y, seg(t1, t2), tbase(t1)),
    ensures
        grew(t0, t2), temps_at(seg(t0, t2), tbase(t0)), unit_likes(m, fs, f, i + 1, true) is Some,
        ucount(m, fs, f, i + 1) == seg(t0, t2).len(),
        forall|j: int| 0 <= j < i + 1 ==> ul_img(m, #[trigger] fs[j], f, ops.push(y)[j],
            seg(t0, t2).subrange(ucount(m, fs, f, j as nat) as int, ucount(m, fs, f, (j + 1) as nat) as int), tbase(t0) + ucount(m, fs, f, j as nat)),
{
    lemma_seg_trans(t0, t1, t2);
    assert forall|j: int| 0 <= j < i + 1 implies ul_img(m, #[trigger] fs[j], f, ops.push(y)[j],
        seg(t0, t2).subrange(ucount(m, fs, f, j as nat) as int, ucount(m, fs, f, (j + 1) as nat) as int), tbase(t0) + ucount(m, fs, f, j as nat)) by {
        if j < i {
            lemma_ucount_mono(m, fs, f, (j + 1) as nat, i);
            lemma_ucount_mono(m, fs, f, j as nat, (j + 1) as nat);
            assert(seg(t0, t2).subrange(ucount(m, fs, f, j as nat) as int, ucount(m, fs, f, (j + 1) as nat) as int)
                =~= seg(t0, t1).subrange(ucount(m, fs, f, j as nat) as int, ucount(m, fs, f, (j + 1) as nat) as int));
        } else {
            assert(ops.push(y)[j] == y);
            assert(seg(t0, t2).subrange(ucount(m, fs, f, j as nat) as int, ucount(m, fs, f, (j + 1) as nat) as int) =~= seg(t1, t2));
        }
    };
}

proof fn lemma_ucount_mono(m: MirCrate, fs: Seq<Ty>, f: nat, j: nat, n: nat)
    requires j <= n, unit_likes(m, fs, f, n, true) is Some,
    ensures unit_likes(m, fs, f, j, true) is Some, ucount(m, fs, f, j) <= ucount(m, fs, f, n),
    decreases n - j,
{
    if j < n { lemma_ucount_mono(m, fs, f, j, (n - 1) as nat); }
}

/// The struct's own temp closes `x_ul`.
proof fn lemma_ul_close(m: MirCrate, t: Ty, fuel: nat, t0: Tmp, t2: Tmp, t3: Tmp, x: nat)
    requires
        fuel > 0, rigid(m, t) matches Some(RigidTy::Adt(_, _)),
        adt_row(m, t) matches Some(row) && !row.is_box && !(row.kind is Union) && row.variants@.len() == 1 && {
            let fs = row.variants@[0].fields@;
            let f = (fuel - 1) as nat;
            &&& grew(t0, t2) && temps_at(seg(t0, t2), tbase(t0))
            &&& unit_likes(m, fs, f, fs.len(), true) is Some && ucount(m, fs, f, fs.len()) == seg(t0, t2).len()
            &&& t3.pre@.last() is Assign && t3.pre@.last()->Assign_1 is Aggregate && t3.pre@.last()->Assign_1->Aggregate_0 == c::AggKind::Adt(0)
            &&& t3.pre@.last()->Assign_1->Aggregate_1@.len() == fs.len()
            &&& forall|j: int| 0 <= j < fs.len() ==> ul_img(m, #[trigger] fs[j], f, t3.pre@.last()->Assign_1->Aggregate_1@[j],
                    seg(t0, t2).subrange(ucount(m, fs, f, j as nat) as int, ucount(m, fs, f, (j + 1) as nat) as int), tbase(t0) + ucount(m, fs, f, j as nat))
        },
        x == tbase(t2), grew(t2, t3), t3.pre@.len() == t2.pre@.len() + 1,
        t3.pre@.last()->Assign_0.local == x, t3.pre@.last()->Assign_0.proj@.len() == 0,
    ensures grew(t0, t3), seg(t0, t3).len() >= 1, x == tbase(t0) + seg(t0, t3).len() - 1,
        forall|y: c::Operand| is_tmp(y, x) ==> ul_img(m, t, fuel, y, seg(t0, t3), tbase(t0)),
{
    let row = adt_row(m, t)->Some_0;
    let fs = row.variants@[0].fields@;
    let f = (fuel - 1) as nat;
    let c = ucount(m, fs, f, fs.len());
    lemma_one_temp(t2, t3, x);
    lemma_seg_trans(t0, t2, t3);
    let pre = seg(t0, t3);
    assert(pre[c as int] == t3.pre@.last()) by { assert(seg(t2, t3)[0] == pre[c as int]); };
    assert(unit_like(m, t, fuel, true) == Some((ctcore::sem::Val::Adt(0, unit_likes(m, fs, f, fs.len(), true)->Some_0.0), c + 1)));
    assert forall|j: int| 0 <= j < fs.len() implies ul_img(m, #[trigger] fs[j], f, tmp_rv(pre, c as int)->Aggregate_1@[j],
        pre.subrange(ucount(m, fs, f, j as nat) as int, ucount(m, fs, f, (j + 1) as nat) as int), tbase(t0) + ucount(m, fs, f, j as nat)) by {
        lemma_ucount_mono(m, fs, f, (j + 1) as nat, fs.len());
        lemma_ucount_mono(m, fs, f, j as nat, (j + 1) as nat);
        assert(pre.subrange(ucount(m, fs, f, j as nat) as int, ucount(m, fs, f, (j + 1) as nat) as int)
            =~= seg(t0, t2).subrange(ucount(m, fs, f, j as nat) as int, ucount(m, fs, f, (j + 1) as nat) as int));
    };
}

/// `()` at `off`: `dec_tuple` of no fields.
fn unit_tuple_ok(m: &MirCrate, t: Ty) -> (r: bool)
    ensures r ==> (layout(*m, t) matches Some(l) && offs_of(l.fields) matches Some(o) && o.len() == 0),
{
    match x_layout(m, t) { Some(l) => match &l.fields { FieldsShape::Arbitrary { offsets } => offsets.len() == 0, _ => false }, None => false }
}

/// A value nested in an ADT constant: as many temps as `dec` counts nodes.
pub fn x_cv(m: &MirCrate, t: Ty, a: &Allocation, off: usize, fuel: usize, tmp: &mut Tmp) -> (r: Result<c::Operand, Vec<u8>>)
    ensures r matches Ok(y) ==> grew(*old(tmp), *final(tmp)) && lowers_cv(*m, t, *a, off as nat, fuel as nat, y, seg(*old(tmp), *final(tmp)), tbase(*old(tmp))),
    decreases fuel, 2nat,
{
    if fuel == 0 { return Err(msg(b"constant nested too deeply")); }
    match x_rigid(m, t) {
        Some(RigidTy::Adt(_, _)) => return x_adt(m, t, a, off, fuel, tmp),
        Some(RigidTy::Tuple(ts)) => {
            if ts.len() == 0 && unit_tuple_ok(m, t) {
                proof { lemma_unit_tuple_cv(*m, t, *a, off as nat, fuel as nat, *tmp); }
                return Ok(c::Operand::Lit(c::ConstVal::Unit));
            }
            return Err(msg(b"tuple constant"));
        },
        Some(RigidTy::Ref(_, p, Mutability::Not)) => {
            if matches!(x_rigid(m, *p), Some(RigidTy::Adt(_, _))) && x_is_zst(m, *p) {
                if !ref_target_ok(m, a, off) { return Err(msg(b"a constant reference to a non-memory allocation")); }
                let tf = match x_tfuel(m) { Some(tf) => tf, None => return Err(msg(b"too many types")) };
                let ghost t0 = *old(tmp);
                let y = x_ul(m, *p, tf, tmp)?;
                let ghost t1 = *tmp;
                let ct = lower_ty(m, t, TYF)?;
                let q = match y { c::Operand::Copy(q) => q, _ => return Err(msg(b"constant reference")) };
                let x = fresh(tmp, ct, c::Rvalue::RefShr(q))?;
                let z = c::Operand::Copy(pl(x));
                proof { lemma_zref_close(*m, t, *p, *a, off as nat, fuel as nat, t0, t1, *tmp, x as nat, y); assert(is_tmp(z, x as nat)); }
                return Ok(z);
            }
        },
        _ => {},
    }
    let ghost t0 = *old(tmp);
    let (v, k) = x_lit(m, t, a, off, fuel)?;
    if k == 0 {
        proof { assert(seg(t0, *tmp) =~= Seq::<c::Stmt>::empty()); assert(tmp.pre@.subrange(0, tmp.pre@.len() as int) =~= tmp.pre@); }
        match (x_int_ty(m, t), v) {
            (Some(it), c::ConstVal::Int(n)) => Ok(c::Operand::Const(it, n)),
            (_, v) => Ok(c::Operand::Lit(v)),
        }
    } else if k == 1 {
        let ct = lower_ty(m, t, TYF)?;
        let ghost cv = v;
        let x = fresh(tmp, ct, c::Rvalue::Use(c::Operand::Lit(v)))?;
        proof { lemma_one_temp(t0, *tmp, x as nat); }
        Ok(c::Operand::Copy(pl(x)))
    } else {
        Err(msg(b"a constant array of references inside an ADT constant"))
    }
}

proof fn lemma_unit_tuple_cv(m: MirCrate, t: Ty, a: Allocation, off: nat, fuel: nat, t1: Tmp)
    requires fuel > 0, rigid(m, t) matches Some(RigidTy::Tuple(ts)) && ts@.len() == 0,
        layout(m, t) matches Some(l) && offs_of(l.fields) matches Some(o) && o.len() == 0,
    ensures grew(t1, t1), lowers_cv(m, t, a, off, fuel, c::Operand::Lit(c::ConstVal::Unit), seg(t1, t1), tbase(t1)),
{
    assert(t1.pre@.subrange(0, t1.pre@.len() as int) =~= t1.pre@);
    assert(seg(t1, t1) =~= Seq::<c::Stmt>::empty());
    let ts = rigid(m, t)->Some_0->Tuple_0;
    let o = offs_of(layout(m, t)->Some_0.fields)->Some_0;
    assert(dec_fields(m, ts@, o, a, off, (fuel - 1) as nat, 0) == Some((Seq::<ctcore::sem::Val>::empty(), 0nat)));
    assert(dec_tuple(m, t, ts@, a, off, (fuel - 1) as nat) == Some((unit_val(), 0nat)));
    assert(int_of(rigid(m, t)->Some_0) is None);
    assert(dec(m, t, a, off, fuel) == Some((unit_val(), 0nat)));
}

/// A `&` of a unit-like struct closes `x_cv`.
proof fn lemma_zref_close(m: MirCrate, t: Ty, p: Ty, a: Allocation, off: nat, fuel: nat, t0: Tmp, t1: Tmp, t3: Tmp, x: nat, y: c::Operand)
    requires
        fuel > 0, rigid(m, t) == Some(RigidTy::Ref(rigid(m, t)->Some_0->Ref_0, p, Mutability::Not)), rigid(m, p) matches Some(RigidTy::Adt(_, _)),
        is_zst(m, p), le(a, off, 8) is Some,
        match prov_at(a, off) { Some(id) => alloc_mem(m, id) is Some, None => no_prov(a, off, 8) },
        grew(t0, t1), seg(t0, t1).len() >= 1, is_tmp(y, (tbase(t0) + seg(t0, t1).len() - 1) as nat),
        ul_img(m, p, tfuel(m), y, seg(t0, t1), tbase(t0)),
        x == tbase(t1), grew(t1, t3), t3.pre@.len() == t1.pre@.len() + 1,
        t3.pre@.last() is Assign && t3.pre@.last()->Assign_0.local == x && t3.pre@.last()->Assign_0.proj@.len() == 0,
        t3.pre@.last()->Assign_1 is RefShr, c::Operand::Copy(t3.pre@.last()->Assign_1->RefShr_0) == y,
    ensures grew(t0, t3), forall|z: c::Operand| is_tmp(z, x) ==> lowers_cv(m, t, a, off, fuel, z, seg(t0, t3), tbase(t0)),
{
    lemma_one_temp(t1, t3, x);
    assert(temps_at(seg(t0, t1), tbase(t0)));
    lemma_seg_trans(t0, t1, t3);
    let pre = seg(t0, t3);
    let c = seg(t0, t1).len();
    assert(pre[c as int] == t3.pre@.last()) by { assert(seg(t1, t3)[0] == pre[c as int]); };
    assert(pre.subrange(0, c as int) =~= seg(t0, t1));
    let uv = unit_like(m, p, tfuel(m), true)->Some_0.0;
    assert(dec_zst_ref(m, p) == Some((ctcore::sem::Val::Shr(Box::new(uv)), c + 1)));
    assert(dec_ref(m, p, a, off, (fuel - 1) as nat) == Some((ctcore::sem::Val::Shr(Box::new(uv)), c + 1)));
    assert(dec(m, t, a, off, fuel) == Some((ctcore::sem::Val::Shr(Box::new(uv)), c + 1)));
    assert forall|z: c::Operand| is_tmp(z, x) implies lowers_cv(m, t, a, off, fuel, z, pre, tbase(t0)) by {
        assert(zref_img(m, t, z, pre, tbase(t0)));
    };
}

/// The provenance cases of `dec_ref` that reach `dec_zst_ref`.
fn ref_target_ok(m: &MirCrate, a: &Allocation, off: usize) -> (r: bool)
    ensures r ==> le(*a, off as nat, 8) is Some && match prov_at(*a, off as nat) {
        Some(id) => alloc_mem(*m, id) is Some,
        None => no_prov(*a, off as nat, 8),
    },
{
    if x_le(a, off, 8).is_none() { return false; }
    match x_prov_at(a, off) { Some(id) => x_alloc_mem(m, id).is_some(), None => x_no_prov(a, off, 8) }
}

/// `dfuel(m)` (`None` past usize).
pub fn x_dfuel(m: &MirCrate) -> (r: Option<usize>)
    ensures r matches Some(f) ==> f as nat == dfuel(*m),
{
    if m.tys.len() < 0xffff_ffff && m.allocs.len() < 0xffff_ffff {
        proof { assert((m.tys@.len() + 1) * (m.allocs@.len() + 1) <= 0xffff_ffff * 0xffff_ffff) by (nonlinear_arith)
            requires m.tys@.len() < 0xffff_ffff, m.allocs@.len() < 0xffff_ffff; }
        Some((m.tys.len() + 1) * (m.allocs.len() + 1))
    } else { None }
}

/// No temps: `grew` and an empty segment.
pub proof fn lemma_no_temps(t: Tmp)
    ensures grew(t, t), seg(t, t) == Seq::<c::Stmt>::empty(),
{
    assert(t.pre@.subrange(0, t.pre@.len() as int) =~= t.pre@);
    assert(seg(t, t) =~= Seq::<c::Stmt>::empty());
}

/// An operand constant (decision 5).
pub fn x_const(m: &MirCrate, k: &ConstOperand, tmp: &mut Tmp) -> (r: Result<c::Operand, Vec<u8>>)
    ensures r matches Ok(y) ==> grew(*old(tmp), *final(tmp)) && lowers_const(*m, *k, y, seg(*old(tmp), *final(tmp)), tbase(*old(tmp))),
{
    proof { lemma_no_temps(*tmp); }
    let t = k.const_.ty;
    match &k.const_.kind {
        ConstantKind::ZeroSized => {
            let tf = match x_tfuel(m) { Some(tf) => tf, None => return Err(msg(b"too many types")) };
            lower_ty(m, t, TYF)?;
            if x_unit_like(m, t, tf, true) { Ok(c::Operand::Lit(c::ConstVal::Unit)) } else { Err(msg(b"a zero-sized constant of a non-unit-like type")) }
        },
        ConstantKind::Allocated(a) => {
            let df = match x_dfuel(m) { Some(f) => f, None => return Err(msg(b"too many types")) };
            lower_ty(m, t, TYF)?;
            let charged = match x_rigid(m, t) {
                Some(RigidTy::Adt(_, _)) => true,
                Some(RigidTy::Ref(_, p, _)) => x_is_zst(m, *p),
                _ => false,
            };
            proof { assert(charged == crate::sem::charged(*m, t)); }
            if charged { return x_cv(m, t, a, 0, df, tmp); }
            if let Some(RigidTy::Tuple(ts)) = x_rigid(m, t) {
                if ts.len() == 0 && unit_tuple_ok(m, t) {
                    proof { assert(df > 0) by (nonlinear_arith) requires df as nat == dfuel(*m); lemma_unit_tuple_cv(*m, t, *a, 0, df as nat, *tmp); }
                    return Ok(c::Operand::Lit(c::ConstVal::Unit));
                }
                return Err(msg(b"tuple constant"));
            }
            let (v, _) = x_lit(m, t, a, 0, df)?;
            match (x_int_ty(m, t), v) {
                (Some(it), c::ConstVal::Int(n)) => Ok(c::Operand::Const(it, n)),
                (_, v) => Ok(c::Operand::Lit(v)),
            }
        },
        _ => Err(msg(b"unevaluated constant")),
    }
}

} // verus!
