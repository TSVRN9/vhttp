//! The translator's types and constants. A type lowers structurally (`lower_ty`). A constant
//! lowers to a core operand plus the temps it needs (`Tmp`): ints are `Const`, int arrays and
//! shared references to them `Lit`, and an ADT value or a `&ZST` one temp per ADT or reference
//! node, assigned in post-order before the statement that reads it (decision 7's charge).
use crate::json::bytes_eq;
use crate::look::*;
use crate::mir::*;
#[cfg(verus_keep_ghost)]
use crate::sem::*;
use ctcore::syntax as c;
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

pub fn lower_ty(m: &MirCrate, t: Ty, fuel: usize) -> (r: Result<c::Ty, Vec<u8>>)
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
                invariant k <= ts@.len(),
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

pub fn lower_adt_ty(m: &MirCrate, t: Ty, f: usize) -> (r: Result<c::Ty, Vec<u8>>)
    decreases f, 0nat,
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
        invariant k <= a.variants@.len(),
        decreases a.variants.len() - k,
    {
        let fs = &a.variants[k].fields;
        let mut v: Vec<c::Ty> = Vec::new();
        let mut i: usize = 0;
        while i < fs.len()
            invariant i <= fs@.len(),
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
            proof { crate::look::lemma_find(ps@, |e: (usize, AllocId)| e.0 as nat == off as nat, k as nat); }
            return Some(ps[k].1);
        }
        k += 1;
    }
    proof { crate::look::lemma_find(ps@, |e: (usize, AllocId)| e.0 as nat == off as nat, k as nat); }
    None
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
fn tag_mod(bits: usize) -> (r: Option<u128>) {
    if bits == 8 { Some(0x100) } else if bits == 16 { Some(0x1_0000) } else if bits == 32 { Some(0x1_0000_0000) }
    else if bits == 64 { Some(0x1_0000_0000_0000_0000) } else { None }
}

/// `tag_variant(row, enc, t, tbits)`; 128-bit tags are rejected.
pub fn x_tag_variant(row: &Adt, enc: &TagEncoding, t: u128, tbits: usize) -> (r: Option<usize>) {
    let md = match tag_mod(tbits) { Some(md) => md, None => return None };
    match enc {
        TagEncoding::Direct => {
            let mut k: usize = 0;
            while k < row.variants.len()
                invariant k <= row.variants@.len(),
                decreases row.variants.len() - k,
            {
                if let Some(d) = row.variants[k].discr {
                    if d % md == t { return Some(k); }
                }
                k += 1;
            }
            None
        },
        TagEncoding::Niche { untagged_variant, niche_variants, niche_start } => {
            if t >= md { return None; }
            let ns = *niche_start % md;
            let rel = if t >= ns { t - ns } else { t + (md - ns) };
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
pub fn x_adt_sel<'a>(row: &Adt, l: &'a LayoutShape, a: &Allocation, off: usize) -> (r: Option<(usize, &'a Vec<MachineSize>)>) {
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

// ------------------------------------------------------------------ constant values

/// The temps of one body: fresh locals after the MIR ones (`nloc`), their types, and the
/// pending assignments of the statement or terminator being lowered.
pub struct Tmp { pub nloc: usize, pub tys: Vec<c::Ty>, pub pre: Vec<c::Stmt> }

pub fn pl(local: usize) -> (p: c::Place)
    ensures p.local == local, p.proj@.len() == 0,
{
    c::Place { local, proj: Vec::new() }
}

/// A fresh temp of type `ty`, assigned `rv` in `tmp.pre`.
pub fn fresh(tmp: &mut Tmp, ty: c::Ty, rv: c::Rvalue) -> (r: Result<usize, Vec<u8>>) {
    if tmp.tys.len() >= usize::MAX - tmp.nloc { return Err(msg(b"too many temps")); }
    let local = tmp.nloc + tmp.tys.len();
    tmp.tys.push(ty);
    tmp.pre.push(c::Stmt::Assign(pl(local), rv));
    Ok(local)
}

/// The value of a "literal" type (ints, arrays of literals, `&str`, `&ZST` with a literal value,
/// `&[T; N]`) at `off`, and its ADT/reference node count, mirroring `dec`.
pub fn x_lit(m: &MirCrate, t: Ty, a: &Allocation, off: usize, fuel: usize) -> (r: Result<(c::ConstVal, usize), Vec<u8>>)
    decreases fuel,
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
        RigidTy::Array(e, cn) => {
            let n = match x_const_usize(m, cn.id) { Some(n) => n, None => return Err(msg(b"array length")) };
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
                invariant i <= n,
                decreases n - i,
            {
                let (v, k) = x_lit(m, *e, a, at, f)?;
                vs.push(v);
                if cnt > usize::MAX - k || at > usize::MAX - stride { return Err(msg(b"constant too large")); }
                cnt = cnt + k;
                at = at + stride;
                i += 1;
            }
            Ok((c::ConstVal::Arr(vs), cnt))
        },
        RigidTy::Ref(_, p, Mutability::Not) => {
            if matches!(x_rigid(m, *p), Some(RigidTy::Str)) {
                return match x_prov_at(a, off) {
                    Some(id) => if x_alloc_mem(m, id).is_some() { Ok((c::ConstVal::Unit, 0)) } else { Err(msg(b"&str constant into a non-memory allocation")) },
                    None => Ok((c::ConstVal::Unit, 0)),
                };
            }
            if off > usize::MAX - 8 { return Err(msg(b"constant too large")); }
            let addr = match x_le(a, off, 8) { Some(x) => x, None => return Err(msg(b"a constant reference with uninitialized bytes")) };
            let target = match x_prov_at(a, off) {
                Some(id) => match x_alloc_mem(m, id) { Some(a2) => Some(a2), None => return Err(msg(b"a constant reference to a non-memory allocation")) },
                None => if x_no_prov(a, off, 8) { None } else { return Err(msg(b"a constant reference with a partial pointer")) },
            };
            if x_is_zst(m, *p) {
                let tf = match x_tfuel(m) { Some(tf) => tf, None => return Err(msg(b"too many types")) };
                let (v, k) = x_ul_lit(m, *p, tf)?;
                return Ok((c::ConstVal::Shr(Box::new(v)), k + 1));
            }
            match (target, x_rigid(m, *p)) {
                (Some(a2), Some(RigidTy::Array(_, _))) => {
                    if addr > usize::MAX as u128 { return Err(msg(b"constant reference address")); }
                    let (v, k) = x_lit(m, *p, a2, addr as usize, f)?;
                    if k == usize::MAX { return Err(msg(b"constant too large")); }
                    Ok((c::ConstVal::Shr(Box::new(v)), k + 1))
                },
                _ => Err(msg(b"a constant reference to a non-zero-sized value")),
            }
        },
        _ => Err(msg(b"constant of a type outside the subset (a tuple, ..)")),
    }
}

/// A literal unit-like value (`unit_like` with closures allowed): fn items, closures, `[T; 0]`.
pub fn x_ul_lit(m: &MirCrate, t: Ty, fuel: usize) -> (r: Result<(c::ConstVal, usize), Vec<u8>>)
{
    if fuel == 0 { return Err(msg(b"constant nested too deeply")); }
    match x_rigid(m, t) {
        Some(RigidTy::FnDef(_, _)) | Some(RigidTy::Closure(_, _)) => Ok((c::ConstVal::Unit, 0)),
        Some(RigidTy::Array(_, cn)) => match x_const_usize(m, cn.id) {
            Some(0) => Ok((c::ConstVal::Arr(Vec::new()), 0)),
            _ => Err(msg(b"a constant reference to a non-empty array of zero-sized values")),
        },
        _ => Err(msg(b"a constant reference to a zero-sized value that is not a literal")),
    }
}

/// The ADT node at `off` (`dec_adt` at `fuel - 1`): its fields, then one temp.
pub fn x_adt(m: &MirCrate, t: Ty, a: &Allocation, off: usize, fuel: usize, tmp: &mut Tmp) -> (r: Result<c::Operand, Vec<u8>>)
    decreases fuel, 1nat,
{
    if fuel == 0 { return Err(msg(b"constant nested too deeply")); }
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
    let mut ops: Vec<c::Operand> = Vec::new();
    let mut i: usize = 0;
    while i < fs.len()
        invariant i <= fs@.len(), fs@.len() == o@.len(),
        decreases fs.len() - i,
    {
        if o[i].num_bits % 8 != 0 { return Err(msg(b"constant field offset")); }
        let rel = o[i].num_bits / 8;
        if off > usize::MAX - rel { return Err(msg(b"constant too large")); }
        let y = x_cv(m, fs[i], a, off + rel, f, tmp)?;
        ops.push(y);
        i += 1;
    }
    let x = fresh(tmp, ct, c::Rvalue::Aggregate(c::AggKind::Adt(k), ops))?;
    Ok(c::Operand::Copy(pl(x)))
}

/// A unit-like ADT value (`unit_like` with closures allowed): its fields, then one temp.
pub fn x_ul(m: &MirCrate, t: Ty, fuel: usize, tmp: &mut Tmp) -> (r: Result<c::Operand, Vec<u8>>)
    decreases fuel,
{
    if fuel == 0 { return Err(msg(b"constant nested too deeply")); }
    let f = fuel - 1;
    let ct = lower_ty(m, t, TYF)?;
    if !matches!(ct, c::Ty::Adt(_)) { return Err(msg(b"constant of a unit-mapped ADT (Ghost, Tracked)")); }
    let row = match x_adt_row(m, t) { Some(r) => r, None => return Err(msg(b"constant of a type with no adts row")) };
    if row.is_box || matches!(row.kind, AdtKind::Union) || row.variants.len() != 1 { return Err(msg(b"a zero-sized constant that is not a struct")); }
    let fs = &row.variants[0].fields;
    let mut ops: Vec<c::Operand> = Vec::new();
    let mut i: usize = 0;
    while i < fs.len()
        invariant i <= fs@.len(),
        decreases fs.len() - i,
    {
        let y = match x_rigid(m, fs[i]) {
            Some(RigidTy::Adt(_, _)) => x_ul(m, fs[i], f, tmp)?,
            Some(RigidTy::Tuple(ts)) => if ts.len() == 0 { c::Operand::Lit(c::ConstVal::Unit) } else {
                return Err(msg(b"a zero-sized constant with a tuple field"));
            },
            _ => { let (v, _) = x_ul_lit(m, fs[i], f)?; c::Operand::Lit(v) },
        };
        ops.push(y);
        i += 1;
    }
    let x = fresh(tmp, ct, c::Rvalue::Aggregate(c::AggKind::Adt(0), ops))?;
    Ok(c::Operand::Copy(pl(x)))
}

/// `()` at `off`: `dec_tuple` of no fields.
fn unit_tuple_ok(m: &MirCrate, t: Ty) -> bool {
    match x_layout(m, t) { Some(l) => match &l.fields { FieldsShape::Arbitrary { offsets } => offsets.len() == 0, _ => false }, None => false }
}

/// A value nested in an ADT constant: as many temps as `dec` counts nodes.
pub fn x_cv(m: &MirCrate, t: Ty, a: &Allocation, off: usize, fuel: usize, tmp: &mut Tmp) -> (r: Result<c::Operand, Vec<u8>>)
    decreases fuel, 2nat,
{
    if fuel == 0 { return Err(msg(b"constant nested too deeply")); }
    match x_rigid(m, t) {
        Some(RigidTy::Adt(_, _)) => return x_adt(m, t, a, off, fuel, tmp),
        Some(RigidTy::Tuple(ts)) => {
            if ts.len() == 0 && unit_tuple_ok(m, t) { return Ok(c::Operand::Lit(c::ConstVal::Unit)); }
            return Err(msg(b"tuple constant"));
        },
        Some(RigidTy::Ref(_, p, Mutability::Not)) => {
            if matches!(x_rigid(m, *p), Some(RigidTy::Adt(_, _))) && x_is_zst(m, *p) {
                if !ref_target_ok(m, a, off) { return Err(msg(b"a constant reference to a non-memory allocation")); }
                let tf = match x_tfuel(m) { Some(tf) => tf, None => return Err(msg(b"too many types")) };
                let y = x_ul(m, *p, tf, tmp)?;
                let ct = lower_ty(m, t, TYF)?;
                let q = match y { c::Operand::Copy(q) => q, _ => return Err(msg(b"constant reference")) };
                let x = fresh(tmp, ct, c::Rvalue::RefShr(q))?;
                return Ok(c::Operand::Copy(pl(x)));
            }
        },
        _ => {},
    }
    let (v, k) = x_lit(m, t, a, off, fuel)?;
    if k == 0 {
        match (x_int_ty(m, t), v) {
            (Some(it), c::ConstVal::Int(n)) => Ok(c::Operand::Const(it, n)),
            (_, v) => Ok(c::Operand::Lit(v)),
        }
    } else if k == 1 {
        let ct = lower_ty(m, t, TYF)?;
        let x = fresh(tmp, ct, c::Rvalue::Use(c::Operand::Lit(v)))?;
        Ok(c::Operand::Copy(pl(x)))
    } else {
        Err(msg(b"a constant array of references inside an ADT constant"))
    }
}

/// The provenance cases of `dec_ref` that reach `dec_zst_ref`.
fn ref_target_ok(m: &MirCrate, a: &Allocation, off: usize) -> bool {
    if off > usize::MAX - 8 || x_le(a, off, 8).is_none() { return false; }
    match x_prov_at(a, off) { Some(id) => x_alloc_mem(m, id).is_some(), None => x_no_prov(a, off, 8) }
}

/// `dfuel(m)` (`None` past usize).
pub fn x_dfuel(m: &MirCrate) -> (r: Option<usize>)
    ensures r matches Some(f) ==> f as nat == dfuel(*m),
{
    if m.tys.len() < 0x1_0000_0000 && m.allocs.len() < 0x1_0000_0000 { Some((m.tys.len() + 1) * (m.allocs.len() + 1)) } else { None }
}

/// An operand constant (decision 5).
pub fn x_const(m: &MirCrate, k: &ConstOperand, tmp: &mut Tmp) -> (r: Result<c::Operand, Vec<u8>>) {
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
            if charged { return x_cv(m, t, a, 0, df, tmp); }
            if let Some(RigidTy::Tuple(ts)) = x_rigid(m, t) {
                if ts.len() == 0 && unit_tuple_ok(m, t) { return Ok(c::Operand::Lit(c::ConstVal::Unit)); }
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
