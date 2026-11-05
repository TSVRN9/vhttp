//! The selftest vector grammar (`tools/ct-driver/selftest.txt`, `tools/ct-fixtures/semconf/
//! vectors.txt`) as a spec, its verified parser, and the verified vector check over the verified
//! evaluator (`eval`).
//! A line is `<path> <arg>... => <ret> <mut-out>...` or `<path> <arg>... => panic`. `vector_spec`
//! is the grammar of the words after the path; the line's split into words at ASCII whitespace,
//! and its cut at the first comment word (one starting `#` and not then a digit), are done by
//! `pipeline::selftest`, outside this grammar.
//! Values (`value`):
//! - hex bytes (an `Arr` of byte `Int`s; `-` is the empty one);
//! - `0x<hex><suffix>` (an `Int`, the suffix one of `u8`..`u128`, `usize`, `i8`..`i128`, `isize`,
//!   the digits' value below `2^width`); `true`/`false`;
//! - `[v,..]` (an `Arr`), `(v,..)` (a `Tup`), `()`, `None`, `Some(v)`, `#k(v,..)` (variant `k`).
//! A plain argument that is an `Arr` is passed by shared reference, as is any plain argument of a
//! `Shr` parameter (`entry_args`); a `mut:` argument is the initial pointee of a `&mut` parameter.
use crate::eval::x_wt_args;
use crate::eval_run::{mir_eval, Ev};
use crate::eval_tab::Tabs;
#[cfg(verus_keep_ghost)]
use crate::eval_tab::tabs_ok;
use crate::mir::MirCrate;
use crate::policy::Policy;
#[cfg(verus_keep_ghost)]
use crate::policy::cpol;
#[cfg(verus_keep_ghost)]
use crate::sem::{closed, in_subset, mir_entry, mir_run, Out};
#[cfg(verus_keep_ghost)]
use crate::sim_entry::wt_args;
#[allow(unused_imports)]
use crate::interp_val::*;
#[cfg(verus_keep_ghost)]
use crate::policy::starts;
use crate::policy::sub;
#[cfg(verus_keep_ghost)]
use crate::rel::views;
#[cfg(verus_keep_ghost)]
use ctcore::sem::{bits, nth, Loc, Root};
use ctcore::sem::Val;
use ctcore::syntax::{Program, Ty};
use vstd::prelude::*;

verus! {

/// Per-activation fuel for a vector run (the old interpreter's).
pub const FUEL: u64 = 1u64 << 32;

// ------------------------------------------------------------------ characters

pub open spec fn is_hex(c: u8) -> bool { (48 <= c && c <= 57) || (97 <= c && c <= 102) || (65 <= c && c <= 70) }

pub open spec fn hv(c: u8) -> nat {
    if 48 <= c && c <= 57 { (c - 48) as nat } else if 97 <= c && c <= 102 { (c - 87) as nat } else { (c - 55) as nat }
}

pub open spec fn hexval(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { hexval(s.drop_last()) * 16 + hv(s.last()) }
}

pub open spec fn is_dec(c: u8) -> bool { 48 <= c && c <= 57 }

pub open spec fn decval(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { decval(s.drop_last()) * 10 + (s.last() - 48) as nat }
}

pub open spec fn all_hex(s: Seq<u8>) -> bool { forall|i: int| 0 <= i < s.len() ==> is_hex(#[trigger] s[i]) }

pub open spec fn all_dec(s: Seq<u8>) -> bool { forall|i: int| 0 <= i < s.len() ==> is_dec(#[trigger] s[i]) }

/// The first index at or after `i` that is not a hex digit, or `s.len()`.
pub open spec fn hex_end(s: Seq<u8>, i: nat) -> nat
    decreases s.len() - i,
{
    if i >= s.len() || !is_hex(s[i as int]) { i } else { hex_end(s, i + 1) }
}

/// The first `(` at or after `i`, or `s.len()`.
pub open spec fn paren_at(s: Seq<u8>, i: nat) -> nat
    decreases s.len() - i,
{
    if i >= s.len() || s[i as int] == 40u8 { i } else { paren_at(s, i + 1) }
}

// ------------------------------------------------------------------ top-level comma split

pub open spec fn push_ne(out: Seq<Seq<u8>>, p: Seq<u8>) -> Seq<Seq<u8>> { if p.len() > 0 { out.push(p) } else { out } }

/// `s` split at the commas outside any `(..)`/`[..]`, empty pieces dropped: from byte `i`, at depth
/// `d`, with the current piece starting at `st`.
pub open spec fn scan(s: Seq<u8>, i: nat, d: int, st: nat, out: Seq<Seq<u8>>) -> Seq<Seq<u8>>
    decreases s.len() - i,
{
    if i >= s.len() {
        push_ne(out, s.subrange(st as int, s.len() as int))
    } else {
        let c = s[i as int];
        if c == 40u8 || c == 91u8 { scan(s, i + 1, d + 1, st, out) }
        else if c == 41u8 || c == 93u8 { scan(s, i + 1, d - 1, st, out) }
        else if c == 44u8 && d == 0 { scan(s, i + 1, d, i + 1, push_ne(out, s.subrange(st as int, i as int))) }
        else { scan(s, i + 1, d, st, out) }
    }
}

pub open spec fn split_top(s: Seq<u8>) -> Seq<Seq<u8>> { scan(s, 0, 0, 0, seq![]) }

// ------------------------------------------------------------------ values

/// An int literal's digits and width: `0x<hex digits><suffix>`.
pub open spec fn int_lit(t: Seq<u8>) -> Option<(Seq<u8>, nat)> {
    if !starts(t, b"0x"@) { None } else {
        let r = t.subrange(2, t.len() as int);
        let e = hex_end(r, 0);
        let suf = r.subrange(e as int, r.len() as int);
        let w: nat = if suf == b"u8"@ || suf == b"i8"@ { 8 }
            else if suf == b"u16"@ || suf == b"i16"@ { 16 }
            else if suf == b"u32"@ || suf == b"i32"@ { 32 }
            else if suf == b"u64"@ || suf == b"i64"@ || suf == b"usize"@ || suf == b"isize"@ { 64 }
            else if suf == b"u128"@ || suf == b"i128"@ { 128 }
            else { 0 };
        if w == 0 { None } else { Some((r.subrange(0, e as int), w)) }
    }
}

pub open spec fn wmod(w: nat) -> nat {
    if w == 8 { 0x100 } else if w == 16 { 0x1_0000 } else if w == 32 { 0x1_0000_0000 } else if w == 64 { 0x1_0000_0000_0000_0000 }
    else { u128::MAX as nat + 1 }
}

pub open spec fn bytes_val(t: Seq<u8>) -> Val {
    Val::Arr(Seq::new(t.len() / 2, |i: int| Val::Int((hv(t[2 * i]) * 16 + hv(t[2 * i + 1])) as u128)))
}

pub open spec fn inner(t: Seq<u8>, a: int, b: int) -> Seq<u8> { t.subrange(a, t.len() - b) }

/// A value word (`fuel` bounds the nesting; `value_top` gives enough).
pub open spec fn value(t: Seq<u8>, fuel: nat) -> Option<Val>
    decreases fuel, 0nat,
{
    if fuel == 0 { None }
    else if t == b"-"@ { Some(Val::Arr(seq![])) }
    else if t == b"()"@ { Some(Val::Unit) }
    else if t == b"true"@ { Some(Val::Int(1)) }
    else if t == b"false"@ { Some(Val::Int(0)) }
    else if t == b"None"@ { Some(Val::Adt(0, seq![])) }
    else if starts(t, b"Some("@) && t.len() >= 6 && t.last() == 41u8 {
        match value(inner(t, 5, 1), (fuel - 1) as nat) { Some(v) => Some(Val::Adt(1, seq![v])), None => None }
    } else if starts(t, b"#"@) {
        let r = inner(t, 1, 1);
        let q = paren_at(r, 0);
        let k = r.subrange(0, q as int);
        if t.len() >= 2 && t.last() == 41u8 && q < r.len() && k.len() > 0 && all_dec(k) && decval(k) <= usize::MAX {
            match vals_of(split_top(r.subrange((q + 1) as int, r.len() as int)), (fuel - 1) as nat) { Some(vs) => Some(Val::Adt(decval(k), vs)), None => None }
        } else { None }
    } else if starts(t, b"("@) && t.len() >= 2 && t.last() == 41u8 {
        match vals_of(split_top(inner(t, 1, 1)), (fuel - 1) as nat) { Some(vs) => Some(Val::Tup(vs)), None => None }
    } else if starts(t, b"0x"@) {
        match int_lit(t) {
            Some((dg, w)) => if dg.len() > 0 && hexval(dg) < wmod(w) { Some(Val::Int(hexval(dg) as u128)) } else { None },
            None => None,
        }
    } else if starts(t, b"["@) && t.len() >= 2 && t.last() == 93u8 {
        match vals_of(split_top(inner(t, 1, 1)), (fuel - 1) as nat) { Some(vs) => Some(Val::Arr(vs)), None => None }
    } else if t.len() % 2 == 0 && all_hex(t) {
        Some(bytes_val(t))
    } else { None }
}

pub open spec fn vals_of(ps: Seq<Seq<u8>>, fuel: nat) -> Option<Seq<Val>>
    decreases fuel, ps.len() + 1,
{
    if ps.len() == 0 { Some(seq![]) } else {
        match (vals_of(ps.drop_last(), fuel), value(ps.last(), fuel)) { (Some(a), Some(v)) => Some(a.push(v)), _ => None }
    }
}

pub open spec fn value_top(t: Seq<u8>) -> Option<Val> { value(t, t.len() + 1) }

// ------------------------------------------------------------------ vectors

/// `bits`/`wbits`: the width suffix of each argument and wanted value that is an int literal.
pub struct VSpec { pub args: Seq<(bool, Val)>, pub want: Seq<Val>, pub bits: Seq<Option<nat>>, pub wbits: Seq<Option<nat>>, pub panic: bool }

/// The first `=>` at or after `k`, or `toks.len()`.
pub open spec fn arrow_at(toks: Seq<Seq<u8>>, k: nat) -> nat
    decreases toks.len() - k,
{
    if k >= toks.len() || toks[k as int] == b"=>"@ { k } else { arrow_at(toks, k + 1) }
}

pub open spec fn arg_of(t: Seq<u8>) -> Option<(bool, Val)> {
    if starts(t, b"mut:"@) {
        match value_top(t.subrange(4, t.len() as int)) { Some(v) => Some((true, v)), None => None }
    } else {
        match value_top(t) { Some(v) => Some((false, if v is Arr { Val::Shr(Box::new(v)) } else { v })), None => None }
    }
}

pub open spec fn bits_of(t: Seq<u8>) -> Option<nat> {
    let u = if starts(t, b"mut:"@) { t.subrange(4, t.len() as int) } else { t };
    match int_lit(u) { Some((_, w)) => Some(w), None => None }
}

pub open spec fn args_of(ts: Seq<Seq<u8>>) -> Option<Seq<(bool, Val)>>
    decreases ts.len(),
{
    if ts.len() == 0 { Some(seq![]) } else {
        match (args_of(ts.drop_last()), arg_of(ts.last())) { (Some(a), Some(x)) => Some(a.push(x)), _ => None }
    }
}

pub open spec fn wants_of(ts: Seq<Seq<u8>>) -> Option<Seq<Val>>
    decreases ts.len(),
{
    if ts.len() == 0 { Some(seq![]) } else {
        match (wants_of(ts.drop_last()), value_top(ts.last())) { (Some(a), Some(x)) => Some(a.push(x)), _ => None }
    }
}

/// The vector of a line's words after its path.
pub open spec fn vector_spec(toks: Seq<Seq<u8>>) -> Option<VSpec> {
    let at = arrow_at(toks, 0);
    let (a, w) = (toks.subrange(0, at as int), toks.subrange((at + 1) as int, toks.len() as int));
    if at >= toks.len() { None } else {
        match args_of(a) {
            None => None,
            Some(args) => {
                let bits = Seq::new(a.len(), |j: int| bits_of(a[j]));
                if w == seq![b"panic"@] { Some(VSpec { args, want: seq![], bits, wbits: seq![], panic: true }) }
                else { match wants_of(w) { Some(want) => Some(VSpec { args, want, bits, wbits: Seq::new(w.len(), |k: int| bits_of(w[k])), panic: false }), None => None } }
            },
        }
    }
}

/// The exec vector; `args.0` marks a `mut:` argument.
pub struct Vector { pub args: Vec<(bool, CVal)>, pub want: Vec<CVal>, pub bits: Vec<Option<u32>>, pub wbits: Vec<Option<u32>>, pub panic: bool }

pub open spec fn vector_v(v: Vector) -> VSpec {
    VSpec {
        args: Seq::new(v.args@.len(), |j: int| (v.args@[j].0, cv(v.args@[j].1))),
        want: cvs(v.want@),
        bits: Seq::new(v.bits@.len(), |j: int| match v.bits@[j] { Some(w) => Some(w as nat), None => None }),
        wbits: Seq::new(v.wbits@.len(), |j: int| match v.wbits@[j] { Some(w) => Some(w as nat), None => None }),
        panic: v.panic,
    }
}

// ------------------------------------------------------------------ the exec parser

fn is_hex_exec(c: u8) -> (r: bool) ensures r == is_hex(c) { (48 <= c && c <= 57) || (97 <= c && c <= 102) || (65 <= c && c <= 70) }

fn hv_exec(c: u8) -> (r: u8)
    requires is_hex(c),
    ensures r as nat == hv(c), r < 16,
{
    if 48 <= c && c <= 57 { c - 48 } else if 97 <= c && c <= 102 { c - 87 } else { c - 55 }
}

fn eq_bytes(a: &[u8], b: &[u8]) -> (r: bool)
    ensures r == (a@ == b@),
{
    if a.len() != b.len() { return false; }
    let mut i: usize = 0;
    while i < a.len()
        invariant i <= a@.len() == b@.len(), forall|q: int| 0 <= q < i ==> a@[q] == b@[q],
        decreases a.len() - i,
    {
        if a[i] != b[i] { return false; }
        i += 1;
    }
    proof { assert(a@ =~= b@); }
    true
}

fn starts_with(t: &[u8], p: &[u8]) -> (r: bool)
    ensures r == starts(t@, p@),
{
    if p.len() > t.len() { return false; }
    let mut i: usize = 0;
    while i < p.len()
        invariant i <= p@.len() <= t@.len(), forall|q: int| 0 <= q < i ==> t@[q] == p@[q],
        decreases p.len() - i,
    {
        if t[i] != p[i] {
            proof { assert(t@.subrange(0, p@.len() as int)[i as int] != p@[i as int]); }
            return false;
        }
        i += 1;
    }
    proof { assert(t@.subrange(0, p@.len() as int) =~= p@); }
    true
}

pub fn split_top_exec(s: &[u8]) -> (r: Vec<Vec<u8>>)
    ensures views(r@) == split_top(s@),
{
    let mut out: Vec<Vec<u8>> = Vec::new();
    proof { assert(views(out@) =~= Seq::<Seq<u8>>::empty()); }
    let mut d: i128 = 0;
    let mut st: usize = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant st <= i <= s@.len(), -(i as int) <= d <= i, scan(s@, i as nat, d as int, st as nat, views(out@)) == split_top(s@),
        decreases s.len() - i,
    {
        let c = s[i];
        if c == 40u8 || c == 91u8 {
            d = d + 1;
        } else if c == 41u8 || c == 93u8 {
            d = d - 1;
        } else if c == 44u8 && d == 0 {
            if i > st {
                let piece = sub(s, st, i);
                proof { crate::policy::lemma_views_push(out@, piece); }
                out.push(piece);
            }
            st = i + 1;
        }
        i += 1;
    }
    if s.len() > st {
        let piece = sub(s, st, s.len());
        proof { crate::policy::lemma_views_push(out@, piece); }
        out.push(piece);
    }
    out
}

/// `hexval(s)` if it is below `2^128`.
fn hexval_exec(s: &[u8]) -> (r: Option<u128>)
    requires all_hex(s@),
    ensures match r { Some(n) => n as nat == hexval(s@), None => hexval(s@) > u128::MAX },
{
    let mut n: u128 = 0;
    let mut big = false;
    let mut i: usize = 0;
    while i < s.len()
        invariant i <= s@.len(), all_hex(s@),
            big ==> hexval(s@.subrange(0, i as int)) > u128::MAX, !big ==> n as nat == hexval(s@.subrange(0, i as int)),
        decreases s.len() - i,
    {
        let d = hv_exec(s[i]);
        proof { assert(s@.subrange(0, i + 1).drop_last() =~= s@.subrange(0, i as int)); }
        if !big {
            if n > (u128::MAX - d as u128) / 16 {
                big = true;
            } else {
                n = n * 16 + d as u128;
            }
        }
        i += 1;
    }
    proof { assert(s@.subrange(0, s@.len() as int) =~= s@); }
    if big { None } else { Some(n) }
}

fn decval_exec(s: &[u8]) -> (r: Option<usize>)
    requires all_dec(s@),
    ensures match r { Some(n) => n as nat == decval(s@), None => decval(s@) > usize::MAX },
{
    let mut n: usize = 0;
    let mut big = false;
    let mut i: usize = 0;
    while i < s.len()
        invariant i <= s@.len(), all_dec(s@),
            big ==> decval(s@.subrange(0, i as int)) > usize::MAX, !big ==> n as nat == decval(s@.subrange(0, i as int)),
        decreases s.len() - i,
    {
        let d = (s[i] - 48) as usize;
        proof { assert(s@.subrange(0, i + 1).drop_last() =~= s@.subrange(0, i as int)); }
        if !big {
            if n > (usize::MAX - d) / 10 {
                big = true;
            } else {
                n = n * 10 + d;
            }
        }
        i += 1;
    }
    proof { assert(s@.subrange(0, s@.len() as int) =~= s@); }
    if big { None } else { Some(n) }
}

fn int_lit_exec(t: &[u8]) -> (r: Option<(Vec<u8>, u32)>)
    ensures match int_lit(t@) { Some((dg, w)) => r matches Some((d, x)) && d@ == dg && x as nat == w && all_hex(dg), None => r is None },
{
    if !starts_with(t, b"0x") { return None; }
    let r = sub(t, 2, t.len());
    let mut e: usize = 0;
    while e < r.len() && is_hex_exec(r[e])
        invariant e <= r@.len(), hex_end(r@, 0) == hex_end(r@, e as nat), forall|q: int| 0 <= q < e ==> is_hex(#[trigger] r@[q]),
        decreases r.len() - e,
    {
        e += 1;
    }
    let suf = sub(r.as_slice(), e, r.len());
    let s = suf.as_slice();
    let w: u32 = if eq_bytes(s, b"u8") || eq_bytes(s, b"i8") { 8 }
        else if eq_bytes(s, b"u16") || eq_bytes(s, b"i16") { 16 }
        else if eq_bytes(s, b"u32") || eq_bytes(s, b"i32") { 32 }
        else if eq_bytes(s, b"u64") || eq_bytes(s, b"i64") || eq_bytes(s, b"usize") || eq_bytes(s, b"isize") { 64 }
        else if eq_bytes(s, b"u128") || eq_bytes(s, b"i128") { 128 }
        else { 0 };
    if w == 0 { return None; }
    let d = sub(r.as_slice(), 0, e);
    proof { assert(r@ == t@.subrange(2, t@.len() as int)); }
    Some((d, w))
}

fn wmod_ok(n: u128, w: u32) -> (r: bool)
    requires w == 8 || w == 16 || w == 32 || w == 64 || w == 128,
    ensures r == ((n as nat) < wmod(w as nat)),
{
    if w == 128 { true } else if w == 64 { n < 0x1_0000_0000_0000_0000 } else if w == 32 { n < 0x1_0000_0000 } else if w == 16 { n < 0x1_0000 } else { n < 0x100 }
}

fn bytes_exec(t: &[u8]) -> (r: CVal)
    requires t@.len() % 2 == 0, all_hex(t@),
    ensures cv(r) == bytes_val(t@),
{
    let mut vs: Vec<CVal> = Vec::new();
    let mut i: usize = 0;
    while i < t.len() / 2
        invariant i <= t@.len() / 2, t@.len() % 2 == 0, all_hex(t@), vs@.len() == i,
            forall|q: int| 0 <= q < i ==> cv(#[trigger] vs@[q]) == Val::Int((hv(t@[2 * q]) * 16 + hv(t@[2 * q + 1])) as u128),
        decreases t.len() / 2 - i,
    {
        let (a, b) = (hv_exec(t[2 * i]), hv_exec(t[2 * i + 1]));
        vs.push(CVal::Int(a as u128 * 16 + b as u128));
        i += 1;
    }
    let r = CVal::Arr(vs);
    proof { lemma_cv(r); assert(cvs(vs@) =~= bytes_val(t@)->Arr_0); }
    r
}

fn all_hex_exec(t: &[u8]) -> (r: bool)
    ensures r == all_hex(t@),
{
    let mut i: usize = 0;
    while i < t.len()
        invariant i <= t@.len(), forall|q: int| 0 <= q < i ==> is_hex(#[trigger] t@[q]),
        decreases t.len() - i,
    {
        if !is_hex_exec(t[i]) { return false; }
        i += 1;
    }
    true
}

fn all_dec_exec(t: &[u8]) -> (r: bool)
    ensures r == all_dec(t@),
{
    let mut i: usize = 0;
    while i < t.len()
        invariant i <= t@.len(), forall|q: int| 0 <= q < i ==> is_dec(#[trigger] t@[q]),
        decreases t.len() - i,
    {
        if !(48 <= t[i] && t[i] <= 57) { return false; }
        i += 1;
    }
    true
}

pub fn parse_value(t: &[u8], fuel: u128) -> (r: Option<CVal>)
    ensures match value(t@, fuel as nat) { Some(v) => r matches Some(x) && cv(x) == v, None => r is None },
    decreases fuel, 0nat,
{
    if fuel == 0 { return None; }
    if eq_bytes(t, b"-") {
        let r = CVal::Arr(Vec::new());
        proof { lemma_cv(r); assert(cvs(Seq::<CVal>::empty()) =~= Seq::<Val>::empty()); }
        return Some(r);
    }
    if eq_bytes(t, b"()") { return Some(CVal::Unit); }
    if eq_bytes(t, b"true") { return Some(CVal::Int(1)); }
    if eq_bytes(t, b"false") { return Some(CVal::Int(0)); }
    if eq_bytes(t, b"None") {
        let r = CVal::Adt(0, Vec::new());
        proof { lemma_cv(r); assert(cvs(Seq::<CVal>::empty()) =~= Seq::<Val>::empty()); }
        return Some(r);
    }
    let n = t.len();
    if starts_with(t, b"Some(") && n >= 6 && t[n - 1] == 41u8 {
        let i = sub(t, 5, n - 1);
        return match parse_value(i.as_slice(), fuel - 1) {
            Some(v) => {
                let mut vs = Vec::new();
                vs.push(v);
                let r = CVal::Adt(1, vs);
                proof { lemma_cv(r); assert(cvs(vs@) =~= seq![cv(v)]); }
                Some(r)
            },
            None => None,
        };
    }
    if starts_with(t, b"#") {
        if n < 2 || t[n - 1] != 41u8 { return None; }
        let r = sub(t, 1, n - 1);
        let mut q: usize = 0;
        while q < r.len() && r[q] != 40u8
            invariant q <= r@.len(), paren_at(r@, 0) == paren_at(r@, q as nat),
            decreases r.len() - q,
        {
            q += 1;
        }
        if q >= r.len() || q == 0 { return None; }
        let k = sub(r.as_slice(), 0, q);
        if !all_dec_exec(k.as_slice()) { return None; }
        let kv = match decval_exec(k.as_slice()) { Some(kv) => kv, None => return None };
        let body = sub(r.as_slice(), q + 1, r.len());
        let ps = split_top_exec(body.as_slice());
        return match parse_values(&ps, fuel - 1) {
            Some(vs) => { let x = CVal::Adt(kv, vs); proof { lemma_cv(x); } Some(x) },
            None => None,
        };
    }
    if starts_with(t, b"(") && n >= 2 && t[n - 1] == 41u8 {
        let ps = split_top_exec(sub(t, 1, n - 1).as_slice());
        return match parse_values(&ps, fuel - 1) {
            Some(vs) => { let x = CVal::Tup(vs); proof { lemma_cv(x); } Some(x) },
            None => None,
        };
    }
    if starts_with(t, b"0x") {
        return match int_lit_exec(t) {
            Some((dg, w)) => {
                if dg.len() == 0 { return None; }
                match hexval_exec(dg.as_slice()) {
                    Some(v) => if wmod_ok(v, w) { Some(CVal::Int(v)) } else { None },
                    None => None,
                }
            },
            None => None,
        };
    }
    if starts_with(t, b"[") && n >= 2 && t[n - 1] == 93u8 {
        let ps = split_top_exec(sub(t, 1, n - 1).as_slice());
        return match parse_values(&ps, fuel - 1) {
            Some(vs) => { let x = CVal::Arr(vs); proof { lemma_cv(x); } Some(x) },
            None => None,
        };
    }
    if n % 2 == 0 && all_hex_exec(t) {
        return Some(bytes_exec(t));
    }
    None
}

proof fn lemma_vals_none(ps: Seq<Seq<u8>>, k: int, fuel: nat)
    requires 0 <= k <= ps.len(), vals_of(ps.subrange(0, k), fuel) is None,
    ensures vals_of(ps, fuel) is None,
    decreases ps.len() - k,
{
    if k < ps.len() {
        assert(ps.subrange(0, k + 1).drop_last() =~= ps.subrange(0, k));
        lemma_vals_none(ps, k + 1, fuel);
    } else {
        assert(ps.subrange(0, k) =~= ps);
    }
}

pub fn parse_values(ps: &Vec<Vec<u8>>, fuel: u128) -> (r: Option<Vec<CVal>>)
    ensures match vals_of(views(ps@), fuel as nat) { Some(vs) => r matches Some(xs) && cvs(xs@) == vs, None => r is None },
    decreases fuel, ps@.len() + 1,
{
    let ghost vp = views(ps@);
    let mut out: Vec<CVal> = Vec::new();
    let mut k: usize = 0;
    while k < ps.len()
        invariant k <= ps@.len(), vp == views(ps@), vals_of(vp.subrange(0, k as int), fuel as nat) == Some(cvs(out@)),
        decreases ps.len() - k,
    {
        proof { assert(vp.subrange(0, k + 1).drop_last() =~= vp.subrange(0, k as int)); assert(vp.subrange(0, k + 1).last() == ps@[k as int]@); }
        match parse_value(ps[k].as_slice(), fuel) {
            Some(v) => {
                proof { lemma_cvs_push(out@, v); }
                out.push(v);
            },
            None => {
                proof { lemma_vals_none(vp, k + 1, fuel as nat); }
                return None;
            },
        }
        k += 1;
    }
    proof { assert(vp.subrange(0, ps@.len() as int) =~= vp); }
    Some(out)
}

pub fn parse_value_top(t: &[u8]) -> (r: Option<CVal>)
    ensures match value_top(t@) { Some(v) => r matches Some(x) && cv(x) == v, None => r is None },
{
    parse_value(t, t.len() as u128 + 1)
}

fn arg_exec(t: &[u8]) -> (r: Option<(bool, CVal)>)
    ensures match arg_of(t@) { Some((m, v)) => r matches Some((m2, x)) && m2 == m && cv(x) == v, None => r is None },
{
    if starts_with(t, b"mut:") {
        let u = sub(t, 4, t.len());
        match parse_value_top(u.as_slice()) { Some(x) => Some((true, x)), None => None }
    } else {
        match parse_value_top(t) {
            Some(x) => {
                proof { lemma_cv(x); }
                match x {
                    CVal::Arr(vs) => Some((false, CVal::Shr(Box::new(CVal::Arr(vs))))),
                    x => Some((false, x)),
                }
            },
            None => None,
        }
    }
}

fn bits_exec(t: &[u8]) -> (r: Option<u32>)
    ensures match bits_of(t@) { Some(w) => r == Some(w as u32) && w <= 128, None => r is None },
{
    let u = if starts_with(t, b"mut:") { sub(t, 4, t.len()) } else { sub(t, 0, t.len()) };
    proof { assert(t@.subrange(0, t@.len() as int) =~= t@); }
    match int_lit_exec(u.as_slice()) { Some((_, w)) => Some(w), None => None }
}

/// The vector of a line's words after its path; `Err` names the first bad word.
pub fn parse_vector(toks: &[Vec<u8>]) -> (r: Result<Vector, Vec<u8>>)
    ensures match vector_spec(views(toks@)) { Some(vs) => r matches Ok(v) && vector_v(v) == vs, None => r is Err },
{
    let ghost tv = views(toks@);
    let mut at: usize = 0;
    while at < toks.len() && !eq_bytes(toks[at].as_slice(), b"=>")
        invariant at <= toks@.len(), tv == views(toks@), arrow_at(tv, 0) == arrow_at(tv, at as nat),
        decreases toks.len() - at,
    {
        at += 1;
    }
    if at >= toks.len() { return Err(crate::pipeline::cat(b"no `=>`", b"")); }
    let ghost a = tv.subrange(0, at as int);
    let mut args: Vec<(bool, CVal)> = Vec::new();
    let mut bits: Vec<Option<u32>> = Vec::new();
    let mut j: usize = 0;
    while j < at
        invariant j <= at < toks@.len(), tv == views(toks@), a == tv.subrange(0, at as int), arrow_at(tv, 0) == at as nat,
            args_of(a.subrange(0, j as int)) == Some(Seq::new(args@.len(), |q: int| (args@[q].0, cv(args@[q].1)))),
            bits@.len() == j, forall|q: int| 0 <= q < j ==> (match #[trigger] bits@[q] { Some(w) => Some(w as nat), None => None }) == bits_of(a[q]),
        decreases at - j,
    {
        proof { assert(a.subrange(0, j + 1).drop_last() =~= a.subrange(0, j as int)); assert(a.subrange(0, j + 1).last() == toks@[j as int]@); }
        match arg_exec(toks[j].as_slice()) {
            Some(x) => {
                let ghost o = args@;
                args.push(x);
                proof { assert(Seq::new(args@.len(), |q: int| (args@[q].0, cv(args@[q].1))) =~= Seq::new(o.len(), |q: int| (o[q].0, cv(o[q].1))).push((x.0, cv(x.1)))); }
            },
            None => {
                proof { lemma_args_none(a, j as int + 1); }
                return Err(crate::pipeline::cat(toks[j].as_slice(), b": not a value"));
            },
        }
        bits.push(bits_exec(toks[j].as_slice()));
        j += 1;
    }
    proof { assert(a.subrange(0, at as int) =~= a); }
    let ghost w = tv.subrange(at + 1, tv.len() as int);
    let ghost nb = Seq::new(bits@.len(), |q: int| match bits@[q] { Some(x) => Some(x as nat), None => None });
    proof { assert(nb =~= Seq::new(a.len(), |q: int| bits_of(a[q]))); }
    if toks.len() - at == 2 && eq_bytes(toks[at + 1].as_slice(), b"panic") {
        proof { assert(w =~= seq![b"panic"@]); }
        let v = Vector { args, want: Vec::new(), bits, wbits: Vec::new(), panic: true };
        proof {
            assert(cvs(Seq::<CVal>::empty()) =~= Seq::<Val>::empty());
            assert(vector_v(v).wbits =~= Seq::<Option<nat>>::empty());
        }
        return Ok(v);
    }
    proof { if w == seq![b"panic"@] { assert(w.len() == 1); assert(toks@[at + 1]@ == w[0]); } }
    let mut want: Vec<CVal> = Vec::new();
    let mut wbits: Vec<Option<u32>> = Vec::new();
    let mut k: usize = at + 1;
    while k < toks.len()
        invariant at + 1 <= k <= toks@.len(), tv == views(toks@), w == tv.subrange(at + 1, tv.len() as int), arrow_at(tv, 0) == at as nat,
            a == tv.subrange(0, at as int), args_of(a) == Some(Seq::new(args@.len(), |q: int| (args@[q].0, cv(args@[q].1)))), w != seq![b"panic"@],
            wants_of(w.subrange(0, k - at - 1)) == Some(cvs(want@)), wbits@.len() == k - at - 1,
            forall|q: int| 0 <= q < k - at - 1 ==> (match #[trigger] wbits@[q] { Some(x) => Some(x as nat), None => None }) == bits_of(w[q]),
        decreases toks.len() - k,
    {
        proof { assert(w.subrange(0, k - at).drop_last() =~= w.subrange(0, k - at - 1)); assert(w.subrange(0, k - at).last() == toks@[k as int]@); }
        match parse_value_top(toks[k].as_slice()) {
            Some(x) => {
                proof { lemma_cvs_push(want@, x); assert(w[k - at - 1] == toks@[k as int]@); }
                want.push(x);
                wbits.push(bits_exec(toks[k].as_slice()));
            },
            None => {
                proof { lemma_wants_none(w, k - at); }
                return Err(crate::pipeline::cat(toks[k].as_slice(), b": not a value"));
            },
        }
        k += 1;
    }
    let v = Vector { args, want, bits, wbits, panic: false };
    proof {
        assert(w.subrange(0, w.len() as int) =~= w);
        assert(vector_v(v).wbits =~= Seq::new(w.len(), |q: int| bits_of(w[q])));
    }
    Ok(v)
}

proof fn lemma_args_none(a: Seq<Seq<u8>>, k: int)
    requires 0 <= k <= a.len(), args_of(a.subrange(0, k)) is None,
    ensures args_of(a) is None,
    decreases a.len() - k,
{
    if k < a.len() { assert(a.subrange(0, k + 1).drop_last() =~= a.subrange(0, k)); lemma_args_none(a, k + 1); } else { assert(a.subrange(0, k) =~= a); }
}

proof fn lemma_wants_none(a: Seq<Seq<u8>>, k: int)
    requires 0 <= k <= a.len(), wants_of(a.subrange(0, k)) is None,
    ensures wants_of(a) is None,
    decreases a.len() - k,
{
    if k < a.len() { assert(a.subrange(0, k + 1).drop_last() =~= a.subrange(0, k)); lemma_wants_none(a, k + 1); } else { assert(a.subrange(0, k) =~= a); }
}

// ------------------------------------------------------------------ the vector check

pub open spec fn mut_param(b: ctcore::syntax::Body, j: int) -> bool { j < b.nargs && 1 + j < b.locals@.len() && b.locals@[1 + j] is Mut }

pub open spec fn entry_arg(b: ctcore::syntax::Body, m: bool, j: int, x: Val) -> Val {
    if !m && 1 + j < b.locals@.len() && b.locals@[1 + j] is Shr && !(x is Shr) { Val::Shr(Box::new(x)) } else { x }
}

pub open spec fn entry_args(b: ctcore::syntax::Body, v: VSpec) -> Seq<Val> {
    Seq::new(v.args.len(), |j: int| entry_arg(b, v.args[j].0, j, v.args[j].1))
}

pub open spec fn entry_slots(b: ctcore::syntax::Body, a: Seq<Val>) -> Seq<Val> {
    Seq::new(a.len(), |j: int| if mut_param(b, j) { a[j] } else { Val::Unit })
}

/// The final slots of the `mut:` arguments among the first `n`, in order.
pub open spec fn mouts(args: Seq<(bool, Val)>, slots: Seq<Val>, n: nat) -> Seq<Val>
    decreases n,
{
    if n == 0 { seq![] } else { mouts(args, slots, (n - 1) as nat) + if args[n - 1].0 { seq![nth(slots, (n - 1) as nat)] } else { Seq::<Val>::empty() } }
}

/// An int type's width, through one `Mut`.
pub open spec fn wint(t: Ty) -> Option<nat> {
    match t {
        Ty::Int(it) => Some(bits(it)),
        Ty::Mut(inner) => match *inner { Ty::Int(it) => Some(bits(it)), _ => None },
        _ => None,
    }
}

/// A width suffix `w` (if any) is the width of `t`.
pub open spec fn wok(t: Ty, w: Option<nat>) -> bool { w is None || wint(t) == w }

/// Parameter `j`'s type (`Unit` past the locals).
pub open spec fn arg_ty(b: ctcore::syntax::Body, j: int) -> Ty { if 1 + j < b.locals@.len() { b.locals@[1 + j] } else { Ty::Unit } }

/// The types of the `mut:` parameters among the first `n`, in order (as `mouts`).
pub open spec fn otys(b: ctcore::syntax::Body, args: Seq<(bool, Val)>, n: nat) -> Seq<Ty>
    decreases n,
{
    if n == 0 { seq![] } else { otys(b, args, (n - 1) as nat) + if args[n - 1].0 { seq![arg_ty(b, n - 1)] } else { Seq::<Ty>::empty() } }
}

proof fn lemma_otys_len(b: ctcore::syntax::Body, args: Seq<(bool, Val)>, n: nat)
    ensures otys(b, args, n).len() <= n,
    decreases n,
{
    if n > 0 { lemma_otys_len(b, args, (n - 1) as nat); }
}

/// Every width suffix fits: an argument's its parameter's type, a wanted value's the return
/// local's or its `mut:` parameter's pointee type.
pub open spec fn widths_ok(b: ctcore::syntax::Body, v: VSpec) -> bool {
    &&& v.bits.len() == v.args.len() && forall|j: int| 0 <= j < v.args.len() ==> wok(arg_ty(b, j), #[trigger] v.bits[j])
    &&& v.wbits.len() == v.want.len()
    &&& b.locals@.len() > 0
    &&& forall|k: int| 0 <= k < v.want.len() && k < 1 + otys(b, v.args, v.args.len()).len() ==>
            wok((seq![b.locals@[0]] + otys(b, v.args, v.args.len()))[k], #[trigger] v.wbits[k])
}

/// The vector's shape fits fn 0: one argument per parameter, `mut:` exactly at the `&mut` ones.
pub open spec fn shape_ok(p: Program, v: VSpec) -> bool {
    p.fns@.len() > 0 && v.args.len() == p.fns@[0].nargs && (forall|j: int| 0 <= j < v.args.len() ==> (#[trigger] v.args[j]).0 == mut_param(p.fns@[0], j))
        && widths_ok(p.fns@[0], v)
}

/// The MIR arguments: `entry_args`, except a `Mut(Slot(j))` at each `&mut` parameter `j`
/// (`wt_rec` accepts only a `Mut` at a `&mut` type; `entry_local` binds the slot there anyway).
pub open spec fn mir_args(b: ctcore::syntax::Body, v: VSpec) -> Seq<Val> {
    Seq::new(v.args.len(), |j: int| if mut_param(b, j) { Val::Mut(Loc { root: Root::Slot(j as nat), path: seq![] }) } else { entry_arg(b, v.args[j].0, j, v.args[j].1) })
}

/// The vector's slots: the `mut:` arguments' initial pointees.
pub open spec fn mir_slots(b: ctcore::syntax::Body, v: VSpec) -> Seq<Val> { entry_slots(b, entry_args(b, v)) }

/// Root `insts[i]`'s MIR run on the vector, from `mir_entry`, at `FUEL`.
#[verifier::opaque]
pub open spec fn vec_run(m: MirCrate, pol: Policy, i: nat, p: Program, v: VSpec) -> Out {
    mir_run(m, cpol(pol), i, mir_entry(m, i, mir_args(p.fns@[0], v), mir_slots(p.fns@[0], v)), FUEL as nat)
}

/// The vector's MIR arguments and slots are well-typed for root `insts[i]` (`wt_args`).
#[verifier::opaque]
pub open spec fn vec_wt(m: MirCrate, i: nat, p: Program, v: VSpec) -> bool {
    wt_args(m, i, mir_args(p.fns@[0], v), mir_slots(p.fns@[0], v))
}

/// **A passing vector**: the root's MIR run on the vector's (well-typed) arguments completes in
/// `n` steps with the wanted return value and final `mut:` pointees.
pub open spec fn passes(m: MirCrate, pol: Policy, i: nat, p: Program, v: VSpec, n: nat) -> bool {
    shape_ok(p, v) && !v.panic && vec_wt(m, i, p, v)
        && (vec_run(m, pol, i, p, v) matches Out::Done(fr, _, k) && k == n && want_ok(v, fr))
}

/// The final frame's return value and `mut:` pointees are the vector's wanted values.
#[verifier::opaque]
pub open spec fn want_ok(v: VSpec, fr: ctcore::sem::Frame) -> bool {
    seq![nth(fr.locals, 0)] + mouts(v.args, fr.slots, v.args.len()) == v.want
}

/// **A passing panic vector**: the root's MIR run on the vector's (well-typed) arguments panics.
/// (`Out::Panic` also covers a stuck state, so this is no never-Stuck evidence.)
pub open spec fn panics(m: MirCrate, pol: Policy, i: nat, p: Program, v: VSpec) -> bool {
    shape_ok(p, v) && v.panic && vec_wt(m, i, p, v) && vec_run(m, pol, i, p, v) is Panic
}

fn is_mut_param(b: &ctcore::syntax::Body, j: usize) -> (r: bool)
    ensures r == mut_param(*b, j as int),
{
    j < b.nargs && b.locals.len() > 0 && j < b.locals.len() - 1 && match &b.locals[1 + j] { Ty::Mut(_) => true, _ => false }
}

fn int_width(t: &Ty) -> (r: Option<u32>)
    ensures match r { Some(x) => wint(*t) == Some(x as nat), None => wint(*t) is None },
{
    match t {
        Ty::Int(it) => Some(crate::interp_arith::bits_exec(it)),
        Ty::Mut(inner) => match &**inner { Ty::Int(it) => Some(crate::interp_arith::bits_exec(it)), _ => None },
        _ => None,
    }
}

/// Wanted value `k`'s width suffix `w` fits type `t`.
fn want_width(t: &Ty, w: Option<u32>, k: usize) -> (r: Result<(), Vec<u8>>)
    requires k < usize::MAX,
    ensures r is Ok ==> wok(*t, match w { Some(x) => Some(x as nat), None => None }),
{
    match w {
        None => Ok(()),
        Some(x) => match int_width(t) {
            Some(y) => if y == x { Ok(()) } else {
                let mut e = crate::pipeline::cat(b"want #", crate::text::dec(k as u64 + 1).as_slice());
                crate::text::put(&mut e, b": a ");
                crate::text::put(&mut e, crate::text::dec(x as u64).as_slice());
                crate::text::put(&mut e, b"-bit value for a ");
                crate::text::put(&mut e, crate::text::dec(y as u64).as_slice());
                crate::text::put(&mut e, b"-bit result");
                Err(e)
            },
            None => {
                let mut e = crate::pipeline::cat(b"want #", crate::text::dec(k as u64 + 1).as_slice());
                crate::text::put(&mut e, b": a ");
                crate::text::put(&mut e, crate::text::dec(x as u64).as_slice());
                crate::text::put(&mut e, b"-bit value for a non-int result");
                Err(e)
            },
        },
    }
}

/// Checks vector `v` against root `insts[i]`, whose translation is `p` (shapes and widths are read
/// from `p`'s fn 0): `Ok(Some(steps))` for a completed MIR run with the wanted values, `Ok(None)`
/// for a panic vector whose run panics, `Err(why)` otherwise.
pub fn check_vector(m: &MirCrate, tb: &Tabs, pol: &Policy, i: usize, p: &Program, v: &Vector) -> (r: Result<Option<u64>, Vec<u8>>)
    requires tabs_ok(*m, *tb), in_subset(*m, cpol(*pol), i as nat), p.fns@.len() > 0,
    ensures
        r matches Ok(Some(n)) ==> passes(*m, *pol, i as nat, *p, vector_v(*v), n as nat),
        r matches Ok(None) ==> panics(*m, *pol, i as nat, *p, vector_v(*v)),
{
    hide(closed);
    let ghost vs = vector_v(*v);
    if p.fns.len() == 0 { return Err(crate::pipeline::cat(b"empty program", b"")); }
    let b = &p.fns[0];
    if v.args.len() != b.nargs {
        let mut e = crate::text::dec(v.args.len() as u64);
        crate::text::put(&mut e, b" args for ");
        crate::text::put(&mut e, crate::text::dec(b.nargs as u64).as_slice());
        crate::text::put(&mut e, b" params");
        return Err(e);
    }
    let mut j: usize = 0;
    while j < v.args.len()
        invariant p.fns@.len() > 0, j <= v.args@.len() == b.nargs, b == p.fns@[0], vs == vector_v(*v),
            forall|q: int| 0 <= q < j ==> (#[trigger] vs.args[q]).0 == mut_param(*b, q),
        decreases v.args.len() - j,
    {
        if v.args[j].0 != is_mut_param(b, j) {
            let mut e = crate::pipeline::cat(b"param #", crate::text::dec(j as u64 + 1).as_slice());
            crate::text::put(&mut e, b": `mut:` must mark exactly the &mut params");
            return Err(e);
        }
        j += 1;
    }
    if v.bits.len() != v.args.len() { return Err(crate::pipeline::cat(b"a width per argument", b"")); }
    let mut j: usize = 0;
    while j < v.bits.len()
        invariant p.fns@.len() > 0, b == p.fns@[0], vs == vector_v(*v), j <= v.bits@.len() == v.args@.len(),
            forall|q: int| 0 <= q < j ==> wok(arg_ty(*b, q), #[trigger] vs.bits[q]),
        decreases v.bits.len() - j,
    {
        if let Some(w) = v.bits[j] {
            let pw = if b.locals.len() > 0 && j < b.locals.len() - 1 { int_width(&b.locals[1 + j]) } else { None };
            proof { if !(1 + j < b.locals@.len()) { assert(wint(arg_ty(*b, j as int)) is None); } }
            match pw {
                Some(x) => if x != w {
                    let mut e = crate::pipeline::cat(b"param #", crate::text::dec(j as u64 + 1).as_slice());
                    crate::text::put(&mut e, b": a ");
                    crate::text::put(&mut e, crate::text::dec(w as u64).as_slice());
                    crate::text::put(&mut e, b"-bit int arg for a ");
                    crate::text::put(&mut e, crate::text::dec(x as u64).as_slice());
                    crate::text::put(&mut e, b"-bit param");
                    return Err(e);
                },
                None => {
                    let mut e = crate::pipeline::cat(b"param #", crate::text::dec(j as u64 + 1).as_slice());
                    crate::text::put(&mut e, b": a ");
                    crate::text::put(&mut e, crate::text::dec(w as u64).as_slice());
                    crate::text::put(&mut e, b"-bit int arg for a non-int param");
                    return Err(e);
                },
            }
        }
        j += 1;
    }
    // the wanted values' widths: the return local's type, then each `mut:` parameter's
    if b.locals.len() == 0 { return Err(crate::pipeline::cat(b"no return local", b"")); }
    if v.wbits.len() != v.want.len() { return Err(crate::pipeline::cat(b"a width per wanted value", b"")); }
    if v.want.len() > 0 { want_width(&b.locals[0], v.wbits[0], 0)?; }
    let ghost l0 = b.locals@[0];
    let mut c: usize = 1;
    let mut j: usize = 0;
    while j < v.args.len()
        invariant p.fns@.len() > 0, b == p.fns@[0], vs == vector_v(*v), j <= v.args@.len() == b.nargs, l0 == b.locals@[0],
            b.locals@.len() > 0, vs.wbits.len() == vs.want.len(), c as int == 1 + otys(*b, vs.args, j as nat).len(),
            forall|q: int| (0 <= q < vs.want.len() && q < c) ==> wok((seq![l0] + otys(*b, vs.args, j as nat))[q], #[trigger] vs.wbits[q]),
            forall|q: int| 0 <= q < v.args@.len() ==> (#[trigger] vs.args[q]).0 == mut_param(*b, q),
        decreases v.args.len() - j,
    {
        let ghost t0 = seq![l0] + otys(*b, vs.args, j as nat);
        let ghost t1 = seq![l0] + otys(*b, vs.args, (j + 1) as nat);
        proof {
            assert(otys(*b, vs.args, (j + 1) as nat) == otys(*b, vs.args, j as nat) + if vs.args[j as int].0 { seq![arg_ty(*b, j as int)] } else { Seq::<Ty>::empty() });
            assert(forall|q: int| 0 <= q < t0.len() ==> t1[q] == t0[q]);
        }
        if v.args[j].0 {
            proof { assert(t1[c as int] == arg_ty(*b, j as int)); assert(mut_param(*b, j as int)); }
            if c < v.want.len() { want_width(&b.locals[1 + j], v.wbits[c], c)?; }
            if c == usize::MAX { return Err(crate::pipeline::cat(b"too many wanted values", b"")); }
            c = c + 1;
        }
        j += 1;
    }
    proof { assert(otys(*b, vs.args, vs.args.len()) == otys(*b, vs.args, j as nat)); }
    // the entry arguments and slots
    let mut args: Vec<CVal> = Vec::new();
    let mut slots: Vec<CVal> = Vec::new();
    let mut nm: usize = 0;
    let mut j: usize = 0;
    while j < v.args.len()
        invariant p.fns@.len() > 0, j <= v.args@.len() == b.nargs, b == p.fns@[0], vs == vector_v(*v), args@.len() == j, slots@.len() == j, nm <= j,
            forall|q: int| 0 <= q < j ==> cv(#[trigger] args@[q]) == entry_args(*b, vs)[q],
            forall|q: int| 0 <= q < j ==> cv(#[trigger] slots@[q]) == entry_slots(*b, entry_args(*b, vs))[q],
        decreases v.args.len() - j,
    {
        let (m, x) = (&v.args[j].0, &v.args[j].1);
        let shr_param = b.locals.len() > 0 && j < b.locals.len() - 1 && match &b.locals[1 + j] { Ty::Shr(_) => true, _ => false };
        let a = if !*m && shr_param && !(match x { CVal::Shr(_) => true, _ => false }) { CVal::Shr(Box::new(cclone(x))) } else { cclone(x) };
        proof { lemma_cv(*x); }
        if is_mut_param(b, j) { slots.push(cclone(&a)); } else { slots.push(CVal::Unit); }
        if *m { nm = nm + 1; }
        args.push(a);
        j += 1;
    }
    proof {
        assert(cvs(args@) =~= entry_args(*b, vs));
        assert(cvs(slots@) =~= entry_slots(*b, entry_args(*b, vs)));
    }
    proof { assert(shape_ok(*p, vs)); }
    run_vector(m, tb, pol, i, p, v, args, slots, nm)
}

/// The run part of `check_vector`, on the shaped entry arguments.
fn run_vector(m: &MirCrate, tb: &Tabs, pol: &Policy, i: usize, p: &Program, v: &Vector, args: Vec<CVal>, slots: Vec<CVal>, nm: usize)
    -> (r: Result<Option<u64>, Vec<u8>>)
    requires tabs_ok(*m, *tb), in_subset(*m, cpol(*pol), i as nat), p.fns@.len() > 0, shape_ok(*p, vector_v(*v)),
        cvs(args@) == entry_args(p.fns@[0], vector_v(*v)), cvs(slots@) == entry_slots(p.fns@[0], entry_args(p.fns@[0], vector_v(*v))),
    ensures
        r matches Ok(Some(n)) ==> passes(*m, *pol, i as nat, *p, vector_v(*v), n as nat),
        r matches Ok(None) ==> panics(*m, *pol, i as nat, *p, vector_v(*v)),
{
    hide(mir_run);
    hide(mir_entry);
    hide(in_subset);
    hide(closed);
    hide(shape_ok);
    proof { reveal(vec_run); reveal(vec_wt); }
    let ghost vs = vector_v(*v);
    let b = &p.fns[0];
    if !v.panic && (nm >= usize::MAX || v.want.len() != nm + 1) {
        let mut e = crate::text::dec(v.want.len() as u64);
        crate::text::put(&mut e, b" expected values for 1 return value and ");
        crate::text::put(&mut e, crate::text::dec(nm as u64).as_slice());
        crate::text::put(&mut e, b" &mut params");
        return Err(e);
    }
    let margs = mir_args_exec(b, &args, Ghost(vs));
    if !x_wt_args(m, tb, i, &margs, &slots) { return Err(crate::pipeline::cat(b"args not well-typed", b"")); }
    let r = mir_eval(m, tb, pol, i, &margs, &slots, FUEL);
    if v.panic {
        return match r {
            Ev::Panic => Ok(None),
            Ev::Done(_, _) => Err(crate::pipeline::cat(b"the run completed (want panic)", b"")),
            Ev::Fuel => Err(crate::pipeline::cat(b"mir: fuel", b"")),
            Ev::GaveUp => Err(crate::pipeline::cat(b"mir: gave up", b"")),
        };
    }
    match r {
        Ev::Panic => Err(crate::pipeline::cat(b"mir: panic", b"")),
        Ev::Fuel => Err(crate::pipeline::cat(b"mir: fuel", b"")),
        Ev::GaveUp => Err(crate::pipeline::cat(b"mir: gave up", b"")),
        Ev::Done(fr, n) => match got_want(fr, v) {
            Ok(()) => Ok(Some(n)),
            Err(e) => Err(e),
        },
    }
}

/// A completed run's return value and final `mut:` pointees, against the wanted values.
fn got_want(fr: CFrame, v: &Vector) -> (r: Result<(), Vec<u8>>)
    ensures r is Ok ==> want_ok(vector_v(*v), fv(fr)),
{
    proof { reveal(want_ok); }
    let ghost vs = vector_v(*v);
    let CFrame { locals: mut cl, slots: sl } = fr;
    let ghost l0 = cvs(cl@);
    let ret = if cl.len() > 0 { take_at(&mut cl, 0) } else { CVal::Unit };
    proof { assert(cv(ret) == nth(l0, 0)); }
    let mut got: Vec<CVal> = Vec::new();
    got.push(ret);
    let mut j: usize = 0;
    while j < v.args.len()
        invariant j <= v.args@.len(), vs == vector_v(*v), got@.len() >= 1, cv(got@[0]) == cv(ret),
            cvs(got@) == seq![cv(ret)] + mouts(vs.args, cvs(sl@), j as nat),
        decreases v.args.len() - j,
    {
        if v.args[j].0 {
            let x = if j < sl.len() { cclone(&sl[j]) } else { CVal::Unit };
            proof { lemma_cvs_push(got@, x); }
            got.push(x);
        }
        proof { assert(mouts(vs.args, cvs(sl@), (j + 1) as nat) =~= mouts(vs.args, cvs(sl@), j as nat) + if vs.args[j as int].0 { seq![nth(cvs(sl@), j as nat)] } else { Seq::<Val>::empty() }); }
        j += 1;
    }
    if ceq_vec(&got, &v.want) {
        Ok(())
    } else {
        let mut e = crate::pipeline::cat(b"got", b"");
        let mut k: usize = 0;
        while k < got.len() decreases got.len() - k { e.push(32u8); show(&got[k], &mut e); k += 1; }
        crate::text::put(&mut e, b" want");
        let mut k: usize = 0;
        while k < v.want.len() decreases v.want.len() - k { e.push(32u8); show(&v.want[k], &mut e); k += 1; }
        Err(e)
    }
}

/// `mir_args` from the entry arguments: a `Mut(Slot(j))` at each `&mut` parameter.
fn mir_args_exec(b: &ctcore::syntax::Body, args: &Vec<CVal>, Ghost(vs): Ghost<VSpec>) -> (r: Vec<CVal>)
    requires cvs(args@) == entry_args(*b, vs),
    ensures cvs(r@) == mir_args(*b, vs),
{
    let mut r: Vec<CVal> = Vec::new();
    let mut j: usize = 0;
    proof { assert(cvs(args@).len() == args@.len()); assert(entry_args(*b, vs).len() == vs.args.len()); }
    while j < args.len()
        invariant j <= args@.len() == vs.args.len(), cvs(args@) == entry_args(*b, vs), r@.len() == j,
            forall|q: int| 0 <= q < j ==> cv(#[trigger] r@[q]) == mir_args(*b, vs)[q],
        decreases args.len() - j,
    {
        let x = if is_mut_param(b, j) {
            let l = CLoc { root: CRoot::Slot(j), path: Vec::new() };
            proof { assert(pes(l.path@) =~= Seq::<ctcore::sem::PE>::empty()); }
            CVal::Mut(l)
        } else {
            proof { assert(cvs(args@)[j as int] == cv(args@[j as int])); }
            cclone(&args[j])
        };
        proof {
            assert(mir_args(*b, vs)[j as int] == if mut_param(*b, j as int) { Val::Mut(Loc { root: Root::Slot(j as nat), path: seq![] }) } else { entry_arg(*b, vs.args[j as int].0, j as int, vs.args[j as int].1) });
            assert(entry_args(*b, vs)[j as int] == entry_arg(*b, vs.args[j as int].0, j as int, vs.args[j as int].1));
            assert(cv(x) == mir_args(*b, vs)[j as int]);
        }
        r.push(x);
        j += 1;
    }
    proof { assert(cvs(r@) =~= mir_args(*b, vs)); }
    r
}

fn put_hex(out: &mut Vec<u8>, n: u128)
    decreases n,
{
    if n >= 16 { put_hex(out, n / 16); }
    let d = (n % 16) as u8;
    out.push(if d < 10 { 48 + d } else { 87 + d });
}

/// A value in the vector syntax (byte arrays as hex; ints without a suffix).
fn show(v: &CVal, out: &mut Vec<u8>)
    decreases v,
{
    match v {
        CVal::Int(n) => { crate::text::put(out, b"0x"); put_hex(out, *n); },
        CVal::Unit => crate::text::put(out, b"()"),
        CVal::Arr(vs) => {
            let mut bytes = true;
            let mut k: usize = 0;
            while k < vs.len() decreases vs.len() - k {
                match &vs[k] { CVal::Int(n) => if *n >= 256 { bytes = false; }, _ => { bytes = false; } }
                k += 1;
            }
            if vs.len() == 0 { out.push(45u8); }
            else if bytes {
                let mut k: usize = 0;
                while k < vs.len() decreases vs.len() - k {
                    if let CVal::Int(n) = &vs[k] { if *n < 16 { out.push(48u8); } put_hex(out, *n); }
                    k += 1;
                }
            } else { show_list(b"[", vs, b"]", out); }
        },
        CVal::Tup(vs) => show_list(b"(", vs, b")", out),
        CVal::Adt(k, vs) => { out.push(35u8); crate::text::put(out, crate::text::dec(*k as u64).as_slice()); show_list(b"(", vs, b")", out); },
        CVal::Shr(b) => { out.push(38u8); show(&**b, out); },
        CVal::Mut(_) => crate::text::put(out, b"&mut"),
    }
}

fn show_list(open: &[u8], vs: &Vec<CVal>, close: &[u8], out: &mut Vec<u8>)
    decreases vs,
{
    crate::text::put(out, open);
    let mut k: usize = 0;
    while k < vs.len() decreases vs.len() - k {
        if k > 0 { out.push(44u8); }
        show(&vs[k], out);
        k += 1;
    }
    crate::text::put(out, close);
}

} // verus!
