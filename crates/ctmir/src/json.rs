//! The JSON reader. `print` is serde_json's compact writer (`serde_json::to_string`) as a spec and
//! is trusted; `parse` is proved to return only values whose `print` is exactly the input.
use vstd::prelude::*;

verus! {

#[derive(Debug, PartialEq, Eq)]
pub enum Json { Null, Bool(bool), Num(bool, u128), Str(Vec<u8>), Arr(Vec<Json>), Obj(Vec<(Vec<u8>, Json)>) }

// ------------------------------------------------------------------ the trusted writer spec

/// A lowercase hex digit, as serde_json's `HEX_DIGITS` table.
pub open spec fn hex(n: u8) -> u8 { if n < 10 { (b'0' + n) as u8 } else { (b'a' + n - 10) as u8 } }

/// serde_json's `format_escaped_str_contents` for one byte: its `ESCAPE` table, with
/// `\u00XX` for the other control bytes and every other byte (DEL and >= 0x80 included) raw.
pub open spec fn esc(c: u8) -> Seq<u8> {
    if c == 0x22 { seq![b'\\', b'"'] }
    else if c == 0x5c { seq![b'\\', b'\\'] }
    else if c == 0x08 { seq![b'\\', b'b'] }
    else if c == 0x0c { seq![b'\\', b'f'] }
    else if c == 0x0a { seq![b'\\', b'n'] }
    else if c == 0x0d { seq![b'\\', b'r'] }
    else if c == 0x09 { seq![b'\\', b't'] }
    else if c < 0x20 { seq![b'\\', b'u', b'0', b'0', hex(c / 16), hex(c % 16)] }
    else { seq![c] }
}

pub open spec fn esc_all(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 { seq![] } else { esc_all(s.subrange(0, s.len() - 1)) + esc(s.last()) }
}

pub open spec fn print_str(s: Seq<u8>) -> Seq<u8> { seq![b'"'] + esc_all(s) + seq![b'"'] }

/// Decimal, no leading zeros, `0` alone for zero (itoa).
pub open spec fn digits(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 10 { seq![(b'0' + n) as u8] } else { digits(n / 10) + seq![(b'0' + n % 10) as u8] }
}

pub open spec fn sep(n: nat) -> Seq<u8> { if n == 0 { seq![] } else { seq![b','] } }

pub open spec fn print(j: Json) -> Seq<u8>
    decreases j,
{
    match j {
        Json::Null => seq![b'n', b'u', b'l', b'l'],
        Json::Bool(t) => if t { seq![b't', b'r', b'u', b'e'] } else { seq![b'f', b'a', b'l', b's', b'e'] },
        Json::Num(neg, m) => (if neg { seq![b'-'] } else { seq![] }) + digits(m as nat),
        Json::Str(s) => print_str(s@),
        Json::Arr(v) => seq![b'['] + print_elems(v@) + seq![b']'],
        Json::Obj(v) => seq![b'{'] + print_fields(v@) + seq![b'}'],
    }
}

/// Array elements, comma-separated.
pub open spec fn print_elems(s: Seq<Json>) -> Seq<u8>
    decreases s,
{
    if s.len() == 0 { seq![] } else {
        let n = s.len() - 1;
        print_elems(s.subrange(0, n)) + sep(n as nat) + print(s[n])
    }
}

/// Object members `"key":value`, comma-separated, in order.
pub open spec fn print_fields(s: Seq<(Vec<u8>, Json)>) -> Seq<u8>
    decreases s,
{
    if s.len() == 0 { seq![] } else {
        let n = s.len() - 1;
        print_fields(s.subrange(0, n)) + sep(n as nat) + print_str(s[n].0@) + seq![b':'] + print(s[n].1)
    }
}

// ------------------------------------------------------------------ depth

/// Nesting depth: scalars are 0, an array or object is one more than its deepest member.
pub open spec fn depth(j: Json) -> nat
    decreases j,
{
    match j {
        Json::Arr(v) => 1 + depth_elems(v@),
        Json::Obj(v) => 1 + depth_fields(v@),
        _ => 0,
    }
}

pub open spec fn depth_elems(s: Seq<Json>) -> nat
    decreases s,
{
    if s.len() == 0 { 0 } else {
        let n = s.len() - 1;
        let a = depth_elems(s.subrange(0, n));
        let b = depth(s[n]);
        if a < b { b } else { a }
    }
}

pub open spec fn depth_fields(s: Seq<(Vec<u8>, Json)>) -> nat
    decreases s,
{
    if s.len() == 0 { 0 } else {
        let n = s.len() - 1;
        let a = depth_fields(s.subrange(0, n));
        let b = depth(s[n].1);
        if a < b { b } else { a }
    }
}

pub const MAX_DEPTH: usize = 256;

// ------------------------------------------------------------------ lookup

/// The value of the first member named `k`.
pub open spec fn obj_get_spec(f: Seq<(Vec<u8>, Json)>, k: Seq<u8>) -> Option<Json>
    decreases f.len(),
{
    if f.len() == 0 { None } else if f[0].0@ == k { Some(f[0].1) } else { obj_get_spec(f.subrange(1, f.len() as int), k) }
}

pub fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures r == (a@ == b@),
{
    if a.len() != b.len() { return false; }
    let mut i: usize = 0;
    while i < a.len()
        invariant i <= a.len(), a.len() == b.len(), forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases a.len() - i,
    {
        if a[i] != b[i] { return false; }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

pub fn obj_get<'a>(fields: &'a Vec<(Vec<u8>, Json)>, k: &[u8]) -> (r: Option<&'a Json>)
    ensures
        match r {
            Some(x) => obj_get_spec(fields@, k@) == Some(*x),
            None => obj_get_spec(fields@, k@) is None,
        },
{
    let mut i: usize = 0;
    assert(fields@.subrange(0, fields.len() as int) =~= fields@);
    while i < fields.len()
        invariant i <= fields.len(), obj_get_spec(fields@, k@) == obj_get_spec(fields@.subrange(i as int, fields.len() as int), k@),
        decreases fields.len() - i,
    {
        let ghost rest = fields@.subrange(i as int, fields.len() as int);
        assert(rest.subrange(1, rest.len() as int) =~= fields@.subrange(i + 1, fields.len() as int));
        if bytes_eq(fields[i].0.as_slice(), k) { return Some(&fields[i].1); }
        i += 1;
    }
    None
}

// ------------------------------------------------------------------ the reader

/// One string-body unit at `p`: a raw byte or an escape, in serde's canonical form only.
fn unescape(b: &[u8], p: usize) -> (r: Option<(u8, usize)>)
    requires p < b.len(),
    ensures r matches Some((x, q)) ==> p < q <= b.len() && b@.subrange(p as int, q as int) == esc(x),
{
    let c = b[p];
    if c == b'"' || c < 0x20 { return None; }
    if c != b'\\' {
        assert(b@.subrange(p as int, p + 1) =~= seq![c]);
        return Some((c, p + 1));
    }
    if p + 1 >= b.len() { return None; }
    let e = b[p + 1];
    if e == b'u' { return unescape_u(b, p); }
    let x: u8 = if e == b'"' { 0x22 } else if e == b'\\' { 0x5c } else if e == b'b' { 0x08 } else if e == b'f' { 0x0c }
        else if e == b'n' { 0x0a } else if e == b'r' { 0x0d } else if e == b't' { 0x09 } else { return None; };
    assert(b@.subrange(p as int, p + 2) =~= esc(x));
    Some((x, p + 2))
}

/// `\u00XX` with lowercase hex, for a control byte that has no short escape.
fn unescape_u(b: &[u8], p: usize) -> (r: Option<(u8, usize)>)
    requires p + 1 < b.len(), b[p as int] == b'\\', b[p + 1] == b'u',
    ensures r matches Some((x, q)) ==> p < q <= b.len() && b@.subrange(p as int, q as int) == esc(x),
{
    if b.len() - p <= 5 || b[p + 2] != b'0' || b[p + 3] != b'0' { return None; }
    let h = b[p + 4];
    let l = b[p + 5];
    let hv: u8 = if h == b'0' { 0 } else if h == b'1' { 1 } else { return None; };
    let lv: u8 = if b'0' <= l && l <= b'9' { l - b'0' } else if b'a' <= l && l <= b'f' { l - b'a' + 10 } else { return None; };
    let x: u8 = hv * 16 + lv;
    if x == 0x08 || x == 0x09 || x == 0x0a || x == 0x0c || x == 0x0d { return None; }
    assert(x / 16 == hv && x % 16 == lv);
    assert(b@.subrange(p as int, p + 6) =~= esc(x));
    Some((x, p + 6))
}

/// A string starting at its opening quote `b[i]`.
fn parse_str(b: &[u8], i: usize) -> (r: Option<(Vec<u8>, usize)>)
    ensures r matches Some((s, k)) ==> i < k <= b.len() && b@.subrange(i as int, k as int) == print_str(s@),
{
    if i >= b.len() || b[i] != b'"' { return None; }
    let mut out: Vec<u8> = Vec::new();
    let mut p = i + 1;
    while p < b.len()
        invariant i < p <= b.len(), b@[i as int] == b'"', b@.subrange(i + 1, p as int) == esc_all(out@),
        decreases b.len() - p,
    {
        if b[p] == b'"' {
            assert(b@.subrange(i as int, p + 1) =~= seq![b'"'] + b@.subrange(i + 1, p as int) + seq![b'"']);
            return Some((out, p + 1));
        }
        match unescape(b, p) {
            None => { return None; },
            Some((x, q)) => {
                proof {
                    assert(out@.push(x).subrange(0, out@.len() as int) =~= out@);
                    assert(b@.subrange(i + 1, q as int) =~= b@.subrange(i + 1, p as int) + b@.subrange(p as int, q as int));
                }
                out.push(x);
                p = q;
            },
        }
    }
    None
}

proof fn lemma_digits_step(m: nat, d: nat)
    requires m >= 1, d < 10,
    ensures digits(m * 10 + d) == digits(m) + seq![(b'0' + d) as u8],
{
    assert((m * 10 + d) / 10 == m && (m * 10 + d) % 10 == d) by (nonlinear_arith) requires d < 10;
}

/// An integer: optional `-`, no leading zeros, no `-0`, at most `u128::MAX` in magnitude.
fn parse_num(b: &[u8], i: usize) -> (r: Option<(Json, usize)>)
    requires i < b.len(),
    ensures r matches Some((j, k)) ==> i < k <= b.len() && b@.subrange(i as int, k as int) == print(j) && depth(j) == 0,
{
    let neg = b[i] == b'-';
    let s = if neg { i + 1 } else { i };
    if s >= b.len() || b[s] < b'0' || b[s] > b'9' { return None; }
    let ghost pre: Seq<u8> = if neg { seq![b'-'] } else { seq![] };
    if b[s] == b'0' {
        if neg { return None; }
        assert(b@.subrange(i as int, i + 1) =~= digits(0));
        assert(b@.subrange(i as int, i + 1) =~= print(Json::Num(false, 0)));
        return Some((Json::Num(false, 0), s + 1));
    }
    let mut m: u128 = (b[s] - b'0') as u128;
    let mut p = s + 1;
    assert(b@.subrange(s as int, p as int) =~= digits(m as nat));
    while p < b.len() && b'0' <= b[p] && b[p] <= b'9'
        invariant
            s < p <= b.len(), m >= 1, b@.subrange(s as int, p as int) == digits(m as nat),
            s == if neg { i + 1 } else { i as int },
        decreases b.len() - p,
    {
        let d = (b[p] - b'0') as u128;
        if m > (u128::MAX - d) / 10 { return None; }
        proof {
            lemma_digits_step(m as nat, d as nat);
            assert(b@.subrange(s as int, p + 1) =~= b@.subrange(s as int, p as int) + seq![b[p as int]]);
        }
        m = m * 10 + d;
        p += 1;
    }
    assert(b@.subrange(i as int, p as int) =~= pre + b@.subrange(s as int, p as int));
    Some((Json::Num(neg, m), p))
}

/// A value starting at `b[i]`, nested at most `d` deep.
fn parse_value(b: &[u8], i: usize, d: usize) -> (r: Option<(Json, usize)>)
    ensures r matches Some((j, k)) ==> i < k <= b.len() && b@.subrange(i as int, k as int) == print(j) && depth(j) <= d,
    decreases d, 1nat,
{
    if i >= b.len() { return None; }
    let c = b[i];
    if c == b'[' {
        parse_arr(b, i, d)
    } else if c == b'{' {
        parse_obj(b, i, d)
    } else if c == b'"' {
        match parse_str(b, i) {
            Some((s, k)) => Some((Json::Str(s), k)),
            None => None,
        }
    } else if c == b'n' {
        if b.len() - i >= 4 && b[i + 1] == b'u' && b[i + 2] == b'l' && b[i + 3] == b'l' {
            assert(b@.subrange(i as int, i + 4) =~= print(Json::Null));
            Some((Json::Null, i + 4))
        } else { None }
    } else if c == b't' {
        if b.len() - i >= 4 && b[i + 1] == b'r' && b[i + 2] == b'u' && b[i + 3] == b'e' {
            assert(b@.subrange(i as int, i + 4) =~= print(Json::Bool(true)));
            Some((Json::Bool(true), i + 4))
        } else { None }
    } else if c == b'f' {
        if b.len() - i >= 5 && b[i + 1] == b'a' && b[i + 2] == b'l' && b[i + 3] == b's' && b[i + 4] == b'e' {
            assert(b@.subrange(i as int, i + 5) =~= print(Json::Bool(false)));
            Some((Json::Bool(false), i + 5))
        } else { None }
    } else {
        parse_num(b, i)
    }
}

/// An array starting at `b[i] == '['`.
fn parse_arr(b: &[u8], i: usize, d: usize) -> (r: Option<(Json, usize)>)
    requires i < b.len(), b[i as int] == b'[',
    ensures r matches Some((j, k)) ==> i < k <= b.len() && b@.subrange(i as int, k as int) == print(j) && depth(j) <= d,
    decreases d, 0nat,
{
    if d == 0 { return None; }
    let mut v: Vec<Json> = Vec::new();
    let mut p = i + 1;
    if p < b.len() && b[p] == b']' {
        assert(b@.subrange(i as int, p + 1) =~= print(Json::Arr(v)));
        return Some((Json::Arr(v), p + 1));
    }
    loop
        invariant
            i < p <= b.len(), d >= 1,
            b@.subrange(i as int, p as int) == seq![b'['] + print_elems(v@) + sep(v@.len()),
            depth_elems(v@) < d,
        decreases b.len() - p,
    {
        match parse_value(b, p, d - 1) {
            None => { return None; },
            Some((x, k)) => {
                let ghost v0 = v@;
                v.push(x);
                proof {
                    assert(v@.subrange(0, v0.len() as int) =~= v0);
                    assert(b@.subrange(i as int, k as int) =~= b@.subrange(i as int, p as int) + b@.subrange(p as int, k as int));
                    assert(b@.subrange(i as int, k as int) =~= seq![b'['] + print_elems(v@));
                }
                if k >= b.len() { return None; }
                if b[k] == b',' {
                    assert(b@.subrange(i as int, k + 1) =~= b@.subrange(i as int, k as int) + seq![b',']);
                    p = k + 1;
                } else if b[k] == b']' {
                    assert(b@.subrange(i as int, k + 1) =~= b@.subrange(i as int, k as int) + seq![b']']);
                    return Some((Json::Arr(v), k + 1));
                } else {
                    return None;
                }
            },
        }
    }
}

/// Whether `v` already has a member named `k`.
fn has_key(v: &Vec<(Vec<u8>, Json)>, k: &Vec<u8>) -> bool {
    let mut i: usize = 0;
    while i < v.len()
        decreases v.len() - i,
    {
        if bytes_eq(v[i].0.as_slice(), k.as_slice()) { return true; }
        i += 1;
    }
    false
}

/// An object starting at `b[i] == '{'`; a repeated key is rejected.
fn parse_obj(b: &[u8], i: usize, d: usize) -> (r: Option<(Json, usize)>)
    requires i < b.len(), b[i as int] == b'{',
    ensures r matches Some((j, k)) ==> i < k <= b.len() && b@.subrange(i as int, k as int) == print(j) && depth(j) <= d,
    decreases d, 0nat,
{
    if d == 0 { return None; }
    let mut v: Vec<(Vec<u8>, Json)> = Vec::new();
    let mut p = i + 1;
    if p < b.len() && b[p] == b'}' {
        assert(b@.subrange(i as int, p + 1) =~= print(Json::Obj(v)));
        return Some((Json::Obj(v), p + 1));
    }
    loop
        invariant
            i < p <= b.len(), d >= 1,
            b@.subrange(i as int, p as int) == seq![b'{'] + print_fields(v@) + sep(v@.len()),
            depth_fields(v@) < d,
        decreases b.len() - p,
    {
        let (key, q) = match parse_str(b, p) { Some(x) => x, None => { return None; } };
        if q >= b.len() || b[q] != b':' { return None; }
        // ponytail: linear scan per key, quadratic per object; rustc_public objects are structs with few keys.
        if has_key(&v, &key) { return None; }
        let (x, k) = match parse_value(b, q + 1, d - 1) { Some(x) => x, None => { return None; } };
        let ghost v0 = v@;
        v.push((key, x));
        proof {
            assert(v@.subrange(0, v0.len() as int) =~= v0);
            assert(b@.subrange(i as int, k as int) =~= b@.subrange(i as int, p as int) + b@.subrange(p as int, q as int)
                + seq![b':'] + b@.subrange(q + 1, k as int));
            assert(b@.subrange(i as int, k as int) =~= seq![b'{'] + print_fields(v@));
        }
        if k >= b.len() { return None; }
        if b[k] == b',' {
            assert(b@.subrange(i as int, k + 1) =~= b@.subrange(i as int, k as int) + seq![b',']);
            p = k + 1;
        } else if b[k] == b'}' {
            assert(b@.subrange(i as int, k + 1) =~= b@.subrange(i as int, k as int) + seq![b'}']);
            return Some((Json::Obj(v), k + 1));
        } else {
            return None;
        }
    }
}

/// Parses `b` as one compact serde_json document. Anything serde_json's compact writer would not
/// have produced byte for byte (whitespace, floats, `-0`, leading zeros, non-canonical escapes,
/// raw control bytes), a repeated key, or nesting deeper than `MAX_DEPTH` is rejected.
pub fn parse(b: &[u8]) -> (r: Option<Json>)
    ensures r matches Some(j) ==> print(j) == b@ && depth(j) <= MAX_DEPTH,
{
    match parse_value(b, 0, MAX_DEPTH) {
        Some((j, k)) => {
            if k != b.len() { return None; }
            assert(b@.subrange(0, b.len() as int) =~= b@);
            Some(j)
        },
        None => None,
    }
}

} // verus!
