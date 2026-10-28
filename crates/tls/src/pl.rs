//! RFC 8446 §3 presentation language: big-endian integers, `<floor..ceiling>` vectors and
//! u16 lists. RFC-transcribed specs, index-based exec readers and writers, and proofs that
//! parsing and serializing are mutually inverse (canonicity and round-trip).
use vstd::prelude::*;

verus! {

// =============================================================================
// RFC 8446 §3 transcription
// =============================================================================

// RFC 8446 §3.4: "The length will be in the form of a number consuming as many bytes as
// required to hold the vector's specified maximum (ceiling) length."
/// Width in bytes of a `<floor..ceiling>` vector's length field.
pub open spec fn len_width(ceiling: nat) -> nat {
    if ceiling < 0x100 {
        1
    } else if ceiling < 0x1_0000 {
        2
    } else {
        3
    }
}

// RFC 8446 §3.3: "All values, here and elsewhere in the specification, are transmitted in
// network byte (big-endian) order".
/// Big-endian value of `b.take(w)`, for `w <= 3` (every width this crate reads).
/// Callers pass `len_width(..)` or the literal 3 (the §4 uint24 handshake length);
/// any `w > 3` silently reads as width 3.
pub open spec fn be(b: Seq<u8>, w: nat) -> nat {
    if w == 0 {
        0
    } else if w == 1 {
        b[0] as nat
    } else if w == 2 {
        b[0] as nat * 256 + b[1] as nat
    } else {
        b[0] as nat * 65536 + b[1] as nat * 256 + b[2] as nat
    }
}

/// The `w`-byte big-endian encoding of `x` (`w <= 3`); the inverse of `be` for `x < 256^w`.
/// Same width contract as `be`: any `w > 3` silently writes 3 bytes.
pub open spec fn spec_be_bytes(x: nat, w: nat) -> Seq<u8> {
    if w == 0 {
        seq![]
    } else if w == 1 {
        seq![(x % 256) as u8]
    } else if w == 2 {
        seq![((x / 256) % 256) as u8, (x % 256) as u8]
    } else {
        seq![((x / 65536) % 256) as u8, ((x / 256) % 256) as u8, (x % 256) as u8]
    }
}

// RFC 8446 §3.4: "Variable-length vectors are defined by specifying a subrange of legal
// lengths, inclusively, using the notation <floor..ceiling>.  When these are encoded, the
// actual length precedes the vector's contents in the byte stream.  The length will be in
// the form of a number consuming as many bytes as required to hold the vector's specified
// maximum (ceiling) length."
/// A `<floor..ceiling>` vector at the front of `b`: `(content, rest)`.
pub open spec fn rfc_vec(b: Seq<u8>, floor: nat, ceiling: nat) -> Option<(Seq<u8>, Seq<u8>)> {
    let w = len_width(ceiling);
    if b.len() < w {
        None
    } else {
        let n = be(b, w);
        if floor <= n && n <= ceiling && w + n <= b.len() {
            Some((b.subrange(w as int, (w + n) as int), b.skip((w + n) as int)))
        } else {
            None
        }
    }
}

/// A vector that is all of `b`.
pub open spec fn rfc_vec_exact(b: Seq<u8>, floor: nat, ceiling: nat) -> Option<Seq<u8>> {
    match rfc_vec(b, floor, ceiling) {
        Some((c, r)) => if r.len() == 0 {
            Some(c)
        } else {
            None
        },
        None => None,
    }
}

// RFC 8446 §3.4: "The length of an encoded vector must be an exact multiple of the length of
// a single element (e.g., a 17-byte vector of uint16 would be illegal)."
/// The contents of a `uint16` vector, as big-endian pairs.
pub open spec fn rfc_u16_list(b: Seq<u8>) -> Option<Seq<u16>> {
    if b.len() % 2 != 0 {
        None
    } else {
        Some(Seq::new(b.len() / 2, |i: int| be(b.skip(2 * i), 2) as u16))
    }
}

// =============================================================================
// Serialization specs
// =============================================================================

pub open spec fn spec_vec_bytes(ceiling: nat, c: Seq<u8>) -> Seq<u8> {
    spec_be_bytes(c.len(), len_width(ceiling)) + c
}

pub open spec fn spec_u16_list_bytes(s: Seq<u16>) -> Seq<u8> {
    Seq::new(2 * s.len(), |i: int| spec_be_bytes(s[i / 2] as nat, 2)[i % 2])
}

// =============================================================================
// Proofs
// =============================================================================

/// `be` reads back what `spec_be_bytes` wrote, whatever follows.
pub proof fn lemma_be_roundtrip(x: nat, w: nat, r: Seq<u8>)
    requires
        1 <= w <= 3,
        w == 1 ==> x < 0x100,
        w == 2 ==> x < 0x1_0000,
        w == 3 ==> x < 0x100_0000,
    ensures
        be(spec_be_bytes(x, w) + r, w) == x,
        spec_be_bytes(x, w).len() == w,
{
    let b = spec_be_bytes(x, w) + r;
    if w == 2 {
        assert(b[0] as nat == x / 256 && b[1] as nat == x % 256);
    } else if w == 3 {
        assert(b[0] as nat == x / 65536 && b[1] as nat == (x / 256) % 256);
        assert(b[2] as nat == x % 256);
        assert(x == (x / 65536) * 65536 + ((x / 256) % 256) * 256 + x % 256) by (nonlinear_arith);
    }
}

/// `spec_be_bytes` rewrites what `be` read.
pub proof fn lemma_be_canonical(b: Seq<u8>, w: nat)
    requires
        1 <= w <= 3,
        b.len() >= w,
    ensures
        spec_be_bytes(be(b, w), w) == b.take(w as int),
{
    let x = be(b, w);
    if w == 3 {
        let (b0, b1, b2) = (b[0] as nat, b[1] as nat, b[2] as nat);
        assert(x / 65536 == b0 && (x / 256) % 256 == b1 && x % 256 == b2) by (nonlinear_arith)
            requires
                x == b0 * 65536 + b1 * 256 + b2,
                b0 < 256,
                b1 < 256,
                b2 < 256,
        ;
    }
    assert(spec_be_bytes(x, w) =~= b.take(w as int));
}

pub proof fn lemma_vec_canonical(b: Seq<u8>, floor: nat, ceiling: nat, x: Seq<u8>, r: Seq<u8>)
    requires
        rfc_vec(b, floor, ceiling) == Some((x, r)),
    ensures
        b == spec_vec_bytes(ceiling, x) + r,
{
    let w = len_width(ceiling);
    lemma_be_canonical(b, w);
    assert(b =~= b.take(w as int) + x + r);
}

pub proof fn lemma_vec_roundtrip(x: Seq<u8>, r: Seq<u8>, floor: nat, ceiling: nat)
    requires
        floor <= x.len() <= ceiling < 0x100_0000,
    ensures
        rfc_vec(spec_vec_bytes(ceiling, x) + r, floor, ceiling) == Some((x, r)),
{
    let w = len_width(ceiling);
    let b = spec_vec_bytes(ceiling, x) + r;
    lemma_be_roundtrip(x.len(), w, x + r);
    assert(b =~= spec_be_bytes(x.len(), w) + (x + r));
    assert(b.subrange(w as int, (w + x.len()) as int) =~= x);
    assert(b.skip((w + x.len()) as int) =~= r);
}

pub proof fn lemma_u16_list_canonical(b: Seq<u8>, s: Seq<u16>)
    requires
        rfc_u16_list(b) == Some(s),
    ensures
        spec_u16_list_bytes(s) == b,
{
    assert forall|i: int| 0 <= i < b.len() implies #[trigger] spec_u16_list_bytes(s)[i] == b[i] by {
        let k = i / 2;
        lemma_be_canonical(b.skip(2 * k), 2);
        assert(b.skip(2 * k).take(2)[i % 2] == b[i]);
    }
    assert(spec_u16_list_bytes(s) =~= b);
}

pub proof fn lemma_u16_list_roundtrip(s: Seq<u16>)
    ensures
        rfc_u16_list(spec_u16_list_bytes(s)) == Some(s),
{
    let b = spec_u16_list_bytes(s);
    assert forall|k: int| 0 <= k < s.len() implies be(b.skip(2 * k), 2) as u16 == s[k] by {
        lemma_be_roundtrip(s[k] as nat, 2, seq![]);
        assert(b.skip(2 * k)[0] == b[2 * k] && b.skip(2 * k)[1] == b[2 * k + 1]);
        assert(b[2 * k] == spec_be_bytes(s[k] as nat, 2)[0]);
        assert(b[2 * k + 1] == spec_be_bytes(s[k] as nat, 2)[1]);
    }
    assert(rfc_u16_list(b).unwrap() =~= s);
}

// =============================================================================
// Exec
// =============================================================================

/// The `(start, end)` indices of the content of the `<floor..ceiling>` vector at `b[pos..]`.
pub fn read_vec(b: &[u8], pos: usize, floor: usize, ceiling: usize) -> (r: Option<(usize, usize)>)
    requires
        pos <= b@.len(),
        ceiling < 0x100_0000,
    ensures
        r is None <==> rfc_vec(b@.skip(pos as int), floor as nat, ceiling as nat) is None,
        r matches Some((s, e)) ==> rfc_vec(b@.skip(pos as int), floor as nat, ceiling as nat)
            == Some((b@.subrange(s as int, e as int), b@.skip(e as int))),
        r matches Some((s, e)) ==> pos <= s <= e <= b@.len(),
{
    let ghost t = b@.skip(pos as int);
    let avail = b.len() - pos;
    let w: usize = if ceiling < 0x100 {
        1
    } else if ceiling < 0x1_0000 {
        2
    } else {
        3
    };
    if avail < w {
        return None;
    }
    let n: usize = if w == 1 {
        b[pos] as usize
    } else if w == 2 {
        b[pos] as usize * 256 + b[pos + 1] as usize
    } else {
        b[pos] as usize * 65536 + b[pos + 1] as usize * 256 + b[pos + 2] as usize
    };
    assert(n == be(t, w as nat));
    if n < floor || n > ceiling || n > avail - w {
        return None;
    }
    assert(t.subrange(w as int, (w + n) as int) =~= b@.subrange(
        (pos + w) as int,
        (pos + w + n) as int,
    ));
    assert(t.skip((w + n) as int) =~= b@.skip((pos + w + n) as int));
    Some((pos + w, pos + w + n))
}

/// The big-endian `uint16` at `b[pos..]`.
pub fn read_u16(b: &[u8], pos: usize) -> (r: Option<u16>)
    ensures
        match r {
            None => pos + 2 > b@.len(),
            Some(x) => pos + 2 <= b@.len() && x as nat == be(b@.skip(pos as int), 2),
        },
{
    if pos > b.len() || b.len() - pos < 2 {
        return None;
    }
    Some(b[pos] as u16 * 256 + b[pos + 1] as u16)
}

pub fn parse_u16_list(b: &[u8]) -> (r: Option<Vec<u16>>)
    ensures
        r.deep_view() == rfc_u16_list(b@),
{
    if b.len() % 2 != 0 {
        return None;
    }
    let n = b.len() / 2;
    let mut v: Vec<u16> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            n == b@.len() / 2,
            b@.len() % 2 == 0,
            i <= n,
            v@.len() == i,
            forall|j: int| 0 <= j < i ==> v@[j] == be(b@.skip(2 * j), 2) as u16,
        decreases n - i,
    {
        let x = b[2 * i] as u16 * 256 + b[2 * i + 1] as u16;
        v.push(x);
        i += 1;
    }
    assert(v@ =~= rfc_u16_list(b@).unwrap());
    Some(v)
}

pub fn put_u16(out: &mut Vec<u8>, x: u16)
    ensures
        final(out)@ == old(out)@ + spec_be_bytes(x as nat, 2),
{
    out.push((x / 256) as u8);
    out.push((x % 256) as u8);
    assert(final(out)@ =~= old(out)@ + spec_be_bytes(x as nat, 2));
}

/// `c` as a `<_..ceiling>` vector.
pub fn put_vec(out: &mut Vec<u8>, ceiling: usize, c: &[u8])
    requires
        c@.len() <= ceiling < 0x100_0000,
    ensures
        final(out)@ == old(out)@ + spec_vec_bytes(ceiling as nat, c@),
{
    let n = c.len();
    if ceiling >= 0x1_0000 {
        out.push((n / 65536) as u8);
    }
    if ceiling >= 0x100 {
        out.push(((n / 256) % 256) as u8);
    }
    out.push((n % 256) as u8);
    let ghost mid = out@;
    assert(mid =~= old(out)@ + spec_be_bytes(n as nat, len_width(ceiling as nat)));
    let mut i: usize = 0;
    while i < n
        invariant
            n == c@.len(),
            i <= n,
            out@ == mid + c@.take(i as int),
        decreases n - i,
    {
        out.push(c[i]);
        assert(c@.take(i as int + 1) =~= c@.take(i as int).push(c@[i as int]));
        assert((mid + c@.take(i as int)).push(c@[i as int]) =~= mid + c@.take(i as int + 1));
        i += 1;
    }
    assert(c@.take(n as int) =~= c@);
}

} // verus!
