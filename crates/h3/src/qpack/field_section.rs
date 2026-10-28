//! QPACK encoded field sections (RFC 9204 §4.5) at dynamic table capacity 0: an RFC-transcribed
//! decode spec, a request decoder proved equal to it, and a response encoder proved to round-trip
//! through it.
use super::huffman::*;
use super::int::*;
use super::static_table::*;
use crate::codes::QPACK_DECOMPRESSION_FAILED;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd::slice::{slice_subrange, slice_to_vec};

verus! {

pub struct FieldLine {
    pub name: Vec<u8>,
    pub value: Vec<u8>,
}

impl View for FieldLine {
    type V = (Seq<u8>, Seq<u8>);

    open spec fn view(&self) -> (Seq<u8>, Seq<u8>) {
        (self.name@, self.value@)
    }
}

pub open spec fn fields_view(v: Seq<FieldLine>) -> Seq<(Seq<u8>, Seq<u8>)> {
    v.map_values(|f: FieldLine| f@)
}

// =============================================================================
// RFC 9204 §4.5 transcription (dynamic table capacity 0)
// =============================================================================

//= https://www.rfc-editor.org/rfc/rfc9204#section-4.1.2
//# The string uses one bit for the Huffman flag,
//# followed by the length of the encoded string as a (N-1)-bit prefix
//# integer.
/// An `(n + 1)`-bit prefix string literal at the front of `b` (its H flag is bit `n` of `b[0]`):
/// `(string, bytes consumed)`. A length running past `b` is truncation.
pub open spec fn rfc_string(n: u8, b: Seq<u8>) -> Option<(Seq<u8>, nat)> {
    match rfc_prefix_int(n, b) {
        PrefixIntSpec::Value { value: len, consumed: c } => {
            if c + len > b.len() {
                None
            } else {
                let raw = b.subrange(c as int, (c + len) as int);
                if (b[0] >> n) & 1u8 == 0 {
                    Some((raw, c + len))
                } else if exists|s: Seq<u8>| rfc_huffman_decodes(raw, s) {
                    // Unique by `lemma_huffman_unique`.
                    Some((choose|s: Seq<u8>| rfc_huffman_decodes(raw, s), c + len))
                } else {
                    None
                }
            }
        },
        _ => None,
    }
}

//= https://www.rfc-editor.org/rfc/rfc9204#section-4.5.2
//# This representation starts with the '1' 1-bit pattern, followed by
//# the 'T' bit, indicating whether the reference is into the static or
//# dynamic table.
//= https://www.rfc-editor.org/rfc/rfc9204#section-4.5.4
//# This representation starts with the '01' 2-bit pattern.
//= https://www.rfc-editor.org/rfc/rfc9204#section-4.5.4
//# The fourth ('T') bit indicates whether the reference is to the static
//# or dynamic table.
//= https://www.rfc-editor.org/rfc/rfc9204#section-4.5.6
//# This representation starts with the '001' 3-bit pattern.  The fourth
//# bit is the 'N' bit as described in Section 4.5.4.  The name follows,
//# represented as a 4-bit prefix string literal, then the value,
//# represented as an 8-bit prefix string literal; see Section 4.1.2.
//= https://www.rfc-editor.org/rfc/rfc9204#section-2.2.3
//# If the decoder encounters a reference in a field line representation
//# to a dynamic table entry that has already been evicted or that has an
//# absolute index greater than or equal to the declared Required Insert
//# Count (Section 4.5.1), it MUST treat this as a connection error of
//# type QPACK_DECOMPRESSION_FAILED.
//= https://www.rfc-editor.org/rfc/rfc9204#section-2.2.1
//# If it encounters a Required
//# Insert Count smaller than expected, it MUST treat this as a connection error
//# of type QPACK_DECOMPRESSION_FAILED; see Section 2.2.3.
//= https://www.rfc-editor.org/rfc/rfc9204#section-3.1
//# When the decoder encounters an invalid static table index in a field
//# line representation, it MUST treat this as a connection error of type
//# QPACK_DECOMPRESSION_FAILED.
/// One field line representation at the front of non-empty `b`: `(field line, bytes consumed)`.
/// With Required Insert Count 0 every dynamic reference (T=0, or either post-Base form) is
/// beyond it, hence invalid (and the declared count is smaller than the section needs); the N
/// bit is ignored.
pub open spec fn rfc_field_line(b: Seq<u8>) -> Option<((Seq<u8>, Seq<u8>), nat)> {
    let b0 = b[0];
    if b0 & 0x80u8 != 0 {
        // Indexed Field Line: 1 T Index(6+).
        if b0 & 0x40u8 == 0 {
            None
        } else {
            match rfc_prefix_int(6, b) {
                PrefixIntSpec::Value { value: i, consumed: c } => match spec_static_entry(i) {
                    Some(e) => Some((e, c)),
                    None => None,
                },
                _ => None,
            }
        }
    } else if b0 & 0x40u8 != 0 {
        // Literal Field Line with Name Reference: 0 1 N T NameIndex(4+), then the value.
        if b0 & 0x10u8 == 0 {
            None
        } else {
            match rfc_prefix_int(4, b) {
                PrefixIntSpec::Value { value: i, consumed: c } => match spec_static_entry(i) {
                    Some((name, _)) => match rfc_string(7, b.skip(c as int)) {
                        Some((value, c2)) => Some(((name, value), c + c2)),
                        None => None,
                    },
                    None => None,
                },
                _ => None,
            }
        }
    } else if b0 & 0x20u8 != 0 {
        // Literal Field Line with Literal Name: 0 0 1 N H NameLen(3+), name, then the value.
        match rfc_string(3, b) {
            Some((name, c)) => match rfc_string(7, b.skip(c as int)) {
                Some((value, c2)) => Some(((name, value), c + c2)),
                None => None,
            },
            None => None,
        }
    } else {
        // 0001: Indexed Field Line with Post-Base Index; 0000: Literal Field Line with Post-Base
        // Name Reference. Both are dynamic references.
        None
    }
}

//= https://www.rfc-editor.org/rfc/rfc9204#section-4.5
//# An encoded field section consists of a prefix and a possibly empty
//# sequence of representations defined in this section.
//= https://www.rfc-editor.org/rfc/rfc9204#section-2.2
//# The decoder MUST emit field lines in the order their representations
//# appear in the encoded field section.
pub open spec fn rfc_field_lines(b: Seq<u8>) -> Option<Seq<(Seq<u8>, Seq<u8>)>>
    decreases b.len(),
    via field_lines_decreases
{
    if b.len() == 0 {
        Some(seq![])
    } else {
        match rfc_field_line(b) {
            Some((f, c)) => match rfc_field_lines(b.skip(c as int)) {
                Some(rest) => Some(seq![f] + rest),
                None => None,
            },
            None => None,
        }
    }
}

#[verifier::decreases_by]
proof fn field_lines_decreases(b: Seq<u8>) {
    if b.len() > 0 {
        lemma_field_line_consumed(b);
    }
}

//= https://www.rfc-editor.org/rfc/rfc9204#section-4.5.1
//# Each encoded field section is prefixed with two integers.  The
//# Required Insert Count is encoded as an integer with an 8-bit prefix
//# using the encoding described in Section 4.5.1.1.  The Base is encoded
//# as a Sign bit ('S') and a Delta Base value with a 7-bit prefix; see
//# Section 4.5.1.2.
//= https://www.rfc-editor.org/rfc/rfc9204#section-4.5.1.1
//# If the decoder encounters a value
//# of EncodedInsertCount that could not have been produced by a
//# conformant encoder, it MUST treat this as a connection error of type
//# QPACK_DECOMPRESSION_FAILED.
//= https://www.rfc-editor.org/rfc/rfc9204#section-2.1.2
//# If a decoder encounters more blocked streams than it promised to
//# support, it MUST treat this as a connection error of type
//# QPACK_DECOMPRESSION_FAILED.
//= https://www.rfc-editor.org/rfc/rfc9204#section-4.5.1.2
//# An endpoint MUST treat a field block
//# with a Sign bit of 1 as invalid if the value of Required Insert Count
//# is less than or equal to the value of Delta Base.
/// Decoding of a whole field section (the full HEADERS payload). With MaxEntries 0 the only
/// producible EncodedInsertCount is 0 (any other exceeds FullRange = 0, and with 0 blocked
/// streams allowed a non-zero one could only block), so Required Insert Count is 0 and Sign=1
/// always makes Base negative. Truncation, excess bytes and oversized integers all fail.
pub open spec fn rfc_decode_field_section(b: Seq<u8>) -> Result<Seq<(Seq<u8>, Seq<u8>)>, u64> {
    match rfc_prefix_int(8, b) {
        PrefixIntSpec::Value { value: ric, consumed: c } => {
            let rest = b.skip(c as int);
            if ric != 0 {
                Err(QPACK_DECOMPRESSION_FAILED)
            } else {
                match rfc_prefix_int(7, rest) {
                    PrefixIntSpec::Value { consumed: c2, .. } => {
                        if rest[0] & 0x80u8 != 0 {
                            Err(QPACK_DECOMPRESSION_FAILED)
                        } else {
                            match rfc_field_lines(rest.skip(c2 as int)) {
                                Some(f) => Ok(f),
                                None => Err(QPACK_DECOMPRESSION_FAILED),
                            }
                        }
                    },
                    _ => Err(QPACK_DECOMPRESSION_FAILED),
                }
            }
        },
        _ => Err(QPACK_DECOMPRESSION_FAILED),
    }
}

// =============================================================================
// Lemmas
// =============================================================================

proof fn lemma_string_consumed(n: u8, b: Seq<u8>)
    ensures
        rfc_string(n, b) matches Some((_, c)) ==> 1 <= c <= b.len(),
{
    lemma_prefix_int_consumed(n, b);
}

proof fn lemma_field_line_consumed(b: Seq<u8>)
    requires
        b.len() > 0,
    ensures
        rfc_field_line(b) matches Some((_, c)) ==> 1 <= c <= b.len(),
{
    lemma_prefix_int_consumed(6, b);
    lemma_prefix_int_consumed(4, b);
    lemma_string_consumed(3, b);
    if let PrefixIntSpec::Value { consumed: c, .. } = rfc_prefix_int(4, b) {
        lemma_string_consumed(7, b.skip(c as int));
    }
    if let Some((_, c)) = rfc_string(3, b) {
        lemma_string_consumed(7, b.skip(c as int));
    }
}

proof fn lemma_string_append(n: u8, b: Seq<u8>, t: Seq<u8>)
    requires
        rfc_string(n, b) is Some,
    ensures
        rfc_string(n, b + t) == rfc_string(n, b),
{
    lemma_prefix_int_append(n, b, t);
    if let PrefixIntSpec::Value { value: len, consumed: c } = rfc_prefix_int(n, b) {
        assert((b + t)[0] == b[0]);
        assert((b + t).subrange(c as int, (c + len) as int) =~= b.subrange(
            c as int,
            (c + len) as int,
        ));
    }
}

proof fn lemma_field_line_append(b: Seq<u8>, t: Seq<u8>)
    requires
        b.len() > 0,
        rfc_field_line(b) is Some,
    ensures
        rfc_field_line(b + t) == rfc_field_line(b),
{
    let b0 = b[0];
    assert((b + t)[0] == b0);
    if b0 & 0x80u8 != 0 {
        lemma_prefix_int_append(6, b, t);
    } else if b0 & 0x40u8 != 0 {
        lemma_prefix_int_append(4, b, t);
        lemma_prefix_int_consumed(4, b);
        if let PrefixIntSpec::Value { consumed: c, .. } = rfc_prefix_int(4, b) {
            assert((b + t).skip(c as int) =~= b.skip(c as int) + t);
            lemma_string_append(7, b.skip(c as int), t);
        }
    } else {
        lemma_string_append(3, b, t);
        lemma_string_consumed(3, b);
        if let Some((_, c)) = rfc_string(3, b) {
            assert((b + t).skip(c as int) =~= b.skip(c as int) + t);
            lemma_string_append(7, b.skip(c as int), t);
        }
    }
}

/// Field-line sequences concatenate: decoding is self-delimiting.
proof fn lemma_field_lines_append(a: Seq<u8>, c: Seq<u8>)
    requires
        rfc_field_lines(a) is Some,
        rfc_field_lines(c) is Some,
    ensures
        rfc_field_lines(a + c) == Some(rfc_field_lines(a).unwrap() + rfc_field_lines(c).unwrap()),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + c =~= c);
        assert(rfc_field_lines(a).unwrap() + rfc_field_lines(c).unwrap() =~= rfc_field_lines(
            c,
        ).unwrap());
    } else {
        lemma_field_line_consumed(a);
        lemma_field_line_append(a, c);
        let (f, k) = rfc_field_line(a).unwrap();
        assert((a + c).skip(k as int) =~= a.skip(k as int) + c);
        lemma_field_lines_append(a.skip(k as int), c);
        let ra = rfc_field_lines(a.skip(k as int)).unwrap();
        let rc = rfc_field_lines(c).unwrap();
        assert(seq![f] + (ra + rc) =~= (seq![f] + ra) + rc);
    }
}

/// The first byte of a serialized prefix integer keeps the caller's flag bits.
proof fn lemma_first_byte(n: u8, flags: u8, v: u64)
    requires
        1 <= n <= 8,
        flags & (0xffu8 >> (8 - n) as u8) == 0,
    ensures
        spec_prefix_int_bytes(n, flags, v)[0] >> n == flags >> n,
{
    let m = 0xffu8 >> (8 - n) as u8;
    let y: u8 = if v < m { v as u8 } else { m };
    assert(y <= m);
    assert(spec_prefix_int_bytes(n, flags, v)[0] == flags | y);
    assert((flags | y) >> n == flags >> n) by (bit_vector)
        requires
            1 <= n <= 8,
            m == 0xffu8 >> (8 - n) as u8,
            y <= m,
    ;
}

/// A serialized H=0 string literal decodes back to its bytes.
proof fn lemma_string_roundtrip(n: u8, flags: u8, s: Seq<u8>)
    requires
        1 <= n <= 7,
        flags as nat % pow2(n as nat) == 0,
        flags & (0xffu8 >> (8 - n) as u8) == 0,
        (flags >> n) & 1u8 == 0,
        s.len() <= PREFIX_INT_MAX,
    ensures
        ({
            let e = spec_prefix_int_bytes(n, flags, s.len() as u64) + s;
            rfc_string(n, e) == Some((s, e.len()))
        }),
{
    let p = spec_prefix_int_bytes(n, flags, s.len() as u64);
    let e = p + s;
    theorem_prefix_int_roundtrip(n, flags, s.len() as u64);
    lemma_prefix_int_append(n, p, s);
    lemma_first_byte(n, flags, s.len() as u64);
    assert(e[0] == p[0]);
    assert(e.subrange(p.len() as int, e.len() as int) =~= s);
}

proof fn lemma_one_line(e: Seq<u8>, f: (Seq<u8>, Seq<u8>))
    requires
        e.len() > 0,
        rfc_field_line(e) == Some((f, e.len())),
    ensures
        rfc_field_lines(e) == Some(seq![f]),
{
    assert(e.skip(e.len() as int) =~= Seq::<u8>::empty());
    assert(rfc_field_lines(e.skip(e.len() as int)) == Some(Seq::<(Seq<u8>, Seq<u8>)>::empty()));
    assert(seq![f] + Seq::<(Seq<u8>, Seq<u8>)>::empty() =~= seq![f]);
}

// =============================================================================
// Decoder
// =============================================================================

//= https://www.rfc-editor.org/rfc/rfc9204#section-7.4
//# If an implementation encounters a value larger than it is able to
//# decode, this MUST be treated as a stream error of type
//# QPACK_DECOMPRESSION_FAILED if on a request stream
fn decode_string(n: u8, b: &[u8]) -> (r: Option<(Vec<u8>, usize)>)
    requires
        1 <= n <= 7,
    ensures
        match r {
            Some((s, c)) => c <= b@.len() && rfc_string(n, b@) == Some((s@, c as nat)),
            None => rfc_string(n, b@) is None,
        },
{
    match parse_prefix_int(n, b) {
        PrefixInt::Value { value: len, consumed: c } => {
            proof {
                lemma_prefix_int_consumed(n, b@);
            }
            // The length is checked against the bytes present before anything is allocated.
            if len > (b.len() - c) as u64 {
                return None;
            }
            let end = c + len as usize;
            let raw = slice_subrange(b, c, end);
            if (b[0] >> n) & 1 == 0 {
                Some((slice_to_vec(raw), end))
            } else {
                match huffman_decode(raw) {
                    Some(s) => {
                        proof {
                            let ch = choose|x: Seq<u8>| rfc_huffman_decodes(raw@, x);
                            lemma_huffman_unique(raw@, s@, ch);
                        }
                        Some((s, end))
                    },
                    None => None,
                }
            }
        },
        _ => None,
    }
}

fn decode_field_line(b: &[u8]) -> (r: Option<(FieldLine, usize)>)
    requires
        b@.len() > 0,
    ensures
        match r {
            Some((f, c)) => rfc_field_line(b@) == Some((f@, c as nat)),
            None => rfc_field_line(b@) is None,
        },
{
    let b0 = b[0];
    if b0 & 0x80 != 0 {
        if b0 & 0x40 == 0 {
            return None;
        }
        match parse_prefix_int(6, b) {
            PrefixInt::Value { value, consumed } => match static_entry(value) {
                Some((n, v)) => Some(
                    (FieldLine { name: slice_to_vec(n), value: slice_to_vec(v) }, consumed),
                ),
                None => None,
            },
            _ => None,
        }
    } else if b0 & 0x40 != 0 {
        if b0 & 0x10 == 0 {
            return None;
        }
        match parse_prefix_int(4, b) {
            PrefixInt::Value { value, consumed } => match static_entry(value) {
                Some((n, _)) => {
                    proof {
                        lemma_prefix_int_consumed(4, b@);
                    }
                    match decode_string(7, slice_subrange(b, consumed, b.len())) {
                        Some((v, c2)) => Some(
                            (FieldLine { name: slice_to_vec(n), value: v }, consumed + c2),
                        ),
                        None => None,
                    }
                },
                None => None,
            },
            _ => None,
        }
    } else if b0 & 0x20 != 0 {
        match decode_string(3, b) {
            Some((name, c)) => match decode_string(7, slice_subrange(b, c, b.len())) {
                Some((value, c2)) => Some((FieldLine { name, value }, c + c2)),
                None => None,
            },
            None => None,
        }
    } else {
        None
    }
}

/// Decodes a request's encoded field section (the whole HEADERS frame payload).
pub fn decode_field_section(b: &[u8]) -> (r: Result<Vec<FieldLine>, u64>)
    ensures
        match r {
            Ok(v) => rfc_decode_field_section(b@) == Ok::<_, u64>(fields_view(v@)),
            Err(e) => rfc_decode_field_section(b@) == Err::<Seq<(Seq<u8>, Seq<u8>)>, u64>(e),
        },
{
    let c = match parse_prefix_int(8, b) {
        PrefixInt::Value { value, consumed } => {
            if value != 0 {
                return Err(QPACK_DECOMPRESSION_FAILED);
            }
            consumed
        },
        _ => return Err(QPACK_DECOMPRESSION_FAILED),
    };
    proof {
        lemma_prefix_int_consumed(8, b@);
    }
    let rest = slice_subrange(b, c, b.len());
    let c2 = match parse_prefix_int(7, rest) {
        PrefixInt::Value { consumed, .. } => consumed,
        _ => return Err(QPACK_DECOMPRESSION_FAILED),
    };
    if rest[0] & 0x80 != 0 {
        return Err(QPACK_DECOMPRESSION_FAILED);
    }
    proof {
        lemma_prefix_int_consumed(7, rest@);
        assert(rest@ =~= b@.skip(c as int));
    }
    let lines = slice_subrange(rest, c2, rest.len());
    proof {
        assert(lines@ =~= rest@.skip(c2 as int));
    }
    match decode_lines(lines) {
        Some(v) => Ok(v),
        None => Err(QPACK_DECOMPRESSION_FAILED),
    }
}

/// Decodes field line representations up to the end of `lines`.
fn decode_lines(lines: &[u8]) -> (r: Option<Vec<FieldLine>>)
    ensures
        match r {
            Some(v) => rfc_field_lines(lines@) == Some(fields_view(v@)),
            None => rfc_field_lines(lines@) is None,
        },
{
    proof {
        assert(lines@.skip(0) =~= lines@);
        assert(fields_view(Seq::<FieldLine>::empty()) =~= Seq::empty());
        if let Some(r) = rfc_field_lines(lines@) {
            assert(Seq::<(Seq<u8>, Seq<u8>)>::empty() + r =~= r);
        }
    }
    let mut out: Vec<FieldLine> = Vec::new();
    let mut pos: usize = 0;
    while pos < lines.len()
        invariant
            pos <= lines@.len(),
            rfc_field_lines(lines@) == match rfc_field_lines(lines@.skip(pos as int)) {
                Some(r) => Some(fields_view(out@) + r),
                None => None,
            },
        decreases lines@.len() - pos,
    {
        let tail = slice_subrange(lines, pos, lines.len());
        proof {
            assert(tail@ =~= lines@.skip(pos as int));
        }
        match decode_field_line(tail) {
            Some((f, k)) => {
                proof {
                    lemma_field_line_consumed(tail@);
                    assert(tail@.skip(k as int) =~= lines@.skip(pos + k));
                    assert(fields_view(out@.push(f)) =~= fields_view(out@).push(f@));
                    if let Some(r) = rfc_field_lines(lines@.skip(pos + k)) {
                        assert(fields_view(out@) + (seq![f@] + r) =~= fields_view(out@).push(f@)
                            + r);
                    }
                }
                out.push(f);
                pos += k;
            },
            None => {
                proof {
                    assert(rfc_field_lines(lines@.skip(pos as int)) is None);
                    assert(rfc_field_lines(lines@) is None);
                }
                return None;
            },
        }
    }
    proof {
        assert(lines@.skip(pos as int) =~= Seq::<u8>::empty());
        assert(fields_view(out@) + Seq::empty() =~= fields_view(out@));
    }
    Some(out)
}

// =============================================================================
// Encoder
// =============================================================================

/// Appends an H=0 string literal (length under `flags` in an `n`-bit prefix, then the bytes).
fn encode_string(n: u8, flags: u8, s: &[u8], out: &mut Vec<u8>)
    requires
        1 <= n <= 8,
        flags as nat % pow2(n as nat) == 0,
        s@.len() <= PREFIX_INT_MAX,
    ensures
        final(out)@ == old(out)@ + spec_prefix_int_bytes(n, flags, s@.len() as u64) + s@,
{
    serialize_prefix_int(n, flags, s.len() as u64, out);
    let mut tmp = slice_to_vec(s);
    out.append(&mut tmp);
}

/// Bytes emitted for an exact static match decode to that entry.
proof fn lemma_exact_line(i: u64, f: (Seq<u8>, Seq<u8>))
    requires
        i < STATIC_TABLE_LEN,
        spec_static_entry(i as nat) == Some(f),
    ensures
        ({
            let e = spec_prefix_int_bytes(6, 0xc0, i);
            e.len() > 0 && rfc_field_line(e) == Some((f, e.len()))
        }),
{
    let e = spec_prefix_int_bytes(6, 0xc0, i);
    lemma2_to64();
    theorem_prefix_int_roundtrip(6, 0xc0, i);
    assert(0xc0u8 & (0xffu8 >> 2u8) == 0) by (bit_vector);
    lemma_first_byte(6, 0xc0, i);
    let x = e[0];
    assert(x & 0x80u8 != 0 && x & 0x40u8 != 0) by (bit_vector)
        requires
            x >> 6u8 == 0xc0u8 >> 6u8,
    ;
}

/// Bytes emitted for a static name match decode to that name and the literal value.
proof fn lemma_name_line(i: u64, name: Seq<u8>, value: Seq<u8>)
    requires
        i < STATIC_TABLE_LEN,
        spec_name_is(i as nat, name),
        value.len() <= PREFIX_INT_MAX,
    ensures
        ({
            let e = spec_prefix_int_bytes(4, 0x50, i) + (spec_prefix_int_bytes(
                7,
                0x00,
                value.len() as u64,
            ) + value);
            e.len() > 0 && rfc_field_line(e) == Some(((name, value), e.len()))
        }),
{
    let p = spec_prefix_int_bytes(4, 0x50, i);
    let s = spec_prefix_int_bytes(7, 0x00, value.len() as u64) + value;
    let e = p + s;
    lemma2_to64();
    theorem_prefix_int_roundtrip(4, 0x50, i);
    lemma_prefix_int_append(4, p, s);
    assert(0x50u8 & (0xffu8 >> 4u8) == 0) by (bit_vector);
    lemma_first_byte(4, 0x50, i);
    let x = e[0];
    assert(x == p[0]);
    assert(x & 0x80u8 == 0 && x & 0x40u8 != 0 && x & 0x10u8 != 0) by (bit_vector)
        requires
            x >> 4u8 == 0x50u8 >> 4u8,
    ;
    assert(e.skip(p.len() as int) =~= s);
    assert(0x00u8 & (0xffu8 >> 1u8) == 0 && (0x00u8 >> 7u8) & 1u8 == 0) by (bit_vector);
    lemma_string_roundtrip(7, 0x00, value);
}

/// Bytes emitted with a literal name decode to that name and value.
proof fn lemma_literal_line(name: Seq<u8>, value: Seq<u8>)
    requires
        name.len() <= PREFIX_INT_MAX,
        value.len() <= PREFIX_INT_MAX,
    ensures
        ({
            let e = (spec_prefix_int_bytes(3, 0x20, name.len() as u64) + name) + (
            spec_prefix_int_bytes(7, 0x00, value.len() as u64) + value);
            e.len() > 0 && rfc_field_line(e) == Some(((name, value), e.len()))
        }),
{
    let p = spec_prefix_int_bytes(3, 0x20, name.len() as u64);
    let a = p + name;
    let s = spec_prefix_int_bytes(7, 0x00, value.len() as u64) + value;
    let e = a + s;
    lemma2_to64();
    assert(0x20u8 & (0xffu8 >> 5u8) == 0 && (0x20u8 >> 3u8) & 1u8 == 0) by (bit_vector);
    assert(0x00u8 & (0xffu8 >> 1u8) == 0 && (0x00u8 >> 7u8) & 1u8 == 0) by (bit_vector);
    lemma_string_roundtrip(3, 0x20, name);
    lemma_string_append(3, a, s);
    lemma_first_byte(3, 0x20, name.len() as u64);
    let x = e[0];
    assert(x == p[0]);
    assert(x & 0x80u8 == 0 && x & 0x40u8 == 0 && x & 0x20u8 != 0) by (bit_vector)
        requires
            x >> 3u8 == 0x20u8 >> 3u8,
    ;
    assert(e.skip(a.len() as int) =~= s);
    lemma_string_roundtrip(7, 0x00, value);
}

fn encode_field_line(f: &FieldLine, out: &mut Vec<u8>)
    requires
        f.name@.len() <= PREFIX_INT_MAX,
        f.value@.len() <= PREFIX_INT_MAX,
    ensures
        final(out)@.len() > old(out)@.len(),
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        rfc_field_line(final(out)@.skip(old(out)@.len() as int)) == Some(
            (f@, (final(out)@.len() - old(out)@.len()) as nat),
        ),
{
    let ghost o = out@;
    proof {
        lemma2_to64();
    }
    match find_static(f.name.as_slice(), f.value.as_slice()) {
        StaticMatch::Exact(i) => {
            serialize_prefix_int(6, 0xc0, i, out);
            proof {
                assert(out@.skip(o.len() as int) =~= spec_prefix_int_bytes(6, 0xc0, i));
                lemma_exact_line(i, f@);
            }
        },
        StaticMatch::Name(i) => {
            serialize_prefix_int(4, 0x50, i, out);
            encode_string(7, 0x00, f.value.as_slice(), out);
            proof {
                assert(out@.skip(o.len() as int) =~= spec_prefix_int_bytes(4, 0x50, i) + (
                spec_prefix_int_bytes(7, 0x00, f.value@.len() as u64) + f.value@));
                lemma_name_line(i, f.name@, f.value@);
            }
        },
        StaticMatch::None => {
            encode_string(3, 0x20, f.name.as_slice(), out);
            encode_string(7, 0x00, f.value.as_slice(), out);
            proof {
                assert(out@.skip(o.len() as int) =~= (spec_prefix_int_bytes(
                    3,
                    0x20,
                    f.name@.len() as u64,
                ) + f.name@) + (spec_prefix_int_bytes(7, 0x00, f.value@.len() as u64)
                    + f.value@));
                lemma_literal_line(f.name@, f.value@);
            }
        },
    }
    proof {
        assert(out@.subrange(0, o.len() as int) =~= o);
    }
}

//= https://www.rfc-editor.org/rfc/rfc9204#section-2.1
//# An encoder MUST emit field representations in the order
//# they appear in the input field section.
/// Appends a response field section: prefix `0x00 0x00` (Required Insert Count 0, Base 0), then
/// per field an indexed static line on an exact static match, a literal with a static name
/// reference on a name match, else a literal with a literal name (N=0, H=0 throughout).
pub fn encode_field_section(fields: &[FieldLine], out: &mut Vec<u8>)
    requires
        forall|i: int|
            0 <= i < fields@.len() ==> #[trigger] fields@[i].name@.len() <= PREFIX_INT_MAX
                && fields@[i].value@.len() <= PREFIX_INT_MAX,
    ensures
        final(out)@.len() >= old(out)@.len(),
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        rfc_decode_field_section(final(out)@.skip(old(out)@.len() as int)) == Ok::<_, u64>(
            fields_view(fields@),
        ),
{
    out.push(0);
    out.push(0);
    let ghost mut enc: Seq<u8> = Seq::empty();
    proof {
        assert(out@ =~= old(out)@ + seq![0u8, 0u8] + enc);
        assert(fields_view(fields@.take(0)) =~= Seq::empty());
    }
    let mut i: usize = 0;
    while i < fields.len()
        invariant
            i <= fields@.len(),
            out@ == old(out)@ + seq![0u8, 0u8] + enc,
            rfc_field_lines(enc) == Some(fields_view(fields@.take(i as int))),
            forall|j: int|
                0 <= j < fields@.len() ==> #[trigger] fields@[j].name@.len() <= PREFIX_INT_MAX
                    && fields@[j].value@.len() <= PREFIX_INT_MAX,
        decreases fields.len() - i,
    {
        let ghost before = out@;
        encode_field_line(&fields[i], out);
        proof {
            let e = out@.skip(before.len() as int);
            let f = fields@[i as int];
            lemma_one_line(e, f@);
            lemma_field_lines_append(enc, e);
            assert(out@ =~= before + e);
            enc = enc + e;
            assert(fields_view(fields@.take(i + 1)) =~= fields_view(fields@.take(i as int)) + seq![
                f@,
            ]);
        }
        i += 1;
    }
    proof {
        let b = seq![0u8, 0u8] + enc;
        assert(out@.skip(old(out)@.len() as int) =~= b);
        assert(out@.subrange(0, old(out)@.len() as int) =~= old(out)@);
        assert(fields@.take(fields@.len() as int) =~= fields@);
        assert(b[0] == 0u8 && b.skip(1)[0] == 0u8);
        assert(b.skip(1).skip(1) =~= enc);
        lemma2_to64();
        assert(rfc_prefix_int(8, b) == PrefixIntSpec::Value { value: 0, consumed: 1 });
        assert(rfc_prefix_int(7, b.skip(1)) == PrefixIntSpec::Value { value: 0, consumed: 1 });
        assert(0u8 & 0x80u8 == 0) by (bit_vector);
    }
}

} // verus!
