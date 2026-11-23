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
use byteq::capvec::CapVec;
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


/// A field section the bounded decoder rejects: a QPACK error (a connection error code), or a
/// decoded size over the budget.
#[derive(Debug, PartialEq, Eq)]
pub enum BoundedError {
    Qpack(u64),
    OverBudget,
}

/// Where the field line representations start, past the prefix `rfc_decode_field_section`
/// accepts.
pub open spec fn rfc_section_start(b: Seq<u8>) -> Option<nat> {
    match rfc_prefix_int(8, b) {
        PrefixIntSpec::Value { value: ric, consumed: c } => {
            let rest = b.skip(c as int);
            if ric != 0 {
                None
            } else {
                match rfc_prefix_int(7, rest) {
                    PrefixIntSpec::Value { consumed: c2, .. } => {
                        if rest[0] & 0x80u8 != 0 {
                            None
                        } else {
                            Some(c + c2)
                        }
                    },
                    _ => None,
                }
            }
        },
        _ => None,
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.2.2
//# The size of a field list is calculated based on the
//# uncompressed size of fields, including the length of the name and
//# value in bytes plus an overhead of 32 bytes for each field.
pub open spec fn field_line_size(f: (Seq<u8>, Seq<u8>)) -> int {
    f.0.len() + f.1.len() + 32int
}

/// `rfc_field_lines` with `left` bytes of decoded size to spend: each line is decoded, then
/// charged, and the first line that does not fit is `OverBudget`.
pub open spec fn rfc_field_lines_bounded(b: Seq<u8>, left: u64) -> Result<
    Seq<(Seq<u8>, Seq<u8>)>,
    BoundedError,
>
    decreases b.len(),
    via field_lines_bounded_decreases
{
    if b.len() == 0 {
        Ok(seq![])
    } else {
        match rfc_field_line(b) {
            None => Err(BoundedError::Qpack(QPACK_DECOMPRESSION_FAILED)),
            Some((f, c)) => if field_line_size(f) > left {
                Err(BoundedError::OverBudget)
            } else {
                match rfc_field_lines_bounded(b.skip(c as int), (left - field_line_size(f)) as u64) {
                    Ok(rest) => Ok(seq![f] + rest),
                    Err(e) => Err(e),
                }
            },
        }
    }
}

#[verifier::decreases_by]
proof fn field_lines_bounded_decreases(b: Seq<u8>, left: u64) {
    if b.len() > 0 {
        lemma_field_line_consumed(b);
    }
}

/// `rfc_decode_field_section` under a decoded-size budget (RFC 9114 §4.2.2).
pub open spec fn rfc_decode_field_section_bounded(b: Seq<u8>, budget: u64) -> Result<
    Seq<(Seq<u8>, Seq<u8>)>,
    BoundedError,
> {
    match rfc_section_start(b) {
        None => Err(BoundedError::Qpack(QPACK_DECOMPRESSION_FAILED)),
        Some(c) => rfc_field_lines_bounded(b.skip(c as int), budget),
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

pub(crate) proof fn lemma_field_line_consumed(b: Seq<u8>)
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
    hide(rfc_string);
    hide(rfc_prefix_int);
    hide(spec_static_entry);
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
    // Each line's facts come from lemma_field_line_consumed and lemma_field_line_append; its definition stays closed
    // (seed robustness, docs/rca/2026-11-16-smt-order-fragility.md).
    hide(rfc_field_line);
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


proof fn lemma_lines_bounded_refines(b: Seq<u8>, left: u64)
    ensures
        rfc_field_lines_bounded(b, left) matches Ok(f) ==> rfc_field_lines(b) == Some(f),
        rfc_field_lines_bounded(b, left) matches Err(BoundedError::Qpack(c)) ==> c
            == QPACK_DECOMPRESSION_FAILED && rfc_field_lines(b) is None,
    decreases b.len(),
{
    hide(rfc_field_line);
    if b.len() > 0 {
        lemma_field_line_consumed(b);
        if let Some((f, c)) = rfc_field_line(b) {
            if field_line_size(f) <= left {
                lemma_lines_bounded_refines(b.skip(c as int), (left - field_line_size(f)) as u64);
            }
        }
    }
}

/// Within budget the bounded decoder agrees with `rfc_decode_field_section`, and its QPACK
/// errors are that decoder's errors.
pub proof fn lemma_bounded_refines(b: Seq<u8>, budget: u64)
    ensures
        rfc_decode_field_section_bounded(b, budget) matches Ok(f) ==> rfc_decode_field_section(b)
            == Ok::<_, u64>(f),
        rfc_decode_field_section_bounded(b, budget) matches Err(BoundedError::Qpack(c))
            ==> rfc_decode_field_section(b) == Err::<Seq<(Seq<u8>, Seq<u8>)>, u64>(c),
{
    hide(rfc_field_lines_bounded);
    hide(rfc_field_lines);
    hide(rfc_field_line);
    lemma_prefix_int_consumed(8, b);
    if let PrefixIntSpec::Value { consumed: c, .. } = rfc_prefix_int(8, b) {
        let rest = b.skip(c as int);
        lemma_prefix_int_consumed(7, rest);
        if let PrefixIntSpec::Value { consumed: c2, .. } = rfc_prefix_int(7, rest) {
            assert(rest.skip(c2 as int) =~= b.skip((c + c2) as int));
            lemma_lines_bounded_refines(b.skip((c + c2) as int), budget);
        }
    }
}

/// Every static entry's name and value: `static_sizes_from(0)`, evaluated by Verus's `by (compute)` interpreter.
spec fn static_size_ok(i: nat) -> bool {
    spec_static_entry(i) matches Some(e) ==> e.0.len() + e.1.len() <= 76
}

spec fn static_sizes_from(i: nat) -> bool
    decreases 99 - i,
{
    if i >= 99 {
        true
    } else {
        static_size_ok(i) && static_sizes_from(i + 1)
    }
}

proof fn lemma_sizes_from(i: nat, j: nat)
    requires
        static_sizes_from(i),
        i <= j < 99,
    ensures
        static_size_ok(j),
    decreases j - i,
{
    if i < j {
        lemma_sizes_from(i + 1, j);
    }
}

/// Every static entry's name and value are at most 76 bytes together (index 85, content-security-policy).
pub proof fn lemma_static_size(i: nat)
    ensures
        spec_static_entry(i) matches Some(e) ==> e.0.len() + e.1.len() <= 76,
{
    assert(static_sizes_from(0)) by (compute_only);
    if i < 99 {
        lemma_sizes_from(0, i);
    }
}

/// A string literal decodes to at most 8/5 of the bytes it takes (raw: as many; Huffman: `lemma_decoded_len`).
proof fn lemma_string_len(n: u8, b: Seq<u8>)
    ensures
        rfc_string(n, b) matches Some((s, c)) ==> 5 * s.len() <= 8 * c,
{
    if let PrefixIntSpec::Value { value: len, consumed: c } = rfc_prefix_int(n, b) {
        if c + len <= b.len() {
            let raw = b.subrange(c as int, (c + len) as int);
            if (b[0] >> n) & 1u8 != 0 && exists|s: Seq<u8>| rfc_huffman_decodes(raw, s) {
                let s = choose|s: Seq<u8>| rfc_huffman_decodes(raw, s);
                lemma_decoded_len(raw, s);
            }
        }
    }
}

/// A field line decodes to at most 76 bytes per byte it takes: a static entry is at most 76 bytes and its line at
/// least one byte, a string at most 8/5 of its bytes. With RFC 9114 §4.2.2's 32 bytes of overhead, at most 108.
pub proof fn lemma_line_expansion(b: Seq<u8>)
    requires
        b.len() > 0,
    ensures
        rfc_field_line(b) matches Some((f, k)) ==> 1 <= k && line_bytes(f) <= 76 * k && field_line_size(f) <= 108 * k,
{
    lemma_field_line_consumed(b);
    lemma_prefix_int_consumed(6, b);
    lemma_prefix_int_consumed(4, b);
    lemma_string_consumed(3, b);
    lemma_string_len(3, b);
    if let PrefixIntSpec::Value { value: i, consumed: c } = rfc_prefix_int(6, b) {
        lemma_static_size(i);
    }
    if let PrefixIntSpec::Value { value: i, consumed: c } = rfc_prefix_int(4, b) {
        lemma_static_size(i);
        lemma_string_len(7, b.skip(c as int));
    }
    if let Some((_, c)) = rfc_string(3, b) {
        lemma_string_len(7, b.skip(c as int));
    }
}

// =============================================================================
// Decoder
// =============================================================================

/// The string a scan located: the Huffman output, else the raw bytes `b[s..e]`.
spec fn str_of(h: Option<Vec<u8>>, b: Seq<u8>, s: usize, e: usize) -> Seq<u8> {
    match h {
        Some(v) => v@,
        None => b.subrange(s as int, e as int),
    }
}

/// The cost constant of `scan_string`: a prefix integer and a Huffman decode.
#[verifier::inline]
pub open spec fn c_str() -> nat {
    40
}

/// The per-line cost constant of the field-line decoders, on top of one unit per decoded byte.
#[verifier::inline]
pub open spec fn c_line() -> nat {
    64
}

/// A copy of `s` into an exact buffer: one allocation, one unit per byte.
pub fn copy_bytes(s: &[u8]) -> (r: (Vec<u8>, Ghost<nat>))
    ensures
        r.0@ == s@,
        r.1@ == s@.len() + 1,
{
    let mut v = CapVec::new(s.len());
    let Ghost(c) = v.push_slice(s);
    assert(v@ =~= s@);
    (v.into_vec(), Ghost(c + 1))
}

//= https://www.rfc-editor.org/rfc/rfc9204#section-7.4
//# If an implementation encounters a value larger than it is able to
//# decode, this MUST be treated as a stream error of type
//# QPACK_DECOMPRESSION_FAILED if on a request stream
/// Locates the string literal at the front of `b` without copying a raw (H=0) string:
/// `(Huffman output, s, e)`, consuming `e` bytes. Only a Huffman string is allocated, and its
/// output is bounded by the input.
fn scan_string(n: u8, b: &[u8]) -> (r: (Option<(Option<Vec<u8>>, usize, usize)>, Ghost<nat>))
    requires
        1 <= n <= 7,
        b@.len() <= usize::MAX / 8,
    ensures
        match r.0 {
            Some((h, s, e)) => s <= e <= b@.len() && rfc_string(n, b@) == Some(
                (str_of(h, b@, s, e), e as nat),
            ) && r.1@ <= c_str() * (e + 1),
            None => rfc_string(n, b@) is None,
        },
        r.1@ <= c_str() * (b@.len() + 1),
{
    let (pi, Ghost(cp)) = parse_prefix_int_w(n, b);
    match pi {
        PrefixInt::Value { value: len, consumed: c } => {
            proof {
                lemma_prefix_int_consumed(n, b@);
            }
            // The length is checked against the bytes present before anything is allocated.
            if len > (b.len() - c) as u64 {
                return (None, Ghost(cp + 1));
            }
            let end = c + len as usize;
            if (b[0] >> n) & 1 == 0 {
                (Some((None, c, end)), Ghost(cp + 1))
            } else {
                let raw = slice_subrange(b, c, end);
                let (hd, Ghost(ch)) = huffman_decode_w(raw);
                match hd {
                    Some(s) => {
                        proof {
                            let x = choose|x: Seq<u8>| rfc_huffman_decodes(raw@, x);
                            lemma_huffman_unique(raw@, s@, x);
                        }
                        (Some((Some(s), c, end)), Ghost(cp + 1 + ch))
                    },
                    None => (None, Ghost(cp + 1 + ch)),
                }
            }
        },
        _ => (None, Ghost(cp + 1)),
    }
}

fn str_len(h: &Option<Vec<u8>>, s: usize, e: usize) -> (r: usize)
    requires
        s <= e,
    ensures
        r == match *h {
            Some(v) => v@.len() as int,
            None => e - s,
        },
{
    match h {
        Some(v) => v.len(),
        None => e - s,
    }
}

/// The scanned string: the Huffman output moved, or the raw bytes copied.
fn take_str(h: Option<Vec<u8>>, b: &[u8], s: usize, e: usize) -> (r: (Vec<u8>, Ghost<nat>))
    requires
        s <= e <= b@.len(),
    ensures
        r.0@ == str_of(h, b@, s, e),
        r.1@ <= e - s + 1,
{
    match h {
        Some(v) => (v, Ghost(1)),
        None => copy_bytes(slice_subrange(b, s, e)),
    }
}

/// The cost constant of `decode_string`: a scan and the copy.
#[verifier::inline]
pub open spec fn c_dstr() -> nat {
    41
}

fn decode_string(n: u8, b: &[u8]) -> (r: (Option<(Vec<u8>, usize)>, Ghost<nat>))
    requires
        1 <= n <= 7,
        b@.len() <= usize::MAX / 8,
    ensures
        match r.0 {
            Some((s, c)) => c <= b@.len() && rfc_string(n, b@) == Some((s@, c as nat)) && r.1@ <= c_dstr() * (c + 1),
            None => rfc_string(n, b@) is None,
        },
        r.1@ <= c_dstr() * (b@.len() + 1),
{
    let (sc, Ghost(c1)) = scan_string(n, b);
    match sc {
        Some((h, s, e)) => {
            let (v, Ghost(c2)) = take_str(h, b, s, e);
            (Some((v, e)), Ghost(c1 + c2))
        },
        None => (None, Ghost(c1)),
    }
}

/// The decoded bytes of a field line.
pub open spec fn line_bytes(f: (Seq<u8>, Seq<u8>)) -> nat {
    f.0.len() + f.1.len()
}

/// The two copies of a static entry.
fn copy_entry(n: &[u8], v: &[u8]) -> (r: (FieldLine, Ghost<nat>))
    ensures
        r.0@ == (n@, v@),
        r.1@ == n@.len() + v@.len() + 2,
{
    let (nm, Ghost(c1)) = copy_bytes(n);
    let (vl, Ghost(c2)) = copy_bytes(v);
    (FieldLine { name: nm, value: vl }, Ghost(c1 + c2))
}

/// The cost of a field-line decoder's result `r` on `b`: per line, `c_line` per byte taken plus one per byte decoded;
/// on a failure, `c_line` per byte present.
pub open spec fn line_cost_ok<E>(b: Seq<u8>, r: Result<(FieldLine, usize), E>, w: nat) -> bool {
    match r {
        Ok((f, c)) => w <= c_line() * (c + 1) + line_bytes(f@),
        Err(_) => w <= c_line() * (b.len() + 1),
    }
}

fn decode_field_line(b: &[u8]) -> (r: (Option<(FieldLine, usize)>, Ghost<nat>))
    requires
        b@.len() > 0,
        b@.len() <= usize::MAX / 8,
    ensures
        match r.0 {
            Some((f, c)) => rfc_field_line(b@) == Some((f@, c as nat)) && r.1@ <= c_line() * (c + 1) + line_bytes(
                f@,
            ),
            None => rfc_field_line(b@) is None && r.1@ <= c_line() * (b@.len() + 1),
        },
{
    let b0 = b[0];
    if b0 & 0x80 != 0 {
        if b0 & 0x40 == 0 {
            return (None, Ghost(1));
        }
        let (pi, Ghost(cp)) = parse_prefix_int_w(6, b);
        match pi {
            PrefixInt::Value { value, consumed } => match static_entry(value) {
                Some((n, v)) => {
                    let (f, Ghost(cf)) = copy_entry(n, v);
                    (Some((f, consumed)), Ghost(cp + cf + 1))
                },
                None => (None, Ghost(cp + 1)),
            },
            _ => (None, Ghost(cp + 1)),
        }
    } else if b0 & 0x40 != 0 {
        if b0 & 0x10 == 0 {
            return (None, Ghost(1));
        }
        let (pi, Ghost(cp)) = parse_prefix_int_w(4, b);
        match pi {
            PrefixInt::Value { value, consumed } => match static_entry(value) {
                Some((n, _)) => {
                    proof {
                        lemma_prefix_int_consumed(4, b@);
                    }
                    let (ds, Ghost(cs)) = decode_string(7, slice_subrange(b, consumed, b.len()));
                    match ds {
                        Some((v, c2)) => {
                            let (nm, Ghost(cn)) = copy_bytes(n);
                            (Some((FieldLine { name: nm, value: v }, consumed + c2)), Ghost(cp + cs + cn + 1))
                        },
                        None => (None, Ghost(cp + cs + 1)),
                    }
                },
                None => (None, Ghost(cp + 1)),
            },
            _ => (None, Ghost(cp + 1)),
        }
    } else if b0 & 0x20 != 0 {
        proof {
            lemma_string_consumed(3, b@);
        }
        let (d1, Ghost(c1)) = decode_string(3, b);
        match d1 {
            Some((name, c)) => {
                let (d2, Ghost(c2)) = decode_string(7, slice_subrange(b, c, b.len()));
                match d2 {
                    Some((value, c3)) => (Some((FieldLine { name, value }, c + c3)), Ghost(c1 + c2 + 1)),
                    None => (None, Ghost(c1 + c2 + 1)),
                }
            },
            None => (None, Ghost(c1 + 1)),
        }
    } else {
        (None, Ghost(1))
    }
}

/// The cost constant of the field-section decoders: two prefix integers (at most 23 with the step), then the lines
/// (`c_lines`).
#[verifier::inline]
pub open spec fn c_sec() -> nat {
    264
}

/// Decodes a request's encoded field section (the whole HEADERS frame payload).
pub fn decode_field_section(b: &[u8]) -> (r: (Result<Vec<FieldLine>, u64>, Ghost<nat>))
    requires
        b@.len() <= usize::MAX / 8,
    ensures
        match r.0 {
            Ok(v) => rfc_decode_field_section(b@) == Ok::<_, u64>(fields_view(v@)),
            Err(e) => rfc_decode_field_section(b@) == Err::<Seq<(Seq<u8>, Seq<u8>)>, u64>(e),
        },
        r.1@ <= c_sec() * (b@.len() + 1),
{
    let (p1, Ghost(w1)) = parse_prefix_int_w(8, b);
    let c = match p1 {
        PrefixInt::Value { value, consumed } => {
            if value != 0 {
                return (Err(QPACK_DECOMPRESSION_FAILED), Ghost(w1 + 1));
            }
            consumed
        },
        _ => return (Err(QPACK_DECOMPRESSION_FAILED), Ghost(w1 + 1)),
    };
    proof {
        lemma_prefix_int_consumed(8, b@);
    }
    let rest = slice_subrange(b, c, b.len());
    let (p2, Ghost(w2)) = parse_prefix_int_w(7, rest);
    let c2 = match p2 {
        PrefixInt::Value { consumed, .. } => consumed,
        _ => return (Err(QPACK_DECOMPRESSION_FAILED), Ghost(w1 + w2 + 1)),
    };
    if rest[0] & 0x80 != 0 {
        return (Err(QPACK_DECOMPRESSION_FAILED), Ghost(w1 + w2 + 1));
    }
    proof {
        lemma_prefix_int_consumed(7, rest@);
        assert(rest@ =~= b@.skip(c as int));
    }
    let lines = slice_subrange(rest, c2, rest.len());
    proof {
        assert(lines@ =~= rest@.skip(c2 as int));
    }
    let (dl, Ghost(w3)) = decode_lines(lines);
    match dl {
        Some(v) => (Ok(v), Ghost(w1 + w2 + w3 + 1)),
        None => (Err(QPACK_DECOMPRESSION_FAILED), Ghost(w1 + w2 + w3 + 1)),
    }
}

type Lines = Seq<(Seq<u8>, Seq<u8>)>;

/// `decode_lines`' invariant at `pos`, with `acc` decoded so far.
pub open spec fn lines_inv(lines: Seq<u8>, pos: int, acc: Lines) -> bool {
    rfc_field_lines(lines) == match rfc_field_lines(lines.skip(pos)) {
        Some(r) => Some(acc + r),
        None => None,
    }
}

/// The size of decoded lines (RFC 9114 §4.2.2): Σ `field_line_size`.
pub open spec fn lines_size(s: Lines) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        lines_size(s.drop_last()) + field_line_size(s.last())
    }
}

/// `decode_lines_bounded`'s invariant at `pos` with `left` of the budget.
pub open spec fn lines_bounded_inv(lines: Seq<u8>, budget: u64, pos: int, left: u64, acc: Lines) -> bool {
    rfc_field_lines_bounded(lines, budget) == match rfc_field_lines_bounded(lines.skip(pos), left) {
        Ok(r) => Ok(acc + r),
        Err(e) => Err(e),
    }
}

proof fn lemma_lines_start(lines: Seq<u8>, budget: u64)
    ensures
        lines_inv(lines, 0, Seq::empty()),
        lines_bounded_inv(lines, budget, 0, budget, Seq::empty()),
{
    hide(rfc_field_line);
    assert(lines.skip(0) =~= lines);
    if let Some(r) = rfc_field_lines(lines) {
        assert(Seq::<(Seq<u8>, Seq<u8>)>::empty() + r =~= r);
    }
    if let Ok(r) = rfc_field_lines_bounded(lines, budget) {
        assert(Seq::<(Seq<u8>, Seq<u8>)>::empty() + r =~= r);
    }
}

/// One line decoded at `pos` moves `decode_lines`' invariant to `pos + k`.
proof fn lemma_lines_step(lines: Seq<u8>, pos: int, k: nat, acc: Lines, f: (Seq<u8>, Seq<u8>))
    requires
        0 <= pos < lines.len(),
        rfc_field_line(lines.skip(pos)) == Some((f, k)),
        lines_inv(lines, pos, acc),
    ensures
        1 <= k,
        pos + k <= lines.len(),
        lines_inv(lines, pos + k, acc.push(f)),
{
    hide(rfc_field_line);
    lemma_field_line_consumed(lines.skip(pos));
    assert(lines.skip(pos).skip(k as int) =~= lines.skip(pos + k));
    if let Some(r) = rfc_field_lines(lines.skip(pos + k)) {
        assert(acc + (seq![f] + r) =~= acc.push(f) + r);
    }
}

/// A line that does not decode at `pos` fails the whole section.
proof fn lemma_lines_none(lines: Seq<u8>, pos: int, acc: Lines)
    requires
        0 <= pos < lines.len(),
        rfc_field_line(lines.skip(pos)) is None,
        lines_inv(lines, pos, acc),
    ensures
        rfc_field_lines(lines) is None,
{
    hide(rfc_field_line);
}

/// At the end, the invariant is the result.
proof fn lemma_lines_end(lines: Seq<u8>, budget: u64, pos: int, left: u64, acc: Lines)
    requires
        pos == lines.len(),
    ensures
        lines_inv(lines, pos, acc) ==> rfc_field_lines(lines) == Some(acc),
        lines_bounded_inv(lines, budget, pos, left, acc) ==> rfc_field_lines_bounded(lines, budget) == Ok::<
            _,
            BoundedError,
        >(acc),
{
    hide(rfc_field_line);
    assert(lines.skip(pos) =~= Seq::<u8>::empty());
    assert(acc + Seq::empty() =~= acc);
}

/// One line decoded within `left` at `pos` moves `decode_lines_bounded`' invariant to `pos + k`.
proof fn lemma_lines_bounded_step(
    lines: Seq<u8>,
    budget: u64,
    pos: int,
    left: u64,
    k: nat,
    acc: Lines,
    f: (Seq<u8>, Seq<u8>),
)
    requires
        0 <= pos < lines.len(),
        rfc_field_line(lines.skip(pos)) == Some((f, k)),
        field_line_size(f) <= left,
        lines_bounded_inv(lines, budget, pos, left, acc),
    ensures
        1 <= k,
        pos + k <= lines.len(),
        lines_bounded_inv(lines, budget, pos + k, (left - field_line_size(f)) as u64, acc.push(f)),
{
    hide(rfc_field_line);
    let left2 = (left - field_line_size(f)) as u64;
    lemma_field_line_consumed(lines.skip(pos));
    assert(lines.skip(pos).skip(k as int) =~= lines.skip(pos + k));
    if let Ok(r) = rfc_field_lines_bounded(lines.skip(pos + k), left2) {
        assert(acc + (seq![f] + r) =~= acc.push(f) + r);
    }
}

/// A line that fails at `pos` (QPACK error or over `left`) fails the whole section with that error.
proof fn lemma_lines_bounded_err(lines: Seq<u8>, budget: u64, pos: int, left: u64, acc: Lines, e: BoundedError)
    requires
        0 <= pos < lines.len(),
        lines_bounded_inv(lines, budget, pos, left, acc),
        match e {
            BoundedError::Qpack(c) => c == QPACK_DECOMPRESSION_FAILED && rfc_field_line(lines.skip(pos)) is None,
            BoundedError::OverBudget => rfc_field_line(lines.skip(pos)) matches Some((f, _)) && field_line_size(f)
                > left,
        },
    ensures
        rfc_field_lines_bounded(lines, budget) == Err::<Lines, BoundedError>(e),
{
    hide(rfc_field_line);
}

/// The buffers a dropped list of `n` decoded lines frees: the list's, and each line's name and value.
spec fn lines_free(n: nat) -> nat {
    2 * n + 1
}

/// The per-byte cost constant of `decode_lines` and `decode_lines_bounded`: each line's `c_line` per byte taken (2
/// with its +1) and its push, plus its decoded bytes, at most 108 per byte taken with the 32 of overhead
/// (`lemma_line_expansion`).
#[verifier::inline]
pub open spec fn c_lines() -> nat {
    240
}

/// Decodes field line representations up to the end of `lines`. Each line takes at least one byte, so `out` is created
/// at `lines.len()` lines.
fn decode_lines(lines: &[u8]) -> (r: (Option<Vec<FieldLine>>, Ghost<nat>))
    requires
        lines@.len() <= usize::MAX / 8,
    ensures
        match r.0 {
            Some(v) => rfc_field_lines(lines@) == Some(fields_view(v@)),
            None => rfc_field_lines(lines@) is None,
        },
        r.1@ <= c_lines() * (lines@.len() + 1),
{
    hide(rfc_field_lines);
    hide(rfc_field_line);
    hide(lines_inv);
    proof {
        lemma_lines_start(lines@, 0);
        assert(fields_view(Seq::<FieldLine>::empty()) =~= Seq::empty());
    }
    let mut out: CapVec<FieldLine> = CapVec::new(lines.len());
    let mut pos: usize = 0;
    let ghost mut dec: nat = 0;
    let ghost mut work: nat = 1;
    while pos < lines.len()
        invariant
            pos <= lines@.len(),
            lines@.len() <= usize::MAX / 8,
            lines_inv(lines@, pos as int, fields_view(out@)),
            out.wf(),
            out.cap() == lines@.len(),
            out@.len() <= pos,
            dec <= 76 * pos,
            work <= 130 * pos + dec + 1,
        decreases lines@.len() - pos,
    {
        let ghost w_it: nat = work;
        let tail = slice_subrange(lines, pos, lines.len());
        proof {
            assert(tail@ =~= lines@.skip(pos as int));
        }
        let (dl, Ghost(cl)) = decode_field_line(tail);
        proof {
            // the line's cost, charged before the exit after it (rca-early-return-cost)
            work = work + cl;
        }
        match dl {
            Some((f, k)) => {
                proof {
                    lemma_lines_step(lines@, pos as int, k as nat, fields_view(out@), f@);
                    lemma_line_expansion(tail@);
                    assert(fields_view(out@.push(f)) =~= fields_view(out@).push(f@));
                    dec = dec + line_bytes(f@);
                    work = work + 1;
                }
                out.push(f);
                pos += k;
            },
            None => {
                // the exit's own charge: the free of `out` and its lines
                let ghost ret: nat = work + lines_free(out@.len() as nat);
                proof {
                    lemma_lines_none(lines@, pos as int, fields_view(out@));
                    crate::frame::lemma_paid(work, lines_free(out@.len() as nat), ret);
                }
                proof {
                    // the iteration's charges are in what the exit returns (rca-early-return-cost)
                    crate::frame::lemma_paid(w_it, cl, work);
                }
                return (None, Ghost(ret));
            },
        }
    }
    proof {
        lemma_lines_end(lines@, 0, pos as int, 0, fields_view(out@));
    }
    (Some(out.into_vec()), Ghost(work))
}

/// `a + c + 32 <= left`, computed without overflow.
fn fits(a: usize, c: usize, left: u64) -> (r: bool)
    ensures
        r == (a + c + 32 <= left),
{
    let x = a as u64;
    let y = c as u64;
    x <= left && y <= left - x && 32 <= left - x - y
}

/// `decode_field_line_bounded`'s result `r` on `b` with `left` of the budget.
pub open spec fn line_bounded_ok(b: Seq<u8>, left: u64, r: Result<(FieldLine, usize), BoundedError>) -> bool {
    match r {
        Ok((f, c)) => rfc_field_line(b) == Some((f@, c as nat)) && field_line_size(f@) <= left,
        Err(BoundedError::Qpack(e)) => e == QPACK_DECOMPRESSION_FAILED && rfc_field_line(b) is None,
        Err(BoundedError::OverBudget) => rfc_field_line(b) matches Some((f, _)) && field_line_size(f) > left,
    }
}

//= https://www.rfc-editor.org/rfc/rfc9204#section-3.1
//# When the decoder encounters an invalid static table index in a field
//# line representation, it MUST treat this as a connection error of type
//# QPACK_DECOMPRESSION_FAILED.
//= https://www.rfc-editor.org/rfc/rfc9204#section-7.4
//# If an implementation encounters a value larger than it is able to
//# decode, this MUST be treated as a stream error of type
//# QPACK_DECOMPRESSION_FAILED if on a request stream
//= https://www.rfc-editor.org/rfc/rfc9114#section-4.2.2
//# An HTTP/3 implementation MAY impose a limit on the maximum size of
//# the message header it will accept on an individual HTTP message.
/// The errors a field-line decoder may return on `b` with `left` of the budget, `decode_lines_bounded`'s
/// requirements restated: QPACK_DECOMPRESSION_FAILED when no field line decodes (RFC 9204 §4.5, §2.2.3, §3.1, §7.4,
/// cited at `rfc_field_line` and `scan_string`), OverBudget when one does but exceeds what is left of the field
/// section's size limit (RFC 9114 §4.2.2, cited at `field_line_size`).
pub open spec fn line_allowed_err(b: Seq<u8>, left: u64, e: BoundedError) -> bool {
    match e {
        BoundedError::Qpack(c) => c == QPACK_DECOMPRESSION_FAILED && rfc_field_line(b) is None,
        BoundedError::OverBudget => rfc_field_line(b) matches Some((f, _)) && field_line_size(f) > left,
    }
}

/// An indexed field line (`1 1 Index(6+)`): the static entry, copied once it fits.
fn indexed_line(b: &[u8], left: u64) -> (r: (Result<(FieldLine, usize), BoundedError>, Ghost<nat>))
    requires
        b@.len() > 0,
        b@[0] & 0x80u8 != 0,
        b@[0] & 0x40u8 != 0,
    ensures
        line_bounded_ok(b@, left, r.0),
        r.0 matches Err(e) ==> line_allowed_err(b@, left, e),
        line_cost_ok(b@, r.0, r.1@),
{
    let (pi, Ghost(cp)) = parse_prefix_int_w(6, b);
    match pi {
        PrefixInt::Value { value, consumed } => match static_entry(value) {
            Some((n, v)) => if fits(n.len(), v.len(), left) {
                let (f, Ghost(cf)) = copy_entry(n, v);
                (Ok((f, consumed)), Ghost(cp + cf + 1))
            } else {
                (Err(BoundedError::OverBudget), Ghost(cp + 1))
            },
            None => (Err(BoundedError::Qpack(QPACK_DECOMPRESSION_FAILED)), Ghost(cp + 1)),
        },
        _ => (Err(BoundedError::Qpack(QPACK_DECOMPRESSION_FAILED)), Ghost(cp + 1)),
    }
}

/// A literal line with a static name reference (`0 1 N T NameIndex(4+)`, then the value): the value is scanned
/// (a Huffman one decoded) before the size check, the copies made after it.
fn name_ref_line(b: &[u8], left: u64) -> (r: (Result<(FieldLine, usize), BoundedError>, Ghost<nat>))
    requires
        b@.len() > 0,
        b@.len() <= usize::MAX / 8,
        b@[0] & 0x80u8 == 0,
        b@[0] & 0x40u8 != 0,
    ensures
        line_bounded_ok(b@, left, r.0),
        r.0 matches Err(e) ==> line_allowed_err(b@, left, e),
        line_cost_ok(b@, r.0, r.1@),
{
    if b[0] & 0x10 == 0 {
        return (Err(BoundedError::Qpack(QPACK_DECOMPRESSION_FAILED)), Ghost(1));
    }
    let (pi, Ghost(cp)) = parse_prefix_int_w(4, b);
    match pi {
        PrefixInt::Value { value, consumed } => match static_entry(value) {
            Some((n, _)) => {
                proof {
                    lemma_prefix_int_consumed(4, b@);
                }
                let rest = slice_subrange(b, consumed, b.len());
                let (sc, Ghost(cs)) = scan_string(7, rest);
                match sc {
                    Some((h, s, e)) => if fits(n.len(), str_len(&h, s, e), left) {
                        let (nm, Ghost(cn)) = copy_bytes(n);
                        let (v, Ghost(cv)) = take_str(h, rest, s, e);
                        (Ok((FieldLine { name: nm, value: v }, consumed + e)), Ghost(cp + cs + cn + cv + 1))
                    } else {
                        (Err(BoundedError::OverBudget), Ghost(cp + cs + 1))
                    },
                    None => (Err(BoundedError::Qpack(QPACK_DECOMPRESSION_FAILED)), Ghost(cp + cs + 1)),
                }
            },
            None => (Err(BoundedError::Qpack(QPACK_DECOMPRESSION_FAILED)), Ghost(cp + 1)),
        },
        _ => (Err(BoundedError::Qpack(QPACK_DECOMPRESSION_FAILED)), Ghost(cp + 1)),
    }
}

/// A literal line with a literal name (`0 0 1 N H NameLen(3+)`, the name, then the value): both strings are scanned
/// (Huffman ones decoded) before the size check, the raw ones copied after it.
fn literal_line(b: &[u8], left: u64) -> (r: (Result<(FieldLine, usize), BoundedError>, Ghost<nat>))
    requires
        b@.len() > 0,
        b@.len() <= usize::MAX / 8,
        b@[0] & 0x80u8 == 0,
        b@[0] & 0x40u8 == 0,
        b@[0] & 0x20u8 != 0,
    ensures
        line_bounded_ok(b@, left, r.0),
        r.0 matches Err(e) ==> line_allowed_err(b@, left, e),
        line_cost_ok(b@, r.0, r.1@),
{
    proof {
        lemma_string_consumed(3, b@);
    }
    let (s1, Ghost(c1)) = scan_string(3, b);
    match s1 {
        Some((h1, a1, e1)) => {
            let rest = slice_subrange(b, e1, b.len());
            let (s2, Ghost(c2)) = scan_string(7, rest);
            match s2 {
                Some((h2, a2, e2)) => if fits(str_len(&h1, a1, e1), str_len(&h2, a2, e2), left) {
                    let (name, Ghost(cn)) = take_str(h1, b, a1, e1);
                    let (value, Ghost(cv)) = take_str(h2, rest, a2, e2);
                    (Ok((FieldLine { name, value }, e1 + e2)), Ghost(c1 + c2 + cn + cv + 1))
                } else {
                    (Err(BoundedError::OverBudget), Ghost(c1 + c2 + 1))
                },
                None => (Err(BoundedError::Qpack(QPACK_DECOMPRESSION_FAILED)), Ghost(c1 + c2 + 1)),
            }
        },
        None => (Err(BoundedError::Qpack(QPACK_DECOMPRESSION_FAILED)), Ghost(c1 + 1)),
    }
}

/// `decode_field_line` under a budget, in the spec's order: decode, then charge. The whole line
/// is located and its Huffman strings are decoded first: both strings of a literal-name line, and
/// the value of a name-reference line even when the static name alone exceeds `left`. Each such
/// allocation is bounded by the input bytes present. Then the line's size is checked against
/// `left`, and only then are the static and raw bytes copied.
fn decode_field_line_bounded(b: &[u8], left: u64) -> (r: (Result<(FieldLine, usize), BoundedError>, Ghost<nat>))
    requires
        b@.len() > 0,
        b@.len() <= usize::MAX / 8,
    ensures
        line_bounded_ok(b@, left, r.0),
        line_cost_ok(b@, r.0, r.1@),
{
    let b0 = b[0];
    if b0 & 0x80 != 0 {
        if b0 & 0x40 == 0 {
            return (Err(BoundedError::Qpack(QPACK_DECOMPRESSION_FAILED)), Ghost(1));
        }
        indexed_line(b, left)
    } else if b0 & 0x40 != 0 {
        name_ref_line(b, left)
    } else if b0 & 0x20 != 0 {
        literal_line(b, left)
    } else {
        (Err(BoundedError::Qpack(QPACK_DECOMPRESSION_FAILED)), Ghost(1))
    }
}

/// `decode_lines` under a decoded-size budget. Each line takes at least one byte and 32 of the budget, so `out` is
/// created at `min(lines.len(), budget / 32)` lines.
fn decode_lines_bounded(lines: &[u8], budget: u64) -> (r: (Result<Vec<FieldLine>, BoundedError>, Ghost<nat>))
    requires
        lines@.len() <= usize::MAX / 8,
    ensures
        match r.0 {
            Ok(v) => rfc_field_lines_bounded(lines@, budget) == Ok::<_, BoundedError>(fields_view(v@)),
            Err(e) => rfc_field_lines_bounded(lines@, budget) == Err::<
                Seq<(Seq<u8>, Seq<u8>)>,
                BoundedError,
            >(e),
        },
        r.1@ <= c_lines() * (lines@.len() + 1),
{
    hide(rfc_field_lines_bounded);
    hide(rfc_field_line);
    hide(lines_bounded_inv);
    proof {
        lemma_lines_start(lines@, budget);
        assert(fields_view(Seq::<FieldLine>::empty()) =~= Seq::empty());
    }
    let n = lines.len();
    let cap = if n as u64 <= budget / 32 {
        n
    } else {
        (budget / 32) as usize
    };
    let mut out: CapVec<FieldLine> = CapVec::new(cap);
    let mut pos: usize = 0;
    let mut left: u64 = budget;
    let ghost mut work: nat = 1;
    while pos < lines.len()
        invariant
            pos <= lines@.len(),
            lines@.len() <= usize::MAX / 8,
            lines_bounded_inv(lines@, budget, pos as int, left, fields_view(out@)),
            // What is left is the budget less the RFC 9114 §4.2.2 size of the lines decoded so far.
            left == budget - lines_size(fields_view(out@)),
            out.wf(),
            out.cap() == cap,
            cap <= lines@.len(),
            cap == lines@.len() || 32 * cap + 32 > budget,
            out@.len() <= pos,
            32 * out@.len() + left <= budget,
            budget - left <= 108 * pos,
            work <= 130 * pos + (budget - left) + 1,
        decreases lines@.len() - pos,
    {
        let ghost w_it: nat = work;
        let tail = slice_subrange(lines, pos, lines.len());
        proof {
            assert(tail@ =~= lines@.skip(pos as int));
        }
        let (lr, Ghost(cl)) = decode_field_line_bounded(tail, left);
        proof {
            // the line's cost, charged before the exit after it (rca-early-return-cost)
            work = work + cl;
        }
        match lr {
            Ok((f, k)) => {
                proof {
                    lemma_lines_bounded_step(lines@, budget, pos as int, left, k as nat, fields_view(out@), f@);
                    lemma_line_expansion(tail@);
                    assert(fields_view(out@.push(f)) =~= fields_view(out@).push(f@));
                    work = work + 1;
                }
                let ghost done = fields_view(out@);
                left = left - f.name.len() as u64 - f.value.len() as u64 - 32;
                out.push(f);
                pos += k;
                proof {
                    assert(done.push(f@).drop_last() =~= done);
                }
            },
            Err(e) => {
                // the exit's own charge: the free of `out` and its lines
                let ghost ret: nat = work + lines_free(out@.len() as nat);
                proof {
                    lemma_lines_bounded_err(lines@, budget, pos as int, left, fields_view(out@), e);
                    crate::frame::lemma_paid(work, lines_free(out@.len() as nat), ret);
                }
                proof {
                    // the iteration's charges are in what the exit returns (rca-early-return-cost)
                    crate::frame::lemma_paid(w_it, cl, work);
                }
                return (Err(e), Ghost(ret));
            },
        }
    }
    proof {
        lemma_lines_end(lines@, budget, pos as int, left, fields_view(out@));
    }
    (Ok(out.into_vec()), Ghost(work))
}

fn section_start(b: &[u8]) -> (r: (Option<usize>, Ghost<nat>))
    ensures
        match r.0 {
            Some(c) => c <= b@.len() && rfc_section_start(b@) == Some(c as nat),
            None => rfc_section_start(b@) is None,
        },
        r.1@ <= 23,
{
    let (p1, Ghost(w1)) = parse_prefix_int_w(8, b);
    let c = match p1 {
        PrefixInt::Value { value, consumed } => {
            if value != 0 {
                return (None, Ghost(w1 + 1));
            }
            consumed
        },
        _ => return (None, Ghost(w1 + 1)),
    };
    proof {
        lemma_prefix_int_consumed(8, b@);
    }
    let rest = slice_subrange(b, c, b.len());
    let (p2, Ghost(w2)) = parse_prefix_int_w(7, rest);
    let c2 = match p2 {
        PrefixInt::Value { consumed, .. } => consumed,
        _ => return (None, Ghost(w1 + w2 + 1)),
    };
    if rest[0] & 0x80 != 0 {
        return (None, Ghost(w1 + w2 + 1));
    }
    proof {
        lemma_prefix_int_consumed(7, rest@);
        assert(rest@ =~= b@.skip(c as int));
    }
    (Some(c + c2), Ghost(w1 + w2 + 1))
}

/// `decode_field_section` under a decoded-size budget: Σ(name + value + 32) over the lines may
/// not exceed `budget`. Decoding stops at the first line that would, after decoding its Huffman
/// strings (bounded by the input size) but before copying its static or raw bytes.
pub fn decode_field_section_bounded(b: &[u8], budget: u64) -> (r: (Result<
    Vec<FieldLine>,
    BoundedError,
>, Ghost<nat>))
    requires
        b@.len() <= usize::MAX / 8,
    ensures
        match r.0 {
            Ok(v) => rfc_decode_field_section_bounded(b@, budget) == Ok::<_, BoundedError>(
                fields_view(v@),
            ),
            Err(e) => rfc_decode_field_section_bounded(b@, budget) == Err::<
                Seq<(Seq<u8>, Seq<u8>)>,
                BoundedError,
            >(e),
        },
        r.1@ <= c_sec() * (b@.len() + 1),
{
    let (st, Ghost(c1)) = section_start(b);
    match st {
        None => (Err(BoundedError::Qpack(QPACK_DECOMPRESSION_FAILED)), Ghost(c1 + 1)),
        Some(c) => {
            let lines = slice_subrange(b, c, b.len());
            proof {
                assert(lines@ =~= b@.skip(c as int));
            }
            let (r, Ghost(c2)) = decode_lines_bounded(lines, budget);
            (r, Ghost(c1 + c2 + 1))
        },
    }
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

/// A prefix integer below 128 takes at most two bytes.
proof fn lemma_prefix_small(n: u8, flags: u8, v: u64)
    requires
        1 <= n <= 8,
        v < 128,
    ensures
        spec_prefix_int_bytes(n, flags, v).len() <= 2,
{
    let m = (0xffu8 >> (8 - n) as u8);
    if v >= m {
        assert(spec_prefix_cont_bytes((v - m) as u64).len() == 1);
    }
}

proof fn lemma_name_line_len(i: u64, value: Seq<u8>)
    requires
        i < 128,
    ensures
        value.len() < 128 ==> spec_prefix_int_bytes(4, 0x50, i).len() + spec_prefix_int_bytes(
            7,
            0x00,
            value.len() as u64,
        ).len() <= 4,
{
    lemma_prefix_small(4, 0x50, i);
    if value.len() < 128 {
        lemma_prefix_small(7, 0x00, value.len() as u64);
    }
}

proof fn lemma_literal_line_len(name: Seq<u8>, value: Seq<u8>)
    ensures
        name.len() < 128 && value.len() < 128 ==> spec_prefix_int_bytes(
            3,
            0x20,
            name.len() as u64,
        ).len() + spec_prefix_int_bytes(7, 0x00, value.len() as u64).len() <= 4,
{
    if name.len() < 128 && value.len() < 128 {
        lemma_prefix_small(3, 0x20, name.len() as u64);
        lemma_prefix_small(7, 0x00, value.len() as u64);
    }
}

/// The encoders' postcondition from one line's bytes `e` appended to `o` (proof moved out of the exec fns, so their
/// contexts stay small and robust to solver seeds; RCA docs/rca/2026-11-16-smt-order-fragility.md).
proof fn lemma_line_out(o: Seq<u8>, out: Seq<u8>, e: Seq<u8>, f: (Seq<u8>, Seq<u8>))
    requires
        out == o + e,
        e.len() > 0,
        rfc_field_line(e) == Some((f, e.len())),
    ensures
        out.len() > o.len(),
        out.subrange(0, o.len() as int) == o,
        rfc_field_line(out.skip(o.len() as int)) == Some((f, (out.len() - o.len()) as nat)),
{
    hide(rfc_field_line);
    assert(out.skip(o.len() as int) =~= e);
    assert(out.subrange(0, o.len() as int) =~= o);
}

/// `encode_exact_line`'s bytes.
proof fn lemma_exact_out(o: Seq<u8>, out: Seq<u8>, i: u64, f: (Seq<u8>, Seq<u8>))
    requires
        i < STATIC_TABLE_LEN,
        spec_static_entry(i as nat) == Some(f),
        out == o.add(spec_prefix_int_bytes(6, 0xc0, i)),
    ensures
        out.len() > o.len(),
        f.0.len() < 128 && f.1.len() < 128 ==> out.len() <= o.len() + 260,
        out.subrange(0, o.len() as int) == o,
        rfc_field_line(out.skip(o.len() as int)) == Some((f, (out.len() - o.len()) as nat)),
{
    hide(rfc_field_line);
    lemma_prefix_small(6, 0xc0, i);
    lemma_exact_line(i, f);
    lemma_line_out(o, out, spec_prefix_int_bytes(6, 0xc0, i), f);
}

/// `encode_name_line`'s bytes.
proof fn lemma_name_out(o: Seq<u8>, out: Seq<u8>, i: u64, name: Seq<u8>, value: Seq<u8>)
    requires
        i < STATIC_TABLE_LEN,
        spec_name_is(i as nat, name),
        value.len() <= PREFIX_INT_MAX,
        out == o.add(spec_prefix_int_bytes(4, 0x50, i)) + spec_prefix_int_bytes(7, 0x00, value.len() as u64)
            + value,
    ensures
        out.len() > o.len(),
        name.len() < 128 && value.len() < 128 ==> out.len() <= o.len() + 260,
        out.subrange(0, o.len() as int) == o,
        rfc_field_line(out.skip(o.len() as int)) == Some(((name, value), (out.len() - o.len()) as nat)),
{
    hide(rfc_field_line);
    let (p, q) = (spec_prefix_int_bytes(4, 0x50, i), spec_prefix_int_bytes(7, 0x00, value.len() as u64));
    lemma_name_line_len(i, value);
    lemma_cat_assoc3(o, p, q, value);
    lemma_name_line(i, name, value);
    lemma_line_out(o, out, p + (q + value), (name, value));
}

/// `o + a + b + v` regrouped, in its own small context (`lemma_name_out` varied 0.35M-7.96M over seeds 0-4 with the
/// equality inline, 9b3 Task 12).
proof fn lemma_cat_assoc3(o: Seq<u8>, a: Seq<u8>, b: Seq<u8>, v: Seq<u8>)
    ensures
        o.add(a) + b + v == o + (a + (b + v)),
{
    assert(o.add(a) + b + v =~= o + (a + (b + v)));
}

/// `encode_literal_line`'s bytes.
proof fn lemma_literal_out(o: Seq<u8>, out: Seq<u8>, name: Seq<u8>, value: Seq<u8>)
    requires
        name.len() <= PREFIX_INT_MAX,
        value.len() <= PREFIX_INT_MAX,
        out == o + spec_prefix_int_bytes(3, 0x20, name.len() as u64) + name + spec_prefix_int_bytes(
            7,
            0x00,
            value.len() as u64,
        ) + value,
    ensures
        out.len() > o.len(),
        name.len() < 128 && value.len() < 128 ==> out.len() <= o.len() + 260,
        out.subrange(0, o.len() as int) == o,
        rfc_field_line(out.skip(o.len() as int)) == Some(((name, value), (out.len() - o.len()) as nat)),
{
    hide(rfc_field_line);
    lemma_literal_line_len(name, value);
    let e = (spec_prefix_int_bytes(3, 0x20, name.len() as u64) + name) + (spec_prefix_int_bytes(
        7,
        0x00,
        value.len() as u64,
    ) + value);
    assert(out =~= o + e);
    lemma_literal_line(name, value);
    lemma_line_out(o, out, e, (name, value));
}

/// The flag bytes the encoders pass to `serialize_prefix_int` fit their prefixes.
proof fn lemma_enc_flags()
    ensures
        0xc0u8 as nat % pow2(6) == 0,
        0x50u8 as nat % pow2(4) == 0,
        0x20u8 as nat % pow2(3) == 0,
        0x00u8 as nat % pow2(7) == 0,
{
    lemma2_to64();
}

// `f` appears only in the spec, which a plain `cargo build` erases.
#[allow(unused_variables)]
fn encode_exact_line(f: &FieldLine, i: u64, out: &mut Vec<u8>)
    requires
        i < STATIC_TABLE_LEN,
        spec_static_entry(i as nat) == Some((f.name@, f.value@)),
    ensures
        final(out)@.len() > old(out)@.len(),
        f.name@.len() < 128 && f.value@.len() < 128 ==> final(out)@.len() <= old(out)@.len() + 260,
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        rfc_field_line(final(out)@.skip(old(out)@.len() as int)) == Some(
            (f@, (final(out)@.len() - old(out)@.len()) as nat),
        ),
{
    hide(rfc_field_line);
    hide(spec_prefix_int_bytes);
    let ghost o = out@;
    proof {
        lemma_enc_flags();
    }
    serialize_prefix_int(6, 0xc0, i, out);
    proof {
        lemma_exact_out(o, out@, i, f@);
    }
}

fn encode_name_line(f: &FieldLine, i: u64, out: &mut Vec<u8>)
    requires
        i < STATIC_TABLE_LEN,
        spec_name_is(i as nat, f.name@),
        f.value@.len() <= PREFIX_INT_MAX,
    ensures
        final(out)@.len() > old(out)@.len(),
        f.name@.len() < 128 && f.value@.len() < 128 ==> final(out)@.len() <= old(out)@.len() + 260,
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        rfc_field_line(final(out)@.skip(old(out)@.len() as int)) == Some(
            (f@, (final(out)@.len() - old(out)@.len()) as nat),
        ),
{
    hide(rfc_field_line);
    hide(spec_prefix_int_bytes);
    let ghost o = out@;
    proof {
        lemma_enc_flags();
    }
    serialize_prefix_int(4, 0x50, i, out);
    encode_string(7, 0x00, f.value.as_slice(), out);
    proof {
        lemma_name_out(o, out@, i, f.name@, f.value@);
    }
}

fn encode_literal_line(f: &FieldLine, out: &mut Vec<u8>)
    requires
        f.name@.len() <= PREFIX_INT_MAX,
        f.value@.len() <= PREFIX_INT_MAX,
    ensures
        final(out)@.len() > old(out)@.len(),
        f.name@.len() < 128 && f.value@.len() < 128 ==> final(out)@.len() <= old(out)@.len() + 260,
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        rfc_field_line(final(out)@.skip(old(out)@.len() as int)) == Some(
            (f@, (final(out)@.len() - old(out)@.len()) as nat),
        ),
{
    hide(rfc_field_line);
    hide(spec_prefix_int_bytes);
    let ghost o = out@;
    proof {
        lemma_enc_flags();
    }
    encode_string(3, 0x20, f.name.as_slice(), out);
    encode_string(7, 0x00, f.value.as_slice(), out);
    proof {
        lemma_literal_out(o, out@, f.name@, f.value@);
    }
}

fn encode_field_line(f: &FieldLine, out: &mut Vec<u8>)
    requires
        f.name@.len() <= PREFIX_INT_MAX,
        f.value@.len() <= PREFIX_INT_MAX,
    ensures
        final(out)@.len() > old(out)@.len(),
        f.name@.len() < 128 && f.value@.len() < 128 ==> final(out)@.len() <= old(out)@.len() + 260,
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        rfc_field_line(final(out)@.skip(old(out)@.len() as int)) == Some(
            (f@, (final(out)@.len() - old(out)@.len()) as nat),
        ),
{
    match find_static(f.name.as_slice(), f.value.as_slice()) {
        StaticMatch::Exact(i) => encode_exact_line(f, i, out),
        StaticMatch::Name(i) => encode_name_line(f, i, out),
        StaticMatch::None => encode_literal_line(f, out),
    }
}

/// One step of `encode_field_section`: the line appended after `base + enc` extends the decoded lines by `f`.
proof fn lemma_section_step(
    base: Seq<u8>,
    enc: Seq<u8>,
    out: Seq<u8>,
    lines: Seq<(Seq<u8>, Seq<u8>)>,
    f: (Seq<u8>, Seq<u8>),
)
    requires
        out.len() > (base + enc).len(),
        out.subrange(0, (base + enc).len() as int) == base + enc,
        rfc_field_line(out.skip((base + enc).len() as int)) == Some((f, (out.len() - (base + enc).len()) as nat)),
        rfc_field_lines(enc) == Some(lines),
    ensures
        out == base + (enc + out.skip((base + enc).len() as int)),
        rfc_field_lines(enc + out.skip((base + enc).len() as int)) == Some(lines.push(f)),
{
    hide(rfc_field_line);
    hide(rfc_field_lines);
    let e = out.skip((base + enc).len() as int);
    lemma_one_line(e, f);
    lemma_field_lines_append(enc, e);
    let n = (base + enc).len() as int;
    assert(out =~= out.subrange(0, n) + out.skip(n));
    assert((base + enc) + e =~= base + (enc + e));
    assert(lines + seq![f] =~= lines.push(f));
}

/// `encode_field_section`'s end: the two-byte prefix then the lines decode to `lines`.
proof fn lemma_section_out(o: Seq<u8>, enc: Seq<u8>, out: Seq<u8>, lines: Seq<(Seq<u8>, Seq<u8>)>)
    requires
        out == o + seq![0u8, 0u8] + enc,
        rfc_field_lines(enc) == Some(lines),
    ensures
        out.subrange(0, o.len() as int) == o,
        rfc_decode_field_section(out.skip(o.len() as int)) == Ok::<_, u64>(lines),
{
    hide(rfc_field_lines);
    hide(rfc_prefix_int);
    let b = seq![0u8, 0u8] + enc;
    assert(out.skip(o.len() as int) =~= b);
    assert(out.subrange(0, o.len() as int) =~= o);
    assert(b[0] == 0u8 && b.skip(1)[0] == 0u8);
    assert(b.skip(1).skip(1) =~= enc);
    lemma_prefix_zero(8, b);
    lemma_prefix_zero(7, b.skip(1));
    assert(0u8 & 0x80u8 == 0) by (bit_vector);
}

/// A zero first byte is the prefix integer 0 in one byte.
proof fn lemma_prefix_zero(n: u8, b: Seq<u8>)
    requires
        1 <= n <= 8,
        b.len() > 0,
        b[0] == 0u8,
    ensures
        rfc_prefix_int(n, b) == (PrefixIntSpec::Value { value: 0, consumed: 1 }),
{
    lemma2_to64();
}

/// The empty encoding decodes to no lines.
proof fn lemma_lines_empty()
    ensures
        rfc_field_lines(Seq::<u8>::empty()) == Some(Seq::<(Seq<u8>, Seq<u8>)>::empty()),
{
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
        (forall|i: int|
            0 <= i < fields@.len() ==> #[trigger] fields@[i].name@.len() < 128
                && fields@[i].value@.len() < 128) ==> final(out)@.len() <= old(out)@.len() + 2
            + 260 * fields@.len(),
{
    hide(rfc_field_line);
    hide(rfc_field_lines);
    hide(rfc_decode_field_section);
    out.push(0);
    out.push(0);
    let ghost mut enc: Seq<u8> = Seq::empty();
    proof {
        assert(out@ =~= old(out)@ + seq![0u8, 0u8] + enc);
        assert(fields_view(fields@.take(0)) =~= Seq::empty());
        lemma_lines_empty();
    }
    let mut i: usize = 0;
    while i < fields.len()
        invariant
            i <= fields@.len(),
            out@ == old(out)@ + seq![0u8, 0u8] + enc,
            rfc_field_lines(enc) == Some(fields_view(fields@.take(i as int))),
            enc.len() <= 260 * i || !(forall|j: int|
                0 <= j < fields@.len() ==> #[trigger] fields@[j].name@.len() < 128
                    && fields@[j].value@.len() < 128),
            forall|j: int|
                0 <= j < fields@.len() ==> #[trigger] fields@[j].name@.len() <= PREFIX_INT_MAX
                    && fields@[j].value@.len() <= PREFIX_INT_MAX,
        decreases fields.len() - i,
    {
        let ghost before = out@;
        encode_field_line(&fields[i], out);
        proof {
            let base = old(out)@ + seq![0u8, 0u8];
            let f = fields@[i as int];
            lemma_section_step(base, enc, out@, fields_view(fields@.take(i as int)), f@);
            enc = enc + out@.skip(before.len() as int);
            assert(fields_view(fields@.take(i + 1)) =~= fields_view(fields@.take(i as int)).push(f@));
        }
        i += 1;
    }
    proof {
        assert(fields@.take(fields@.len() as int) =~= fields@);
        lemma_section_out(old(out)@, enc, out@, fields_view(fields@));
    }
}

} // verus!
