//! QPACK encoder- and decoder-stream instructions at dynamic table capacity 0 (RFC 9204
//! §4.3, §4.4): RFC-derived specs, executable stream scanners, and proofs that the two agree.
//!
//! We advertise SETTINGS_QPACK_MAX_TABLE_CAPACITY = 0 and never send dynamic references, so
//! the only valid peer instructions are Set Dynamic Table Capacity 0 (encoder stream) and
//! Stream Cancellation (decoder stream). Our own encoder side is silent by construction: this
//! crate has no encoder-instruction serializer.

//= https://www.rfc-editor.org/rfc/rfc9204#section-3.2.3
//# When the maximum table capacity is zero, the encoder MUST NOT insert
//# entries into the dynamic table and MUST NOT send any encoder
//# instructions on the encoder stream.
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

use crate::codes::*;
use crate::qpack::int::*;

verus! {

/// `Ok(n)`: `b[..n]` is a sequence of complete valid instructions and `b[n..]` is a strict
/// prefix of one instruction (or empty). `Err(code)`: the stream is a connection error.
pub open spec fn add_ok(r: Result<nat, u64>, n: nat) -> Result<nat, u64> {
    match r {
        Ok(m) => Ok(m + n),
        Err(c) => Err(c),
    }
}

pub open spec fn result_view(r: Result<usize, u64>) -> Result<nat, u64> {
    match r {
        Ok(n) => Ok(n as nat),
        Err(c) => Err(c),
    }
}

// =============================================================================
// Lemmas
// =============================================================================

proof fn lemma_add_ok_zero(r: Result<nat, u64>)
    ensures
        add_ok(r, 0) == r,
{
}

proof fn lemma_skip_skip(b: Seq<u8>, i: int, j: int)
    requires
        0 <= i <= b.len(),
        0 <= j <= b.len() - i,
    ensures
        b.skip(i).skip(j) == b.skip(i + j),
{
    assert(b.skip(i).skip(j) =~= b.skip(i + j));
}

// =============================================================================
// Encoder stream (RFC 9204 §4.3)
// =============================================================================

#[verifier::decreases_by]
proof fn encoder_stream_decreases(b: Seq<u8>) {
    lemma_prefix_int_consumed(5, b);
}

//= https://www.rfc-editor.org/rfc/rfc9204#section-4.3.1
//# The decoder MUST treat a new dynamic table capacity
//# value that exceeds this limit as a connection error of type
//# QPACK_ENCODER_STREAM_ERROR.
//= https://www.rfc-editor.org/rfc/rfc9204#section-3.2.2
//# It is an error if the encoder attempts to add an
//# entry that is larger than the dynamic table capacity; the decoder
//# MUST treat this as a connection error of type
//# QPACK_ENCODER_STREAM_ERROR.
//= https://www.rfc-editor.org/rfc/rfc9204#section-2.2.3
//# If the decoder encounters a reference in an encoder instruction to a
//# dynamic table entry that has already been evicted, it MUST treat this
//# as a connection error of type QPACK_ENCODER_STREAM_ERROR.
/// Capacity is 0 (the limit we advertised), so: Insert With Name Reference (`1…`) and Insert
/// With Literal Name (`01…`) are always oversized, Duplicate (`000…`) always references an
/// evicted (nonexistent) entry, and Set Dynamic Table Capacity (`001…`) is valid only with
/// value 0. Insert and Duplicate are errors from their first byte.
pub open spec fn rfc_encoder_stream(b: Seq<u8>) -> Result<nat, u64>
    decreases b.len(),
    via encoder_stream_decreases
{
    if b.len() == 0 {
        Ok(0)
    } else if b[0] & 0xE0u8 != 0x20u8 {
        Err(QPACK_ENCODER_STREAM_ERROR)
    } else {
        match rfc_prefix_int(5, b) {
            PrefixIntSpec::Incomplete => Ok(0),
            PrefixIntSpec::TooLarge => Err(QPACK_ENCODER_STREAM_ERROR),
            PrefixIntSpec::Value { value, consumed } => if value > 0 {
                Err(QPACK_ENCODER_STREAM_ERROR)
            } else {
                add_ok(rfc_encoder_stream(b.skip(consumed as int)), consumed)
            },
        }
    }
}

/// Scans the peer's encoder-stream bytes; see `rfc_encoder_stream`.
pub fn process_encoder_stream(buf: &[u8]) -> (r: Result<usize, u64>)
    ensures
        result_view(r) == rfc_encoder_stream(buf@),
{
    let mut pos: usize = 0;
    proof {
        assert(buf@.skip(0) =~= buf@);
        lemma_add_ok_zero(rfc_encoder_stream(buf@));
    }
    loop
        invariant
            pos <= buf.len(),
            rfc_encoder_stream(buf@) == add_ok(rfc_encoder_stream(buf@.skip(pos as int)), pos as nat),
        decreases buf.len() - pos,
    {
        if pos == buf.len() {
            proof {
                assert(buf@.skip(pos as int).len() == 0);
            }
            return Ok(pos);
        }
        if buf[pos] & 0xE0 != 0x20 {
            return Err(QPACK_ENCODER_STREAM_ERROR);
        }
        let rest = slice_subrange(buf, pos, buf.len());
        proof {
            assert(rest@ =~= buf@.skip(pos as int));
            lemma_prefix_int_consumed(5, rest@);
        }
        match parse_prefix_int(5, rest) {
            PrefixInt::Incomplete => return Ok(pos),
            PrefixInt::TooLarge => return Err(QPACK_ENCODER_STREAM_ERROR),
            PrefixInt::Value { value, consumed } => {
                if value > 0 {
                    return Err(QPACK_ENCODER_STREAM_ERROR);
                }
                proof {
                    lemma_skip_skip(buf@, pos as int, consumed as int);
                }
                pos += consumed;
            },
        }
    }
}

/// Split: once `b` scans to `Ok(n)`, bytes appended after it are scanned as if the first `n`
/// (complete instructions) were gone.
pub proof fn lemma_encoder_stream_split(b: Seq<u8>, t: Seq<u8>)
    requires
        rfc_encoder_stream(b) is Ok,
    ensures
        ({
            let n = rfc_encoder_stream(b)->Ok_0;
            &&& n <= b.len()
            &&& rfc_encoder_stream(b + t) == add_ok(rfc_encoder_stream(b.skip(n as int) + t), n)
        }),
    decreases b.len(),
{
    assert(b.skip(0) =~= b);
    if b.len() > 0 && b[0] & 0xE0u8 == 0x20u8 {
        assert((b + t)[0] == b[0]);
        lemma_prefix_int_consumed(5, b);
        if let PrefixIntSpec::Value { value: _, consumed: c } = rfc_prefix_int(5, b) {
            lemma_prefix_int_append(5, b, t);
            let s = b.skip(c as int);
            lemma_encoder_stream_split(s, t);
            let m = rfc_encoder_stream(s)->Ok_0;
            assert((b + t).skip(c as int) =~= s + t);
            lemma_skip_skip(b, c as int, m as int);
        }
    } else if b.len() == 0 {
        assert(b + t =~= t);
    }
}

// =============================================================================
// Decoder stream (RFC 9204 §4.4)
// =============================================================================

#[verifier::decreases_by]
proof fn decoder_stream_decreases(b: Seq<u8>) {
    lemma_prefix_int_consumed(6, b);
}

//= https://www.rfc-editor.org/rfc/rfc9204#section-4.4.1
//# If an encoder receives a Section Acknowledgment instruction referring
//# to a stream on which every encoded field section with a non-zero
//# Required Insert Count has already been acknowledged, this MUST be
//# treated as a connection error of type QPACK_DECODER_STREAM_ERROR.
//= https://www.rfc-editor.org/rfc/rfc9204#section-4.4.3
//# An encoder that receives an Increment field equal to zero, or one
//# that increases the Known Received Count beyond what the encoder has
//# sent, MUST treat this as a connection error of type
//# QPACK_DECODER_STREAM_ERROR.
/// We emit no dynamic references and no insertions, so Section Acknowledgment (`1…`) has no
/// stream to acknowledge and Insert Count Increment (`00…`) always exceeds the 0 we sent;
/// both are errors from their first byte. Stream Cancellation (`01…`, 6-bit stream ID) is
/// valid once complete.
pub open spec fn rfc_decoder_stream(b: Seq<u8>) -> Result<nat, u64>
    decreases b.len(),
    via decoder_stream_decreases
{
    if b.len() == 0 {
        Ok(0)
    } else if b[0] & 0xC0u8 != 0x40u8 {
        Err(QPACK_DECODER_STREAM_ERROR)
    } else {
        match rfc_prefix_int(6, b) {
            PrefixIntSpec::Incomplete => Ok(0),
            PrefixIntSpec::TooLarge => Err(QPACK_DECODER_STREAM_ERROR),
            PrefixIntSpec::Value { value, consumed } => add_ok(
                rfc_decoder_stream(b.skip(consumed as int)),
                consumed,
            ),
        }
    }
}

/// Scans the peer's decoder-stream bytes; see `rfc_decoder_stream`.
pub fn process_decoder_stream(buf: &[u8]) -> (r: Result<usize, u64>)
    ensures
        result_view(r) == rfc_decoder_stream(buf@),
{
    let mut pos: usize = 0;
    proof {
        assert(buf@.skip(0) =~= buf@);
        lemma_add_ok_zero(rfc_decoder_stream(buf@));
    }
    loop
        invariant
            pos <= buf.len(),
            rfc_decoder_stream(buf@) == add_ok(rfc_decoder_stream(buf@.skip(pos as int)), pos as nat),
        decreases buf.len() - pos,
    {
        if pos == buf.len() {
            proof {
                assert(buf@.skip(pos as int).len() == 0);
            }
            return Ok(pos);
        }
        if buf[pos] & 0xC0 != 0x40 {
            return Err(QPACK_DECODER_STREAM_ERROR);
        }
        let rest = slice_subrange(buf, pos, buf.len());
        proof {
            assert(rest@ =~= buf@.skip(pos as int));
            lemma_prefix_int_consumed(6, rest@);
        }
        match parse_prefix_int(6, rest) {
            PrefixInt::Incomplete => return Ok(pos),
            PrefixInt::TooLarge => return Err(QPACK_DECODER_STREAM_ERROR),
            PrefixInt::Value { value: _, consumed } => {
                proof {
                    lemma_skip_skip(buf@, pos as int, consumed as int);
                }
                pos += consumed;
            },
        }
    }
}

/// Split: once `b` scans to `Ok(n)`, bytes appended after it are scanned as if the first `n`
/// (complete instructions) were gone.
pub proof fn lemma_decoder_stream_split(b: Seq<u8>, t: Seq<u8>)
    requires
        rfc_decoder_stream(b) is Ok,
    ensures
        ({
            let n = rfc_decoder_stream(b)->Ok_0;
            &&& n <= b.len()
            &&& rfc_decoder_stream(b + t) == add_ok(rfc_decoder_stream(b.skip(n as int) + t), n)
        }),
    decreases b.len(),
{
    assert(b.skip(0) =~= b);
    if b.len() > 0 && b[0] & 0xC0u8 == 0x40u8 {
        assert((b + t)[0] == b[0]);
        lemma_prefix_int_consumed(6, b);
        if let PrefixIntSpec::Value { value: _, consumed: c } = rfc_prefix_int(6, b) {
            lemma_prefix_int_append(6, b, t);
            let s = b.skip(c as int);
            lemma_decoder_stream_split(s, t);
            let m = rfc_decoder_stream(s)->Ok_0;
            assert((b + t).skip(c as int) =~= s + t);
            lemma_skip_skip(b, c as int, m as int);
        }
    } else if b.len() == 0 {
        assert(b + t =~= t);
    }
}

} // verus!
