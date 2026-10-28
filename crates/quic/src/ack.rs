//! ACK frames (RFC 9000 §19.3): Largest Acknowledged, ACK Delay, the ranges, and the ECN
//! counts of type 0x03. `parse_ack` starts after the frame type, which the frame dispatcher
//! has already read.
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use vest_lib::core::spec::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;
use wire::varint::*;

use crate::codes::*;

verus! {

#[derive(Debug, PartialEq, Eq)]
pub struct AckFrame {
    pub largest: u64,
    pub delay: u64,
    pub first_range: u64,
    /// (Gap, ACK Range Length) pairs in wire order.
    pub ranges: Vec<(u64, u64)>,
    /// (ECT0, ECT1, ECN-CE) counts; present iff the type is 0x03.
    pub ecn: Option<(u64, u64, u64)>,
}

pub struct SpecAck {
    pub largest: u64,
    pub delay: u64,
    pub first_range: u64,
    pub ranges: Seq<(u64, u64)>,
    pub ecn: Option<(u64, u64, u64)>,
}

impl View for AckFrame {
    type V = SpecAck;

    open spec fn view(&self) -> SpecAck {
        SpecAck {
            largest: self.largest,
            delay: self.delay,
            first_range: self.first_range,
            ranges: self.ranges@,
            ecn: self.ecn,
        }
    }
}

// =============================================================================
// RFC 9000 transcription
// =============================================================================

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.3.1
//# The largest value for an ACK Range is determined by cumulatively
//# subtracting the size of all preceding ACK Range Lengths and Gaps.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.3.1
//# The value of the Gap field establishes the largest packet number
//# value for the subsequent ACK Range using the following formula:
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.3.1
//# Thus, given a largest
//# packet number for the range, the smallest value is determined by the
//# following formula:
/// The smallest packet number of the last range in `ranges`, walking down from `s0`, the
/// smallest of the First ACK Range: each `(gap, len)` gives `largest = smallest - gap - 2`
/// and then `smallest = largest - len`.
pub open spec fn spec_ack_smallest(s0: int, ranges: Seq<(u64, u64)>) -> int
    decreases ranges.len(),
{
    if ranges.len() == 0 {
        s0
    } else {
        let x = ranges.last();
        spec_ack_smallest(s0, ranges.drop_last()) - x.0 - 2 - x.1
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.3.1
//# If any computed packet number is negative, an endpoint MUST generate
//# a connection error of type FRAME_ENCODING_ERROR.
/// Every `largest` and `smallest` the walk from `s0` computes is non-negative.
pub open spec fn rfc_ack_ranges_from(s0: int, ranges: Seq<(u64, u64)>) -> bool
    decreases ranges.len(),
{
    if ranges.len() == 0 {
        true
    } else {
        let x = ranges.last();
        let largest = spec_ack_smallest(s0, ranges.drop_last()) - x.0 - 2;
        &&& rfc_ack_ranges_from(s0, ranges.drop_last())
        &&& largest >= 0
        &&& largest - x.1 >= 0
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.3
//# That is, the smallest packet acknowledged in
//# the range is determined by subtracting the First ACK Range value
//# from the Largest Acknowledged field.
pub open spec fn rfc_ack_ranges_valid(largest: u64, first_range: u64, ranges: Seq<(u64, u64)>) -> bool {
    first_range <= largest && rfc_ack_ranges_from(largest - first_range, ranges)
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.3.1
//# An ACK Range acknowledges all packets between the smallest packet
//# number and the largest, inclusive.
/// Range `i` as `(smallest, largest)`; range -1 is the First ACK Range.
pub open spec fn ack_range(a: SpecAck, i: int) -> (int, int) {
    let s0 = a.largest - a.first_range;
    if i < 0 {
        (s0, a.largest as int)
    } else {
        let hi = spec_ack_smallest(s0, a.ranges.take(i)) - a.ranges[i].0 - 2;
        (hi - a.ranges[i].1, hi)
    }
}

/// `a` acknowledges `pn`. Meaningful only for a frame with valid ranges, which every
/// `rfc_ack` result has; otherwise a computed bound can be negative.
pub open spec fn ack_contains(a: SpecAck, pn: u64) -> bool
    recommends
        rfc_ack_ranges_valid(a.largest, a.first_range, a.ranges),
{
    exists|i: int|
        -1 <= i < a.ranges.len() && (#[trigger] ack_range(a, i)).0 <= pn <= ack_range(a, i).1
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.3.1
//# The number of Gap and ACK Range Length values is
//# determined by the ACK Range Count field; one of each value is present
//# for each value in the ACK Range Count field.
/// `count` (Gap, ACK Range Length) pairs from offset `p`, with the offset after them; `None`
/// when the bytes run out first.
pub open spec fn rfc_ack_pairs(b: Seq<u8>, p: int, count: nat) -> Option<(Seq<(u64, u64)>, int)>
    decreases count,
{
    if count == 0 {
        Some((Seq::empty(), p))
    } else {
        match rfc_varint_decode(b.skip(p)) {
            None => None,
            Some((n1, gap)) => match rfc_varint_decode(b.skip(p + n1)) {
                None => None,
                Some((n2, len)) => match rfc_ack_pairs(b, p + n1 + n2, (count - 1) as nat) {
                    None => None,
                    Some((rest, q)) => Some((seq![(gap, len)] + rest, q)),
                },
            },
        }
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.3.2
//# ECN counts are only present when the ACK
//# frame type is 0x03.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.3.2
//# When present, there are three ECN counts, as shown in Figure 27.
/// ECT0, ECT1 and ECN-CE from offset `p`, with the offset after them.
pub open spec fn rfc_ecn(b: Seq<u8>, p: int) -> Option<((u64, u64, u64), int)> {
    match rfc_varint_decode(b.skip(p)) {
        None => None,
        Some((n1, e0)) => match rfc_varint_decode(b.skip(p + n1)) {
            None => None,
            Some((n2, e1)) => match rfc_varint_decode(b.skip(p + n1 + n2)) {
                None => None,
                Some((n3, ce)) => Some(((e0, e1, ce), p + n1 + n2 + n3)),
            },
        },
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.3
//# QUIC implementations MUST properly handle both
//# types, and, if they have enabled ECN for packets they send, they
//# SHOULD use the information in the ECN section to manage their
//# congestion state.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.3
//# ACK Range Count:  A variable-length integer specifying the number of
//# ACK Range fields in the frame.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-20.1
//# FRAME_ENCODING_ERROR (0x07):  An endpoint received a frame that was
//# badly formatted -- for instance, a frame of an unknown type or an
//# ACK frame that has more acknowledgment ranges than the remainder
//# of the packet could carry.
/// An ACK frame of type `ty` (0x02 or 0x03) from `b`, which starts after the type, with the
/// bytes consumed. A missing field or an invalid range is FRAME_ENCODING_ERROR. Using the
/// ECN counts for congestion control is phase 6's job.
pub open spec fn rfc_ack(ty: u64, b: Seq<u8>) -> Result<(SpecAck, nat), u64> {
    match rfc_varint_decode(b) {
        None => Err(FRAME_ENCODING_ERROR),
        Some((n1, largest)) => match rfc_varint_decode(b.skip(n1 as int)) {
            None => Err(FRAME_ENCODING_ERROR),
            Some((n2, delay)) => match rfc_varint_decode(b.skip((n1 + n2) as int)) {
                None => Err(FRAME_ENCODING_ERROR),
                Some((n3, count)) => match rfc_varint_decode(b.skip((n1 + n2 + n3) as int)) {
                    None => Err(FRAME_ENCODING_ERROR),
                    Some((n4, first_range)) => match rfc_ack_pairs(
                        b,
                        (n1 + n2 + n3 + n4) as int,
                        count as nat,
                    ) {
                        None => Err(FRAME_ENCODING_ERROR),
                        Some((ranges, q)) => if !rfc_ack_ranges_valid(largest, first_range, ranges) {
                            Err(FRAME_ENCODING_ERROR)
                        } else if ty == FRAME_ACK_ECN {
                            match rfc_ecn(b, q) {
                                None => Err(FRAME_ENCODING_ERROR),
                                Some((ecn, e)) => Ok(
                                    (
                                        SpecAck { largest, delay, first_range, ranges, ecn: Some(ecn) },
                                        e as nat,
                                    ),
                                ),
                            }
                        } else {
                            Ok((SpecAck { largest, delay, first_range, ranges, ecn: None }, q as nat))
                        },
                    },
                },
            },
        },
    }
}

// =============================================================================
// Serialization specs
// =============================================================================

/// Every field fits a varint, the range count included.
pub open spec fn ack_encodable(a: SpecAck) -> bool {
    &&& a.largest <= VARINT_MAX
    &&& a.delay <= VARINT_MAX
    &&& a.first_range <= VARINT_MAX
    &&& a.ranges.len() <= VARINT_MAX
    &&& forall|i: int|
        0 <= i < a.ranges.len() ==> (#[trigger] a.ranges[i]).0 <= VARINT_MAX && a.ranges[i].1
            <= VARINT_MAX
    &&& a.ecn matches Some((e0, e1, ce)) ==> e0 <= VARINT_MAX && e1 <= VARINT_MAX && ce
        <= VARINT_MAX
}

pub open spec fn spec_ack_type(a: SpecAck) -> u64 {
    if a.ecn is Some {
        FRAME_ACK_ECN
    } else {
        FRAME_ACK
    }
}

pub open spec fn spec_pair_bytes(x: (u64, u64)) -> Seq<u8> {
    spec_varint(x.0) + spec_varint(x.1)
}

pub open spec fn spec_ranges_bytes(r: Seq<(u64, u64)>) -> Seq<u8>
    decreases r.len(),
{
    if r.len() == 0 {
        Seq::empty()
    } else {
        spec_pair_bytes(r[0]) + spec_ranges_bytes(r.skip(1))
    }
}

pub open spec fn spec_ecn_bytes(ecn: Option<(u64, u64, u64)>) -> Seq<u8> {
    match ecn {
        Some((e0, e1, ce)) => spec_varint(e0) + spec_varint(e1) + spec_varint(ce),
        None => Seq::empty(),
    }
}

/// Everything after the type.
pub open spec fn spec_ack_body(a: SpecAck) -> Seq<u8> {
    spec_varint(a.largest) + (spec_varint(a.delay) + (spec_varint(a.ranges.len() as u64) + (
    spec_varint(a.first_range) + (spec_ranges_bytes(a.ranges) + spec_ecn_bytes(a.ecn)))))
}

/// The whole frame, type included.
pub open spec fn spec_ack_bytes(a: SpecAck) -> Seq<u8> {
    spec_varint(spec_ack_type(a)) + spec_ack_body(a)
}

// =============================================================================
// Proofs
// =============================================================================

/// A walk invalid on a prefix stays invalid however it continues.
proof fn lemma_ranges_prefix(s0: int, s: Seq<(u64, u64)>, t: Seq<(u64, u64)>)
    requires
        rfc_ack_ranges_from(s0, s + t),
    ensures
        rfc_ack_ranges_from(s0, s),
    decreases t.len(),
{
    if t.len() > 0 {
        assert((s + t).drop_last() =~= s + t.drop_last());
        lemma_ranges_prefix(s0, s, t.drop_last());
    } else {
        assert(s + t =~= s);
    }
}

/// The minimal varint of `v` at offset `p` reads back, and the bytes after it are `tail`.
pub(crate) proof fn lemma_varint_at(b: Seq<u8>, p: int, v: u64, tail: Seq<u8>)
    requires
        0 <= p <= b.len(),
        v <= VARINT_MAX,
        b.skip(p) == spec_varint(v) + tail,
    ensures
        rfc_varint_decode(b.skip(p)) == Some((spec_varint(v).len(), v)),
        1 <= spec_varint(v).len() <= 8,
        b.skip(p + spec_varint(v).len()) == tail,
{
    theorem_serialize_matches_rfc(v);
    lemma_decode_prefix(spec_varint(v), tail);
    lemma_decode_len_bounds(spec_varint(v));
    let n = spec_varint(v).len() as int;
    assert forall|i: int| 0 <= i < tail.len() implies b.skip(p + n)[i] == tail[i] by {
        assert(b.skip(p)[n + i] == b[p + n + i]);
    }
    assert(b.skip(p + n) =~= tail);
}

proof fn lemma_ranges_parse(b: Seq<u8>, p: int, r: Seq<(u64, u64)>, tail: Seq<u8>)
    requires
        0 <= p <= b.len(),
        b.skip(p) == spec_ranges_bytes(r) + tail,
        forall|i: int|
            0 <= i < r.len() ==> (#[trigger] r[i]).0 <= VARINT_MAX && r[i].1 <= VARINT_MAX,
    ensures
        rfc_ack_pairs(b, p, r.len()) == Some((r, p + spec_ranges_bytes(r).len())),
        b.skip(p + spec_ranges_bytes(r).len()) == tail,
    decreases r.len(),
{
    if r.len() == 0 {
        assert(r =~= Seq::<(u64, u64)>::empty());
        assert(spec_ranges_bytes(r) + tail =~= tail);
    } else {
        let (g, l) = r[0];
        let r1 = r.skip(1);
        let rb1 = spec_ranges_bytes(r1);
        assert(b.skip(p) =~= spec_varint(g) + (spec_varint(l) + (rb1 + tail)));
        lemma_varint_at(b, p, g, spec_varint(l) + (rb1 + tail));
        let p1 = p + spec_varint(g).len();
        lemma_varint_at(b, p1, l, rb1 + tail);
        let p2 = p1 + spec_varint(l).len();
        assert forall|i: int| 0 <= i < r1.len() implies (#[trigger] r1[i]).0 <= VARINT_MAX
            && r1[i].1 <= VARINT_MAX by {
            assert(r1[i] == r[i + 1]);
        }
        lemma_ranges_parse(b, p2, r1, tail);
        assert(seq![(g, l)] + r1 =~= r);
    }
}

proof fn lemma_ranges_bytes_snoc(s: Seq<(u64, u64)>, x: (u64, u64))
    ensures
        spec_ranges_bytes(s.push(x)) == spec_ranges_bytes(s) + spec_pair_bytes(x),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.push(x)[0] == x);
        assert(s.push(x).skip(1) =~= Seq::<(u64, u64)>::empty());
        assert(spec_ranges_bytes(s) == Seq::<u8>::empty());
        assert(spec_ranges_bytes(Seq::<(u64, u64)>::empty()) == Seq::<u8>::empty());
        assert(spec_pair_bytes(x) + Seq::empty() =~= Seq::<u8>::empty() + spec_pair_bytes(x));
    } else {
        assert(s.push(x)[0] == s[0]);
        assert(s.push(x).skip(1) =~= s.skip(1).push(x));
        lemma_ranges_bytes_snoc(s.skip(1), x);
        assert(spec_pair_bytes(s[0]) + (spec_ranges_bytes(s.skip(1)) + spec_pair_bytes(x))
            =~= spec_pair_bytes(s[0]) + spec_ranges_bytes(s.skip(1)) + spec_pair_bytes(x));
    }
}

/// Every field of `spec_ack_body(a) + rest` reads back where `rfc_ack` looks for it.
proof fn lemma_ack_layout(a: SpecAck, rest: Seq<u8>)
    requires
        ack_encodable(a),
    ensures
        ({
            let b = spec_ack_body(a) + rest;
            let n1 = spec_varint(a.largest).len();
            let n2 = spec_varint(a.delay).len();
            let n3 = spec_varint(a.ranges.len() as u64).len();
            let n4 = spec_varint(a.first_range).len();
            let q = n1 + n2 + n3 + n4 + spec_ranges_bytes(a.ranges).len();
            &&& rfc_varint_decode(b) == Some((n1, a.largest))
            &&& rfc_varint_decode(b.skip(n1 as int)) == Some((n2, a.delay))
            &&& rfc_varint_decode(b.skip((n1 + n2) as int)) == Some((n3, a.ranges.len() as u64))
            &&& rfc_varint_decode(b.skip((n1 + n2 + n3) as int)) == Some((n4, a.first_range))
            &&& rfc_ack_pairs(b, (n1 + n2 + n3 + n4) as int, a.ranges.len()) == Some(
                (a.ranges, q as int),
            )
            &&& match a.ecn {
                Some(e) => rfc_ecn(b, q as int) == Some((e, spec_ack_body(a).len() as int)),
                None => q == spec_ack_body(a).len(),
            }
        }),
{
    // Each decode fact comes from `lemma_varint_at`; unfolding the decoder only adds noise.
    hide(rfc_varint_decode);
    let cnt = a.ranges.len() as u64;
    let rb = spec_ranges_bytes(a.ranges);
    let eb = spec_ecn_bytes(a.ecn);
    // The body's suffixes: body = v(largest) + k1, k1 = v(delay) + k2, ...
    let k4 = rb + eb;
    let k3 = spec_varint(a.first_range) + k4;
    let k2 = spec_varint(cnt) + k3;
    let k1 = spec_varint(a.delay) + k2;
    let b = spec_ack_body(a) + rest;
    lemma_assoc(spec_varint(a.largest), k1, rest);
    lemma_assoc(spec_varint(a.delay), k2, rest);
    lemma_assoc(spec_varint(cnt), k3, rest);
    lemma_assoc(spec_varint(a.first_range), k4, rest);
    lemma_assoc(rb, eb, rest);
    lemma_skip0(b);
    lemma_varint_at(b, 0, a.largest, k1 + rest);
    let n1 = spec_varint(a.largest).len() as int;
    lemma_varint_at(b, n1, a.delay, k2 + rest);
    let n2 = spec_varint(a.delay).len() as int;
    lemma_varint_at(b, n1 + n2, cnt, k3 + rest);
    let n3 = spec_varint(cnt).len() as int;
    lemma_varint_at(b, n1 + n2 + n3, a.first_range, k4 + rest);
    let p = n1 + n2 + n3 + spec_varint(a.first_range).len();
    lemma_ranges_parse(b, p, a.ranges, eb + rest);
    let q = p + rb.len();
    match a.ecn {
        Some((e0, e1, ce)) => {
            let (v0, v1, v2) = (spec_varint(e0), spec_varint(e1), spec_varint(ce));
            lemma_assoc(v0 + v1, v2, rest);
            lemma_assoc(v0, v1, v2 + rest);
            lemma_varint_at(b, q, e0, v1 + (v2 + rest));
            let m1 = q + v0.len();
            lemma_varint_at(b, m1, e1, v2 + rest);
            lemma_varint_at(b, m1 + v1.len(), ce, rest);
        },
        None => {
            lemma_empty_add(rest);
        },
    }
}

pub(crate) proof fn lemma_skip0(b: Seq<u8>)
    ensures
        b.skip(0) == b,
{
    assert(b.skip(0) =~= b);
}

proof fn lemma_empty_add(b: Seq<u8>)
    ensures
        Seq::<u8>::empty() + b == b,
{
    assert(Seq::<u8>::empty() + b =~= b);
}

proof fn lemma_assoc(x: Seq<u8>, y: Seq<u8>, z: Seq<u8>)
    ensures
        (x + y) + z == x + (y + z),
{
    assert((x + y) + z =~= x + (y + z));
}

/// Every decoded varint fits in 62 bits.
pub(crate) proof fn lemma_decoded_bounded()
    ensures
        forall|s: Seq<u8>| (#[trigger] rfc_varint_decode(s)) is Some ==> rfc_varint_decode(s).unwrap().1
            <= VARINT_MAX,
{
    assert forall|s: Seq<u8>| (#[trigger] rfc_varint_decode(s)) is Some implies rfc_varint_decode(
        s,
    ).unwrap().1 <= VARINT_MAX by {
        theorem_matches_rfc(s);
        lemma_parse_bound::<false>(s);
    }
}

/// `count` pairs read back are `count` pairs of 62-bit values.
proof fn lemma_ack_pairs_bounded(b: Seq<u8>, p: int, count: nat)
    ensures
        rfc_ack_pairs(b, p, count) matches Some((r, _)) ==> r.len() == count && forall|i: int|
            0 <= i < r.len() ==> (#[trigger] r[i]).0 <= VARINT_MAX && r[i].1 <= VARINT_MAX,
    decreases count,
{
    if count > 0 {
        lemma_decoded_bounded();
        if let Some((n1, gap)) = rfc_varint_decode(b.skip(p)) {
            if let Some((n2, len)) = rfc_varint_decode(b.skip(p + n1)) {
                lemma_ack_pairs_bounded(b, p + n1 + n2, (count - 1) as nat);
                if let Some((rest, q)) = rfc_ack_pairs(b, p + n1 + n2, (count - 1) as nat) {
                    let r = seq![(gap, len)] + rest;
                    assert forall|i: int| 0 <= i < r.len() implies (#[trigger] r[i]).0
                        <= VARINT_MAX && r[i].1 <= VARINT_MAX by {
                        if i > 0 {
                            assert(r[i] == rest[i - 1]);
                        }
                    }
                }
            }
        }
    }
}

/// Every ACK frame `rfc_ack` accepts is one `serialize_ack` can write back, with ECN counts
/// exactly when the type is 0x03; every failure is FRAME_ENCODING_ERROR.
pub proof fn lemma_ack_received(ty: u64, b: Seq<u8>)
    ensures
        rfc_ack(ty, b) matches Ok((a, _)) ==> ack_encodable(a) && rfc_ack_ranges_valid(
            a.largest,
            a.first_range,
            a.ranges,
        ) && (a.ecn is Some <==> ty == FRAME_ACK_ECN),
        rfc_ack(ty, b) matches Err(e) ==> e == FRAME_ENCODING_ERROR,
{
    lemma_decoded_bounded();
    if let Some((n1, _)) = rfc_varint_decode(b) {
        if let Some((n2, _)) = rfc_varint_decode(b.skip(n1 as int)) {
            if let Some((n3, count)) = rfc_varint_decode(b.skip((n1 + n2) as int)) {
                if let Some((n4, _)) = rfc_varint_decode(b.skip((n1 + n2 + n3) as int)) {
                    lemma_ack_pairs_bounded(b, (n1 + n2 + n3 + n4) as int, count as nat);
                }
            }
        }
    }
}

/// Parsing what `serialize_ack` wrote, minus the type byte and followed by anything,
/// recovers the frame and consumes exactly its body.
pub proof fn theorem_ack_roundtrip(a: SpecAck, rest: Seq<u8>)
    requires
        ack_encodable(a),
        rfc_ack_ranges_valid(a.largest, a.first_range, a.ranges),
    ensures
        ({
            let w = spec_ack_bytes(a);
            &&& w.len() >= 1
            &&& w[0] == spec_ack_type(a)
            &&& rfc_ack(spec_ack_type(a), w.skip(1) + rest) == Ok::<(SpecAck, nat), u64>(
                (a, (w.len() - 1) as nat),
            )
        }),
{
    let ty = spec_ack_type(a);
    lemma_serialize_bytes::<true>(ty);
    assert(spec_varint(ty) =~= seq![ty as u8]);
    assert(spec_ack_bytes(a).skip(1) =~= spec_ack_body(a));
    lemma_ack_layout(a, rest);
}

// =============================================================================
// Executable code
// =============================================================================

/// The varint at offset `off`.
pub(crate) fn varint_at(b: &[u8], off: usize) -> (r: Option<(usize, u64)>)
    requires
        off <= b.len(),
    ensures
        match r {
            Some((n, v)) => {
                &&& rfc_varint_decode(b@.skip(off as int)) == Some((n as nat, v))
                &&& 1 <= n <= b.len() - off
                &&& v <= VARINT_MAX
            },
            None => rfc_varint_decode(b@.skip(off as int)) is None,
        },
{
    let t = slice_subrange(b, off, b.len());
    proof {
        assert(t@ =~= b@.skip(off as int));
        theorem_matches_rfc(t@);
        lemma_parse_bound::<false>(t@);
    }
    parse_varint(t)
}

/// An ACK frame of type `ty` from `b`, which starts after the type, with the bytes consumed.
pub fn parse_ack(ty: u64, b: &[u8]) -> (r: Result<(AckFrame, usize), u64>)
    requires
        ty == FRAME_ACK || ty == FRAME_ACK_ECN,
    ensures
        match r {
            Ok((f, n)) => rfc_ack(ty, b@) == Ok::<(SpecAck, nat), u64>((f@, n as nat)) && n
                <= b.len(),
            Err(e) => rfc_ack(ty, b@) == Err::<(SpecAck, nat), u64>(e),
        },
{
    proof {
        assert(b@.skip(0) =~= b@);
    }
    let (n1, largest) = match varint_at(b, 0) {
        Some(x) => x,
        None => return Err(FRAME_ENCODING_ERROR),
    };
    let (n2, delay) = match varint_at(b, n1) {
        Some(x) => x,
        None => return Err(FRAME_ENCODING_ERROR),
    };
    let (n3, count) = match varint_at(b, n1 + n2) {
        Some(x) => x,
        None => return Err(FRAME_ENCODING_ERROR),
    };
    let (n4, first_range) = match varint_at(b, n1 + n2 + n3) {
        Some(x) => x,
        None => return Err(FRAME_ENCODING_ERROR),
    };
    let p = n1 + n2 + n3 + n4;
    if first_range > largest {
        return Err(FRAME_ENCODING_ERROR);
    }
    let ghost s0: int = largest - first_range;
    let mut smallest: u64 = largest - first_range;
    // One push per range read: nothing is reserved from the untrusted count.
    let mut ranges: Vec<(u64, u64)> = Vec::new();
    let mut off: usize = p;
    let mut i: u64 = 0;
    proof {
        if let Some((all, q)) = rfc_ack_pairs(b@, p as int, count as nat) {
            assert(ranges@ + all =~= all);
        }
    }
    while i < count
        invariant
            p <= off <= b.len(),
            i <= count,
            s0 == largest - first_range,
            first_range <= largest,
            ty == FRAME_ACK || ty == FRAME_ACK_ECN,
            p == n1 + n2 + n3 + n4,
            rfc_varint_decode(b@) == Some((n1 as nat, largest)),
            rfc_varint_decode(b@.skip(n1 as int)) == Some((n2 as nat, delay)),
            rfc_varint_decode(b@.skip((n1 + n2) as int)) == Some((n3 as nat, count)),
            rfc_varint_decode(b@.skip((n1 + n2 + n3) as int)) == Some((n4 as nat, first_range)),
            rfc_ack_pairs(b@, p as int, count as nat) == (match rfc_ack_pairs(
                b@,
                off as int,
                (count - i) as nat,
            ) {
                Some((rest, q)) => Some((ranges@ + rest, q)),
                None => None,
            }),
            rfc_ack_ranges_from(s0, ranges@),
            smallest as int == spec_ack_smallest(s0, ranges@),
        decreases count - i,
    {
        let (m1, gap) = match varint_at(b, off) {
            Some(x) => x,
            None => {
                proof {
                    assert(rfc_ack_pairs(b@, off as int, (count - i) as nat) is None);
                }
                return Err(FRAME_ENCODING_ERROR);
            },
        };
        let (m2, len) = match varint_at(b, off + m1) {
            Some(x) => x,
            None => {
                proof {
                    assert(rfc_ack_pairs(b@, off as int, (count - i) as nat) is None);
                }
                return Err(FRAME_ENCODING_ERROR);
            },
        };
        let ghost x = (gap, len);
        let ghost next = ranges@.push(x);
        proof {
            assert(next.drop_last() =~= ranges@);
            if let Some((rest, q)) = rfc_ack_pairs(b@, (off + m1 + m2) as int, (count - i - 1) as nat) {
                assert(ranges@ + (seq![x] + rest) =~= next + rest);
            }
        }
        if gap + 2 > smallest || len > smallest - gap - 2 {
            proof {
                if let Some((all, q)) = rfc_ack_pairs(b@, p as int, count as nat) {
                    let rest = all.skip(next.len() as int);
                    assert(all =~= next + rest);
                    if rfc_ack_ranges_from(s0, all) {
                        lemma_ranges_prefix(s0, next, rest);
                    }
                }
            }
            return Err(FRAME_ENCODING_ERROR);
        }
        ranges.push((gap, len));
        smallest = smallest - gap - 2 - len;
        off = off + m1 + m2;
        i = i + 1;
    }
    let ghost q = off;
    if ty == FRAME_ACK_ECN {
        let (k1, e0) = match varint_at(b, off) {
            Some(x) => x,
            None => return Err(FRAME_ENCODING_ERROR),
        };
        let (k2, e1) = match varint_at(b, off + k1) {
            Some(x) => x,
            None => return Err(FRAME_ENCODING_ERROR),
        };
        let (k3, ce) = match varint_at(b, off + k1 + k2) {
            Some(x) => x,
            None => return Err(FRAME_ENCODING_ERROR),
        };
        off = off + k1 + k2 + k3;
        Ok((AckFrame { largest, delay, first_range, ranges, ecn: Some((e0, e1, ce)) }, off))
    } else {
        Ok((AckFrame { largest, delay, first_range, ranges, ecn: None }, off))
    }
}

/// Writes the whole ACK frame, type included: 0x03 iff it carries ECN counts.
#[verifier::spinoff_prover]
pub fn serialize_ack(a: &AckFrame, out: &mut Vec<u8>)
    requires
        ack_encodable(a@),
        rfc_ack_ranges_valid(a.largest, a.first_range, a.ranges@),
    ensures
        final(out)@ == old(out)@ + spec_ack_bytes(a@),
{
    let ghost start = old(out)@;
    let ty = if a.ecn.is_some() {
        FRAME_ACK_ECN
    } else {
        FRAME_ACK
    };
    put_varint(ty, out);
    put_varint(a.largest, out);
    put_varint(a.delay, out);
    put_varint(a.ranges.len() as u64, out);
    put_varint(a.first_range, out);
    let ghost head = out@;
    let mut i: usize = 0;
    while i < a.ranges.len()
        invariant
            i <= a.ranges@.len(),
            ack_encodable(a@),
            out@ == head + spec_ranges_bytes(a.ranges@.take(i as int)),
        decreases a.ranges@.len() - i,
    {
        let (gap, len) = a.ranges[i];
        proof {
            assert(a.ranges@.take(i + 1) =~= a.ranges@.take(i as int).push(a.ranges@[i as int]));
            lemma_ranges_bytes_snoc(a.ranges@.take(i as int), a.ranges@[i as int]);
            assert(a.ranges@[i as int].0 <= VARINT_MAX);
        }
        let ghost before = out@;
        put_varint(gap, out);
        put_varint(len, out);
        proof {
            assert(before + spec_varint(gap) + spec_varint(len) =~= before + spec_pair_bytes(
                (gap, len),
            ));
            assert(head + spec_ranges_bytes(a.ranges@.take(i as int)) + spec_pair_bytes((gap, len))
                =~= head + (spec_ranges_bytes(a.ranges@.take(i as int)) + spec_pair_bytes(
                (gap, len),
            )));
        }
        i = i + 1;
    }
    proof {
        assert(a.ranges@.take(a.ranges@.len() as int) =~= a.ranges@);
    }
    let ghost mid = out@;
    match a.ecn {
        Some((e0, e1, ce)) => {
            put_varint(e0, out);
            put_varint(e1, out);
            put_varint(ce, out);
            proof {
                assert(out@ =~= mid + spec_ecn_bytes(a.ecn));
            }
        },
        None => {
            proof {
                assert(out@ =~= mid + spec_ecn_bytes(a.ecn));
            }
        },
    }
    proof {
        assert(out@ =~= start + spec_ack_bytes(a@));
    }
}

} // verus!
