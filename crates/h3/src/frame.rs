//! HTTP/3 frame layout and the SETTINGS / GOAWAY payloads (RFC 9114 §7): RFC-transcribed
//! specs, executable codec, and proofs that the two agree.
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use vest_lib::core::spec::*;
use vstd::prelude::*;
use byteq::capvec::CapVec;
use vstd::slice::{slice_subrange, slice_to_vec};
pub use wire::varint::*;

use crate::codes::*;

verus! {

#[derive(Debug, PartialEq, Eq)]
pub enum FrameHeader {
    Incomplete,
    Complete { ty: u64, len: u64, hdr_len: usize },
}

#[derive(Debug, PartialEq, Eq)]
pub enum Frame {
    /// DATA carries no payload: the connection layer streams DATA bytes without buffering.
    Data,
    Headers(Vec<u8>),
    CancelPush(u64),
    Settings(Vec<(u64, u64)>),
    PushPromise { push_id: u64, field_section: Vec<u8> },
    Goaway(u64),
    MaxPushId(u64),
    H2Reserved(u64),
    Unknown(u64),
}

pub enum SpecFrame {
    Data,
    Headers(Seq<u8>),
    CancelPush(u64),
    Settings(Seq<(u64, u64)>),
    PushPromise { push_id: u64, field_section: Seq<u8> },
    Goaway(u64),
    MaxPushId(u64),
    H2Reserved(u64),
    Unknown(u64),
}

impl View for Frame {
    type V = SpecFrame;

    open spec fn view(&self) -> SpecFrame {
        match self {
            Frame::Data => SpecFrame::Data,
            Frame::Headers(v) => SpecFrame::Headers(v@),
            Frame::CancelPush(id) => SpecFrame::CancelPush(*id),
            Frame::Settings(v) => SpecFrame::Settings(v@),
            Frame::PushPromise { push_id, field_section } => SpecFrame::PushPromise {
                push_id: *push_id,
                field_section: field_section@,
            },
            Frame::Goaway(id) => SpecFrame::Goaway(*id),
            Frame::MaxPushId(id) => SpecFrame::MaxPushId(*id),
            Frame::H2Reserved(t) => SpecFrame::H2Reserved(*t),
            Frame::Unknown(t) => SpecFrame::Unknown(*t),
        }
    }
}

// =============================================================================
// RFC 9114 transcription
// =============================================================================

//= https://www.rfc-editor.org/rfc/rfc9114#section-7.1
//# Type:  A variable-length integer that identifies the frame type.
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.1
//# Length:  A variable-length integer that describes the length in bytes
//# of the Frame Payload.
/// `(bytes consumed, type, length)`; both varints may use any encoding length.
pub open spec fn rfc_frame_header(b: Seq<u8>) -> Option<(nat, u64, u64)> {
    match rfc_varint_decode(b) {
        None => None,
        Some((n1, ty)) => match rfc_varint_decode(b.skip(n1 as int)) {
            None => None,
            Some((n2, len)) => Some((n1 + n2, ty, len)),
        },
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-7.1
//# A frame payload that contains additional bytes
//# after the identified fields or a frame payload that terminates before
//# the end of the identified fields MUST be treated as a connection
//# error of type H3_FRAME_ERROR.
/// A payload that is exactly one varint.
pub open spec fn rfc_exact_varint(p: Seq<u8>) -> Option<u64> {
    match rfc_varint_decode(p) {
        Some((n, v)) => if n == p.len() {
            Some(v)
        } else {
            None
        },
        None => None,
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.4
//# The payload of a SETTINGS frame consists of zero or more parameters.
//# Each parameter consists of a setting identifier and a value, both
//# encoded as QUIC variable-length integers.
/// The pairs of a SETTINGS payload; `None` when it ends mid-pair or mid-varint.
pub open spec fn rfc_settings_pairs(p: Seq<u8>) -> Option<Seq<(u64, u64)>>
    decreases p.len(),
    via settings_pairs_decreases
{
    if p.len() == 0 {
        Some(Seq::empty())
    } else {
        match rfc_varint_decode(p) {
            None => None,
            Some((n1, id)) => match rfc_varint_decode(p.skip(n1 as int)) {
                None => None,
                Some((n2, v)) => match rfc_settings_pairs(p.skip((n1 + n2) as int)) {
                    None => None,
                    Some(rest) => Some(seq![(id, v)].add(rest)),
                },
            },
        }
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.4
//# The same setting identifier MUST NOT occur more than once in the
//# SETTINGS frame.
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.4
//# A receiver MAY treat the presence of duplicate
//# setting identifiers as a connection error of type H3_SETTINGS_ERROR.
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.4.1
//# These reserved settings MUST NOT be sent, and
//# their receipt MUST be treated as a connection error of type
//# H3_SETTINGS_ERROR.
pub open spec fn rfc_settings_valid(s: Seq<(u64, u64)>) -> bool {
    &&& forall|i: int, j: int|
        0 <= i < j < s.len() ==> (#[trigger] s[i]).0 != (#[trigger] s[j]).0
    &&& forall|i: int| 0 <= i < s.len() ==> !is_h2_reserved_setting_spec((#[trigger] s[i]).0)
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.8
//# Frame types that were used in HTTP/2 where there is no corresponding
//# HTTP/3 frame have also been reserved (Section 11.2.1).
/// Frame types we receive as `Ok`; grease and unknown types are `Unknown`, HTTP/2-era
/// types are `H2Reserved` (the connection layer turns those into H3_FRAME_UNEXPECTED).
pub open spec fn rfc_frame_payload(ty: u64, p: Seq<u8>) -> Result<SpecFrame, u64> {
    if ty == FRAME_DATA {
        Ok(SpecFrame::Data)
    } else if ty == FRAME_HEADERS {
        Ok(SpecFrame::Headers(p))
    } else if ty == FRAME_CANCEL_PUSH {
        match rfc_exact_varint(p) {
            Some(v) => Ok(SpecFrame::CancelPush(v)),
            None => Err(H3_FRAME_ERROR),
        }
    } else if ty == FRAME_SETTINGS {
        match rfc_settings_pairs(p) {
            None => Err(H3_FRAME_ERROR),
            Some(s) => if rfc_settings_valid(s) {
                Ok(SpecFrame::Settings(s))
            } else {
                Err(H3_SETTINGS_ERROR)
            },
        }
    } else if ty == FRAME_PUSH_PROMISE {
        match rfc_varint_decode(p) {
            Some((n, id)) => Ok(
                SpecFrame::PushPromise { push_id: id, field_section: p.skip(n as int) },
            ),
            None => Err(H3_FRAME_ERROR),
        }
    } else if ty == FRAME_GOAWAY {
        match rfc_exact_varint(p) {
            Some(v) => Ok(SpecFrame::Goaway(v)),
            None => Err(H3_FRAME_ERROR),
        }
    } else if ty == FRAME_MAX_PUSH_ID {
        match rfc_exact_varint(p) {
            Some(v) => Ok(SpecFrame::MaxPushId(v)),
            None => Err(H3_FRAME_ERROR),
        }
    } else if is_h2_reserved_frame_spec(ty) {
        Ok(SpecFrame::H2Reserved(ty))
    } else {
        Ok(SpecFrame::Unknown(ty))
    }
}

// =============================================================================
// Serialization specs
// =============================================================================

pub open spec fn spec_frame_header_bytes(ty: u64, len: u64) -> Seq<u8> {
    spec_varint(ty).add(spec_varint(len))
}

pub open spec fn spec_frame_bytes(ty: u64, payload: Seq<u8>) -> Seq<u8> {
    spec_frame_header_bytes(ty, payload.len() as u64).add(payload)
}

// =============================================================================
// Varint lemmas
// =============================================================================

/// A buffer that does not yet hold a whole varint is shorter than 8 bytes.
pub proof fn lemma_decode_none_short(b: Seq<u8>)
    ensures
        rfc_varint_decode(b) is None ==> b.len() < 8,
{
    if b.len() > 0 {
        let v = b[0];
        assert((1u8 << (v >> 6)) <= 8) by (bit_vector);
    }
}

#[verifier::decreases_by]
proof fn settings_pairs_decreases(p: Seq<u8>) {
    lemma_decode_len_bounds(p);
    if let Some((n1, _)) = rfc_varint_decode(p) {
        lemma_decode_len_bounds(p.skip(n1 as int));
    }
}

// =============================================================================
// Executable helpers
// =============================================================================

fn parse_exact_varint(p: &[u8]) -> (r: Option<u64>)
    ensures
        r == rfc_exact_varint(p@),
{
    match parse_varint(p) {
        Some((n, v)) => if n == p.len() {
            Some(v)
        } else {
            None
        },
        None => None,
    }
}

// -----------------------------------------------------------------------------
// SETTINGS duplicates: a bottom-up merge sort of the identifiers (O(p log p)),
// then one pass over the sorted copy for equal neighbours.
// -----------------------------------------------------------------------------

/// The first clause of `rfc_settings_valid`: no identifier occurs twice.
pub open spec fn ids_distinct(s: Seq<(u64, u64)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> (#[trigger] s[i]).0 != (#[trigger] s[j]).0
}

pub open spec fn sorted_u64(s: Seq<u64>) -> bool {
    forall|a: int, b: int| #![trigger s[a], s[b]] 0 <= a < b < s.len() ==> s[a] <= s[b]
}

/// Within every block of width `w`, nondecreasing.
spec fn sorted_runs(s: Seq<u64>, w: int) -> bool {
    forall|a: int, b: int|
        #![trigger s[a], s[b]]
        0 <= a < b < s.len() && a / w == b / w ==> s[a] <= s[b]
}

spec fn has_dup(s: Seq<u64>) -> bool {
    exists|i: int, j: int| #![trigger s[i], s[j]] 0 <= i < j < s.len() && s[i] == s[j]
}

spec fn has_adj_dup(s: Seq<u64>) -> bool {
    exists|i: int| 0 <= i && i + 1 < s.len() && #[trigger] s[i] == s[i + 1]
}

/// ⌈log2 p⌉: the number of merge passes that sort `p` elements.
pub open spec fn clog2(p: nat) -> nat
    decreases p,
{
    if p <= 1 {
        0
    } else {
        1 + clog2(((p + 1) / 2) as nat)
    }
}

/// `sort_ids_w`'s cost constant.
pub open spec fn c_sort() -> nat {
    3
}

/// `settings_ok`'s cost constant: per pair, one reserved check and one neighbour compare.
pub open spec fn c_ok() -> nat {
    2
}

/// `parse_settings`' cost constant, over the payload length.
pub open spec fn c_pset() -> nat {
    25
}

/// x lies in block q of width d exactly when x / d == q.
proof fn lemma_block(x: int, d: int, q: int)
    requires
        d > 0,
        x >= 0,
        q >= 0,
    ensures
        (q * d <= x && x < q * d + d) <==> x / d == q,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, d);
    let r = x % d;
    assert(0 <= r < d);
    if q * d <= x && x < q * d + d {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x, d, q, x - q * d);
    } else {
        assert(x / d != q) by (nonlinear_arith)
            requires
                x == d * (x / d) + r,
                0 <= r < d,
                !(q * d <= x && x < q * d + d),
        {}
    }
}

/// Pushing `e` into block k (start lo) keeps sorted_runs(_, w2) when e is at least the block's last entry.
proof fn lemma_push_runs(out: Seq<u64>, e: u64, w2: int, lo: int, k: int)
    requires
        w2 > 0,
        k >= 0,
        lo == k * w2,
        sorted_runs(out, w2),
        lo <= out.len() < lo + w2,
        out.len() > lo ==> out.last() <= e,
    ensures
        sorted_runs(out.push(e), w2),
{
    let s = out.push(e);
    let p = out.len() as int;
    lemma_block(p, w2, k);
    assert forall|a: int, b: int|
        #![trigger s[a], s[b]]
        0 <= a < b < s.len() && a / w2 == b / w2 implies s[a] <= s[b] by {
        if b == p {
            lemma_block(a, w2, k);
            lemma_block(p - 1, w2, k);
            assert(a >= lo);
            if a < p - 1 {
                assert(out[a] <= out[p - 1]);
            }
        } else {
            assert(s[a] == out[a] && s[b] == out[b]);
        }
    }
}

proof fn lemma_runs_one(s: Seq<u64>)
    ensures
        sorted_runs(s, 1),
{
    assert forall|a: int, b: int|
        #![trigger s[a], s[b]]
        0 <= a < b < s.len() && a / 1 == b / 1 implies s[a] <= s[b] by {
        assert(a / 1 == a && b / 1 == b);
    }
}

/// One block covering the whole sequence: sorted, and so every width's runs are.
proof fn lemma_runs_all(s: Seq<u64>, w: int, w2: int)
    requires
        w >= s.len(),
        w > 0,
        w2 > 0,
        sorted_runs(s, w),
    ensures
        sorted_u64(s),
        sorted_runs(s, w2),
{
    assert forall|a: int, b: int| #![trigger s[a], s[b]] 0 <= a < b < s.len() implies s[a] <= s[b] by {
        lemma_block(a, w, 0);
        lemma_block(b, w, 0);
    }
}

/// A pass taken while the width 2^k is below p is one of at most clog2(p).
proof fn lemma_clog2(k: nat, p: nat)
    requires
        vstd::arithmetic::power2::pow2(k) < p,
    ensures
        k < clog2(p),
    decreases k,
{
    vstd::arithmetic::power2::lemma_pow2_pos(k);
    if k == 0 {
        vstd::arithmetic::power2::lemma_pow2(0);
        vstd::arithmetic::power::lemma_pow0(2);
    } else {
        vstd::arithmetic::power2::lemma_pow2_unfold(k);
        lemma_clog2((k - 1) as nat, ((p + 1) / 2) as nat);
    }
}

proof fn lemma_clog2_le(p: nat)
    ensures
        clog2(p) <= p,
    decreases p,
{
    if p > 1 {
        lemma_clog2_le(((p + 1) / 2) as nat);
    }
}

proof fn lemma_clog2_mono(p: nat, q: nat)
    requires
        p <= q,
    ensures
        clog2(p) <= clog2(q),
    decreases q,
{
    if p > 1 {
        lemma_clog2_mono(((p + 1) / 2) as nat, ((q + 1) / 2) as nat);
    }
}

/// D7's lemma_sorted_dup: in a sorted sequence an equal pair gives an equal adjacent pair.
proof fn lemma_sorted_dup(s: Seq<u64>)
    requires
        sorted_u64(s),
    ensures
        has_dup(s) <==> has_adj_dup(s),
{
    if has_dup(s) {
        let (i, j) = choose|i: int, j: int|
            #![trigger s[i], s[j]]
            0 <= i < j < s.len() && s[i] == s[j];
        if i + 1 < j {
            assert(s[i] <= s[i + 1] && s[i + 1] <= s[j]);
        }
        assert(s[i] == s[i + 1]);
    }
    if has_adj_dup(s) {
        let i = choose|i: int| 0 <= i && i + 1 < s.len() && #[trigger] s[i] == s[i + 1];
        assert(s[i] == s[i + 1]);
    }
}

/// Some value occurs twice exactly when its count is at least 2.
proof fn lemma_dup_count(s: Seq<u64>)
    ensures
        has_dup(s) <==> exists|x: u64| #[trigger] s.to_multiset().count(x) >= 2,
    decreases s.len(),
{
    broadcast use vstd::multiset::group_multiset_axioms, vstd::seq_lib::group_to_multiset_ensures;

    if s.len() == 0 {
        assert(s.to_multiset() =~= vstd::multiset::Multiset::<u64>::empty());
    } else {
        let t = s.drop_last();
        let a = s.last();
        assert(s == t.push(a));
        assert(t.push(a).to_multiset() =~= t.to_multiset().insert(a));
        lemma_dup_count(t);
        if has_dup(s) {
            let (i, j) = choose|i: int, j: int|
                #![trigger s[i], s[j]]
                0 <= i < j < s.len() && s[i] == s[j];
            if j < s.len() - 1 {
                assert(t[i] == s[i] && t[j] == s[j]);
                assert(has_dup(t));
                let x = choose|x: u64| #[trigger] t.to_multiset().count(x) >= 2;
                assert(s.to_multiset().count(x) >= 2);
            } else {
                assert(t[i] == a);
                assert(t.contains(a));
                assert(s.to_multiset().count(a) >= 2);
            }
        }
        if exists|x: u64| #[trigger] s.to_multiset().count(x) >= 2 {
            let x = choose|x: u64| #[trigger] s.to_multiset().count(x) >= 2;
            if x == a {
                assert(t.to_multiset().count(a) > 0);
                assert(t.contains(a));
                let i = choose|i: int| 0 <= i < t.len() && t[i] == a;
                assert(s[i] == s[s.len() - 1]);
            } else {
                assert(t.to_multiset().count(x) >= 2);
                let (i, j) = choose|i: int, j: int|
                    #![trigger t[i], t[j]]
                    0 <= i < j < t.len() && t[i] == t[j];
                assert(s[i] == t[i] && s[j] == t[j]);
            }
        }
    }
}

/// D7's conclusion: the sorted copy has equal neighbours exactly when `v` repeats an identifier.
proof fn lemma_settings_dup(v: Seq<(u64, u64)>, srt: Seq<u64>)
    requires
        sorted_u64(srt),
        srt.to_multiset() == v.map_values(|x: (u64, u64)| x.0).to_multiset(),
    ensures
        ids_distinct(v) <==> !has_adj_dup(srt),
{
    let ids = v.map_values(|x: (u64, u64)| x.0);
    lemma_sorted_dup(srt);
    lemma_dup_count(srt);
    lemma_dup_count(ids);
    if has_dup(ids) {
        let (i, j) = choose|i: int, j: int|
            #![trigger ids[i], ids[j]]
            0 <= i < j < ids.len() && ids[i] == ids[j];
        assert(v[i].0 == v[j].0);
    }
    if !ids_distinct(v) {
        let (i, j) = choose|i: int, j: int|
            0 <= i < j < v.len() && (#[trigger] v[i]).0 == (#[trigger] v[j]).0;
        assert(ids[i] == ids[j]);
    }
}

/// `sort_ids_w`'s bound from its accounting: a copy pass and `passes <= clog2(n)` merge passes of 2n + 2.
proof fn lemma_sort_cost(n: nat, passes: nat, work: nat)
    requires
        passes <= clog2(n),
        work <= (n + 1) + passes * (2 * n + 2),
    ensures
        work <= c_sort() * (n * (clog2(n) + 1) + 1),
{
    let c = clog2(n);
    lemma_clog2_le(n);
    vstd::arithmetic::mul::lemma_mul_inequality(passes as int, c as int, (2 * n + 2) as int);
    assert((n + 1) + c * (2 * n + 2) <= 3 * (n * (c + 1) + 1)) by (nonlinear_arith)
        requires
            c <= n,
    {}
}

/// Merges the runs `src[lo..mid)` and `src[mid..hi)` (block k of width 2w) onto `out`.
fn merge_runs(
    src: &[u64],
    lo: usize,
    mid: usize,
    hi: usize,
    out: &mut CapVec<u64>,
    _w: usize,
    _k: Ghost<int>,
) -> (r: Ghost<nat>)
    requires
        1 <= _w,
        _k@ >= 0,
        lo == _k@ * (2 * _w),
        lo <= mid <= hi <= src.len(),
        mid <= lo + _w,
        hi <= lo + 2 * _w,
        mid < hi ==> mid == lo + _w,
        sorted_runs(src@, _w as int),
        old(out).wf(),
        hi <= old(out).cap(),
        old(out)@.len() == lo,
        old(out)@.to_multiset() == src@.subrange(0, lo as int).to_multiset(),
        sorted_runs(old(out)@, 2 * _w),
    ensures
        final(out).wf(),
        final(out).cap() == old(out).cap(),
        final(out)@.to_multiset() == src@.subrange(0, hi as int).to_multiset(),
        sorted_runs(final(out)@, 2 * _w),
        r@ <= 2 * (hi - lo),
{
    let ghost w2 = 2 * _w as int;
    let ghost kk = _k@;
    let ghost mut work: nat = 0;
    let mut i = lo;
    let mut j = mid;
    proof {
        assert(kk * w2 == (2 * kk) * _w) by (nonlinear_arith)
            requires
                w2 == 2 * _w,
        {}
        assert(src@.subrange(mid as int, mid as int) =~= Seq::<u64>::empty());
        assert(Seq::<u64>::empty().to_multiset() =~= vstd::multiset::Multiset::<u64>::empty()) by {
            broadcast use vstd::multiset::group_multiset_axioms, vstd::seq_lib::group_to_multiset_ensures;

        }
        assert(out@.to_multiset().add(vstd::multiset::Multiset::empty()) =~= out@.to_multiset());
    }
    while i < mid || j < hi
        invariant
            1 <= _w,
            w2 == 2 * _w,
            sorted_runs(src@, _w as int),
            kk >= 0,
            lo == kk * w2,
            lo == (2 * kk) * _w,
            lo <= i <= mid <= j <= hi <= src.len(),
            mid <= lo + _w,
            hi <= lo + 2 * _w,
            mid < hi ==> mid == lo + _w,
            out.wf(),
            out.cap() == old(out).cap(),
            hi <= out.cap(),
            out@.len() == i + j - mid,
            out@.to_multiset() == src@.subrange(0, i as int).to_multiset().add(
                src@.subrange(mid as int, j as int).to_multiset(),
            ),
            sorted_runs(out@, w2),
            out@.len() > lo ==> (i < mid ==> out@.last() <= src@[i as int]) && (j < hi
                ==> out@.last() <= src@[j as int]),
            work == 2 * (out@.len() - lo),
        decreases (mid - i) + (hi - j),
    {
        let ghost o = out@;
        if i < mid && (j >= hi || src[i] <= src[j]) {
            let e = src[i];
            proof {
                lemma_push_runs(o, e, w2, lo as int, kk);
                assert(src@.subrange(0, i + 1) =~= src@.subrange(0, i as int).push(e));
                if i + 1 < mid {
                    lemma_block(i as int, _w as int, 2 * kk);
                    lemma_block(i + 1, _w as int, 2 * kk);
                }
            }
            out.push(e);
            i += 1;
            proof {
                broadcast use vstd::seq_lib::group_to_multiset_ensures;

                assert(out@.to_multiset() =~= src@.subrange(0, i as int).to_multiset().add(
                    src@.subrange(mid as int, j as int).to_multiset(),
                ));
            }
        } else {
            let e = src[j];
            proof {
                lemma_push_runs(o, e, w2, lo as int, kk);
                assert(src@.subrange(mid as int, j + 1) =~= src@.subrange(mid as int, j as int).push(
                    e,
                ));
                if j + 1 < hi {
                    lemma_block(j as int, _w as int, 2 * kk + 1);
                    lemma_block(j + 1, _w as int, 2 * kk + 1);
                    assert((2 * kk + 1) * _w == (2 * kk) * _w + _w) by (nonlinear_arith);
                }
            }
            out.push(e);
            j += 1;
            proof {
                broadcast use vstd::seq_lib::group_to_multiset_ensures;

                assert(out@.to_multiset() =~= src@.subrange(0, i as int).to_multiset().add(
                    src@.subrange(mid as int, j as int).to_multiset(),
                ));
            }
        }
        // one compare and one copy
        proof {
            work = work + 2;
        }
    }
    proof {
        broadcast use vstd::seq_lib::lemma_multiset_commutative;

        assert(src@.subrange(0, hi as int) =~= src@.subrange(0, mid as int) + src@.subrange(
            mid as int,
            hi as int,
        ));
    }
    Ghost(work)
}

/// One pass: merges the runs of width w of `src` into runs of width 2w, into a fresh buffer.
fn merge_pass(src: &[u64], w: usize) -> (r: (CapVec<u64>, Ghost<nat>))
    requires
        1 <= w,
        sorted_runs(src@, w as int),
    ensures
        r.0.wf(),
        r.0@.len() == src.len(),
        r.0@.to_multiset() == src@.to_multiset(),
        sorted_runs(r.0@, 2 * w),
        r.1@ <= 2 * src.len() + 1,
{
    let n = src.len();
    let mut out: CapVec<u64> = CapVec::new(n);
    let ghost mut work: nat = 1;
    let mut lo: usize = 0;
    let ghost mut k: int = 0;
    proof {
        assert(src@.subrange(0, 0) =~= Seq::<u64>::empty());
    }
    while lo < n
        invariant
            n == src.len(),
            1 <= w,
            sorted_runs(src@, w as int),
            lo <= n,
            k >= 0,
            lo < n ==> lo == k * (2 * w),
            out.wf(),
            out.cap() == n,
            out@.len() == lo,
            out@.to_multiset() == src@.subrange(0, lo as int).to_multiset(),
            sorted_runs(out@, 2 * w),
            work <= 1 + 2 * lo,
        decreases n - lo,
    {
        let mid = if w < n - lo {
            lo + w
        } else {
            n
        };
        let hi = if w < n - mid {
            mid + w
        } else {
            n
        };
        let Ghost(c) = merge_runs(src, lo, mid, hi, &mut out, w, Ghost(k));
        proof {
            assert(out@.len() == hi) by {
                broadcast use vstd::seq_lib::group_to_multiset_ensures;

                assert(out@.to_multiset().len() == src@.subrange(0, hi as int).to_multiset().len());
            }
            if hi < n {
                assert((k + 1) * (2 * w) == k * (2 * w) + 2 * w) by (nonlinear_arith);
            }
            k = k + 1;
            work = work + c;
        }
        lo = hi;
    }
    proof {
        assert(src@.subrange(0, n as int) =~= src@);
    }
    (out, Ghost(work))
}

/// Copies the identifiers of `v` and sorts them by bottom-up merging: widths 1, 2, 4, .. below p, one fresh
/// buffer per pass (the previous one freed).
fn sort_ids_w(v: &[(u64, u64)]) -> (r: (CapVec<u64>, Ghost<nat>))
    ensures
        r.0.wf(),
        sorted_u64(r.0@),
        r.0@.to_multiset() == v@.map_values(|x: (u64, u64)| x.0).to_multiset(),
        r.1@ <= c_sort() * (v@.len() * (clog2(v@.len() as nat) + 1) + 1),
{
    let n = v.len();
    let ghost ids = v@.map_values(|x: (u64, u64)| x.0);
    let mut a: CapVec<u64> = CapVec::new(n);
    let ghost mut work: nat = 1;
    let mut i: usize = 0;
    while i < n
        invariant
            n == v@.len(),
            ids == v@.map_values(|x: (u64, u64)| x.0),
            i <= n,
            a.wf(),
            a.cap() == n,
            a@ == ids.take(i as int),
            work == 1 + i,
        decreases n - i,
    {
        a.push(v[i].0);
        proof {
            assert(ids.take(i + 1) =~= ids.take(i as int).push(v@[i as int].0));
        }
        i += 1;
        proof {
            work = work + 1;
        }
    }
    proof {
        assert(ids.take(n as int) =~= ids);
        lemma_runs_one(a@);
        vstd::arithmetic::power2::lemma2_to64();
    }
    let mut w: usize = 1;
    let ghost mut passes: nat = 0;
    while w < n
        invariant
            n == v@.len(),
            ids == v@.map_values(|x: (u64, u64)| x.0),
            1 <= w,
            w < n ==> w as nat == vstd::arithmetic::power2::pow2(passes),
            passes == 0 || vstd::arithmetic::power2::pow2((passes - 1) as nat) < n,
            a.wf(),
            a@.len() == n,
            a@.to_multiset() == ids.to_multiset(),
            sorted_runs(a@, w as int),
            work <= (n + 1) + passes * (2 * n + 2),
        decreases n - w,
    {
        proof {
            lemma_clog2(passes, n as nat);
        }
        let (b, Ghost(c)) = merge_pass(a.as_slice(), w);
        // the previous buffer is freed here
        a = b;
        proof {
            assert(work + c + 1 <= (n + 1) + (passes + 1) * (2 * n + 2)) by (nonlinear_arith)
                requires
                    work <= (n + 1) + passes * (2 * n + 2),
                    c <= 2 * n + 1,
            {}
            work = work + c + 1;
            passes = passes + 1;
        }
        if w <= (n - 1) / 2 {
            proof {
                vstd::arithmetic::power2::lemma_pow2_unfold(passes);
            }
            w = 2 * w;
        } else {
            proof {
                lemma_runs_all(a@, 2 * w as int, n as int);
            }
            w = n;
        }
    }
    proof {
        lemma_runs_all(a@, w as int, 1);
        if passes > 0 {
            lemma_clog2((passes - 1) as nat, n as nat);
        }
        lemma_sort_cost(n as nat, passes, work);
    }
    (a, Ghost(work))
}

/// One pass: reserved identifiers in `v`, equal neighbours in its sorted copy `sorted`.
fn settings_ok(v: &Vec<(u64, u64)>, sorted: &[u64]) -> (r: (bool, Ghost<nat>))
    requires
        sorted_u64(sorted@),
        sorted@.to_multiset() == v@.map_values(|x: (u64, u64)| x.0).to_multiset(),
    ensures
        r.0 == rfc_settings_valid(v@),
        r.1@ <= c_ok() * (v@.len() + 1),
{
    let n = v.len();
    proof {
        broadcast use vstd::seq_lib::group_to_multiset_ensures;

        assert(sorted@.to_multiset().len() == v@.map_values(|x: (u64, u64)| x.0).to_multiset().len());
        assert(sorted@.to_multiset().len() == sorted@.len());
        assert(v@.map_values(|x: (u64, u64)| x.0).to_multiset().len() == v@.map_values(|x: (u64, u64)| x.0).len());
        assert(sorted@.len() == n);
        lemma_settings_dup(v@, sorted@);
    }
    let ghost mut work: nat = 0;
    let mut i: usize = 0;
    // one exit, so the result is not a constant tuple (ct-front translates none)
    while i < n && !is_h2_reserved_setting(v[i].0) && !(i + 1 < n && sorted[i] == sorted[i + 1])
        invariant
            n == v@.len(),
            sorted@.len() == n,
            ids_distinct(v@) <==> !has_adj_dup(sorted@),
            i <= n,
            forall|a: int| 0 <= a < i ==> !is_h2_reserved_setting_spec(#[trigger] v@[a].0),
            forall|a: int| 0 <= a < i && a + 1 < n ==> #[trigger] sorted@[a] != sorted@[a + 1],
            work == 2 * i,
        decreases n - i,
    {
        i += 1;
        proof {
            work = work + 2;
        }
    }
    proof {
        if i == n {
            if has_adj_dup(sorted@) {
                let a = choose|a: int| 0 <= a && a + 1 < sorted@.len() && #[trigger] sorted@[a] == sorted@[a + 1];
                assert(sorted@[a] != sorted@[a + 1]);
            }
            assert(ids_distinct(v@));
        } else if !is_h2_reserved_setting_spec(v@[i as int].0) {
            assert(sorted@[i as int] == sorted@[i + 1]);
            assert(has_adj_dup(sorted@));
        }
    }
    // the last check: one reserved test, one compare
    (i == n, Ghost(work + 2))
}

// =============================================================================
// Header codec
// =============================================================================

/// A buffer without a whole type varint extends to a complete header.
proof fn lemma_header_extends_type(b: Seq<u8>)
    requires
        rfc_varint_decode(b) is None,
    ensures
        rfc_frame_header(b) is None,
        exists|ext: Seq<u8>| #[trigger] rfc_frame_header(b.add(ext)) is Some,
{
    lemma_decode_extend(b);
    let ext1 = choose|ext: Seq<u8>| completes(b, ext);
    let ext = ext1.add(seq![0u8]);
    let full = b.add(ext1);
    let n1 = rfc_varint_decode(full).unwrap().0;
    assert(b.add(ext) =~= full.add(seq![0u8]));
    lemma_decode_prefix(full, seq![0u8]);
    assert(b.add(ext).skip(n1 as int) =~= seq![0u8]);
    lemma_decode_zero();
    assert(rfc_frame_header(b.add(ext)) is Some);
}

/// A buffer with a whole type varint (`n1` bytes) but no whole length varint extends to a complete header.
proof fn lemma_header_extends_len(b: Seq<u8>, n1: nat)
    requires
        rfc_varint_decode(b) matches Some((n, _)) && n == n1,
        rfc_varint_decode(b.skip(n1 as int)) is None,
    ensures
        rfc_frame_header(b) is None,
        exists|ext: Seq<u8>| #[trigger] rfc_frame_header(b.add(ext)) is Some,
{
    let s2 = b.skip(n1 as int);
    lemma_decode_extend(s2);
    let ext = choose|ext: Seq<u8>| completes(s2, ext);
    lemma_decode_prefix(b, ext);
    assert(b.add(ext).skip(n1 as int) =~= s2.add(ext));
    assert(rfc_frame_header(b.add(ext)) is Some);
}

/// `Incomplete` only when `buf` is a strict prefix of some valid header.
pub fn parse_frame_header(buf: &[u8]) -> (r: FrameHeader)
    ensures
        match r {
            FrameHeader::Complete { ty, len, hdr_len } => rfc_frame_header(buf@) == Some(
                (hdr_len as nat, ty, len),
            ),
            FrameHeader::Incomplete => {
                &&& rfc_frame_header(buf@) is None
                &&& exists|ext: Seq<u8>| #[trigger] rfc_frame_header(buf@.add(ext)) is Some
            },
        },
{
    match parse_varint(buf) {
        None => {
            proof {
                lemma_header_extends_type(buf@);
            }
            FrameHeader::Incomplete
        },
        Some((n1, ty)) => {
            let rest = slice_subrange(buf, n1, buf.len());
            proof {
                assert(rest@ =~= buf@.skip(n1 as int));
            }
            match parse_varint(rest) {
                None => {
                    proof {
                        lemma_header_extends_len(buf@, n1 as nat);
                    }
                    FrameHeader::Incomplete
                },
                Some((n2, len)) => FrameHeader::Complete { ty, len, hdr_len: n1 + n2 },
            }
        },
    }
}

/// Appends type and length as minimal varints.
pub fn serialize_frame_header(ty: u64, len: u64, out: &mut Vec<u8>)
    requires
        ty <= VARINT_MAX,
        !is_h2_reserved_frame_spec(ty),
        len <= VARINT_MAX,
    ensures
        final(out)@ == old(out)@.add(spec_frame_header_bytes(ty, len)),
{
    put_varint(ty, out);
    put_varint(len, out);
    proof {
        assert(old(out)@.add(spec_varint(ty)).add(spec_varint(len)) =~= old(out)@.add(
            spec_frame_header_bytes(ty, len),
        ));
    }
}

/// A serialized header parses back to exactly its type, length and size.
pub proof fn theorem_header_roundtrip(ty: u64, len: u64)
    requires
        ty <= VARINT_MAX,
        len <= VARINT_MAX,
    ensures
        rfc_frame_header(spec_frame_header_bytes(ty, len)) == Some(
            (spec_frame_header_bytes(ty, len).len(), ty, len),
        ),
{
    theorem_serialize_matches_rfc(ty);
    theorem_serialize_matches_rfc(len);
    let (a, b) = (spec_varint(ty), spec_varint(len));
    lemma_decode_prefix(a, b);
    assert(a.add(b).skip(a.len() as int) =~= b);
}

/// A complete header occupies 2 to 16 bytes of `b`; an incomplete one leaves `b` under 16 bytes.
pub proof fn lemma_frame_header_bounds(b: Seq<u8>)
    ensures
        rfc_frame_header(b) matches Some((h, _, _)) ==> 2 <= h <= b.len() && h <= 16,
        rfc_frame_header(b) is None ==> b.len() < 16,
{
    lemma_decode_len_bounds(b);
    lemma_decode_none_short(b);
    if let Some((n1, _)) = rfc_varint_decode(b) {
        lemma_decode_len_bounds(b.skip(n1 as int));
        lemma_decode_none_short(b.skip(n1 as int));
    }
}

/// Prefix stability: bytes after a complete header don't change how it parses.
pub proof fn lemma_frame_header_prefix(b: Seq<u8>, t: Seq<u8>)
    requires
        rfc_frame_header(b) is Some,
    ensures
        rfc_frame_header(b.add(t)) == rfc_frame_header(b),
{
    lemma_decode_prefix(b, t);
    let n1 = rfc_varint_decode(b).unwrap().0;
    lemma_decode_len_bounds(b);
    assert(b.add(t).skip(n1 as int) =~= b.skip(n1 as int).add(t));
    lemma_decode_prefix(b.skip(n1 as int), t);
}

/// A serialized frame, followed by anything, parses back to its header and exactly its payload.
pub proof fn lemma_frame_bytes_roundtrip(ty: u64, p: Seq<u8>, rest: Seq<u8>)
    requires
        ty <= VARINT_MAX,
        p.len() <= VARINT_MAX,
    ensures
        ({
            let h = spec_frame_header_bytes(ty, p.len() as u64).len();
            let b = spec_frame_bytes(ty, p).add(rest);
            &&& rfc_frame_header(b) == Some((h, ty, p.len() as u64))
            &&& b.subrange(h as int, (h + p.len()) as int) == p
        }),
{
    let hb = spec_frame_header_bytes(ty, p.len() as u64);
    theorem_header_roundtrip(ty, p.len() as u64);
    lemma_frame_header_prefix(hb, p.add(rest));
    let b = spec_frame_bytes(ty, p).add(rest);
    assert(b =~= hb.add(p.add(rest)));
    assert(b.subrange(hb.len() as int, (hb.len() + p.len()) as int) =~= p);
}

/// Complete frame: header for `body.len()` followed by `body`.
pub fn put_frame(ty: u64, body: &Vec<u8>, out: &mut Vec<u8>)
    requires
        ty <= VARINT_MAX,
        !is_h2_reserved_frame_spec(ty),
        body@.len() <= VARINT_MAX,
    ensures
        final(out)@ == old(out)@.add(spec_frame_bytes(ty, body@)),
{
    serialize_frame_header(ty, body.len() as u64, out);
    let ghost mid = out@;
    let mut i: usize = 0;
    while i < body.len()
        invariant
            i <= body@.len(),
            out@ == mid.add(body@.take(i as int)),
        decreases body@.len() - i,
    {
        out.push(body[i]);
        proof {
            assert(body@.take(i as int + 1) =~= body@.take(i as int).push(body@[i as int]));
            assert(mid.add(body@.take(i as int)).push(body@[i as int]) =~= mid.add(
                body@.take(i as int + 1),
            ));
        }
        i += 1;
    }
    proof {
        assert(body@.take(body@.len() as int) =~= body@);
        assert(old(out)@.add(spec_frame_header_bytes(ty, body@.len() as u64)).add(body@)
            =~= old(out)@.add(spec_frame_bytes(ty, body@)));
    }
}

// =============================================================================
// Payload parsing
// =============================================================================

/// Consumes `payload` exactly: a frame whose fields do not fill it, or overrun it, is
/// `H3_FRAME_ERROR`; a duplicate or HTTP/2-reserved SETTINGS identifier is
/// `H3_SETTINGS_ERROR`.
pub fn parse_frame_payload(ty: u64, payload: &[u8]) -> (r: Result<Frame, u64>)
    ensures
        match r {
            Ok(f) => rfc_frame_payload(ty, payload@) == Ok::<SpecFrame, u64>(f@),
            Err(e) => rfc_frame_payload(ty, payload@) == Err::<SpecFrame, u64>(e),
        },
{
    if ty == FRAME_DATA {
        Ok(Frame::Data)
    } else if ty == FRAME_HEADERS {
        Ok(Frame::Headers(slice_to_vec(payload)))
    } else if ty == FRAME_CANCEL_PUSH {
        match parse_exact_varint(payload) {
            Some(v) => Ok(Frame::CancelPush(v)),
            None => Err(H3_FRAME_ERROR),
        }
    } else if ty == FRAME_SETTINGS {
        // Task 8 makes this fn charge the cost
        let (r, _) = parse_settings(payload);
        r
    } else if ty == FRAME_PUSH_PROMISE {
        match parse_varint(payload) {
            Some((n, id)) => {
                let fs = slice_to_vec(slice_subrange(payload, n, payload.len()));
                Ok(Frame::PushPromise { push_id: id, field_section: fs })
            },
            None => Err(H3_FRAME_ERROR),
        }
    } else if ty == FRAME_GOAWAY {
        match parse_exact_varint(payload) {
            Some(v) => Ok(Frame::Goaway(v)),
            None => Err(H3_FRAME_ERROR),
        }
    } else if ty == FRAME_MAX_PUSH_ID {
        match parse_exact_varint(payload) {
            Some(v) => Ok(Frame::MaxPushId(v)),
            None => Err(H3_FRAME_ERROR),
        }
    } else if is_h2_reserved_frame(ty) {
        Ok(Frame::H2Reserved(ty))
    } else {
        Ok(Frame::Unknown(ty))
    }
}

/// `parse_settings`' bound from its accounting: `t` is its charges besides the sort's (at most 3d + 22), `p` its pairs.
proof fn lemma_pset_cost(d: nat, p: nat, t: nat)
    requires
        2 * p <= d,
        t <= c_sort() * (p * (clog2(p) + 1) + 1) + 3 * d + 22,
    ensures
        t <= c_pset() * (d * (clog2(d) + 1) + 1),
{
    lemma_clog2_mono(p, d);
    let (cp, cd) = (clog2(p), clog2(d));
    vstd::arithmetic::mul::lemma_mul_upper_bound(p as int, d as int, (cp + 1) as int, (cd + 1) as int);
    assert(d <= d * (cd + 1)) by (nonlinear_arith);
}

fn parse_settings(payload: &[u8]) -> (r: (Result<Frame, u64>, Ghost<nat>))
    ensures
        match r.0 {
            Ok(f) => rfc_frame_payload(FRAME_SETTINGS, payload@) == Ok::<SpecFrame, u64>(f@),
            Err(e) => rfc_frame_payload(FRAME_SETTINGS, payload@) == Err::<SpecFrame, u64>(e),
        },
        r.1@ <= c_pset() * (payload@.len() * (clog2(payload@.len() as nat) + 1) + 1),
{
    let ghost d = payload@.len() as nat;
    // a pair takes at least two bytes
    let mut pairs: CapVec<(u64, u64)> = CapVec::new(payload.len() / 2);
    let ghost mut work: nat = 1;
    let mut off: usize = 0;
    proof {
        assert(payload@.skip(0) =~= payload@);
        if let Some(r) = rfc_settings_pairs(payload@) {
            assert(pairs@.add(r) =~= r);
        }
    }
    while off < payload.len()
        invariant
            d == payload@.len(),
            off <= payload@.len(),
            rfc_settings_pairs(payload@) == (match rfc_settings_pairs(payload@.skip(off as int)) {
                Some(rest) => Some(pairs@.add(rest)),
                None => None,
            }),
            pairs.wf(),
            pairs.cap() == payload@.len() / 2,
            2 * pairs@.len() <= off,
            work == 1 + off + pairs@.len(),
        decreases payload@.len() - off,
    {
        let tail = slice_subrange(payload, off, payload.len());
        // a varint reads at most 8 bytes; the free of `pairs`
        let (n1, id) = match parse_varint(tail) {
            Some(x) => x,
            None => {
                proof {
                    lemma_pset_cost(d, pairs@.len(), work + 9);
                }
                return (Err(H3_FRAME_ERROR), Ghost(work + 9));
            },
        };
        let tail2 = slice_subrange(tail, n1, tail.len());
        proof {
            lemma_decode_len_bounds(payload@.skip(off as int));
        }
        let (n2, v) = match parse_varint(tail2) {
            Some(x) => x,
            None => {
                proof {
                    lemma_pset_cost(d, pairs@.len(), (work + n1 + 9) as nat);
                }
                return (Err(H3_FRAME_ERROR), Ghost((work + n1 + 9) as nat));
            },
        };
        proof {
            let t = payload@.skip(off as int);
            assert(tail2@ =~= t.skip(n1 as int));
            assert(t.skip((n1 + n2) as int) =~= payload@.skip((off + n1 + n2) as int));
            lemma_decode_len_bounds(t);
            lemma_decode_len_bounds(t.skip(n1 as int));
            assert(pairs@.push((id, v)).add(Seq::empty()) =~= pairs@.add(seq![(id, v)]));
        }
        let ghost old_pairs = pairs@;
        pairs.push((id, v));
        off = off + n1 + n2;
        proof {
            work = (work + n1 + n2 + 1) as nat;
            // unfold one step: rest(t_old) = [(id,v)] + rest(skip)
            match rfc_settings_pairs(payload@.skip(off as int)) {
                Some(rest) => {
                    assert(old_pairs.add(seq![(id, v)].add(rest)) =~= pairs@.add(rest));
                },
                None => {},
            }
        }
    }
    proof {
        assert(payload@.skip(off as int) =~= Seq::<u8>::empty());
        assert(pairs@.add(Seq::empty()) =~= pairs@);
    }
    let pairs = pairs.into_vec();
    let (sorted, Ghost(cs)) = sort_ids_w(pairs.as_slice());
    let (ok, Ghost(co)) = settings_ok(&pairs, sorted.as_slice());
    // the free of `sorted`, and of `pairs` on the error
    proof {
        lemma_pset_cost(d, pairs@.len(), work + cs + co + 2);
    }
    if ok {
        (Ok(Frame::Settings(pairs)), Ghost(work + cs + co + 1))
    } else {
        (Err(H3_SETTINGS_ERROR), Ghost(work + cs + co + 2))
    }
}

// =============================================================================
// Frame serialization
// =============================================================================

/// Writes a complete SETTINGS frame (type 0x04).
pub fn serialize_settings(settings: &[(u64, u64)], out: &mut Vec<u8>)
    requires
        settings@.len() < 0x1_0000_0000,
        forall|i: int|
            0 <= i < settings@.len() ==> (#[trigger] settings@[i]).0 <= VARINT_MAX && settings@[i].1
                <= VARINT_MAX,
        rfc_settings_valid(settings@),
    ensures
        final(out)@ == old(out)@.add(spec_frame_bytes(FRAME_SETTINGS, spec_pairs_bytes(settings@))),
{
    let mut body: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < settings.len()
        invariant
            i <= settings@.len(),
            settings@.len() < 0x1_0000_0000,
            forall|k: int|
                0 <= k < settings@.len() ==> (#[trigger] settings@[k]).0 <= VARINT_MAX
                    && settings@[k].1 <= VARINT_MAX,
            body@ == spec_pairs_bytes(settings@.take(i as int)),
            body@.len() <= 16 * i,
        decreases settings@.len() - i,
    {
        let (id, v) = settings[i];
        proof {
            assert(settings@.take(i as int + 1) =~= settings@.take(i as int).push(settings@[i as int]));
            lemma_pairs_bytes_snoc(settings@.take(i as int), settings@[i as int]);
            theorem_serialize_matches_rfc(id);
            theorem_serialize_matches_rfc(v);
        }
        let ghost before = body@;
        put_varint(id, &mut body);
        put_varint(v, &mut body);
        proof {
            assert(before.add(spec_varint(id)).add(spec_varint(v)) =~= before.add(
                spec_pair_bytes((id, v)),
            ));
        }
        i += 1;
    }
    proof {
        assert(settings@.take(settings@.len() as int) =~= settings@);
    }
    put_frame(FRAME_SETTINGS, &body, out);
}

/// Writes a complete GOAWAY frame (type 0x07).
pub fn serialize_goaway(id: u64, out: &mut Vec<u8>)
    requires
        id <= VARINT_MAX,
    ensures
        final(out)@ == old(out)@.add(spec_frame_bytes(FRAME_GOAWAY, spec_varint(id))),
{
    let mut body: Vec<u8> = Vec::new();
    put_varint(id, &mut body);
    proof {
        theorem_serialize_matches_rfc(id);
        assert(Seq::<u8>::empty().add(spec_varint(id)) =~= spec_varint(id));
    }
    put_frame(FRAME_GOAWAY, &body, out);
}

proof fn lemma_pair_parses(x: (u64, u64), rest: Seq<u8>)
    requires
        x.0 <= VARINT_MAX,
        x.1 <= VARINT_MAX,
    ensures
        rfc_settings_pairs(spec_pair_bytes(x).add(rest)) == (match rfc_settings_pairs(rest) {
            Some(r) => Some(seq![x].add(r)),
            None => None,
        }),
{
    theorem_serialize_matches_rfc(x.0);
    theorem_serialize_matches_rfc(x.1);
    let (a, b) = (spec_varint(x.0), spec_varint(x.1));
    let p = spec_pair_bytes(x).add(rest);
    assert(p =~= a.add(b.add(rest)));
    lemma_decode_prefix(a, b.add(rest));
    assert(p.skip(a.len() as int) =~= b.add(rest));
    lemma_decode_prefix(b, rest);
    assert(p.skip(a.len() as int).skip(b.len() as int) =~= rest);
    assert(p.skip((a.len() + b.len()) as int) =~= rest);
    lemma_decode_len_bounds(a);
}

proof fn lemma_settings_payload_parses(s: Seq<(u64, u64)>)
    requires
        forall|i: int|
            0 <= i < s.len() ==> (#[trigger] s[i]).0 <= VARINT_MAX && s[i].1 <= VARINT_MAX,
    ensures
        rfc_settings_pairs(spec_pairs_bytes(s)) == Some(s),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s =~= Seq::<(u64, u64)>::empty());
    } else {
        let tail = s.skip(1);
        assert(s[0].0 <= VARINT_MAX && s[0].1 <= VARINT_MAX);
        assert forall|i: int| 0 <= i < tail.len() implies (#[trigger] tail[i]).0 <= VARINT_MAX
            && tail[i].1 <= VARINT_MAX by {
            assert(tail[i] == s[i + 1]);
        }
        lemma_settings_payload_parses(tail);
        lemma_pair_parses(s[0], spec_pairs_bytes(tail));
        assert(seq![s[0]].add(tail) =~= s);
    }
}

/// SETTINGS the peer would accept parse back to the same pairs.
pub proof fn theorem_settings_roundtrip(s: Seq<(u64, u64)>)
    requires
        forall|i: int|
            0 <= i < s.len() ==> (#[trigger] s[i]).0 <= VARINT_MAX && s[i].1 <= VARINT_MAX,
        rfc_settings_valid(s),
    ensures
        rfc_frame_payload(FRAME_SETTINGS, spec_pairs_bytes(s)) == Ok::<SpecFrame, u64>(
            SpecFrame::Settings(s),
        ),
{
    lemma_settings_payload_parses(s);
}

pub proof fn theorem_goaway_roundtrip(id: u64)
    requires
        id <= VARINT_MAX,
    ensures
        rfc_frame_payload(FRAME_GOAWAY, spec_varint(id)) == Ok::<SpecFrame, u64>(
            SpecFrame::Goaway(id),
        ),
{
    theorem_serialize_matches_rfc(id);
}

} // verus!
