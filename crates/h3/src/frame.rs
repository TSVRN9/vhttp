//! HTTP/3 frame layout and the SETTINGS / GOAWAY payloads (RFC 9114 §7): RFC-transcribed
//! specs, executable codec, and proofs that the two agree.
use vest_lib::core::exec::{Parser, SerializerExt};
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use vest_lib::core::spec::*;
use vstd::prelude::*;
use vstd::slice::{slice_subrange, slice_to_vec};
use wire::varint::*;

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

pub open spec fn spec_varint(v: u64) -> Seq<u8> {
    QuicVarInt::<true>.spec_serialize(v)
}

pub open spec fn spec_frame_header_bytes(ty: u64, len: u64) -> Seq<u8> {
    spec_varint(ty).add(spec_varint(len))
}

pub open spec fn spec_frame_bytes(ty: u64, payload: Seq<u8>) -> Seq<u8> {
    spec_frame_header_bytes(ty, payload.len() as u64).add(payload)
}

pub open spec fn spec_pair_bytes(x: (u64, u64)) -> Seq<u8> {
    spec_varint(x.0).add(spec_varint(x.1))
}

pub open spec fn spec_settings_payload(s: Seq<(u64, u64)>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        spec_pair_bytes(s[0]).add(spec_settings_payload(s.skip(1)))
    }
}

// =============================================================================
// Varint lemmas
// =============================================================================

proof fn lemma_decode_len_bounds(b: Seq<u8>)
    ensures
        rfc_varint_decode(b) matches Some((n, _)) ==> 1 <= n <= b.len() && n <= 8,
{
    theorem_matches_rfc(b);
    lemma_parse_bound::<false>(b);
}

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

/// Decoding looks only at the bytes the varint occupies.
pub proof fn lemma_decode_prefix(a: Seq<u8>, r: Seq<u8>)
    requires
        rfc_varint_decode(a) is Some,
    ensures
        rfc_varint_decode(a.add(r)) == rfc_varint_decode(a),
{
    lemma_decode_len_bounds(a);
    let n = rfc_varint_decode(a).unwrap().0;
    assert(a.add(r)[0] == a[0]);
    assert(a.add(r).subrange(1, n as int) =~= a.subrange(1, n as int));
}

pub proof fn lemma_decode_zero()
    ensures
        rfc_varint_decode(seq![0u8]) == Some((1nat, 0u64)),
{
    lemma_serialize_bytes::<true>(0);
    theorem_serialize_matches_rfc(0);
}

pub open spec fn completes(b: Seq<u8>, ext: Seq<u8>) -> bool {
    &&& rfc_varint_decode(b.add(ext)) is Some
    &&& rfc_varint_decode(b.add(ext)).unwrap().0 == b.add(ext).len()
}

/// A buffer too short for its varint can be padded to exactly the varint's length.
pub proof fn lemma_decode_extend(b: Seq<u8>)
    requires
        rfc_varint_decode(b) is None,
    ensures
        exists|ext: Seq<u8>| #[trigger] completes(b, ext),
{
    if b.len() == 0 {
        let ext = seq![0u8];
        assert(b.add(ext) =~= ext);
        lemma_decode_zero();
        assert(completes(b, ext));
    } else {
        let l = (1u8 << (b[0] >> 6)) as nat;
        assert(b.len() < l);
        let ext = Seq::new((l - b.len()) as nat, |i: int| 0u8);
        assert(b.add(ext).len() == l);
        assert(b.add(ext)[0] == b[0]);
        assert(completes(b, ext));
    }
}

// =============================================================================
// Executable helpers
// =============================================================================

pub fn parse_varint(b: &[u8]) -> (r: Option<(usize, u64)>)
    ensures
        match r {
            Some((n, v)) => rfc_varint_decode(b@) == Some((n as nat, v)) && 1 <= n <= b@.len(),
            None => rfc_varint_decode(b@) is None,
        },
{
    proof {
        theorem_matches_rfc(b@);
        lemma_decode_len_bounds(b@);
    }
    match QuicVarInt::<false>.parse(&b) {
        Ok((n, v)) => Some((n, v)),
        Err(_) => None,
    }
}

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

fn put_varint(v: u64, out: &mut Vec<u8>)
    requires
        v <= VARINT_MAX,
    ensures
        final(out)@ == old(out)@.add(spec_varint(v)),
{
    QuicVarInt::<true>.serialize_with_vec(&v, out);
}

// ponytail: O(n^2) duplicate scan; SETTINGS frames are small
fn settings_ok(v: &Vec<(u64, u64)>) -> (r: bool)
    ensures
        r == rfc_settings_valid(v@),
{
    let n = v.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == v@.len(),
            i <= n,
            forall|a: int, b: int|
                0 <= a < i && a < b < n ==> #[trigger] v@[a].0 != #[trigger] v@[b].0,
            forall|a: int| 0 <= a < i ==> !is_h2_reserved_setting_spec(#[trigger] v@[a].0),
        decreases n - i,
    {
        if is_h2_reserved_setting(v[i].0) {
            return false;
        }
        let mut j: usize = i + 1;
        while j < n
            invariant
                n == v@.len(),
                i < n,
                i < j <= n,
                forall|a: int, b: int|
                    0 <= a < i && a < b < n ==> #[trigger] v@[a].0 != #[trigger] v@[b].0,
                forall|b: int| i < b < j ==> v@[i as int].0 != #[trigger] v@[b].0,
            decreases n - j,
        {
            if v[j].0 == v[i].0 {
                return false;
            }
            j += 1;
        }
        i += 1;
    }
    true
}

// =============================================================================
// Header codec
// =============================================================================

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
                lemma_decode_extend(buf@);
                let ext1 = choose|ext: Seq<u8>| completes(buf@, ext);
                let ext = ext1.add(seq![0u8]);
                let full = buf@.add(ext1);
                let n1 = rfc_varint_decode(full).unwrap().0;
                assert(buf@.add(ext) =~= full.add(seq![0u8]));
                lemma_decode_prefix(full, seq![0u8]);
                assert(buf@.add(ext).skip(n1 as int) =~= seq![0u8]);
                lemma_decode_zero();
                assert(rfc_frame_header(buf@.add(ext)) is Some);
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
                        let s2 = buf@.skip(n1 as int);
                        lemma_decode_extend(s2);
                        let ext = choose|ext: Seq<u8>| completes(s2, ext);
                        lemma_decode_prefix(buf@, ext);
                        assert(buf@.add(ext).skip(n1 as int) =~= s2.add(ext));
                        assert(rfc_frame_header(buf@.add(ext)) is Some);
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
        parse_settings(payload)
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

fn parse_settings(payload: &[u8]) -> (r: Result<Frame, u64>)
    ensures
        match r {
            Ok(f) => rfc_frame_payload(FRAME_SETTINGS, payload@) == Ok::<SpecFrame, u64>(f@),
            Err(e) => rfc_frame_payload(FRAME_SETTINGS, payload@) == Err::<SpecFrame, u64>(e),
        },
{
    let mut pairs: Vec<(u64, u64)> = Vec::new();
    let mut off: usize = 0;
    proof {
        assert(payload@.skip(0) =~= payload@);
        if let Some(r) = rfc_settings_pairs(payload@) {
            assert(pairs@.add(r) =~= r);
        }
    }
    while off < payload.len()
        invariant
            off <= payload@.len(),
            rfc_settings_pairs(payload@) == (match rfc_settings_pairs(payload@.skip(off as int)) {
                Some(rest) => Some(pairs@.add(rest)),
                None => None,
            }),
        decreases payload@.len() - off,
    {
        let tail = slice_subrange(payload, off, payload.len());
        let (n1, id) = match parse_varint(tail) {
            Some(x) => x,
            None => return Err(H3_FRAME_ERROR),
        };
        let tail2 = slice_subrange(tail, n1, tail.len());
        let (n2, v) = match parse_varint(tail2) {
            Some(x) => x,
            None => return Err(H3_FRAME_ERROR),
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
            let t_old = payload@.skip((off - n1 - n2) as int);
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
    if settings_ok(&pairs) {
        Ok(Frame::Settings(pairs))
    } else {
        Err(H3_SETTINGS_ERROR)
    }
}

// =============================================================================
// Frame serialization
// =============================================================================

pub proof fn lemma_settings_payload_snoc(s: Seq<(u64, u64)>, x: (u64, u64))
    ensures
        spec_settings_payload(s.push(x)) == spec_settings_payload(s).add(spec_pair_bytes(x)),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.push(x)[0] == x);
        assert(spec_settings_payload(s) == Seq::<u8>::empty());
        assert(s.push(x).skip(1) =~= Seq::<(u64, u64)>::empty());
        assert(spec_settings_payload(Seq::<(u64, u64)>::empty()) == Seq::<u8>::empty());
        assert(spec_pair_bytes(x).add(Seq::empty()) =~= spec_pair_bytes(x));
        assert(Seq::<u8>::empty().add(spec_pair_bytes(x)) =~= spec_pair_bytes(x));
    } else {
        assert(s.push(x).skip(1) =~= s.skip(1).push(x));
        lemma_settings_payload_snoc(s.skip(1), x);
        assert(s.push(x)[0] == s[0]);
        assert(spec_pair_bytes(s[0]).add(spec_settings_payload(s.skip(1)).add(spec_pair_bytes(x)))
            =~= spec_pair_bytes(s[0]).add(spec_settings_payload(s.skip(1))).add(
            spec_pair_bytes(x),
        ));
    }
}

/// Writes a complete SETTINGS frame (type 0x04).
pub fn serialize_settings(settings: &[(u64, u64)], out: &mut Vec<u8>)
    requires
        settings@.len() < 0x1_0000_0000,
        forall|i: int|
            0 <= i < settings@.len() ==> (#[trigger] settings@[i]).0 <= VARINT_MAX && settings@[i].1
                <= VARINT_MAX,
        rfc_settings_valid(settings@),
    ensures
        final(out)@ == old(out)@.add(spec_frame_bytes(FRAME_SETTINGS, spec_settings_payload(settings@))),
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
            body@ == spec_settings_payload(settings@.take(i as int)),
            body@.len() <= 16 * i,
        decreases settings@.len() - i,
    {
        let (id, v) = settings[i];
        proof {
            assert(settings@.take(i as int + 1) =~= settings@.take(i as int).push(settings@[i as int]));
            lemma_settings_payload_snoc(settings@.take(i as int), settings@[i as int]);
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
        rfc_settings_pairs(spec_settings_payload(s)) == Some(s),
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
        lemma_pair_parses(s[0], spec_settings_payload(tail));
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
        rfc_frame_payload(FRAME_SETTINGS, spec_settings_payload(s)) == Ok::<SpecFrame, u64>(
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
