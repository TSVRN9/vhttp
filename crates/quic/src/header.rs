//! Long and short packet headers (RFC 9000 §17.2-17.4). Header protection covers byte 0's
//! low bits and the packet number, so parsing stops at `pn_offset`; the first-byte helpers
//! read those bits once protection is removed.
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use vest_lib::core::spec::*;
use vstd::prelude::*;
use vstd::slice::{slice_subrange, slice_to_vec};
use wire::varint::*;

use crate::ack::*;
use crate::codes::*;
use crate::pn::*;

verus! {

#[derive(Debug, PartialEq, Eq)]
pub enum LongType {
    Initial,
    ZeroRtt,
    Handshake,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Header {
    /// A version 1 long header. `packet_end = pn_offset + Length` ends this packet within a
    /// datagram that may coalesce several.
    Long {
        ty: LongType,
        dcid: Vec<u8>,
        scid: Vec<u8>,
        token: Vec<u8>,
        pn_offset: usize,
        packet_end: usize,
    },
    Short { dcid: Vec<u8>, pn_offset: usize },
    UnsupportedVersion { version: u32, dcid: Vec<u8>, scid: Vec<u8> },
}

pub enum SpecHeader {
    Long {
        ty: LongType,
        dcid: Seq<u8>,
        scid: Seq<u8>,
        token: Seq<u8>,
        pn_offset: nat,
        packet_end: nat,
    },
    Short { dcid: Seq<u8>, pn_offset: nat },
    UnsupportedVersion { version: u32, dcid: Seq<u8>, scid: Seq<u8> },
}

impl View for Header {
    type V = SpecHeader;

    open spec fn view(&self) -> SpecHeader {
        match self {
            Header::Long { ty, dcid, scid, token, pn_offset, packet_end } => SpecHeader::Long {
                ty: *ty,
                dcid: dcid@,
                scid: scid@,
                token: token@,
                pn_offset: *pn_offset as nat,
                packet_end: *packet_end as nat,
            },
            Header::Short { dcid, pn_offset } => SpecHeader::Short {
                dcid: dcid@,
                pn_offset: *pn_offset as nat,
            },
            Header::UnsupportedVersion { version, dcid, scid } => SpecHeader::UnsupportedVersion {
                version: *version,
                dcid: dcid@,
                scid: scid@,
            },
        }
    }
}

// =============================================================================
// RFC 9000 transcription
// =============================================================================

//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# Version:  The QUIC Version is a 32-bit field that follows the first
//# byte.
/// The Version field, big-endian in `b[1..5]`.
pub open spec fn spec_version(b: Seq<u8>) -> u32 {
    ((b[1] as u32) << 24u32) | ((b[2] as u32) << 16u32) | ((b[3] as u32) << 8u32) | (b[4] as u32)
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# Long Packet Type:  The next two bits (those with a mask of 0x30) of
//# byte 0 contain a packet type.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# | 0x00 | Initial   | Section 17.2.2 |
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# | 0x01 | 0-RTT     | Section 17.2.3 |
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# | 0x02 | Handshake | Section 17.2.4 |
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# | 0x03 | Retry     | Section 17.2.5 |
/// Table 5's type for byte 0; `None` for Retry, which a server never receives.
pub open spec fn spec_long_type(b0: u8) -> Option<LongType> {
    let t = (b0 >> 4u8) & 3u8;
    if t == 0 {
        Some(LongType::Initial)
    } else if t == 1 {
        Some(LongType::ZeroRtt)
    } else if t == 2 {
        Some(LongType::Handshake)
    } else {
        None
    }
}

pub open spec fn long_type_code(ty: LongType) -> u8 {
    match ty {
        LongType::Initial => 0,
        LongType::ZeroRtt => 1,
        LongType::Handshake => 2,
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2.2
//# Token Length:  A variable-length integer specifying the length of the
//# Token field, in bytes.  This value is 0 if no token is present.
/// Initial's Token Length and Token at offset `p`, with the offset after them. Other types
/// carry neither.
pub open spec fn rfc_token(b: Seq<u8>, ty: LongType, p: int) -> Option<(Seq<u8>, int)> {
    if ty != LongType::Initial {
        Some((Seq::empty(), p))
    } else {
        match rfc_varint_decode(b.skip(p)) {
            None => None,
            Some((n, tl)) => if p + n + tl > b.len() {
                None
            } else {
                Some((b.subrange(p + n, p + n + tl), p + n + tl))
            },
        }
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# Header Form:  The most significant bit (0x80) of byte 0 (the first
//# byte) is set to 1 for long headers.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# Packets containing a zero
//# value for this bit are not valid packets in this version and MUST
//# be discarded.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# In QUIC version 1, this value MUST NOT exceed
//# 20 bytes.  Endpoints that receive a version 1 long header with a
//# value larger than 20 MUST drop the packet.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# In QUIC version 1, this value MUST NOT
//# exceed 20 bytes.  Endpoints that receive a version 1 long header
//# with a value larger than 20 MUST drop the packet.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# In order to properly
//# form a Version Negotiation packet, servers SHOULD be able to read
//# longer connection IDs from other QUIC versions.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# The header form bit, Destination and Source Connection ID lengths,
//# Destination and Source Connection ID fields, and Version fields of a
//# long header packet are version independent.  The other fields in the
//# first byte are version specific.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2.1
//# Version-
//# specific rules for the connection ID therefore MUST NOT influence a
//# decision about whether to send a Version Negotiation packet.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# Length:  This is the length of the remainder of the packet (that is,
//# the Packet Number and Payload fields) in bytes, encoded as a
//# variable-length integer (Section 16).
/// A long header up to the packet number; `None` means drop. Version 0 is a Version
/// Negotiation packet, which a server never receives (§6.1 forbids answering one). Versions
/// other than 1 keep only the version-independent fields, with CIDs of any length.
pub open spec fn rfc_long_header(b: Seq<u8>) -> Option<SpecHeader> {
    if b.len() < 6 || b[0] & 0x80u8 == 0 {
        None
    } else {
        let version = spec_version(b);
        let d = b[5] as int;
        if b.len() < 7 + d {
            None
        } else {
            let s = b[6 + d] as int;
            let p = 7 + d + s;
            let dcid = b.subrange(6, 6 + d);
            let scid = b.subrange(7 + d, p);
            if b.len() < p || version == 0 {
                None
            } else if version != QUIC_V1 {
                Some(SpecHeader::UnsupportedVersion { version, dcid, scid })
            } else if b[0] & 0x40u8 == 0 || d > MAX_CID_LEN || s > MAX_CID_LEN {
                None
            } else {
                match spec_long_type(b[0]) {
                    None => None,
                    Some(ty) => match rfc_token(b, ty, p) {
                        None => None,
                        Some((token, q)) => match rfc_varint_decode(b.skip(q)) {
                            None => None,
                            Some((m, len)) => if q + m + len > b.len() {
                                None
                            } else {
                                Some(
                                    SpecHeader::Long {
                                        ty,
                                        dcid,
                                        scid,
                                        token,
                                        pn_offset: (q + m) as nat,
                                        packet_end: (q + m + len) as nat,
                                    },
                                )
                            },
                        },
                    },
                }
            }
        }
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-17.3.1
//# Header Form:  The most significant bit (0x80) of byte 0 is set to 0
//# for the short header.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.3.1
//# Fixed Bit:  The next bit (0x40) of byte 0 is set to 1.  Packets
//# containing a zero value for this bit are not valid packets in this
//# version and MUST be discarded.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-10.3
//# Endpoints MUST discard packets that are too small to be valid QUIC
//# packets.  To give an example, with the set of AEAD functions defined
//# in [QUIC-TLS], short header packets that are smaller than 21 bytes
//# are never valid.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.4
//# When the spin bit is disabled, endpoints MAY set the spin bit to any
//# value and MUST ignore any incoming value.
/// Dispatches on the header form. A short header's DCID has the length we issued; the spin
/// bit (0x20) is never read.
pub open spec fn rfc_header(b: Seq<u8>, dcid_len: nat) -> Option<SpecHeader> {
    if b.len() == 0 {
        None
    } else if b[0] & 0x80u8 != 0 {
        rfc_long_header(b)
    } else if b.len() < MIN_SHORT_PACKET || b.len() < 1 + dcid_len || b[0] & 0x40u8 == 0 {
        None
    } else {
        Some(SpecHeader::Short { dcid: b.subrange(1, 1 + dcid_len as int), pn_offset: 1 + dcid_len })
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# That is, the length of the
//# Packet Number field is the value of this field plus one.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.3.1
//# That is, the
//# length of the Packet Number field is the value of this field plus
//# one.
pub open spec fn spec_pn_len(b0: u8) -> u8 {
    ((b0 & 3u8) + 1) as u8
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-17.3.1
//# Key Phase:  The next bit (0x04) of byte 0 indicates the key phase,
//# which allows a recipient of a packet to identify the packet
//# protection keys that are used to protect the packet.
pub open spec fn spec_key_phase(b0: u8) -> bool {
    b0 & 0x04u8 != 0
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# Reserved Bits:  Two bits (those with a mask of 0x0c) of byte 0 are
//# reserved across multiple packet types.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.3.1
//# Reserved Bits:  The next two bits (those with a mask of 0x18) of byte
//# 0 are reserved.
pub open spec fn spec_reserved_bits_zero(b0: u8, long: bool) -> bool {
    b0 & (if long {
        0x0cu8
    } else {
        0x18u8
    }) == 0
}

// =============================================================================
// Serialization specs
// =============================================================================

//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# The value
//# included prior to protection MUST be set to 0.
pub open spec fn spec_long_first_byte(ty: LongType, pn_len: u8) -> u8 {
    0xc0u8 | (long_type_code(ty) << 4u8) | ((pn_len - 1) as u8)
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-17.3.1
//# The value included prior to
//# protection MUST be set to 0.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.4
//# An
//# endpoint that does not support this feature MUST disable it, as
//# defined below.
/// The spin bit (0x20) is whatever the caller supplies: the feature is disabled, so the value
/// is arbitrary (RECOMMENDED random) and never read back.
pub open spec fn spec_short_first_byte(key_phase: bool, spin: bool, pn_len: u8) -> u8 {
    0x40u8 | (if spin {
        0x20u8
    } else {
        0u8
    }) | (if key_phase {
        4u8
    } else {
        0u8
    }) | ((pn_len - 1) as u8)
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2.2
//# Initial packets sent by the server MUST set the Token Length field
//# to 0;
pub open spec fn spec_long_header_bytes(
    ty: LongType,
    dcid: Seq<u8>,
    scid: Seq<u8>,
    pn: u64,
    pn_len: u8,
    payload_len: nat,
) -> Seq<u8> {
    spec_long_head(ty, dcid, scid, pn_len) + spec_token_field(ty) + spec_varint(
        (pn_len + payload_len) as u64,
    ) + pn_be(pn, pn_len as nat)
}

/// First byte, Version, and both CIDs with their lengths.
pub open spec fn spec_long_head(ty: LongType, dcid: Seq<u8>, scid: Seq<u8>, pn_len: u8) -> Seq<
    u8,
> {
    seq![
        spec_long_first_byte(ty, pn_len),
        (QUIC_V1 >> 24u32) as u8,
        (QUIC_V1 >> 16u32) as u8,
        (QUIC_V1 >> 8u32) as u8,
        QUIC_V1 as u8,
        dcid.len() as u8,
    ] + dcid + seq![scid.len() as u8] + scid
}

/// Token Length 0 for Initial; nothing for other types.
pub open spec fn spec_token_field(ty: LongType) -> Seq<u8> {
    if ty == LongType::Initial {
        seq![0u8]
    } else {
        Seq::empty()
    }
}

pub open spec fn spec_short_header_bytes(
    dcid: Seq<u8>,
    key_phase: bool,
    spin: bool,
    pn: u64,
    pn_len: u8,
) -> Seq<u8> {
    seq![spec_short_first_byte(key_phase, spin, pn_len)] + dcid + pn_be(pn, pn_len as nat)
}

// =============================================================================
// Proofs
// =============================================================================

proof fn bv_long_first_byte(t: u8, n: u8)
    by (bit_vector)
    requires
        t <= 3,
        n <= 3,
    ensures
        (0xc0u8 | (t << 4u8) | n) & 0x80u8 != 0,
        (0xc0u8 | (t << 4u8) | n) & 0x40u8 != 0,
        ((0xc0u8 | (t << 4u8) | n) >> 4u8) & 3u8 == t,
        (0xc0u8 | (t << 4u8) | n) & 3u8 == n,
        (0xc0u8 | (t << 4u8) | n) & 0x0cu8 == 0,
{
}

proof fn bv_short_first_byte(s: u8, k: u8, n: u8)
    by (bit_vector)
    requires
        s == 0 || s == 0x20,
        k == 0 || k == 4,
        n <= 3,
    ensures
        (0x40u8 | s | k | n) & 0x80u8 == 0,
        (0x40u8 | s | k | n) & 0x40u8 != 0,
        (0x40u8 | s | k | n) & 3u8 == n,
        ((0x40u8 | s | k | n) & 0x04u8 != 0) == (k == 4),
        (0x40u8 | s | k | n) & 0x18u8 == 0,
{
}

proof fn bv_version(v: u32)
    by (bit_vector)
    ensures
        ((((v >> 24u32) as u8) as u32) << 24u32) | ((((v >> 16u32) as u8) as u32) << 16u32) | ((((
        v >> 8u32) as u8) as u32) << 8u32) | ((v as u8) as u32) == v,
{
}

/// The fields `spec_long_head` wrote read back from the front of `b`.
proof fn lemma_long_head(ty: LongType, dcid: Seq<u8>, scid: Seq<u8>, pn_len: u8, tail: Seq<u8>)
    requires
        dcid.len() <= MAX_CID_LEN,
        scid.len() <= MAX_CID_LEN,
        1 <= pn_len <= 4,
    ensures
        ({
            let b = spec_long_head(ty, dcid, scid, pn_len) + tail;
            let d = dcid.len() as int;
            let s = scid.len() as int;
            &&& b.len() == 7 + d + s + tail.len()
            &&& b[0] == spec_long_first_byte(ty, pn_len)
            &&& spec_version(b) == QUIC_V1
            &&& b[5] == d
            &&& b[6 + d] == s
            &&& b.subrange(6, 6 + d) == dcid
            &&& b.subrange(7 + d, 7 + d + s) == scid
            &&& b.skip(7 + d + s) == tail
        }),
{
    let h = spec_long_head(ty, dcid, scid, pn_len);
    let b = h + tail;
    let d = dcid.len() as int;
    let s = scid.len() as int;
    bv_version(QUIC_V1);
    assert(h.len() == 7 + d + s);
    assert(b[6 + d] == h[6 + d]);
    assert(b.subrange(6, 6 + d) =~= dcid);
    assert(b.subrange(7 + d, 7 + d + s) =~= scid);
    assert(b.skip(7 + d + s) =~= tail);
}

/// `rfc_long_header` on a version 1 header whose fields are already known.
proof fn lemma_rfc_long_v1(b: Seq<u8>, ty: LongType, d: int, s: int, q: int, m: nat, len: u64)
    requires
        0 <= d <= MAX_CID_LEN,
        0 <= s <= MAX_CID_LEN,
        b.len() >= 7 + d + s,
        b[0] & 0x80u8 != 0,
        b[0] & 0x40u8 != 0,
        spec_long_type(b[0]) == Some(ty),
        spec_version(b) == QUIC_V1,
        b[5] == d,
        b[6 + d] == s,
        rfc_token(b, ty, 7 + d + s) == Some((Seq::<u8>::empty(), q)),
        rfc_varint_decode(b.skip(q)) == Some((m, len)),
        q + m + len <= b.len(),
    ensures
        rfc_long_header(b) == Some(
            SpecHeader::Long {
                ty,
                dcid: b.subrange(6, 6 + d),
                scid: b.subrange(7 + d, 7 + d + s),
                token: Seq::empty(),
                pn_offset: (q + m) as nat,
                packet_end: (q + m + len) as nat,
            },
        ),
{
}

/// The token field `spec_token_field` wrote at `p` reads back empty, and `after` follows it.
proof fn lemma_token_field(b: Seq<u8>, ty: LongType, p: int, after: Seq<u8>)
    requires
        0 <= p <= b.len(),
        b.skip(p) == spec_token_field(ty) + after,
    ensures
        rfc_token(b, ty, p) == Some((Seq::<u8>::empty(), p + spec_token_field(ty).len())),
        b.skip(p + spec_token_field(ty).len()) == after,
{
    let q = p + spec_token_field(ty).len();
    if ty == LongType::Initial {
        lemma_decode_zero();
        lemma_decode_prefix(seq![0u8], after);
        assert(b.skip(p) =~= seq![0u8] + after);
        assert(b.subrange(p + 1, p + 1) =~= Seq::<u8>::empty());
    }
    let n = spec_token_field(ty).len() as int;
    assert forall|i: int| 0 <= i < after.len() implies #[trigger] b.skip(q)[i] == after[i] by {
        assert(b.skip(p)[n + i] == b[p + n + i]);
    }
    assert(b.skip(q) =~= after);
}

/// Parsing what `serialize_long_header` wrote, followed by the payload and anything after
/// it, recovers every field; the packet ends exactly after the payload.
pub proof fn theorem_long_header_roundtrip(
    ty: LongType,
    dcid: Seq<u8>,
    scid: Seq<u8>,
    pn: u64,
    pn_len: u8,
    p: Seq<u8>,
    rest: Seq<u8>,
)
    requires
        ty != LongType::ZeroRtt,
        dcid.len() <= MAX_CID_LEN,
        scid.len() <= MAX_CID_LEN,
        1 <= pn_len <= 4,
        pn_len + p.len() <= VARINT_MAX,
    ensures
        ({
            let w = spec_long_header_bytes(ty, dcid, scid, pn, pn_len, p.len());
            rfc_long_header(w + p + rest) == Some(
                SpecHeader::Long {
                    ty,
                    dcid,
                    scid,
                    token: Seq::empty(),
                    pn_offset: (w.len() - pn_len) as nat,
                    packet_end: w.len() + p.len(),
                },
            )
        }),
{
    hide(rfc_long_header);
    hide(rfc_token);
    hide(rfc_varint_decode);
    let w = spec_long_header_bytes(ty, dcid, scid, pn, pn_len, p.len());
    let d = dcid.len() as int;
    let s = scid.len() as int;
    let pfx = 7 + d + s;
    let l = (pn_len + p.len()) as u64;
    let lv = spec_varint(l);
    let pnb = pn_be(pn, pn_len as nat);
    let t = spec_token_field(ty);
    let after = pnb + p + rest;
    let tail = t + (lv + after);
    let b = w + p + rest;
    assert(b =~= spec_long_head(ty, dcid, scid, pn_len) + tail);
    lemma_long_head(ty, dcid, scid, pn_len, tail);
    lemma_pn_roundtrip(pn, pn_len as nat);
    theorem_serialize_matches_rfc(l);
    bv_long_first_byte(long_type_code(ty), (pn_len - 1) as u8);
    let q = pfx + t.len();
    lemma_token_field(b, ty, pfx, lv + after);
    lemma_decode_prefix(lv, after);
    lemma_rfc_long_v1(b, ty, d, s, q, lv.len(), l);
}

/// Parsing what `serialize_short_header` wrote, in a packet of at least
/// `MIN_SHORT_PACKET` bytes, recovers the DCID and the packet-number offset.
pub proof fn theorem_short_header_roundtrip(
    dcid: Seq<u8>,
    key_phase: bool,
    spin: bool,
    pn: u64,
    pn_len: u8,
    tail: Seq<u8>,
)
    requires
        1 <= dcid.len() <= MAX_CID_LEN,
        1 <= pn_len <= 4,
        spec_short_header_bytes(dcid, key_phase, spin, pn, pn_len).len() + tail.len()
            >= MIN_SHORT_PACKET,
    ensures
        rfc_header(spec_short_header_bytes(dcid, key_phase, spin, pn, pn_len) + tail, dcid.len())
            == Some(SpecHeader::Short { dcid, pn_offset: 1 + dcid.len() }),
{
    let b = spec_short_header_bytes(dcid, key_phase, spin, pn, pn_len) + tail;
    lemma_pn_roundtrip(pn, pn_len as nat);
    bv_short_first_byte(
        if spin {
            0x20u8
        } else {
            0u8
        },
        if key_phase {
            4u8
        } else {
            0u8
        },
        (pn_len - 1) as u8,
    );
    assert(b[0] == spec_short_first_byte(key_phase, spin, pn_len));
    assert(b.subrange(1, 1 + dcid.len() as int) =~= dcid);
}

// =============================================================================
// Executable code
// =============================================================================

/// `b[from..from + len]` as a `Vec`, once `len` is known to fit.
fn copy_range(b: &[u8], from: usize, len: usize) -> (r: Vec<u8>)
    requires
        from + len <= b.len(),
    ensures
        r@ == b@.subrange(from as int, from + len),
{
    slice_to_vec(slice_subrange(b, from, from + len))
}

pub fn parse_long_header(b: &[u8]) -> (r: Option<Header>)
    ensures
        match r {
            Some(h) => rfc_long_header(b@) == Some(h@),
            None => rfc_long_header(b@) is None,
        },
{
    if b.len() < 6 || b[0] & 0x80 == 0 {
        return None;
    }
    let version = ((b[1] as u32) << 24u32) | ((b[2] as u32) << 16u32) | ((b[3] as u32) << 8u32)
        | (b[4] as u32);
    let d = b[5] as usize;
    if b.len() < 7 + d {
        return None;
    }
    let s = b[6 + d] as usize;
    let p = 7 + d + s;
    if b.len() < p || version == 0 {
        return None;
    }
    if version != QUIC_V1 {
        return Some(
            Header::UnsupportedVersion {
                version,
                dcid: copy_range(b, 6, d),
                scid: copy_range(b, 7 + d, s),
            },
        );
    }
    if b[0] & 0x40 == 0 || d > MAX_CID_LEN || s > MAX_CID_LEN {
        return None;
    }
    let t = (b[0] >> 4u8) & 3u8;
    let ty = if t == 0 {
        LongType::Initial
    } else if t == 1 {
        LongType::ZeroRtt
    } else if t == 2 {
        LongType::Handshake
    } else {
        return None;
    };
    let ghost sty = spec_long_type(b@[0]).unwrap();
    assert(ty == sty);
    let mut q = p;
    let mut token: Vec<u8> = Vec::new();
    if t == 0 {
        match varint_at(b, p) {
            None => return None,
            Some((n, tl)) => {
                if tl > (b.len() - p - n) as u64 {
                    return None;
                }
                token = copy_range(b, p + n, tl as usize);
                q = p + n + tl as usize;
            },
        }
    }
    assert(token@ =~= rfc_token(b@, sty, p as int).unwrap().0);
    assert(q == rfc_token(b@, sty, p as int).unwrap().1);
    match varint_at(b, q) {
        None => None,
        Some((m, len)) => {
            if len > (b.len() - q - m) as u64 {
                None
            } else {
                Some(
                    Header::Long {
                        ty,
                        dcid: copy_range(b, 6, d),
                        scid: copy_range(b, 7 + d, s),
                        token,
                        pn_offset: q + m,
                        packet_end: q + m + len as usize,
                    },
                )
            }
        },
    }
}

pub fn parse_header(b: &[u8], dcid_len: usize) -> (r: Option<Header>)
    requires
        1 <= dcid_len <= MAX_CID_LEN,
    ensures
        match r {
            Some(h) => rfc_header(b@, dcid_len as nat) == Some(h@),
            None => rfc_header(b@, dcid_len as nat) is None,
        },
{
    if b.len() == 0 {
        None
    } else if b[0] & 0x80 != 0 {
        parse_long_header(b)
    } else if b.len() < MIN_SHORT_PACKET || b[0] & 0x40 == 0 {
        None
    } else {
        Some(Header::Short { dcid: copy_range(b, 1, dcid_len), pn_offset: 1 + dcid_len })
    }
}

/// Appends `s`.
pub(crate) fn put_slice(s: &[u8], out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + s@,
{
    out.extend_from_slice(s);
    assert(out@ =~= old(out)@ + s@);
}

/// Writes a long header through the packet number. `payload_len` counts the protected
/// payload including the AEAD tag. Returns the packet-number offset from the first byte
/// written.
pub fn serialize_long_header(
    ty: LongType,
    dcid: &[u8],
    scid: &[u8],
    pn: u64,
    pn_len: u8,
    payload_len: usize,
    out: &mut Vec<u8>,
) -> (pn_offset: usize)
    requires
        ty != LongType::ZeroRtt,
        dcid.len() <= MAX_CID_LEN,
        scid.len() <= MAX_CID_LEN,
        1 <= pn_len <= 4,
        pn_len + payload_len <= VARINT_MAX,
    ensures
        final(out)@ == old(out)@ + spec_long_header_bytes(
            ty,
            dcid@,
            scid@,
            pn,
            pn_len,
            payload_len as nat,
        ),
        pn_offset + pn_len == final(out)@.len() - old(out)@.len(),
        spec_pn_len(final(out)@[old(out)@.len() as int]) == pn_len,
        spec_reserved_bits_zero(final(out)@[old(out)@.len() as int], true),
        forall|p: Seq<u8>, rest: Seq<u8>|
            p.len() == payload_len ==> #[trigger] rfc_long_header(
                final(out)@.skip(old(out)@.len() as int).add(p).add(rest),
            ) == Some(
                SpecHeader::Long {
                    ty,
                    dcid: dcid@,
                    scid: scid@,
                    token: Seq::empty(),
                    pn_offset: pn_offset as nat,
                    packet_end: (pn_offset + pn_len + payload_len) as nat,
                },
            ),
{
    let ghost start = out@;
    let start_len = out.len();
    let code: u8 = match ty {
        LongType::Initial => 0,
        LongType::ZeroRtt => 1,
        LongType::Handshake => 2,
    };
    let initial = code == 0;
    proof {
        bv_long_first_byte(code, (pn_len - 1) as u8);
    }
    out.push(0xc0u8 | (code << 4u8) | (pn_len - 1));
    out.push((QUIC_V1 >> 24u32) as u8);
    out.push((QUIC_V1 >> 16u32) as u8);
    out.push((QUIC_V1 >> 8u32) as u8);
    out.push(QUIC_V1 as u8);
    out.push(dcid.len() as u8);
    put_slice(dcid, out);
    out.push(scid.len() as u8);
    put_slice(scid, out);
    if initial {
        put_varint(0, out);
        proof {
            lemma_serialize_bytes::<true>(0);
        }
    }
    put_varint(pn_len as u64 + payload_len as u64, out);
    let pn_offset = out.len() - start_len;
    put_pn(pn, pn_len, out);
    proof {
        let w = spec_long_header_bytes(ty, dcid@, scid@, pn, pn_len, payload_len as nat);
        assert(out@ =~= start + w);
        assert(out@.skip(start.len() as int) =~= w);
        lemma_pn_roundtrip(pn, pn_len as nat);
        lemma_long_header_parses(ty, dcid@, scid@, pn, pn_len, payload_len as nat);
    }
    pn_offset
}

/// `theorem_long_header_roundtrip` for every payload of `payload_len` bytes (split out of
/// `serialize_long_header` for the rlimit).
proof fn lemma_long_header_parses(
    ty: LongType,
    dcid: Seq<u8>,
    scid: Seq<u8>,
    pn: u64,
    pn_len: u8,
    payload_len: nat,
)
    requires
        ty != LongType::ZeroRtt,
        dcid.len() <= MAX_CID_LEN,
        scid.len() <= MAX_CID_LEN,
        1 <= pn_len <= 4,
        pn_len + payload_len <= VARINT_MAX,
    ensures
        ({
            let w = spec_long_header_bytes(ty, dcid, scid, pn, pn_len, payload_len);
            forall|p: Seq<u8>, rest: Seq<u8>|
                p.len() == payload_len ==> #[trigger] rfc_long_header(w.add(p).add(rest)) == Some(
                    SpecHeader::Long {
                        ty,
                        dcid,
                        scid,
                        token: Seq::empty(),
                        pn_offset: (w.len() - pn_len) as nat,
                        packet_end: w.len() + payload_len,
                    },
                )
        }),
{
    let w = spec_long_header_bytes(ty, dcid, scid, pn, pn_len, payload_len);
    assert forall|p: Seq<u8>, rest: Seq<u8>| p.len() == payload_len implies #[trigger]
        rfc_long_header(w.add(p).add(rest)) == Some(
            SpecHeader::Long {
                ty,
                dcid,
                scid,
                token: Seq::empty(),
                pn_offset: (w.len() - pn_len) as nat,
                packet_end: w.len() + payload_len,
            },
        ) by {
        theorem_long_header_roundtrip(ty, dcid, scid, pn, pn_len, p, rest);
    }
}

/// Writes a short (1-RTT) header through the packet number; the DCID may be empty, since a
/// client may choose an empty CID. `spin` is written to the spin bit. Returns the
/// packet-number offset.
pub fn serialize_short_header(
    dcid: &[u8],
    key_phase: bool,
    spin: bool,
    pn: u64,
    pn_len: u8,
    out: &mut Vec<u8>,
) -> (pn_offset: usize)
    requires
        dcid.len() <= MAX_CID_LEN,
        1 <= pn_len <= 4,
    ensures
        final(out)@ == old(out)@ + spec_short_header_bytes(dcid@, key_phase, spin, pn, pn_len),
        pn_offset == 1 + dcid.len(),
        spec_pn_len(final(out)@[old(out)@.len() as int]) == pn_len,
        spec_key_phase(final(out)@[old(out)@.len() as int]) == key_phase,
        spec_reserved_bits_zero(final(out)@[old(out)@.len() as int], false),
        dcid.len() >= 1 ==> forall|tail: Seq<u8>|
            final(out)@.len() - old(out)@.len() + tail.len() >= MIN_SHORT_PACKET ==> #[trigger]
            rfc_header(final(out)@.skip(old(out)@.len() as int).add(tail), dcid.len() as nat)
                == Some(SpecHeader::Short { dcid: dcid@, pn_offset: pn_offset as nat }),
{
    let ghost start = out@;
    let k: u8 = if key_phase {
        4
    } else {
        0
    };
    let sb: u8 = if spin {
        0x20
    } else {
        0
    };
    proof {
        bv_short_first_byte(sb, k, (pn_len - 1) as u8);
    }
    out.push(0x40u8 | sb | k | (pn_len - 1));
    put_slice(dcid, out);
    put_pn(pn, pn_len, out);
    proof {
        let w = spec_short_header_bytes(dcid@, key_phase, spin, pn, pn_len);
        assert(out@ =~= start + w);
        assert(out@.skip(start.len() as int) =~= w);
        lemma_pn_roundtrip(pn, pn_len as nat);
        if dcid.len() >= 1 {
            assert forall|tail: Seq<u8>|
                out@.len() - start.len() + tail.len() >= MIN_SHORT_PACKET implies #[trigger]
                rfc_header(out@.skip(start.len() as int).add(tail), dcid.len() as nat)
                    == Some(SpecHeader::Short { dcid: dcid@, pn_offset: (1 + dcid.len()) as nat }) by {
                theorem_short_header_roundtrip(dcid@, key_phase, spin, pn, pn_len, tail);
            }
        }
    }
    1 + dcid.len()
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# Packet Number Length:  In packet types that contain a Packet Number
//# field, the least significant two bits (those with a mask of 0x03)
//# of byte 0 contain the length of the Packet Number field, encoded
//# as an unsigned two-bit integer that is one less than the length of
//# the Packet Number field in bytes.
/// Packet-number length in bytes, from an unprotected first byte.
pub fn first_byte_pn_len(b0: u8) -> (n: u8)
    ensures
        n == spec_pn_len(b0),
        1 <= n <= 4,
{
    proof {
        assert(b0 & 3u8 <= 3) by (bit_vector);
    }
    (b0 & 3) + 1
}

/// The Key Phase bit of an unprotected short-header first byte.
pub fn first_byte_key_phase(b0: u8) -> (k: bool)
    ensures
        k == spec_key_phase(b0),
{
    b0 & 0x04 != 0
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# An endpoint MUST
//# treat receipt of a packet that has a non-zero value for these bits
//# after removing both packet and header protection as a connection
//# error of type PROTOCOL_VIOLATION.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.3.1
//# An endpoint MUST treat receipt of a
//# packet that has a non-zero value for these bits, after removing
//# both packet and header protection, as a connection error of type
//# PROTOCOL_VIOLATION.
/// Whether an unprotected first byte's reserved bits are 0. The caller turns `false` into
/// PROTOCOL_VIOLATION only after AEAD succeeds.
pub fn reserved_bits_zero(b0: u8, long: bool) -> (z: bool)
    ensures
        z == spec_reserved_bits_zero(b0, long),
{
    let mask: u8 = if long {
        0x0c
    } else {
        0x18
    };
    b0 & mask == 0
}

} // verus!
