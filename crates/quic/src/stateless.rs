//! Version Negotiation (RFC 9000 §6.1, §17.2.1) and Stateless Reset (§10.3) builders. Both
//! are stateless; the shell calls each at most once per datagram, which keeps §17.2.1's
//! "no more than one Version Negotiation packet" true.
use vstd::prelude::*;
use vstd::slice::slice_subrange;

use crate::codes::*;
use crate::header::*;

verus! {

/// The longest Stateless Reset we send.
pub const RESET_MAX_LEN: usize = 43;

//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2.1
//# The value in the Unused field is set to an arbitrary value by the
//# server.  Clients MUST ignore the value of this field.  Where QUIC
//# might be multiplexed with other protocols (see [RFC7983]), servers
//# SHOULD set the most significant bit of this field (0x40) to 1 so that
//# Version Negotiation packets appear to have the Fixed Bit field.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2.1
//# The Version field of a Version Negotiation packet MUST be set to
//# 0x00000000.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2.1
//# The server MUST include the value from the Source Connection ID field
//# of the packet it receives in the Destination Connection ID field.
//# The value for Source Connection ID MUST be copied from the
//# Destination Connection ID of the received packet, which is initially
//# randomly selected by a client.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2.1
//# The remainder of the Version Negotiation packet is a list of 32-bit
//# versions that the server supports.
/// A Version Negotiation packet: first byte 0xc0, Version 0, the client's SCID as our DCID,
/// the client's DCID as our SCID, then the one version we support.
pub open spec fn spec_vn_bytes(dcid: Seq<u8>, scid: Seq<u8>) -> Seq<u8> {
    seq![0xc0u8, 0u8, 0u8, 0u8, 0u8, scid.len() as u8] + scid + seq![dcid.len() as u8] + dcid
        + seq![0u8, 0u8, 0u8, 1u8]
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-6.1
//# An endpoint MUST NOT send a Version Negotiation packet
//# in response to receiving a Version Negotiation packet.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2.1
//# Version-
//# specific rules for the connection ID therefore MUST NOT influence a
//# decision about whether to send a Version Negotiation packet.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2.1
//# A server MUST NOT send more than one Version Negotiation packet in
//# response to a single UDP datagram.
/// The response to a datagram: `Some` only when it is at least 1200 bytes (§5.2.2) and its
/// first packet has an unsupported version. `rfc_long_header` drops version 0, so a Version
/// Negotiation packet never gets one, and it applies no version-specific CID limits to
/// unsupported versions.
pub open spec fn rfc_version_negotiation(d: Seq<u8>) -> Option<Seq<u8>> {
    if d.len() < MIN_INITIAL_DATAGRAM {
        None
    } else {
        match rfc_long_header(d) {
            Some(SpecHeader::UnsupportedVersion { version, dcid, scid }) => Some(
                spec_vn_bytes(dcid, scid),
            ),
            _ => None,
        }
    }
}

pub open spec fn spec_reset_len(trigger_len: nat) -> nat {
    if trigger_len - 1 < RESET_MAX_LEN {
        (trigger_len - 1) as nat
    } else {
        RESET_MAX_LEN as nat
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-10.3
//# Endpoints MUST send Stateless Resets formatted as a packet with a
//# short header.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-10.3
//# A Stateless Reset uses an entire UDP datagram, starting with the
//# first two bits of the packet header.  The remainder of the first byte
//# and an arbitrary number of bytes following it are set to values that
//# SHOULD be indistinguishable from random.  The last 16 bytes of the
//# datagram contain a stateless reset token.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-10.3
//# An endpoint that sends a Stateless Reset in response to a packet that is
//# 43 bytes or shorter SHOULD send a Stateless Reset that is one byte
//# shorter than the packet it responds to.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-10.3.3
//# An endpoint MUST ensure that every Stateless Reset that it sends is
//# smaller than the packet that triggered it, unless it maintains state
//# sufficient to prevent looping.
/// A Stateless Reset for a trigger of `trigger_len` bytes: `None` when no reset of at least
/// 21 bytes is smaller than the trigger, else `[0x40 | u[0] & 0x3f] ++ u[1..L-16] ++ token`
/// with `L = min(trigger_len - 1, 43)`.
pub open spec fn rfc_stateless_reset(trigger_len: nat, u: Seq<u8>, token: Seq<u8>) -> Option<
    Seq<u8>,
> {
    if trigger_len <= MIN_SHORT_PACKET {
        None
    } else {
        Some(
            seq![0x40u8 | (u[0] & 0x3fu8)] + u.subrange(1, spec_reset_len(trigger_len) - 16)
                + token,
        )
    }
}

fn put_slice(s: &[u8], out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + s@,
{
    out.extend_from_slice(s);
    assert(out@ =~= old(out)@ + s@);
}

/// The Version Negotiation packet answering `datagram`, if it warrants one.
pub fn version_negotiation(datagram: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        r.deep_view() == rfc_version_negotiation(datagram@),
{
    if datagram.len() < MIN_INITIAL_DATAGRAM {
        return None;
    }
    match parse_long_header(datagram) {
        Some(Header::UnsupportedVersion { version: _, dcid, scid }) => {
            let mut out: Vec<u8> = Vec::new();
            out.push(0xc0);
            out.push(0);
            out.push(0);
            out.push(0);
            out.push(0);
            out.push(scid.len() as u8);
            put_slice(scid.as_slice(), &mut out);
            out.push(dcid.len() as u8);
            put_slice(dcid.as_slice(), &mut out);
            out.push(0);
            out.push(0);
            out.push(0);
            out.push(1);
            proof {
                assert(out@ =~= spec_vn_bytes(dcid@, scid@));
            }
            Some(out)
        },
        _ => None,
    }
}

// ponytail: fixed 43-byte cap for large triggers; vary the length if reset fingerprinting matters.
/// A Stateless Reset for a trigger of `trigger_len` bytes, built from at least 27 unpredictable
/// bytes and the connection's 16-byte token.
pub fn stateless_reset(trigger_len: usize, unpredictable: &[u8], token: &[u8]) -> (r: Option<
    Vec<u8>,
>)
    requires
        unpredictable.len() >= 27,
        token.len() == RESET_TOKEN_LEN,
    ensures
        r.deep_view() == rfc_stateless_reset(trigger_len as nat, unpredictable@, token@),
        r is None <==> trigger_len <= MIN_SHORT_PACKET,
        match r {
            None => true,
            Some(v) => {
                &&& MIN_SHORT_PACKET <= v.len() < trigger_len
                &&& v.len() < 3 * trigger_len
                &&& v[0] & 0xc0u8 == 0x40u8
                &&& v@.skip(v.len() - RESET_TOKEN_LEN as int) == token@
            },
        },
{
    if trigger_len <= MIN_SHORT_PACKET {
        return None;
    }
    let l = if trigger_len - 1 < RESET_MAX_LEN {
        trigger_len - 1
    } else {
        RESET_MAX_LEN
    };
    let mut out: Vec<u8> = Vec::new();
    let b0 = 0x40u8 | (unpredictable[0] & 0x3f);
    proof {
        let u0 = unpredictable[0];
        assert((0x40u8 | (u0 & 0x3fu8)) & 0xc0u8 == 0x40u8) by (bit_vector);
    }
    out.push(b0);
    put_slice(slice_subrange(unpredictable, 1, l - 16), &mut out);
    put_slice(token, &mut out);
    proof {
        assert(out@.skip(out@.len() - 16) =~= token@);
    }
    Some(out)
}

} // verus!
