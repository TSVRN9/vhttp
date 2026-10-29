//! The handshake's connection IDs and transport-parameter semantics (RFC 9000 §7.2, §7.3):
//! the IDs fixed by the client's first Initial, our transport parameters (which carry them),
//! the check of the client's, address validation tokens (§8.1.3) and ALPN (§7). Sans-IO.
use vstd::prelude::*;
use vstd::slice::slice_to_vec;
use wire::varint::*;

use crate::cid::*;
use crate::codes::*;
use crate::payload::*;
use crate::streams::*;
use crate::tp::*;

verus! {

// =============================================================================
// A client's parameters are in range for `Streams::new` (obligation 4)
// =============================================================================

/// `peer_tp_wf` gives `Streams::new` its `peer` precondition.
pub proof fn lemma_peer_tp_stream_ok(t: SpecTp)
    requires
        peer_tp_wf(t),
    ensures
        stream_tp_ok(t),
{
}

/// Every client transport parameters extension that parses satisfies `stream_tp_ok`.
pub proof fn theorem_parsed_peer_stream_ok(b: Seq<u8>)
    ensures
        rfc_transport_params(b, true) matches Ok(t) ==> stream_tp_ok(t),
{
    theorem_peer_tp_wf(b);
    if let Ok(t) = rfc_transport_params(b, true) {
        lemma_peer_tp_stream_ok(t);
    }
}

// =============================================================================
// Our transport parameters
// =============================================================================

/// `tp` with valid placeholder values in the three ID fields `fill_local_tp` sets.
pub open spec fn local_fill(tp: SpecTp) -> SpecTp {
    SpecTp {
        original_destination_connection_id: Some(Seq::empty()),
        initial_source_connection_id: Some(Seq::empty()),
        stateless_reset_token: Some(Seq::new(RESET_TOKEN_LEN as nat, |_i: int| 0u8)),
        ..tp
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-6.2
//# Therefore, the transport parameters sent by both clients
//# and servers MUST allow the peer to create at least three
//# unidirectional streams.
/// The transport parameters the shell may give a connection, before `fill_local_tp`: valid
/// once filled, at least 3 and at most `MAX_LOCAL_STREAMS` peer uni streams, at most
/// `MAX_LOCAL_STREAMS` peer bidi streams, an `active_connection_id_limit` that `PeerCids`
/// holds, and no migration.
pub open spec fn local_tp_ok(tp: SpecTp) -> bool {
    &&& server_tp_wf(local_fill(tp))
    &&& 3 <= tp.initial_max_streams_uni <= MAX_LOCAL_STREAMS
    &&& tp.initial_max_streams_bidi <= MAX_LOCAL_STREAMS
    &&& 2 <= tp.active_connection_id_limit <= PEER_CID_CAP
    &&& tp.disable_active_migration
    &&& tp.max_udp_payload_size >= 1200
}

/// `local_tp_ok` gives `Streams::new` its `local` preconditions.
pub proof fn lemma_local_tp_streams(tp: SpecTp)
    requires
        local_tp_ok(tp),
    ensures
        stream_tp_ok(tp),
        tp.initial_max_streams_uni >= 3,
        tp.initial_max_streams_bidi <= MAX_LOCAL_STREAMS,
        tp.initial_max_streams_uni <= MAX_LOCAL_STREAMS,
{
    lemma_server_tp_stream_ok(local_fill(tp));
}

/// `local_tp_ok`, executable.
pub fn is_local_tp_ok(tp: &TransportParams) -> (r: bool)
    ensures
        r == local_tp_ok(tp@),
{
    tp.max_idle_timeout <= VARINT_MAX && tp.max_udp_payload_size <= VARINT_MAX
        && tp.initial_max_data <= VARINT_MAX && tp.initial_max_stream_data_bidi_local
        <= VARINT_MAX && tp.initial_max_stream_data_bidi_remote <= VARINT_MAX
        && tp.initial_max_stream_data_uni <= VARINT_MAX && tp.initial_max_streams_bidi
        <= VARINT_MAX && tp.initial_max_streams_uni <= VARINT_MAX && tp.ack_delay_exponent
        <= VARINT_MAX && tp.max_ack_delay <= VARINT_MAX && tp.active_connection_id_limit
        <= VARINT_MAX && tp.max_udp_payload_size >= 1200 && tp.ack_delay_exponent <= 20
        && tp.max_ack_delay < MAX_ACK_DELAY_LIMIT && tp.active_connection_id_limit >= 2
        && tp.initial_max_streams_bidi <= MAX_STREAMS_LIMIT && tp.initial_max_streams_uni
        <= MAX_STREAMS_LIMIT && 3 <= tp.initial_max_streams_uni && tp.initial_max_streams_uni
        <= MAX_LOCAL_STREAMS && tp.initial_max_streams_bidi <= MAX_LOCAL_STREAMS
        && tp.active_connection_id_limit <= PEER_CID_CAP && tp.disable_active_migration
}

// =============================================================================
// Handshake connection IDs
// =============================================================================

/// The connection IDs fixed by the client's first Initial packet, and our own.
#[derive(Debug, PartialEq, Eq)]
pub struct HandshakeIds {
    odcid: Vec<u8>,
    client_scid: Vec<u8>,
    local_scid: [u8; 8],
}

pub struct SpecHandshakeIds {
    /// The Destination Connection ID of the client's first Initial.
    pub odcid: Seq<u8>,
    /// Its Source Connection ID: the Destination Connection ID we send with.
    pub client_scid: Seq<u8>,
    /// Our Source Connection ID (sequence number 0).
    pub local_scid: Seq<u8>,
}

impl View for HandshakeIds {
    type V = SpecHandshakeIds;

    closed spec fn view(&self) -> SpecHandshakeIds {
        SpecHandshakeIds {
            odcid: self.odcid@,
            client_scid: self.client_scid@,
            local_scid: self.local_scid@,
        }
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-7.2
//= type=exception
//= reason=client-only
//# This Destination Connection ID MUST be at least 8 bytes in
//# length.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.2
//= type=exception
//= reason=client-only
//# Until a packet is received from the server, the client MUST
//# use the same Destination Connection ID value on all packets in this
//# connection.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.2
//= type=exception
//= reason=client-only
//# Once a
//# client has received a valid Initial packet from the server, it MUST
//# discard any subsequent packet it receives on that connection with a
//# different Source Connection ID.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.2
//= type=exception
//= reason=client-only
//# A client MUST change the Destination Connection ID it uses for
//# sending packets in response to only the first received Initial or
//# Retry packet.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.2
//# A server MUST set the Destination Connection ID it
//# uses for sending packets based on the first received Initial packet.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.4.1
//# A server MUST reject 0-RTT data if the restored values for transport
//# parameters cannot be supported.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.4.1
//= type=exception
//= reason=We never accept 0-RTT.
//# If 0-RTT data is accepted by the server, the server MUST NOT reduce
//# any limits or alter any values that might be violated by the client
//# with its 0-RTT data.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.4.1
//= type=exception
//= reason=We never accept 0-RTT.
//# In particular, a server that accepts 0-RTT data
//# MUST NOT set values for the following parameters (Section 18.2) that
//# are smaller than the remembered values of the parameters.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.4.1
//= type=exception
//= reason=binds authors of future specifications, not an implementation
//# The definition of a new transport parameter (Section 7.4.2) MUST
//# specify whether storing the transport parameter for 0-RTT is
//# mandatory, optional, or prohibited.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.4.1
//= type=exception
//= reason=client-only
//# A client MUST NOT use remembered values for the following parameters:
//# ack_delay_exponent, max_ack_delay, initial_source_connection_id,
//# original_destination_connection_id, preferred_address,
//# retry_source_connection_id, and stateless_reset_token.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.4.1
//= type=exception
//= reason=client-only
//# The client
//# MUST use the server's new values in the handshake instead; if the
//# server does not provide new values, the default values are used.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.4.1
//= type=exception
//= reason=client-only
//# A client that attempts to send 0-RTT data MUST remember all other
//# transport parameters used by the server that it is able to process.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.4.1
//= type=exception
//= reason=client-only
//# When sending frames in 0-RTT packets, a client MUST only use
//# remembered transport parameters; importantly, it MUST NOT use updated
//# values that it learns from the server's updated transport parameters
//# or from frames received in 1-RTT packets.
/// The IDs of a connection whose first packet is this client Initial: `None` unless `kind`
/// is Initial, `dcid` is 8 to 20 bytes and `scid` at most 20. `local_scid` is our seq-0 CID.
pub fn from_first(kind: PacketKind, dcid: &[u8], scid: &[u8], local_scid: [u8; 8]) -> (r: Option<
    HandshakeIds,
>)
    ensures
        r is None <==> (!(kind is Initial) || dcid@.len() < 8 || dcid@.len() > MAX_CID_LEN
            || scid@.len() > MAX_CID_LEN),
        r matches Some(h) ==> h.wf() && h@ == (SpecHandshakeIds {
            odcid: dcid@,
            client_scid: scid@,
            local_scid: local_scid@,
        }),
{
    // 0-RTT is always rejected (§7.4.1): `PacketKind` has no 0-RTT variant, the shell drops
    // 0-RTT packets unread (3e), and we never send `early_data` (Phase 4).
    match kind {
        PacketKind::Initial => {},
        PacketKind::Handshake | PacketKind::OneRtt => return None,
    }
    if dcid.len() < 8 || dcid.len() > MAX_CID_LEN || scid.len() > MAX_CID_LEN {
        return None;
    }
    Some(HandshakeIds { odcid: slice_to_vec(dcid), client_scid: slice_to_vec(scid), local_scid })
}

impl HandshakeIds {
    /// The lengths `from_first` checked.
    pub open spec fn wf(&self) -> bool {
        &&& 8 <= self@.odcid.len() <= MAX_CID_LEN
        &&& self@.client_scid.len() <= MAX_CID_LEN
    }

    pub fn odcid(&self) -> (r: &[u8])
        ensures
            r@ == self@.odcid,
    {
        self.odcid.as_slice()
    }

    pub fn client_scid(&self) -> (r: &[u8])
        ensures
            r@ == self@.client_scid,
    {
        self.client_scid.as_slice()
    }

    pub fn local_scid(&self) -> (r: [u8; 8])
        ensures
            r@ == self@.local_scid,
    {
        self.local_scid
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-7.2
    //# Any further changes to the Destination Connection ID are only
    //# permitted if the values are taken from NEW_CONNECTION_ID frames; if
    //# subsequent Initial packets include a different Source Connection ID,
    //# they MUST be discarded.
    /// Whether a later Initial with Source Connection ID `scid` may be processed; one with a
    /// different SCID is dropped, not a connection error. Any further change to the DCID we
    /// send with comes from NEW_CONNECTION_ID frames (`PeerCids`).
    pub fn initial_scid_ok(&self, scid: &[u8]) -> (r: bool)
        ensures
            r == (scid@ == self@.client_scid),
    {
        eq_bytes(scid, self.client_scid.as_slice())
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-7.3
    //# Each endpoint includes the value of the Source Connection ID field
    //# from the first Initial packet it sent in the
    //# initial_source_connection_id transport parameter; see Section 18.2.
    //# A server includes the Destination Connection ID field from the first
    //# Initial packet it received from the client in the
    //# original_destination_connection_id transport parameter;
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-7.3
    //# The values provided by a peer for these transport parameters MUST
    //# match the values that an endpoint used in the Destination and Source
    //# Connection ID fields of Initial packets that it sent (and received,
    //# for servers).
    /// `tp` with our original_destination_connection_id, initial_source_connection_id and
    /// stateless_reset_token (`token0`, the token of our seq-0 CID). We send no Retry, so no
    /// retry_source_connection_id.
    pub fn fill_local_tp(&self, tp: &TransportParams, token0: [u8; 16]) -> (r: TransportParams)
        requires
            self.wf(),
        ensures
            r@ == (SpecTp {
                original_destination_connection_id: Some(self@.odcid),
                initial_source_connection_id: Some(self@.local_scid),
                stateless_reset_token: Some(token0@),
                ..tp@
            }),
            local_tp_ok(tp@) ==> server_tp_wf(r@) && local_tp_ok(r@),
    {
        TransportParams {
            original_destination_connection_id: Some(slice_to_vec(self.odcid.as_slice())),
            max_idle_timeout: tp.max_idle_timeout,
            stateless_reset_token: Some(token0),
            max_udp_payload_size: tp.max_udp_payload_size,
            initial_max_data: tp.initial_max_data,
            initial_max_stream_data_bidi_local: tp.initial_max_stream_data_bidi_local,
            initial_max_stream_data_bidi_remote: tp.initial_max_stream_data_bidi_remote,
            initial_max_stream_data_uni: tp.initial_max_stream_data_uni,
            initial_max_streams_bidi: tp.initial_max_streams_bidi,
            initial_max_streams_uni: tp.initial_max_streams_uni,
            ack_delay_exponent: tp.ack_delay_exponent,
            max_ack_delay: tp.max_ack_delay,
            disable_active_migration: tp.disable_active_migration,
            active_connection_id_limit: tp.active_connection_id_limit,
            initial_source_connection_id: Some(slice_to_vec(self.local_scid.as_slice())),
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-7.3
    //# The values provided by a peer for these transport parameters MUST
    //# match the values that an endpoint used in the Destination and Source
    //# Connection ID fields of Initial packets that it sent (and received,
    //# for servers).  Endpoints MUST validate that received transport
    //# parameters match received connection ID values.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-7.3
    //# An endpoint MUST treat the absence of the
    //# initial_source_connection_id transport parameter from either endpoint
    //# or the absence of the original_destination_connection_id transport
    //# parameter from the server as a connection error of type
    //# TRANSPORT_PARAMETER_ERROR.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-7.3
    //# An endpoint MUST treat the following as a connection error of type
    //# TRANSPORT_PARAMETER_ERROR or PROTOCOL_VIOLATION:
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-7.3
    //# a mismatch between values received from a peer in these transport
    //# parameters and the value sent in the corresponding Destination or
    //# Source Connection ID fields of Initial packets.
    /// The client's initial_source_connection_id must be the Source Connection ID of its first
    /// Initial. A client retry_source_connection_id (or any server-only parameter) is already
    /// TRANSPORT_PARAMETER_ERROR in `parse_transport_params`.
    pub fn check_peer_tp(&self, tp: &TransportParams) -> (r: Result<(), u64>)
        ensures
            r is Ok <==> tp@.initial_source_connection_id == Some(self@.client_scid),
            r is Err ==> r == Err::<(), u64>(TRANSPORT_PARAMETER_ERROR),
    {
        match &tp.initial_source_connection_id {
            Some(c) => if eq_bytes(c.as_slice(), self.client_scid.as_slice()) {
                Ok(())
            } else {
                Err(TRANSPORT_PARAMETER_ERROR)
            },
            None => Err(TRANSPORT_PARAMETER_ERROR),
        }
    }
}

// =============================================================================
// Tokens and ALPN
// =============================================================================

//= https://www.rfc-editor.org/rfc/rfc9000#section-8.1.3
//# When a server receives an Initial packet with an address validation
//# token, it MUST attempt to validate the token, unless it has already
//# completed address validation.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-8.1.3
//= type=exception
//= reason=client-only
//# The client
//# MUST include the token in all Initial packets it sends, unless a
//# Retry replaces the token with a newer one.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-8.1.3
//= type=exception
//= reason=client-only
//# The client MUST NOT use
//# the token provided in a Retry for future connections.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-8.1.3
//= type=exception
//= reason=client-only
//# A client MUST NOT include
//# a token that is not applicable to the server that it is connecting
//# to, unless the client has the knowledge that the server that issued
//# the token and the server the client is connecting to are jointly
//# managing the tokens.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-8.1.3
//= type=exception
//= reason=client-only
//# In comparison, a
//# token obtained in a Retry packet MUST be used immediately during the
//# connection attempt and cannot be used in subsequent connection
//# attempts.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-8.1.3
//= type=exception
//= reason=We send no NEW_TOKEN frames.
//# A token issued with NEW_TOKEN MUST NOT include information that would
//# allow values to be linked by an observer to the connection on which
//# it was issued.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-8.1.3
//= type=exception
//= reason=We send no NEW_TOKEN frames.
//# A server MUST ensure that every NEW_TOKEN frame it sends
//# is unique across all clients, with the exception of those sent to
//# repair losses of previously sent NEW_TOKEN frames.
/// Whether the Token of a client Initial validates its address. We issue no tokens (no Retry,
/// no NEW_TOKEN), so none does: the client proceeds as unvalidated (§8.1.3 SHOULD), never
/// INVALID_TOKEN, which is for Retry tokens.
pub fn token_validates(_token: &[u8]) -> (r: bool)
    ensures
        !r,
{
    false
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-7
//# Endpoints MUST explicitly negotiate an application protocol.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-7
//= type=exception
//= reason=Handshake properties are provided by TLS 1.3 (Phase 4).
//# The cryptographic handshake MUST
//# provide the following properties:
/// The ALPN protocol TLS negotiated must be "h3"; anything else is CRYPTO_ERROR with TLS
/// alert no_application_protocol (0x78; RFC 9001 §8.1).
pub fn check_alpn(alpn: &[u8]) -> (r: Result<(), u64>)
    ensures
        r is Ok <==> alpn@ == seq![0x68u8, 0x33u8],
        r is Err ==> r == Err::<(), u64>((CRYPTO_ERROR_BASE + 0x78) as u64),
{
    assert((alpn@.len() == 2 && alpn@[0] == 0x68 && alpn@[1] == 0x33) ==> alpn@ =~= seq![
        0x68u8,
        0x33u8,
    ]);
    if alpn.len() == 2 && alpn[0] == 0x68 && alpn[1] == 0x33 {
        Ok(())
    } else {
        Err(CRYPTO_ERROR_BASE + 0x78)
    }
}

} // verus!
