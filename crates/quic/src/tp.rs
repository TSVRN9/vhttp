//! QUIC transport parameters (RFC 9000 §7.4, §18): the client's, as a server receives them,
//! and the server's own.
use vstd::prelude::*;
use vstd::slice::{slice_subrange, slice_to_vec};
use wire::varint::*;

use crate::ack::*;
use crate::codes::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::frame::*;
use crate::header::*;

verus! {

/// The transport parameters of one endpoint. An absent parameter holds its RFC default.
#[derive(Debug, PartialEq, Eq)]
pub struct TransportParams {
    pub original_destination_connection_id: Option<Vec<u8>>,
    pub max_idle_timeout: u64,
    pub stateless_reset_token: Option<[u8; 16]>,
    pub max_udp_payload_size: u64,
    pub initial_max_data: u64,
    pub initial_max_stream_data_bidi_local: u64,
    pub initial_max_stream_data_bidi_remote: u64,
    pub initial_max_stream_data_uni: u64,
    pub initial_max_streams_bidi: u64,
    pub initial_max_streams_uni: u64,
    pub ack_delay_exponent: u64,
    pub max_ack_delay: u64,
    pub disable_active_migration: bool,
    pub active_connection_id_limit: u64,
    /// Absence is an error (§7.3), which the connection layer checks.
    pub initial_source_connection_id: Option<Vec<u8>>,
}

pub struct SpecTp {
    pub original_destination_connection_id: Option<Seq<u8>>,
    pub max_idle_timeout: u64,
    pub stateless_reset_token: Option<Seq<u8>>,
    pub max_udp_payload_size: u64,
    pub initial_max_data: u64,
    pub initial_max_stream_data_bidi_local: u64,
    pub initial_max_stream_data_bidi_remote: u64,
    pub initial_max_stream_data_uni: u64,
    pub initial_max_streams_bidi: u64,
    pub initial_max_streams_uni: u64,
    pub ack_delay_exponent: u64,
    pub max_ack_delay: u64,
    pub disable_active_migration: bool,
    pub active_connection_id_limit: u64,
    pub initial_source_connection_id: Option<Seq<u8>>,
}

impl View for TransportParams {
    type V = SpecTp;

    open spec fn view(&self) -> SpecTp {
        SpecTp {
            original_destination_connection_id: match &self.original_destination_connection_id {
                Some(c) => Some(c@),
                None => None,
            },
            max_idle_timeout: self.max_idle_timeout,
            stateless_reset_token: match self.stateless_reset_token {
                Some(k) => Some(k@),
                None => None,
            },
            max_udp_payload_size: self.max_udp_payload_size,
            initial_max_data: self.initial_max_data,
            initial_max_stream_data_bidi_local: self.initial_max_stream_data_bidi_local,
            initial_max_stream_data_bidi_remote: self.initial_max_stream_data_bidi_remote,
            initial_max_stream_data_uni: self.initial_max_stream_data_uni,
            initial_max_streams_bidi: self.initial_max_streams_bidi,
            initial_max_streams_uni: self.initial_max_streams_uni,
            ack_delay_exponent: self.ack_delay_exponent,
            max_ack_delay: self.max_ack_delay,
            disable_active_migration: self.disable_active_migration,
            active_connection_id_limit: self.active_connection_id_limit,
            initial_source_connection_id: match &self.initial_source_connection_id {
                Some(c) => Some(c@),
                None => None,
            },
        }
    }
}

// =============================================================================
// RFC 9000 transcription
// =============================================================================

//= https://www.rfc-editor.org/rfc/rfc9000#section-18.2
//# Transport parameters have a
//# default value of 0 if the transport parameter is absent, unless
//# otherwise stated.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-18.2
//# If this value is absent, a
//# default value of 3 is assumed (indicating a multiplier of 8).
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-18.2
//# If this value is absent, a default of 25 milliseconds is
//# assumed.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-18.2
//# If
//# this transport parameter is absent, a default of 2 is assumed.
/// The parameters of a peer that sent none.
pub open spec fn spec_default_tp() -> SpecTp {
    SpecTp {
        original_destination_connection_id: None,
        max_idle_timeout: 0,
        stateless_reset_token: None,
        max_udp_payload_size: 65527,
        initial_max_data: 0,
        initial_max_stream_data_bidi_local: 0,
        initial_max_stream_data_bidi_remote: 0,
        initial_max_stream_data_uni: 0,
        initial_max_streams_bidi: 0,
        initial_max_streams_uni: 0,
        ack_delay_exponent: 3,
        max_ack_delay: 25,
        disable_active_migration: false,
        active_connection_id_limit: 2,
        initial_source_connection_id: None,
    }
}

/// The parameters whose value is one varint.
pub open spec fn is_int_tp(id: u64) -> bool {
    id == TP_MAX_IDLE_TIMEOUT || (TP_MAX_UDP_PAYLOAD_SIZE <= id && id <= TP_MAX_ACK_DELAY) || id
        == TP_ACTIVE_CONNECTION_ID_LIMIT
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-18.2
//# The default for this parameter is the maximum permitted UDP
//# payload of 65527.  Values below 1200 are invalid.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-18.2
//# Values above 20 are invalid.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-18.2
//# Values of 2^14 or greater are invalid.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-18.2
//# The value of the
//# active_connection_id_limit parameter MUST be at least 2.  An
//# endpoint that receives a value less than 2 MUST close the
//# connection with an error of type TRANSPORT_PARAMETER_ERROR.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-4.6
//# If a max_streams transport parameter or a MAX_STREAMS frame is
//# received with a value greater than 2^60, this would allow a maximum
//# stream ID that cannot be expressed as a variable-length integer; see
//# Section 16.  If either is received, the connection MUST be closed
//# immediately with a connection error of type TRANSPORT_PARAMETER_ERROR
//# if the offending value was received in a transport parameter or of
//# type FRAME_ENCODING_ERROR if it was received in a frame; see
//# Section 10.2.
/// Whether integer parameter `id` may hold `x`.
pub open spec fn tp_int_valid(id: u64, x: u64) -> bool {
    &&& id == TP_MAX_UDP_PAYLOAD_SIZE ==> x >= 1200
    &&& id == TP_ACK_DELAY_EXPONENT ==> x <= 20
    &&& id == TP_MAX_ACK_DELAY ==> x < MAX_ACK_DELAY_LIMIT
    &&& id == TP_ACTIVE_CONNECTION_ID_LIMIT ==> x >= 2
    &&& (id == TP_INITIAL_MAX_STREAMS_BIDI || id == TP_INITIAL_MAX_STREAMS_UNI) ==> x
        <= MAX_STREAMS_LIMIT
}

/// `t` with integer parameter `id` set to `x`.
pub open spec fn spec_set_int(t: SpecTp, id: u64, x: u64) -> SpecTp {
    if id == TP_MAX_IDLE_TIMEOUT {
        SpecTp { max_idle_timeout: x, ..t }
    } else if id == TP_MAX_UDP_PAYLOAD_SIZE {
        SpecTp { max_udp_payload_size: x, ..t }
    } else if id == TP_INITIAL_MAX_DATA {
        SpecTp { initial_max_data: x, ..t }
    } else if id == TP_INITIAL_MAX_STREAM_DATA_BIDI_LOCAL {
        SpecTp { initial_max_stream_data_bidi_local: x, ..t }
    } else if id == TP_INITIAL_MAX_STREAM_DATA_BIDI_REMOTE {
        SpecTp { initial_max_stream_data_bidi_remote: x, ..t }
    } else if id == TP_INITIAL_MAX_STREAM_DATA_UNI {
        SpecTp { initial_max_stream_data_uni: x, ..t }
    } else if id == TP_INITIAL_MAX_STREAMS_BIDI {
        SpecTp { initial_max_streams_bidi: x, ..t }
    } else if id == TP_INITIAL_MAX_STREAMS_UNI {
        SpecTp { initial_max_streams_uni: x, ..t }
    } else if id == TP_ACK_DELAY_EXPONENT {
        SpecTp { ack_delay_exponent: x, ..t }
    } else if id == TP_MAX_ACK_DELAY {
        SpecTp { max_ack_delay: x, ..t }
    } else {
        SpecTp { active_connection_id_limit: x, ..t }
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-7.4
//# An endpoint MUST treat receipt of a transport parameter with an
//# invalid value as a connection error of type
//# TRANSPORT_PARAMETER_ERROR.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-18.2
//# This parameter is
//# a sequence of 16 bytes.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-18.2
//# This
//# parameter is a zero-length value.
/// `t` with known parameter `id` (not 0x0d or 0x10) set from value `v`; `None` when `v` is
/// not a valid value for `id`. An integer value must be exactly one varint, of any length.
pub open spec fn rfc_tp_value(id: u64, v: Seq<u8>, t: SpecTp) -> Option<SpecTp> {
    if is_int_tp(id) {
        match rfc_varint_decode(v) {
            Some((n, x)) => if n == v.len() && tp_int_valid(id, x) {
                Some(spec_set_int(t, id, x))
            } else {
                None
            },
            None => None,
        }
    } else if id == TP_DISABLE_ACTIVE_MIGRATION {
        if v.len() == 0 {
            Some(SpecTp { disable_active_migration: true, ..t })
        } else {
            None
        }
    } else if id == TP_STATELESS_RESET_TOKEN {
        if v.len() == RESET_TOKEN_LEN {
            Some(SpecTp { stateless_reset_token: Some(v), ..t })
        } else {
            None
        }
    } else if id == TP_ORIGINAL_DESTINATION_CONNECTION_ID {
        if v.len() <= MAX_CID_LEN {
            Some(SpecTp { original_destination_connection_id: Some(v), ..t })
        } else {
            None
        }
    } else if id == TP_INITIAL_SOURCE_CONNECTION_ID {
        if v.len() <= MAX_CID_LEN {
            Some(SpecTp { initial_source_connection_id: Some(v), ..t })
        } else {
            None
        }
    } else {
        None
    }
}

/// The seen-mask bit of known parameter `id` (at most 0x10).
pub open spec fn tp_bit(id: u64) -> u32 {
    1u32 << (id as u32)
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-7.4
//# An endpoint MUST NOT send a parameter more than once in a given
//# transport parameters extension.  An endpoint SHOULD treat receipt of
//# duplicate transport parameters as a connection error of type
//# TRANSPORT_PARAMETER_ERROR.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-18.2
//# A client MUST NOT include any server-only transport parameter:
//# original_destination_connection_id, preferred_address,
//# retry_source_connection_id, or stateless_reset_token.  A server MUST
//# treat receipt of any of these transport parameters as a connection
//# error of type TRANSPORT_PARAMETER_ERROR.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-18.2
//# This transport parameter MUST NOT be sent
//# by a client but MAY be sent by a server.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.4.2
//# An endpoint MUST ignore transport parameters that it does
//# not support.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-18.1
//# These transport parameters
//# have no semantics and can carry arbitrary values.
/// One parameter `id` with value `v` applied to `t`, whose known IDs seen so far are the
/// bits of `seen`; `None` is TRANSPORT_PARAMETER_ERROR. Any ID above 0x10 is ignored,
/// including every reserved `31 * N + 27`. preferred_address (0x0d) and
/// retry_source_connection_id (0x10) are errors from either side: we never send them, so
/// they are not modelled.
// ponytail: unknown-ID duplicates are not detected; add a seen-set if a peer abuses it.
pub open spec fn rfc_tp_apply(id: u64, v: Seq<u8>, from_client: bool, t: SpecTp, seen: u32) -> Option<
    (SpecTp, u32),
> {
    if id > TP_RETRY_SOURCE_CONNECTION_ID {
        Some((t, seen))
    } else if seen & tp_bit(id) != 0 {
        None
    } else if id == TP_PREFERRED_ADDRESS || id == TP_RETRY_SOURCE_CONNECTION_ID || (from_client
        && (id == TP_ORIGINAL_DESTINATION_CONNECTION_ID || id == TP_STATELESS_RESET_TOKEN)) {
        None
    } else {
        match rfc_tp_value(id, v, t) {
            Some(t2) => Some((t2, seen | tp_bit(id))),
            None => None,
        }
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-18
//# Each transport parameter is encoded as an (identifier, length, value)
//# tuple, as shown in Figure 21:
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-18
//# The Transport Parameter Length field contains the length of the
//# Transport Parameter Value field in bytes.
/// The parameters from offset `p` to the end of `b`, applied to `t` with mask `seen`.
pub open spec fn rfc_tp_from(b: Seq<u8>, p: int, from_client: bool, t: SpecTp, seen: u32) -> Result<
    SpecTp,
    u64,
>
    decreases (if p < b.len() {
        b.len() - p
    } else {
        0
    }),
    via tp_from_decreases
{
    if p >= b.len() {
        Ok(t)
    } else {
        match rfc_vint(b, p) {
            None => Err(TRANSPORT_PARAMETER_ERROR),
            Some((id, q)) => match rfc_vint(b, q) {
                None => Err(TRANSPORT_PARAMETER_ERROR),
                Some((len, r)) => match rfc_bytes(b, r, len as int) {
                    None => Err(TRANSPORT_PARAMETER_ERROR),
                    Some((v, s)) => match rfc_tp_apply(id, v, from_client, t, seen) {
                        None => Err(TRANSPORT_PARAMETER_ERROR),
                        Some((t2, seen2)) => rfc_tp_from(b, s, from_client, t2, seen2),
                    },
                },
            },
        }
    }
}

#[verifier::decreases_by]
proof fn tp_from_decreases(b: Seq<u8>, p: int, from_client: bool, t: SpecTp, seen: u32) {
    lemma_decode_len_bounds(b.skip(p));
    if let Some((n, _)) = rfc_varint_decode(b.skip(p)) {
        lemma_decode_len_bounds(b.skip(p + n));
    }
}

/// A peer's transport parameters extension value, as a server (`from_client`) receives it.
pub open spec fn rfc_transport_params(b: Seq<u8>, from_client: bool) -> Result<SpecTp, u64> {
    rfc_tp_from(b, 0, from_client, spec_default_tp(), 0)
}

// =============================================================================
// Serialization specs
// =============================================================================

/// The parameters a server may send: both connection IDs and a reset token, and every
/// value valid. The token length is implied by the exec array type; a spec value has to
/// state it.
pub open spec fn server_tp_wf(p: SpecTp) -> bool {
    &&& p.original_destination_connection_id matches Some(c) && c.len() <= MAX_CID_LEN
    &&& p.initial_source_connection_id matches Some(c) && c.len() <= MAX_CID_LEN
    &&& p.stateless_reset_token matches Some(k) && k.len() == RESET_TOKEN_LEN
    &&& p.max_idle_timeout <= VARINT_MAX
    &&& p.max_udp_payload_size <= VARINT_MAX
    &&& p.initial_max_data <= VARINT_MAX
    &&& p.initial_max_stream_data_bidi_local <= VARINT_MAX
    &&& p.initial_max_stream_data_bidi_remote <= VARINT_MAX
    &&& p.initial_max_stream_data_uni <= VARINT_MAX
    &&& p.initial_max_streams_bidi <= VARINT_MAX
    &&& p.initial_max_streams_uni <= VARINT_MAX
    &&& p.ack_delay_exponent <= VARINT_MAX
    &&& p.max_ack_delay <= VARINT_MAX
    &&& p.active_connection_id_limit <= VARINT_MAX
    &&& p.max_udp_payload_size >= 1200
    &&& p.ack_delay_exponent <= 20
    &&& p.max_ack_delay < MAX_ACK_DELAY_LIMIT
    &&& p.active_connection_id_limit >= 2
    &&& p.initial_max_streams_bidi <= MAX_STREAMS_LIMIT
    &&& p.initial_max_streams_uni <= MAX_STREAMS_LIMIT
}

/// One parameter: ID, Length, Value.
pub open spec fn spec_tp_entry(id: u64, v: Seq<u8>) -> Seq<u8> {
    spec_varint(id) + spec_varint(v.len() as u64) + v
}

/// One integer parameter, its value the minimal varint of `x`.
pub open spec fn spec_tp_int(id: u64, x: u64) -> Seq<u8> {
    spec_tp_entry(id, spec_varint(x))
}

/// Integer parameters 0x03 through 0x0b, then 0x0c if set, then 0x0e.
pub open spec fn spec_server_tail(p: SpecTp) -> Seq<u8> {
    spec_tp_int(TP_MAX_UDP_PAYLOAD_SIZE, p.max_udp_payload_size) + (spec_tp_int(
        TP_INITIAL_MAX_DATA,
        p.initial_max_data,
    ) + (spec_tp_int(TP_INITIAL_MAX_STREAM_DATA_BIDI_LOCAL, p.initial_max_stream_data_bidi_local)
        + (spec_tp_int(
        TP_INITIAL_MAX_STREAM_DATA_BIDI_REMOTE,
        p.initial_max_stream_data_bidi_remote,
    ) + (spec_tp_int(TP_INITIAL_MAX_STREAM_DATA_UNI, p.initial_max_stream_data_uni) + (
    spec_tp_int(TP_INITIAL_MAX_STREAMS_BIDI, p.initial_max_streams_bidi) + (spec_tp_int(
        TP_INITIAL_MAX_STREAMS_UNI,
        p.initial_max_streams_uni,
    ) + (spec_tp_int(TP_ACK_DELAY_EXPONENT, p.ack_delay_exponent) + (spec_tp_int(
        TP_MAX_ACK_DELAY,
        p.max_ack_delay,
    ) + spec_server_end(p)))))))))
}

/// disable_active_migration if set, then active_connection_id_limit.
pub open spec fn spec_server_end(p: SpecTp) -> Seq<u8> {
    if p.disable_active_migration {
        spec_tp_entry(TP_DISABLE_ACTIVE_MIGRATION, Seq::empty()) + spec_tp_int(
            TP_ACTIVE_CONNECTION_ID_LIMIT,
            p.active_connection_id_limit,
        )
    } else {
        spec_tp_int(TP_ACTIVE_CONNECTION_ID_LIMIT, p.active_connection_id_limit)
    }
}

/// What `serialize_server_params` writes: 0x00, 0x0f, 0x02, 0x01, 0x03-0x0b, 0x0c if set,
/// 0x0e, each once and every integer even at its default.
pub open spec fn spec_server_tp_bytes(p: SpecTp) -> Seq<u8> {
    spec_tp_entry(
        TP_ORIGINAL_DESTINATION_CONNECTION_ID,
        p.original_destination_connection_id.unwrap(),
    ) + (spec_tp_entry(TP_INITIAL_SOURCE_CONNECTION_ID, p.initial_source_connection_id.unwrap())
        + (spec_tp_entry(TP_STATELESS_RESET_TOKEN, p.stateless_reset_token.unwrap()) + (
    spec_tp_int(TP_MAX_IDLE_TIMEOUT, p.max_idle_timeout) + spec_server_tail(p))))
}

/// The longest `spec_server_tp_bytes`: two 20-byte CIDs (22 each), the token (18), eleven
/// integers (at most 10 each) and disable_active_migration (2).
pub const MAX_SERVER_TP_LEN: usize = 174;

// =============================================================================
// Proofs
// =============================================================================

/// One parameter at offset `p` is read and applied, and parsing continues after it.
proof fn lemma_tp_step(
    b: Seq<u8>,
    p: int,
    id: u64,
    v: Seq<u8>,
    tail: Seq<u8>,
    from_client: bool,
    t: SpecTp,
    seen: u32,
)
    requires
        0 <= p <= b.len(),
        id <= VARINT_MAX,
        v.len() <= VARINT_MAX,
        b.skip(p) == spec_tp_entry(id, v) + tail,
    ensures
        p + spec_tp_entry(id, v).len() <= b.len(),
        b.skip(p + spec_tp_entry(id, v).len()) == tail,
        rfc_tp_from(b, p, from_client, t, seen) == match rfc_tp_apply(id, v, from_client, t, seen) {
            None => Err(TRANSPORT_PARAMETER_ERROR),
            Some((t2, seen2)) => rfc_tp_from(
                b,
                p + spec_tp_entry(id, v).len(),
                from_client,
                t2,
                seen2,
            ),
        },
{
    hide(rfc_varint_decode);
    hide(rfc_tp_apply);
    let len = v.len() as u64;
    let n1 = spec_varint(id).len() as int;
    let n2 = spec_varint(len).len() as int;
    assert(b.skip(p) =~= spec_varint(id) + (spec_varint(len) + (v + tail)));
    lemma_varint_at(b, p, id, spec_varint(len) + (v + tail));
    lemma_varint_at(b, p + n1, len, v + tail);
    let r = p + n1 + n2;
    assert(b.skip(r) == v + tail);
    assert(b.subrange(r, r + v.len()) =~= v) by {
        assert forall|i: int| 0 <= i < v.len() implies b.subrange(r, r + v.len())[i] == v[i] by {
            assert(b.skip(r)[i] == b[r + i]);
        }
    }
    assert(b.skip(r + v.len()) =~= tail) by {
        assert forall|i: int| 0 <= i < tail.len() implies b.skip(r + v.len())[i] == tail[i] by {
            assert(b.skip(r)[v.len() + i] == b[r + v.len() + i]);
        }
    }
}

/// The seen-mask after each parameter the server writes, in its order.
proof fn lemma_server_masks()
    ensures
        0u32 & tp_bit(0x00) == 0 && 0u32 | tp_bit(0x00) == 0x0001u32,
        0x0001u32 & tp_bit(0x0f) == 0 && 0x0001u32 | tp_bit(0x0f) == 0x8001u32,
        0x8001u32 & tp_bit(0x02) == 0 && 0x8001u32 | tp_bit(0x02) == 0x8005u32,
        0x8005u32 & tp_bit(0x01) == 0 && 0x8005u32 | tp_bit(0x01) == 0x8007u32,
        0x8007u32 & tp_bit(0x03) == 0 && 0x8007u32 | tp_bit(0x03) == 0x800fu32,
        0x800fu32 & tp_bit(0x04) == 0 && 0x800fu32 | tp_bit(0x04) == 0x801fu32,
        0x801fu32 & tp_bit(0x05) == 0 && 0x801fu32 | tp_bit(0x05) == 0x803fu32,
        0x803fu32 & tp_bit(0x06) == 0 && 0x803fu32 | tp_bit(0x06) == 0x807fu32,
        0x807fu32 & tp_bit(0x07) == 0 && 0x807fu32 | tp_bit(0x07) == 0x80ffu32,
        0x80ffu32 & tp_bit(0x08) == 0 && 0x80ffu32 | tp_bit(0x08) == 0x81ffu32,
        0x81ffu32 & tp_bit(0x09) == 0 && 0x81ffu32 | tp_bit(0x09) == 0x83ffu32,
        0x83ffu32 & tp_bit(0x0a) == 0 && 0x83ffu32 | tp_bit(0x0a) == 0x87ffu32,
        0x87ffu32 & tp_bit(0x0b) == 0 && 0x87ffu32 | tp_bit(0x0b) == 0x8fffu32,
        0x8fffu32 & tp_bit(0x0c) == 0 && 0x8fffu32 | tp_bit(0x0c) == 0x9fffu32,
        0x8fffu32 & tp_bit(0x0e) == 0,
        0x9fffu32 & tp_bit(0x0e) == 0,
{
    assert(0u32 & (1u32 << 0u32) == 0 && 0u32 | (1u32 << 0u32) == 0x0001u32) by (bit_vector);
    assert(0x0001u32 & (1u32 << 15u32) == 0 && 0x0001u32 | (1u32 << 15u32) == 0x8001u32)
        by (bit_vector);
    assert(0x8001u32 & (1u32 << 2u32) == 0 && 0x8001u32 | (1u32 << 2u32) == 0x8005u32)
        by (bit_vector);
    assert(0x8005u32 & (1u32 << 1u32) == 0 && 0x8005u32 | (1u32 << 1u32) == 0x8007u32)
        by (bit_vector);
    assert(0x8007u32 & (1u32 << 3u32) == 0 && 0x8007u32 | (1u32 << 3u32) == 0x800fu32)
        by (bit_vector);
    assert(0x800fu32 & (1u32 << 4u32) == 0 && 0x800fu32 | (1u32 << 4u32) == 0x801fu32)
        by (bit_vector);
    assert(0x801fu32 & (1u32 << 5u32) == 0 && 0x801fu32 | (1u32 << 5u32) == 0x803fu32)
        by (bit_vector);
    assert(0x803fu32 & (1u32 << 6u32) == 0 && 0x803fu32 | (1u32 << 6u32) == 0x807fu32)
        by (bit_vector);
    assert(0x807fu32 & (1u32 << 7u32) == 0 && 0x807fu32 | (1u32 << 7u32) == 0x80ffu32)
        by (bit_vector);
    assert(0x80ffu32 & (1u32 << 8u32) == 0 && 0x80ffu32 | (1u32 << 8u32) == 0x81ffu32)
        by (bit_vector);
    assert(0x81ffu32 & (1u32 << 9u32) == 0 && 0x81ffu32 | (1u32 << 9u32) == 0x83ffu32)
        by (bit_vector);
    assert(0x83ffu32 & (1u32 << 10u32) == 0 && 0x83ffu32 | (1u32 << 10u32) == 0x87ffu32)
        by (bit_vector);
    assert(0x87ffu32 & (1u32 << 11u32) == 0 && 0x87ffu32 | (1u32 << 11u32) == 0x8fffu32)
        by (bit_vector);
    assert(0x8fffu32 & (1u32 << 12u32) == 0 && 0x8fffu32 | (1u32 << 12u32) == 0x9fffu32)
        by (bit_vector);
    assert(0x8fffu32 & (1u32 << 14u32) == 0 && 0x9fffu32 & (1u32 << 14u32) == 0)
        by (bit_vector);
}

/// One integer parameter the server writes reads back into its field.
proof fn lemma_int_step(
    b: Seq<u8>,
    p: int,
    id: u64,
    x: u64,
    tail: Seq<u8>,
    t: SpecTp,
    seen: u32,
)
    requires
        0 <= p <= b.len(),
        is_int_tp(id),
        x <= VARINT_MAX,
        tp_int_valid(id, x),
        seen & tp_bit(id) == 0,
        b.skip(p) == spec_tp_int(id, x) + tail,
    ensures
        p + spec_tp_int(id, x).len() <= b.len(),
        b.skip(p + spec_tp_int(id, x).len()) == tail,
        rfc_tp_from(b, p, false, t, seen) == rfc_tp_from(
            b,
            p + spec_tp_int(id, x).len(),
            false,
            spec_set_int(t, id, x),
            seen | tp_bit(id),
        ),
{
    theorem_serialize_matches_rfc(x);
    lemma_tp_step(b, p, id, spec_varint(x), tail, false, t, seen);
}

/// Parsing ends at the end of the bytes.
proof fn lemma_tp_end(b: Seq<u8>, p: int, t: SpecTp, seen: u32)
    requires
        0 <= p <= b.len(),
        b.skip(p) == Seq::<u8>::empty(),
    ensures
        rfc_tp_from(b, p, false, t, seen) == Ok::<SpecTp, u64>(t),
{
    assert(b.skip(p).len() == 0);
}

/// The integers and the end of the server's parameters read back into `s`, from a `t` that
/// already holds the rest of `s`.
proof fn lemma_server_tail(b: Seq<u8>, p: int, s: SpecTp, t: SpecTp)
    requires
        0 <= p <= b.len(),
        server_tp_wf(s),
        b.skip(p) == spec_server_tail(s),
        t.original_destination_connection_id == s.original_destination_connection_id,
        t.initial_source_connection_id == s.initial_source_connection_id,
        t.stateless_reset_token == s.stateless_reset_token,
        t.max_idle_timeout == s.max_idle_timeout,
        !t.disable_active_migration,
    ensures
        rfc_tp_from(b, p, false, t, 0x8007u32) == Ok::<SpecTp, u64>(s),
{
    hide(rfc_tp_from);
    hide(spec_tp_int);
    hide(spec_tp_entry);
    lemma_server_masks();
    let i3 = spec_tp_int(TP_MAX_UDP_PAYLOAD_SIZE, s.max_udp_payload_size);
    let i4 = spec_tp_int(TP_INITIAL_MAX_DATA, s.initial_max_data);
    let i5 = spec_tp_int(TP_INITIAL_MAX_STREAM_DATA_BIDI_LOCAL, s.initial_max_stream_data_bidi_local);
    let i6 = spec_tp_int(
        TP_INITIAL_MAX_STREAM_DATA_BIDI_REMOTE,
        s.initial_max_stream_data_bidi_remote,
    );
    let i7 = spec_tp_int(TP_INITIAL_MAX_STREAM_DATA_UNI, s.initial_max_stream_data_uni);
    let i8 = spec_tp_int(TP_INITIAL_MAX_STREAMS_BIDI, s.initial_max_streams_bidi);
    let i9 = spec_tp_int(TP_INITIAL_MAX_STREAMS_UNI, s.initial_max_streams_uni);
    let i10 = spec_tp_int(TP_ACK_DELAY_EXPONENT, s.ack_delay_exponent);
    let i11 = spec_tp_int(TP_MAX_ACK_DELAY, s.max_ack_delay);
    let end = spec_server_end(s);
    let t3 = spec_set_int(t, TP_MAX_UDP_PAYLOAD_SIZE, s.max_udp_payload_size);
    let t4 = spec_set_int(t3, TP_INITIAL_MAX_DATA, s.initial_max_data);
    let t5 = spec_set_int(
        t4,
        TP_INITIAL_MAX_STREAM_DATA_BIDI_LOCAL,
        s.initial_max_stream_data_bidi_local,
    );
    let t6 = spec_set_int(
        t5,
        TP_INITIAL_MAX_STREAM_DATA_BIDI_REMOTE,
        s.initial_max_stream_data_bidi_remote,
    );
    let t7 = spec_set_int(t6, TP_INITIAL_MAX_STREAM_DATA_UNI, s.initial_max_stream_data_uni);
    let t8 = spec_set_int(t7, TP_INITIAL_MAX_STREAMS_BIDI, s.initial_max_streams_bidi);
    let t9 = spec_set_int(t8, TP_INITIAL_MAX_STREAMS_UNI, s.initial_max_streams_uni);
    let t10 = spec_set_int(t9, TP_ACK_DELAY_EXPONENT, s.ack_delay_exponent);
    let t11 = spec_set_int(t10, TP_MAX_ACK_DELAY, s.max_ack_delay);
    let q4 = p + i3.len();
    let q5 = q4 + i4.len();
    let q6 = q5 + i5.len();
    let q7 = q6 + i6.len();
    let q8 = q7 + i7.len();
    let q9 = q8 + i8.len();
    let q10 = q9 + i9.len();
    let q11 = q10 + i10.len();
    let q12 = q11 + i11.len();
    let r10 = i11 + end;
    let r9 = i10 + r10;
    let r8 = i9 + r9;
    let r7 = i8 + r8;
    let r6 = i7 + r7;
    let r5 = i6 + r6;
    let r4 = i5 + r5;
    let r3 = i4 + r4;
    assert(spec_server_tail(s) == i3 + r3);
    lemma_int_step(b, p, TP_MAX_UDP_PAYLOAD_SIZE, s.max_udp_payload_size, r3, t, 0x8007u32);
    lemma_int_step(b, q4, TP_INITIAL_MAX_DATA, s.initial_max_data, r4, t3, 0x800fu32);
    lemma_int_step(
        b,
        q5,
        TP_INITIAL_MAX_STREAM_DATA_BIDI_LOCAL,
        s.initial_max_stream_data_bidi_local,
        r5,
        t4,
        0x801fu32,
    );
    lemma_int_step(
        b,
        q6,
        TP_INITIAL_MAX_STREAM_DATA_BIDI_REMOTE,
        s.initial_max_stream_data_bidi_remote,
        r6,
        t5,
        0x803fu32,
    );
    lemma_int_step(
        b,
        q7,
        TP_INITIAL_MAX_STREAM_DATA_UNI,
        s.initial_max_stream_data_uni,
        r7,
        t6,
        0x807fu32,
    );
    lemma_int_step(b, q8, TP_INITIAL_MAX_STREAMS_BIDI, s.initial_max_streams_bidi, r8, t7, 0x80ffu32);
    lemma_int_step(b, q9, TP_INITIAL_MAX_STREAMS_UNI, s.initial_max_streams_uni, r9, t8, 0x81ffu32);
    lemma_int_step(b, q10, TP_ACK_DELAY_EXPONENT, s.ack_delay_exponent, r10, t9, 0x83ffu32);
    lemma_int_step(b, q11, TP_MAX_ACK_DELAY, s.max_ack_delay, end, t10, 0x87ffu32);
    let acl = spec_tp_int(TP_ACTIVE_CONNECTION_ID_LIMIT, s.active_connection_id_limit);
    assert(acl + Seq::<u8>::empty() =~= acl);
    if s.disable_active_migration {
        let dam = spec_tp_entry(TP_DISABLE_ACTIVE_MIGRATION, Seq::empty());
        let t12 = SpecTp { disable_active_migration: true, ..t11 };
        lemma_tp_step(b, q12, TP_DISABLE_ACTIVE_MIGRATION, Seq::empty(), acl, false, t11, 0x8fffu32);
        lemma_int_step(
            b,
            q12 + dam.len(),
            TP_ACTIVE_CONNECTION_ID_LIMIT,
            s.active_connection_id_limit,
            Seq::empty(),
            t12,
            0x9fffu32,
        );
        let t13 = spec_set_int(t12, TP_ACTIVE_CONNECTION_ID_LIMIT, s.active_connection_id_limit);
        lemma_tp_end(b, q12 + dam.len() + acl.len(), t13, 0x9fffu32 | tp_bit(TP_ACTIVE_CONNECTION_ID_LIMIT));
        assert(t13 == s);
    } else {
        lemma_int_step(
            b,
            q12,
            TP_ACTIVE_CONNECTION_ID_LIMIT,
            s.active_connection_id_limit,
            Seq::empty(),
            t11,
            0x8fffu32,
        );
        let t13 = spec_set_int(t11, TP_ACTIVE_CONNECTION_ID_LIMIT, s.active_connection_id_limit);
        lemma_tp_end(b, q12 + acl.len(), t13, 0x8fffu32 | tp_bit(TP_ACTIVE_CONNECTION_ID_LIMIT));
        assert(t13 == s);
    }
}

/// Parsing what `serialize_server_params` wrote, as if received by a client, recovers the
/// parameters.
pub proof fn theorem_server_tp_roundtrip(p: SpecTp)
    requires
        server_tp_wf(p),
    ensures
        rfc_transport_params(spec_server_tp_bytes(p), false) == Ok::<SpecTp, u64>(p),
{
    hide(rfc_tp_from);
    hide(spec_server_tail);
    lemma_server_masks();
    let b = spec_server_tp_bytes(p);
    let o = p.original_destination_connection_id.unwrap();
    let i = p.initial_source_connection_id.unwrap();
    let k = p.stateless_reset_token.unwrap();
    let eo = spec_tp_entry(TP_ORIGINAL_DESTINATION_CONNECTION_ID, o);
    let ei = spec_tp_entry(TP_INITIAL_SOURCE_CONNECTION_ID, i);
    let ek = spec_tp_entry(TP_STATELESS_RESET_TOKEN, k);
    let e1 = spec_tp_int(TP_MAX_IDLE_TIMEOUT, p.max_idle_timeout);
    let rest = spec_server_tail(p);
    let t0 = spec_default_tp();
    let t1 = SpecTp { original_destination_connection_id: Some(o), ..t0 };
    let t2 = SpecTp { initial_source_connection_id: Some(i), ..t1 };
    let t3 = SpecTp { stateless_reset_token: Some(k), ..t2 };
    let t4 = spec_set_int(t3, TP_MAX_IDLE_TIMEOUT, p.max_idle_timeout);
    lemma_skip0(b);
    lemma_tp_step(b, 0, TP_ORIGINAL_DESTINATION_CONNECTION_ID, o, ei + (ek + (e1 + rest)), false,
        t0, 0u32);
    lemma_tp_step(b, eo.len() as int, TP_INITIAL_SOURCE_CONNECTION_ID, i, ek + (e1 + rest),
        false, t1, 0x0001u32);
    lemma_tp_step(b, (eo.len() + ei.len()) as int, TP_STATELESS_RESET_TOKEN, k, e1 + rest,
        false, t2, 0x8001u32);
    let q = (eo.len() + ei.len() + ek.len()) as int;
    lemma_int_step(b, q, TP_MAX_IDLE_TIMEOUT, p.max_idle_timeout, rest, t3, 0x8005u32);
    lemma_server_tail(b, q + e1.len(), p, t4);
}

// =============================================================================
// Executable code
// =============================================================================

/// The parameters of a peer that sent none.
pub fn default_transport_params() -> (r: TransportParams)
    ensures
        r@ == spec_default_tp(),
{
    TransportParams {
        original_destination_connection_id: None,
        max_idle_timeout: 0,
        stateless_reset_token: None,
        max_udp_payload_size: 65527,
        initial_max_data: 0,
        initial_max_stream_data_bidi_local: 0,
        initial_max_stream_data_bidi_remote: 0,
        initial_max_stream_data_uni: 0,
        initial_max_streams_bidi: 0,
        initial_max_streams_uni: 0,
        ack_delay_exponent: 3,
        max_ack_delay: 25,
        disable_active_migration: false,
        active_connection_id_limit: 2,
        initial_source_connection_id: None,
    }
}

/// `rfc_tp_value`: `t` with known parameter `id` set from `v`.
fn tp_value(id: u64, v: &[u8], t: TransportParams) -> (r: Option<TransportParams>)
    ensures
        match r {
            Some(t2) => rfc_tp_value(id, v@, t@) == Some(t2@),
            None => rfc_tp_value(id, v@, t@) is None,
        },
{
    let mut t = t;
    if id == TP_MAX_IDLE_TIMEOUT || (TP_MAX_UDP_PAYLOAD_SIZE <= id && id <= TP_MAX_ACK_DELAY) || id
        == TP_ACTIVE_CONNECTION_ID_LIMIT {
        let x = match parse_varint(v) {
            Some((n, x)) => if n == v.len() {
                x
            } else {
                return None;
            },
            None => return None,
        };
        if (id == TP_MAX_UDP_PAYLOAD_SIZE && x < 1200) || (id == TP_ACK_DELAY_EXPONENT && x > 20)
            || (id == TP_MAX_ACK_DELAY && x >= MAX_ACK_DELAY_LIMIT) || (id
            == TP_ACTIVE_CONNECTION_ID_LIMIT && x < 2) || ((id == TP_INITIAL_MAX_STREAMS_BIDI || id
            == TP_INITIAL_MAX_STREAMS_UNI) && x > MAX_STREAMS_LIMIT) {
            return None;
        }
        if id == TP_MAX_IDLE_TIMEOUT {
            t.max_idle_timeout = x;
        } else if id == TP_MAX_UDP_PAYLOAD_SIZE {
            t.max_udp_payload_size = x;
        } else if id == TP_INITIAL_MAX_DATA {
            t.initial_max_data = x;
        } else if id == TP_INITIAL_MAX_STREAM_DATA_BIDI_LOCAL {
            t.initial_max_stream_data_bidi_local = x;
        } else if id == TP_INITIAL_MAX_STREAM_DATA_BIDI_REMOTE {
            t.initial_max_stream_data_bidi_remote = x;
        } else if id == TP_INITIAL_MAX_STREAM_DATA_UNI {
            t.initial_max_stream_data_uni = x;
        } else if id == TP_INITIAL_MAX_STREAMS_BIDI {
            t.initial_max_streams_bidi = x;
        } else if id == TP_INITIAL_MAX_STREAMS_UNI {
            t.initial_max_streams_uni = x;
        } else if id == TP_ACK_DELAY_EXPONENT {
            t.ack_delay_exponent = x;
        } else if id == TP_MAX_ACK_DELAY {
            t.max_ack_delay = x;
        } else {
            t.active_connection_id_limit = x;
        }
    } else if id == TP_DISABLE_ACTIVE_MIGRATION {
        if v.len() != 0 {
            return None;
        }
        t.disable_active_migration = true;
    } else if id == TP_STATELESS_RESET_TOKEN {
        if v.len() != RESET_TOKEN_LEN {
            return None;
        }
        let mut k = [0u8; 16];
        k.copy_from_slice(v);
        t.stateless_reset_token = Some(k);
    } else if id == TP_ORIGINAL_DESTINATION_CONNECTION_ID {
        if v.len() > MAX_CID_LEN {
            return None;
        }
        t.original_destination_connection_id = Some(slice_to_vec(v));
    } else if id == TP_INITIAL_SOURCE_CONNECTION_ID {
        if v.len() > MAX_CID_LEN {
            return None;
        }
        t.initial_source_connection_id = Some(slice_to_vec(v));
    } else {
        return None;
    }
    Some(t)
}

/// `rfc_tp_apply`: one parameter applied to `t`, with the new seen-mask.
fn tp_apply(id: u64, v: &[u8], from_client: bool, t: TransportParams, seen: u32) -> (r: Option<
    (TransportParams, u32),
>)
    ensures
        match r {
            Some((t2, seen2)) => rfc_tp_apply(id, v@, from_client, t@, seen) == Some(
                (t2@, seen2),
            ),
            None => rfc_tp_apply(id, v@, from_client, t@, seen) is None,
        },
{
    if id > TP_RETRY_SOURCE_CONNECTION_ID {
        return Some((t, seen));
    }
    let bit = 1u32 << (id as u32);
    if seen & bit != 0 {
        return None;
    }
    if id == TP_PREFERRED_ADDRESS || id == TP_RETRY_SOURCE_CONNECTION_ID || (from_client && (id
        == TP_ORIGINAL_DESTINATION_CONNECTION_ID || id == TP_STATELESS_RESET_TOKEN)) {
        return None;
    }
    match tp_value(id, v, t) {
        Some(t2) => Some((t2, seen | bit)),
        None => None,
    }
}

/// A peer's transport parameters extension value; a server passes `from_client = true`.
pub fn parse_transport_params(b: &[u8], from_client: bool) -> (r: Result<TransportParams, u64>)
    ensures
        match r {
            Ok(t) => rfc_transport_params(b@, from_client) == Ok::<SpecTp, u64>(t@),
            Err(e) => rfc_transport_params(b@, from_client) == Err::<SpecTp, u64>(e),
        },
{
    hide(rfc_varint_decode);
    hide(rfc_tp_apply);
    let mut t = default_transport_params();
    let mut seen: u32 = 0;
    let mut p: usize = 0;
    while p < b.len()
        invariant
            p <= b.len(),
            rfc_transport_params(b@, from_client) == rfc_tp_from(
                b@,
                p as int,
                from_client,
                t@,
                seen,
            ),
        decreases b.len() - p,
    {
        let (n1, id) = match varint_at(b, p) {
            Some(x) => x,
            None => return Err(TRANSPORT_PARAMETER_ERROR),
        };
        let q = p + n1;
        let (n2, len) = match varint_at(b, q) {
            Some(x) => x,
            None => return Err(TRANSPORT_PARAMETER_ERROR),
        };
        let r = q + n2;
        if len > (b.len() - r) as u64 {
            return Err(TRANSPORT_PARAMETER_ERROR);
        }
        let s = r + len as usize;
        let v = slice_subrange(b, r, s);
        match tp_apply(id, v, from_client, t, seen) {
            Some((t2, seen2)) => {
                t = t2;
                seen = seen2;
            },
            None => return Err(TRANSPORT_PARAMETER_ERROR),
        }
        p = s;
    }
    Ok(t)
}

/// Writes one parameter: ID, Length, Value. `rest` names what the caller writes after it.
fn put_tp_entry(id: u64, v: &[u8], out: &mut Vec<u8>, Ghost(rest): Ghost<Seq<u8>>)
    requires
        id <= 63,
        v.len() <= 63,
    ensures
        final(out)@ + rest == old(out)@ + (spec_tp_entry(id, v@) + rest),
        spec_tp_entry(id, v@).len() == 2 + v.len(),
{
    proof {
        lemma_serialize_bytes::<true>(id);
        lemma_serialize_bytes::<true>(v.len() as u64);
    }
    put_varint(id, out);
    put_varint(v.len() as u64, out);
    put_slice(v, out);
    proof {
        assert(final(out)@ + rest =~= old(out)@ + (spec_tp_entry(id, v@) + rest));
    }
}

/// Writes one integer parameter, its value the minimal varint of `x`.
fn put_tp_int(id: u64, x: u64, out: &mut Vec<u8>, Ghost(rest): Ghost<Seq<u8>>)
    requires
        id <= 63,
        x <= VARINT_MAX,
    ensures
        final(out)@ + rest == old(out)@ + (spec_tp_int(id, x) + rest),
        spec_tp_int(id, x).len() <= 10,
{
    let n = varint_len(x);
    proof {
        theorem_serialize_matches_rfc(x);
        lemma_serialize_bytes::<true>(id);
        lemma_serialize_bytes::<true>(n as u64);
    }
    put_varint(id, out);
    put_varint(n as u64, out);
    put_varint(x, out);
    proof {
        assert(final(out)@ + rest =~= old(out)@ + (spec_tp_int(id, x) + rest));
    }
}

/// Writes `spec_server_end`.
fn put_server_end(p: &TransportParams, out: &mut Vec<u8>)
    requires
        p.active_connection_id_limit <= VARINT_MAX,
    ensures
        final(out)@ == old(out)@ + spec_server_end(p@),
        spec_server_end(p@).len() <= 12,
{
    let ghost e = Seq::<u8>::empty();
    let ghost acl = spec_tp_int(TP_ACTIVE_CONNECTION_ID_LIMIT, p.active_connection_id_limit);
    proof {
        assert(acl + e =~= acl);
        assert(old(out)@ + e =~= old(out)@);
    }
    if p.disable_active_migration {
        put_tp_entry(TP_DISABLE_ACTIVE_MIGRATION, &[], out, Ghost(acl));
    }
    let ghost mid = out@;
    put_tp_int(TP_ACTIVE_CONNECTION_ID_LIMIT, p.active_connection_id_limit, out, Ghost(e));
    proof {
        assert(out@ + e =~= out@);
        assert(mid + (acl + e) == mid + acl);
    }
}

/// Writes `spec_server_tail`.
fn put_server_tail(p: &TransportParams, out: &mut Vec<u8>)
    requires
        server_tp_wf(p@),
    ensures
        final(out)@ == old(out)@ + spec_server_tail(p@),
        spec_server_tail(p@).len() <= 102,
{
    let ghost s = p@;
    let ghost i4 = spec_tp_int(TP_INITIAL_MAX_DATA, s.initial_max_data);
    let ghost i5 = spec_tp_int(TP_INITIAL_MAX_STREAM_DATA_BIDI_LOCAL, s.initial_max_stream_data_bidi_local);
    let ghost i6 = spec_tp_int(
        TP_INITIAL_MAX_STREAM_DATA_BIDI_REMOTE,
        s.initial_max_stream_data_bidi_remote,
    );
    let ghost i7 = spec_tp_int(TP_INITIAL_MAX_STREAM_DATA_UNI, s.initial_max_stream_data_uni);
    let ghost i8 = spec_tp_int(TP_INITIAL_MAX_STREAMS_BIDI, s.initial_max_streams_bidi);
    let ghost i9 = spec_tp_int(TP_INITIAL_MAX_STREAMS_UNI, s.initial_max_streams_uni);
    let ghost i10 = spec_tp_int(TP_ACK_DELAY_EXPONENT, s.ack_delay_exponent);
    let ghost i11 = spec_tp_int(TP_MAX_ACK_DELAY, s.max_ack_delay);
    let ghost end = spec_server_end(s);
    let ghost r10 = i11 + end;
    let ghost r9 = i10 + r10;
    let ghost r8 = i9 + r9;
    let ghost r7 = i8 + r8;
    let ghost r6 = i7 + r7;
    let ghost r5 = i6 + r6;
    let ghost r4 = i5 + r5;
    let ghost r3 = i4 + r4;
    put_tp_int(TP_MAX_UDP_PAYLOAD_SIZE, p.max_udp_payload_size, out, Ghost(r3));
    put_tp_int(TP_INITIAL_MAX_DATA, p.initial_max_data, out, Ghost(r4));
    put_tp_int(
        TP_INITIAL_MAX_STREAM_DATA_BIDI_LOCAL,
        p.initial_max_stream_data_bidi_local,
        out,
        Ghost(r5),
    );
    put_tp_int(
        TP_INITIAL_MAX_STREAM_DATA_BIDI_REMOTE,
        p.initial_max_stream_data_bidi_remote,
        out,
        Ghost(r6),
    );
    put_tp_int(TP_INITIAL_MAX_STREAM_DATA_UNI, p.initial_max_stream_data_uni, out, Ghost(r7));
    put_tp_int(TP_INITIAL_MAX_STREAMS_BIDI, p.initial_max_streams_bidi, out, Ghost(r8));
    put_tp_int(TP_INITIAL_MAX_STREAMS_UNI, p.initial_max_streams_uni, out, Ghost(r9));
    put_tp_int(TP_ACK_DELAY_EXPONENT, p.ack_delay_exponent, out, Ghost(r10));
    put_tp_int(TP_MAX_ACK_DELAY, p.max_ack_delay, out, Ghost(end));
    put_server_end(p, out);
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-7.4
//# An endpoint MUST NOT send a parameter more than once in a given
//# transport parameters extension.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-18.2
//# The value of the
//# active_connection_id_limit parameter MUST be at least 2.
/// Writes the server's transport parameters: each ID once, in a fixed order, every integer
/// even at its default. At most `MAX_SERVER_TP_LEN` bytes.
pub fn serialize_server_params(p: &TransportParams, out: &mut Vec<u8>)
    requires
        server_tp_wf(p@),
    ensures
        final(out)@ == old(out)@ + spec_server_tp_bytes(p@),
        final(out)@.len() <= old(out)@.len() + MAX_SERVER_TP_LEN,
{
    let ghost s = p@;
    let ghost ei = spec_tp_entry(TP_INITIAL_SOURCE_CONNECTION_ID, s.initial_source_connection_id.unwrap());
    let ghost ek = spec_tp_entry(TP_STATELESS_RESET_TOKEN, s.stateless_reset_token.unwrap());
    let ghost e1 = spec_tp_int(TP_MAX_IDLE_TIMEOUT, s.max_idle_timeout);
    let ghost tail = spec_server_tail(s);
    match &p.original_destination_connection_id {
        Some(c) => put_tp_entry(
            TP_ORIGINAL_DESTINATION_CONNECTION_ID,
            c.as_slice(),
            out,
            Ghost(ei + (ek + (e1 + tail))),
        ),
        None => {},
    }
    match &p.initial_source_connection_id {
        Some(c) => put_tp_entry(
            TP_INITIAL_SOURCE_CONNECTION_ID,
            c.as_slice(),
            out,
            Ghost(ek + (e1 + tail)),
        ),
        None => {},
    }
    match &p.stateless_reset_token {
        Some(k) => put_tp_entry(TP_STATELESS_RESET_TOKEN, k.as_slice(), out, Ghost(e1 + tail)),
        None => {},
    }
    put_tp_int(TP_MAX_IDLE_TIMEOUT, p.max_idle_timeout, out, Ghost(tail));
    put_server_tail(p, out);
}

} // verus!
