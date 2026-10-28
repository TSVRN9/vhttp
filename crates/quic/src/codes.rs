//! QUIC v1 constants: version, frame types (RFC 9000 Table 3), transport parameters (§18.2),
//! transport error codes (§20.1) and protocol limits.
use vstd::prelude::*;
use wire::varint::*;

verus! {

pub const QUIC_V1: u32 = 0x0000_0001;

pub const FRAME_PADDING: u64 = 0x00;
pub const FRAME_PING: u64 = 0x01;
pub const FRAME_ACK: u64 = 0x02;
pub const FRAME_ACK_ECN: u64 = 0x03;
pub const FRAME_RESET_STREAM: u64 = 0x04;
pub const FRAME_STOP_SENDING: u64 = 0x05;
pub const FRAME_CRYPTO: u64 = 0x06;
pub const FRAME_NEW_TOKEN: u64 = 0x07;
/// STREAM is 0x08 through 0x0f (OFF, LEN and FIN bits).
pub const FRAME_STREAM_MIN: u64 = 0x08;
pub const FRAME_STREAM_MAX: u64 = 0x0f;
pub const FRAME_MAX_DATA: u64 = 0x10;
pub const FRAME_MAX_STREAM_DATA: u64 = 0x11;
pub const FRAME_MAX_STREAMS_BIDI: u64 = 0x12;
pub const FRAME_MAX_STREAMS_UNI: u64 = 0x13;
pub const FRAME_DATA_BLOCKED: u64 = 0x14;
pub const FRAME_STREAM_DATA_BLOCKED: u64 = 0x15;
pub const FRAME_STREAMS_BLOCKED_BIDI: u64 = 0x16;
pub const FRAME_STREAMS_BLOCKED_UNI: u64 = 0x17;
pub const FRAME_NEW_CONNECTION_ID: u64 = 0x18;
pub const FRAME_RETIRE_CONNECTION_ID: u64 = 0x19;
pub const FRAME_PATH_CHALLENGE: u64 = 0x1a;
pub const FRAME_PATH_RESPONSE: u64 = 0x1b;
pub const FRAME_CONNECTION_CLOSE: u64 = 0x1c;
pub const FRAME_CONNECTION_CLOSE_APP: u64 = 0x1d;
pub const FRAME_HANDSHAKE_DONE: u64 = 0x1e;

pub const TP_ORIGINAL_DESTINATION_CONNECTION_ID: u64 = 0x00;
pub const TP_MAX_IDLE_TIMEOUT: u64 = 0x01;
pub const TP_STATELESS_RESET_TOKEN: u64 = 0x02;
pub const TP_MAX_UDP_PAYLOAD_SIZE: u64 = 0x03;
pub const TP_INITIAL_MAX_DATA: u64 = 0x04;
pub const TP_INITIAL_MAX_STREAM_DATA_BIDI_LOCAL: u64 = 0x05;
pub const TP_INITIAL_MAX_STREAM_DATA_BIDI_REMOTE: u64 = 0x06;
pub const TP_INITIAL_MAX_STREAM_DATA_UNI: u64 = 0x07;
pub const TP_INITIAL_MAX_STREAMS_BIDI: u64 = 0x08;
pub const TP_INITIAL_MAX_STREAMS_UNI: u64 = 0x09;
pub const TP_ACK_DELAY_EXPONENT: u64 = 0x0a;
pub const TP_MAX_ACK_DELAY: u64 = 0x0b;
pub const TP_DISABLE_ACTIVE_MIGRATION: u64 = 0x0c;
pub const TP_PREFERRED_ADDRESS: u64 = 0x0d;
pub const TP_ACTIVE_CONNECTION_ID_LIMIT: u64 = 0x0e;
pub const TP_INITIAL_SOURCE_CONNECTION_ID: u64 = 0x0f;
pub const TP_RETRY_SOURCE_CONNECTION_ID: u64 = 0x10;

pub const NO_ERROR: u64 = 0x00;
pub const INTERNAL_ERROR: u64 = 0x01;
pub const CONNECTION_REFUSED: u64 = 0x02;
pub const FLOW_CONTROL_ERROR: u64 = 0x03;
pub const STREAM_LIMIT_ERROR: u64 = 0x04;
pub const STREAM_STATE_ERROR: u64 = 0x05;
pub const FINAL_SIZE_ERROR: u64 = 0x06;
pub const FRAME_ENCODING_ERROR: u64 = 0x07;
pub const TRANSPORT_PARAMETER_ERROR: u64 = 0x08;
pub const CONNECTION_ID_LIMIT_ERROR: u64 = 0x09;
pub const PROTOCOL_VIOLATION: u64 = 0x0a;
pub const INVALID_TOKEN: u64 = 0x0b;
pub const APPLICATION_ERROR: u64 = 0x0c;
pub const CRYPTO_BUFFER_EXCEEDED: u64 = 0x0d;
pub const KEY_UPDATE_ERROR: u64 = 0x0e;
pub const AEAD_LIMIT_REACHED: u64 = 0x0f;
pub const NO_VIABLE_PATH: u64 = 0x10;
/// CRYPTO_ERROR is 0x0100 through 0x01ff: the base plus the TLS alert code.
pub const CRYPTO_ERROR_BASE: u64 = 0x0100;

pub const MAX_CID_LEN: usize = 20;
pub const MIN_INITIAL_DATAGRAM: usize = 1200;
pub const PN_MAX: u64 = VARINT_MAX;
pub const MAX_STREAMS_LIMIT: u64 = 1u64 << 60;
pub const MIN_SHORT_PACKET: usize = 21;
pub const RESET_TOKEN_LEN: usize = 16;
pub const MAX_ACK_DELAY_LIMIT: u64 = 1u64 << 14;

} // verus!
