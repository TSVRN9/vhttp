//! QUIC transport frames (RFC 9000 §12.4, §19): the frame type, every frame body a server
//! can receive, and the serializer for every frame it sends. NEW_TOKEN has no variant: a
//! server never sends one and treats receiving one as PROTOCOL_VIOLATION.
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use vest_lib::core::spec::*;
use vstd::prelude::*;
use vstd::slice::{slice_subrange, slice_to_vec};
use wire::varint::*;

use crate::ack::*;
use crate::codes::*;

verus! {

#[derive(Debug, PartialEq, Eq)]
pub enum Frame {
    Padding,
    Ping,
    Ack(AckFrame),
    ResetStream { stream_id: u64, error_code: u64, final_size: u64 },
    StopSending { stream_id: u64, error_code: u64 },
    Crypto { offset: u64, data: Vec<u8> },
    Stream { stream_id: u64, offset: u64, data: Vec<u8>, fin: bool },
    MaxData(u64),
    MaxStreamData { stream_id: u64, max: u64 },
    MaxStreams { bidi: bool, max: u64 },
    DataBlocked(u64),
    StreamDataBlocked { stream_id: u64, max: u64 },
    StreamsBlocked { bidi: bool, max: u64 },
    NewConnectionId { seq: u64, retire_prior_to: u64, cid: Vec<u8>, reset_token: [u8; 16] },
    RetireConnectionId(u64),
    PathChallenge([u8; 8]),
    PathResponse([u8; 8]),
    /// `app` is type 0x1d, which has no Frame Type field (`frame_type` is then 0).
    ConnectionClose { app: bool, error_code: u64, frame_type: u64, reason: Vec<u8> },
    HandshakeDone,
}

pub enum SpecFrame {
    Padding,
    Ping,
    Ack(SpecAck),
    ResetStream { stream_id: u64, error_code: u64, final_size: u64 },
    StopSending { stream_id: u64, error_code: u64 },
    Crypto { offset: u64, data: Seq<u8> },
    Stream { stream_id: u64, offset: u64, data: Seq<u8>, fin: bool },
    MaxData(u64),
    MaxStreamData { stream_id: u64, max: u64 },
    MaxStreams { bidi: bool, max: u64 },
    DataBlocked(u64),
    StreamDataBlocked { stream_id: u64, max: u64 },
    StreamsBlocked { bidi: bool, max: u64 },
    NewConnectionId { seq: u64, retire_prior_to: u64, cid: Seq<u8>, reset_token: Seq<u8> },
    RetireConnectionId(u64),
    PathChallenge(Seq<u8>),
    PathResponse(Seq<u8>),
    ConnectionClose { app: bool, error_code: u64, frame_type: u64, reason: Seq<u8> },
    HandshakeDone,
}

impl View for Frame {
    type V = SpecFrame;

    open spec fn view(&self) -> SpecFrame {
        match self {
            Frame::Padding => SpecFrame::Padding,
            Frame::Ping => SpecFrame::Ping,
            Frame::Ack(a) => SpecFrame::Ack(a@),
            Frame::ResetStream { stream_id, error_code, final_size } => SpecFrame::ResetStream {
                stream_id: *stream_id,
                error_code: *error_code,
                final_size: *final_size,
            },
            Frame::StopSending { stream_id, error_code } => SpecFrame::StopSending {
                stream_id: *stream_id,
                error_code: *error_code,
            },
            Frame::Crypto { offset, data } => SpecFrame::Crypto { offset: *offset, data: data@ },
            Frame::Stream { stream_id, offset, data, fin } => SpecFrame::Stream {
                stream_id: *stream_id,
                offset: *offset,
                data: data@,
                fin: *fin,
            },
            Frame::MaxData(v) => SpecFrame::MaxData(*v),
            Frame::MaxStreamData { stream_id, max } => SpecFrame::MaxStreamData {
                stream_id: *stream_id,
                max: *max,
            },
            Frame::MaxStreams { bidi, max } => SpecFrame::MaxStreams { bidi: *bidi, max: *max },
            Frame::DataBlocked(v) => SpecFrame::DataBlocked(*v),
            Frame::StreamDataBlocked { stream_id, max } => SpecFrame::StreamDataBlocked {
                stream_id: *stream_id,
                max: *max,
            },
            Frame::StreamsBlocked { bidi, max } => SpecFrame::StreamsBlocked {
                bidi: *bidi,
                max: *max,
            },
            Frame::NewConnectionId { seq, retire_prior_to, cid, reset_token } =>
                SpecFrame::NewConnectionId {
                seq: *seq,
                retire_prior_to: *retire_prior_to,
                cid: cid@,
                reset_token: reset_token@,
            },
            Frame::RetireConnectionId(v) => SpecFrame::RetireConnectionId(*v),
            Frame::PathChallenge(d) => SpecFrame::PathChallenge(d@),
            Frame::PathResponse(d) => SpecFrame::PathResponse(d@),
            Frame::ConnectionClose { app, error_code, frame_type, reason } =>
                SpecFrame::ConnectionClose {
                app: *app,
                error_code: *error_code,
                frame_type: *frame_type,
                reason: reason@,
            },
            Frame::HandshakeDone => SpecFrame::HandshakeDone,
        }
    }
}

// =============================================================================
// RFC 9000 transcription
// =============================================================================

//= https://www.rfc-editor.org/rfc/rfc9000#section-12.4
//# To ensure simple and efficient
//# implementations of frame parsing, a frame type MUST use the shortest
//# possible encoding.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-12.4
//# An endpoint MAY treat the
//# receipt of a frame type that uses a longer encoding than necessary as
//# a connection error of type PROTOCOL_VIOLATION.
/// The frame type and its encoded length. A type that decodes but not at its shortest length
/// is PROTOCOL_VIOLATION; one that does not decode is FRAME_ENCODING_ERROR.
pub open spec fn rfc_frame_type(b: Seq<u8>) -> Result<(u64, nat), u64> {
    match rfc_varint_decode(b) {
        None => Err(FRAME_ENCODING_ERROR),
        Some((n, v)) => if n == rfc_varint_min_len(v) {
            Ok((v, n))
        } else {
            Err(PROTOCOL_VIOLATION)
        },
    }
}

/// The varint at offset `p`, with the offset after it.
pub open spec fn rfc_vint(b: Seq<u8>, p: int) -> Option<(u64, int)> {
    match rfc_varint_decode(b.skip(p)) {
        None => None,
        Some((n, v)) => Some((v, p + n)),
    }
}

/// The `len` bytes at offset `p`, if `b` has them, with the offset after them.
pub open spec fn rfc_bytes(b: Seq<u8>, p: int, len: int) -> Option<(Seq<u8>, int)> {
    if len > b.len() - p {
        None
    } else {
        Some((b.subrange(p, p + len), p + len))
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.6
//# The largest offset delivered on a stream -- the sum of the offset and
//# data length -- cannot exceed 2^62-1.  Receipt of a frame that exceeds
//# this limit MUST be treated as a connection error of type
//# FRAME_ENCODING_ERROR or CRYPTO_BUFFER_EXCEEDED.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.8
//# The largest offset
//# delivered on a stream -- the sum of the offset and data length --
//# cannot exceed 2^62-1, as it is not possible to provide flow control
//# credit for that data.  Receipt of a frame that exceeds this limit
//# MUST be treated as a connection error of type FRAME_ENCODING_ERROR or
//# FLOW_CONTROL_ERROR.
/// CRYPTO or STREAM data of `len` bytes at offset `p`, starting at stream offset `offset`.
pub open spec fn rfc_stream_data(b: Seq<u8>, p: int, offset: u64, len: int) -> Option<
    (Seq<u8>, int),
> {
    if offset + len > VARINT_MAX {
        None
    } else {
        rfc_bytes(b, p, len)
    }
}

/// RESET_STREAM (§19.4): Stream ID, Application Protocol Error Code, Final Size.
pub open spec fn rfc_reset_stream(b: Seq<u8>) -> Option<(SpecFrame, int)> {
    match rfc_vint(b, 0) {
        None => None,
        Some((stream_id, p1)) => match rfc_vint(b, p1) {
            None => None,
            Some((error_code, p2)) => match rfc_vint(b, p2) {
                None => None,
                Some((final_size, q)) => Some(
                    (SpecFrame::ResetStream { stream_id, error_code, final_size }, q),
                ),
            },
        },
    }
}

/// STOP_SENDING (§19.5), MAX_STREAM_DATA (§19.10) and STREAM_DATA_BLOCKED (§19.13): two
/// varints.
pub open spec fn rfc_two_varints(ty: u64, b: Seq<u8>) -> Option<(SpecFrame, int)> {
    match rfc_vint(b, 0) {
        None => None,
        Some((x, p1)) => match rfc_vint(b, p1) {
            None => None,
            Some((y, q)) => Some(
                (if ty == FRAME_STOP_SENDING {
                    SpecFrame::StopSending { stream_id: x, error_code: y }
                } else if ty == FRAME_MAX_STREAM_DATA {
                    SpecFrame::MaxStreamData { stream_id: x, max: y }
                } else {
                    SpecFrame::StreamDataBlocked { stream_id: x, max: y }
                }, q),
            ),
        },
    }
}

/// CRYPTO (§19.6): Offset, Length, Crypto Data.
pub open spec fn rfc_crypto(b: Seq<u8>) -> Option<(SpecFrame, int)> {
    match rfc_vint(b, 0) {
        None => None,
        Some((offset, p1)) => match rfc_vint(b, p1) {
            None => None,
            Some((len, p2)) => match rfc_stream_data(b, p2, offset, len as int) {
                None => None,
                Some((data, q)) => Some((SpecFrame::Crypto { offset, data }, q)),
            },
        },
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.8
//# The OFF bit (0x04) in the frame type is set to indicate that there
//# is an Offset field present.  When set to 1, the Offset field is
//# present.  When set to 0, the Offset field is absent and the Stream
//# Data starts at an offset of 0
/// STREAM's Offset field: present iff the OFF bit is set, else 0.
pub open spec fn rfc_stream_offset(ty: u64, b: Seq<u8>, p: int) -> Option<(u64, int)> {
    if ty & 0x04 != 0 {
        rfc_vint(b, p)
    } else {
        Some((0, p))
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.8
//# The LEN bit (0x02) in the frame type is set to indicate that there
//# is a Length field present.  If this bit is set to 0, the Length
//# field is absent and the Stream Data field extends to the end of
//# the packet.  If this bit is set to 1, the Length field is present.
/// STREAM's Length field: present iff the LEN bit is set, else the rest of `b`.
pub open spec fn rfc_stream_len(ty: u64, b: Seq<u8>, p: int) -> Option<(int, int)> {
    if ty & 0x02 != 0 {
        match rfc_vint(b, p) {
            None => None,
            Some((len, q)) => Some((len as int, q)),
        }
    } else {
        Some((b.len() - p, p))
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.8
//# The FIN bit (0x01) indicates that the frame marks the end of the
//# stream.
/// STREAM (§19.8), types 0x08 to 0x0f: Stream ID, [Offset], [Length], Stream Data.
pub open spec fn rfc_stream(ty: u64, b: Seq<u8>) -> Option<(SpecFrame, int)> {
    match rfc_vint(b, 0) {
        None => None,
        Some((stream_id, p1)) => match rfc_stream_offset(ty, b, p1) {
            None => None,
            Some((offset, p2)) => match rfc_stream_len(ty, b, p2) {
                None => None,
                Some((len, p3)) => match rfc_stream_data(b, p3, offset, len) {
                    None => None,
                    Some((data, q)) => Some(
                        (SpecFrame::Stream { stream_id, offset, data, fin: ty & 0x01 != 0 }, q),
                    ),
                },
            },
        },
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.11
//# This value cannot exceed 2^60, as it is not possible
//# to encode stream IDs larger than 2^62-1.  Receipt of a frame that
//# permits opening of a stream larger than this limit MUST be treated
//# as a connection error of type FRAME_ENCODING_ERROR.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.14
//# This
//# value cannot exceed 2^60, as it is not possible to encode stream
//# IDs larger than 2^62-1.  Receipt of a frame that encodes a larger
//# stream ID MUST be treated as a connection error of type
//# STREAM_LIMIT_ERROR or FRAME_ENCODING_ERROR.
/// MAX_DATA (§19.9), MAX_STREAMS (§19.11), DATA_BLOCKED (§19.12), STREAMS_BLOCKED (§19.14)
/// and RETIRE_CONNECTION_ID (§19.16): one varint. A stream count above 2^60 is invalid.
pub open spec fn rfc_one_varint(ty: u64, b: Seq<u8>) -> Option<(SpecFrame, int)> {
    match rfc_vint(b, 0) {
        None => None,
        Some((v, q)) => if ty == FRAME_MAX_DATA {
            Some((SpecFrame::MaxData(v), q))
        } else if ty == FRAME_DATA_BLOCKED {
            Some((SpecFrame::DataBlocked(v), q))
        } else if ty == FRAME_RETIRE_CONNECTION_ID {
            Some((SpecFrame::RetireConnectionId(v), q))
        } else if v > MAX_STREAMS_LIMIT {
            None
        } else if ty == FRAME_MAX_STREAMS_BIDI || ty == FRAME_MAX_STREAMS_UNI {
            Some((SpecFrame::MaxStreams { bidi: ty == FRAME_MAX_STREAMS_BIDI, max: v }, q))
        } else {
            Some((SpecFrame::StreamsBlocked { bidi: ty == FRAME_STREAMS_BLOCKED_BIDI, max: v }, q))
        },
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.15
//# Length:  An 8-bit unsigned integer containing the length of the
//# connection ID.  Values less than 1 and greater than 20 are invalid
//# and MUST be treated as a connection error of type
//# FRAME_ENCODING_ERROR.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.15
//# Receiving a value in the Retire Prior To field that is greater than
//# that in the Sequence Number field MUST be treated as a connection
//# error of type FRAME_ENCODING_ERROR.
/// NEW_CONNECTION_ID (§19.15): Sequence Number, Retire Prior To, a 1-byte Length, the
/// Connection ID and a 16-byte Stateless Reset Token.
pub open spec fn rfc_new_connection_id(b: Seq<u8>) -> Option<(SpecFrame, int)> {
    match rfc_vint(b, 0) {
        None => None,
        Some((seq, p1)) => match rfc_vint(b, p1) {
            None => None,
            Some((retire_prior_to, p2)) => if p2 >= b.len() {
                None
            } else if b[p2] < 1 || b[p2] > MAX_CID_LEN || retire_prior_to > seq {
                None
            } else {
                match rfc_bytes(b, p2 + 1, b[p2] as int) {
                    None => None,
                    Some((cid, p3)) => match rfc_bytes(b, p3, RESET_TOKEN_LEN as int) {
                        None => None,
                        Some((reset_token, q)) => Some(
                            (SpecFrame::NewConnectionId { seq, retire_prior_to, cid, reset_token }, q),
                        ),
                    },
                }
            },
        },
    }
}

/// PATH_CHALLENGE (§19.17) and PATH_RESPONSE (§19.18): 8 bytes of Data.
pub open spec fn rfc_path(ty: u64, b: Seq<u8>) -> Option<(SpecFrame, int)> {
    match rfc_bytes(b, 0, 8) {
        None => None,
        Some((d, q)) => Some(
            (if ty == FRAME_PATH_CHALLENGE {
                SpecFrame::PathChallenge(d)
            } else {
                SpecFrame::PathResponse(d)
            }, q),
        ),
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.19
//# The CONNECTION_CLOSE frame with a
//# type of 0x1d is used to signal an error with the application that
//# uses QUIC.
/// CONNECTION_CLOSE (§19.19): Error Code, Frame Type (type 0x1c only), Reason Phrase Length
/// and Reason Phrase.
pub open spec fn rfc_close(ty: u64, b: Seq<u8>) -> Option<(SpecFrame, int)> {
    let app = ty == FRAME_CONNECTION_CLOSE_APP;
    match rfc_vint(b, 0) {
        None => None,
        Some((error_code, p1)) => match (if app {
            Some((0u64, p1))
        } else {
            rfc_vint(b, p1)
        }) {
            None => None,
            Some((frame_type, p2)) => match rfc_vint(b, p2) {
                None => None,
                Some((len, p3)) => match rfc_bytes(b, p3, len as int) {
                    None => None,
                    Some((reason, q)) => Some(
                        (SpecFrame::ConnectionClose { app, error_code, frame_type, reason }, q),
                    ),
                },
            },
        },
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-12.4
//# An endpoint MUST treat the receipt of a frame of unknown type as a
//# connection error of type FRAME_ENCODING_ERROR.
/// The fields of a frame of type `ty` (other than ACK, NEW_TOKEN and HANDSHAKE_DONE) with
/// the bytes consumed; `None` for a truncated or invalid body or an unknown type.
pub open spec fn rfc_frame_fields(ty: u64, b: Seq<u8>) -> Option<(SpecFrame, int)> {
    if ty == FRAME_PADDING {
        Some((SpecFrame::Padding, 0))
    } else if ty == FRAME_PING {
        Some((SpecFrame::Ping, 0))
    } else if ty == FRAME_RESET_STREAM {
        rfc_reset_stream(b)
    } else if ty == FRAME_STOP_SENDING || ty == FRAME_MAX_STREAM_DATA || ty
        == FRAME_STREAM_DATA_BLOCKED {
        rfc_two_varints(ty, b)
    } else if ty == FRAME_CRYPTO {
        rfc_crypto(b)
    } else if FRAME_STREAM_MIN <= ty <= FRAME_STREAM_MAX {
        rfc_stream(ty, b)
    } else if ty == FRAME_MAX_DATA || ty == FRAME_MAX_STREAMS_BIDI || ty == FRAME_MAX_STREAMS_UNI
        || ty == FRAME_DATA_BLOCKED || ty == FRAME_STREAMS_BLOCKED_BIDI || ty
        == FRAME_STREAMS_BLOCKED_UNI || ty == FRAME_RETIRE_CONNECTION_ID {
        rfc_one_varint(ty, b)
    } else if ty == FRAME_NEW_CONNECTION_ID {
        rfc_new_connection_id(b)
    } else if ty == FRAME_PATH_CHALLENGE || ty == FRAME_PATH_RESPONSE {
        rfc_path(ty, b)
    } else if ty == FRAME_CONNECTION_CLOSE || ty == FRAME_CONNECTION_CLOSE_APP {
        rfc_close(ty, b)
    } else {
        None
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.7
//# A server MUST treat receipt
//# of a NEW_TOKEN frame as a connection error of type
//# PROTOCOL_VIOLATION.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.20
//# A
//# server MUST treat receipt of a HANDSHAKE_DONE frame as a connection
//# error of type PROTOCOL_VIOLATION.
/// The frame body after type `ty`, as received by a server, with the bytes consumed.
/// NEW_TOKEN and HANDSHAKE_DONE are PROTOCOL_VIOLATION whatever follows; every other failure
/// is FRAME_ENCODING_ERROR.
pub open spec fn rfc_frame_body(ty: u64, b: Seq<u8>) -> Result<(SpecFrame, nat), u64> {
    if ty == FRAME_NEW_TOKEN || ty == FRAME_HANDSHAKE_DONE {
        Err(PROTOCOL_VIOLATION)
    } else if ty == FRAME_ACK || ty == FRAME_ACK_ECN {
        match rfc_ack(ty, b) {
            Ok((a, n)) => Ok((SpecFrame::Ack(a), n)),
            Err(e) => Err(e),
        }
    } else {
        match rfc_frame_fields(ty, b) {
            Some((f, n)) => Ok((f, n as nat)),
            None => Err(FRAME_ENCODING_ERROR),
        }
    }
}

/// One whole frame from the front of `b`, with the bytes consumed.
pub open spec fn rfc_frame(b: Seq<u8>) -> Result<(SpecFrame, nat), u64> {
    match rfc_frame_type(b) {
        Err(e) => Err(e),
        Ok((ty, n)) => match rfc_frame_body(ty, b.skip(n as int)) {
            Err(e) => Err(e),
            Ok((f, m)) => Ok((f, n + m)),
        },
    }
}

// =============================================================================
// Serialization specs
// =============================================================================

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.15
//# The value in the Retire Prior To field
//# MUST be less than or equal to the value in the Sequence Number field.
/// A frame we may send: every field fits its encoding, and each frame obeys its sender-side
/// limits. The token, path data and reason lengths are implied by the exec types; spec
/// values have to state them.
pub open spec fn frame_wf(f: SpecFrame) -> bool {
    match f {
        SpecFrame::Ack(a) => ack_encodable(a) && rfc_ack_ranges_valid(
            a.largest,
            a.first_range,
            a.ranges,
        ),
        SpecFrame::ResetStream { stream_id, error_code, final_size } => stream_id <= VARINT_MAX
            && error_code <= VARINT_MAX && final_size <= VARINT_MAX,
        SpecFrame::StopSending { stream_id, error_code } => stream_id <= VARINT_MAX && error_code
            <= VARINT_MAX,
        SpecFrame::Crypto { offset, data } => offset + data.len() <= VARINT_MAX,
        SpecFrame::Stream { stream_id, offset, data, fin } => stream_id <= VARINT_MAX && offset
            + data.len() <= VARINT_MAX,
        SpecFrame::MaxData(v) => v <= VARINT_MAX,
        SpecFrame::MaxStreamData { stream_id, max } => stream_id <= VARINT_MAX && max
            <= VARINT_MAX,
        SpecFrame::MaxStreams { bidi, max } => max <= MAX_STREAMS_LIMIT,
        SpecFrame::DataBlocked(v) => v <= VARINT_MAX,
        SpecFrame::StreamDataBlocked { stream_id, max } => stream_id <= VARINT_MAX && max
            <= VARINT_MAX,
        SpecFrame::StreamsBlocked { bidi, max } => max <= MAX_STREAMS_LIMIT,
        SpecFrame::NewConnectionId { seq, retire_prior_to, cid, reset_token } => seq <= VARINT_MAX
            && retire_prior_to <= seq && 1 <= cid.len() <= MAX_CID_LEN && reset_token.len()
            == RESET_TOKEN_LEN,
        SpecFrame::RetireConnectionId(v) => v <= VARINT_MAX,
        SpecFrame::PathChallenge(d) => d.len() == 8,
        SpecFrame::PathResponse(d) => d.len() == 8,
        SpecFrame::ConnectionClose { app, error_code, frame_type, reason } => error_code
            <= VARINT_MAX && frame_type <= VARINT_MAX && reason.len() <= VARINT_MAX && (app
            ==> frame_type == 0),
        _ => true,
    }
}

/// The type `serialize_frame` writes. STREAM always sets LEN, and sets OFF only for a
/// nonzero offset.
pub open spec fn spec_frame_type(f: SpecFrame) -> u64 {
    match f {
        SpecFrame::Padding => FRAME_PADDING,
        SpecFrame::Ping => FRAME_PING,
        SpecFrame::Ack(a) => spec_ack_type(a),
        SpecFrame::ResetStream { .. } => FRAME_RESET_STREAM,
        SpecFrame::StopSending { .. } => FRAME_STOP_SENDING,
        SpecFrame::Crypto { .. } => FRAME_CRYPTO,
        SpecFrame::Stream { offset, fin, .. } => FRAME_STREAM_MIN | (if offset > 0 {
            0x04u64
        } else {
            0
        }) | 0x02 | (if fin {
            0x01u64
        } else {
            0
        }),
        SpecFrame::MaxData(_) => FRAME_MAX_DATA,
        SpecFrame::MaxStreamData { .. } => FRAME_MAX_STREAM_DATA,
        SpecFrame::MaxStreams { bidi, .. } => if bidi {
            FRAME_MAX_STREAMS_BIDI
        } else {
            FRAME_MAX_STREAMS_UNI
        },
        SpecFrame::DataBlocked(_) => FRAME_DATA_BLOCKED,
        SpecFrame::StreamDataBlocked { .. } => FRAME_STREAM_DATA_BLOCKED,
        SpecFrame::StreamsBlocked { bidi, .. } => if bidi {
            FRAME_STREAMS_BLOCKED_BIDI
        } else {
            FRAME_STREAMS_BLOCKED_UNI
        },
        SpecFrame::NewConnectionId { .. } => FRAME_NEW_CONNECTION_ID,
        SpecFrame::RetireConnectionId(_) => FRAME_RETIRE_CONNECTION_ID,
        SpecFrame::PathChallenge(_) => FRAME_PATH_CHALLENGE,
        SpecFrame::PathResponse(_) => FRAME_PATH_RESPONSE,
        SpecFrame::ConnectionClose { app, .. } => if app {
            FRAME_CONNECTION_CLOSE_APP
        } else {
            FRAME_CONNECTION_CLOSE
        },
        SpecFrame::HandshakeDone => FRAME_HANDSHAKE_DONE,
    }
}

/// Everything after the type.
pub open spec fn spec_frame_body(f: SpecFrame) -> Seq<u8> {
    match f {
        SpecFrame::Ack(a) => spec_ack_body(a),
        SpecFrame::ResetStream { stream_id, error_code, final_size } => spec_varint(stream_id) + (
        spec_varint(error_code) + spec_varint(final_size)),
        SpecFrame::StopSending { stream_id, error_code } => spec_varint(stream_id) + spec_varint(
            error_code,
        ),
        SpecFrame::Crypto { offset, data } => spec_varint(offset) + (spec_varint(
            data.len() as u64,
        ) + data),
        SpecFrame::Stream { stream_id, offset, data, .. } => spec_varint(stream_id) + ((if offset
            > 0 {
            spec_varint(offset)
        } else {
            Seq::empty()
        }) + (spec_varint(data.len() as u64) + data)),
        SpecFrame::MaxData(v) => spec_varint(v),
        SpecFrame::MaxStreamData { stream_id, max } => spec_varint(stream_id) + spec_varint(max),
        SpecFrame::MaxStreams { max, .. } => spec_varint(max),
        SpecFrame::DataBlocked(v) => spec_varint(v),
        SpecFrame::StreamDataBlocked { stream_id, max } => spec_varint(stream_id) + spec_varint(
            max,
        ),
        SpecFrame::StreamsBlocked { max, .. } => spec_varint(max),
        SpecFrame::NewConnectionId { seq, retire_prior_to, cid, reset_token } => spec_varint(seq)
            + (spec_varint(retire_prior_to) + (seq![cid.len() as u8] + (cid + reset_token))),
        SpecFrame::RetireConnectionId(v) => spec_varint(v),
        SpecFrame::PathChallenge(d) => d,
        SpecFrame::PathResponse(d) => d,
        SpecFrame::ConnectionClose { app, error_code, frame_type, reason } => spec_varint(
            error_code,
        ) + ((if app {
            Seq::empty()
        } else {
            spec_varint(frame_type)
        }) + (spec_varint(reason.len() as u64) + reason)),
        _ => Seq::empty(),
    }
}

/// The whole frame, type included.
pub open spec fn spec_frame_bytes(f: SpecFrame) -> Seq<u8> {
    spec_varint(spec_frame_type(f)) + spec_frame_body(f)
}

// =============================================================================
// Proofs
// =============================================================================

proof fn lemma_stream_type_bits(o: u64, f: u64) by (bit_vector)
    requires
        o == 0 || o == 4,
        f == 0 || f == 1,
    ensures
        8 <= (8u64 | o | 2u64 | f) <= 15,
        ((8u64 | o | 2u64 | f) & 4u64 != 0) == (o == 4),
        (8u64 | o | 2u64 | f) & 2u64 != 0,
        ((8u64 | o | 2u64 | f) & 1u64 != 0) == (f == 1),
{
}

proof fn lemma_streams_limit()
    ensures
        MAX_STREAMS_LIMIT <= VARINT_MAX,
{
    assert(MAX_STREAMS_LIMIT <= VARINT_MAX) by (compute_only);
}

proof fn lemma_frame_type_small(f: SpecFrame)
    ensures
        spec_frame_type(f) <= FRAME_HANDSHAKE_DONE,
{
    if let SpecFrame::Stream { offset, fin, .. } = f {
        lemma_stream_type_bits(if offset > 0 { 4 } else { 0 }, if fin { 1 } else { 0 });
    }
}

/// The minimal varint of `v` at offset `p` reads back through `rfc_vint`.
proof fn lemma_vint_at(b: Seq<u8>, p: int, v: u64, tail: Seq<u8>)
    requires
        0 <= p <= b.len(),
        v <= VARINT_MAX,
        b.skip(p) == spec_varint(v) + tail,
    ensures
        rfc_vint(b, p) == Some((v, p + spec_varint(v).len())),
        p + spec_varint(v).len() <= b.len(),
        b.skip(p + spec_varint(v).len()) == tail,
{
    lemma_varint_at(b, p, v, tail);
}

/// `d` at offset `p` reads back through `rfc_bytes`.
proof fn lemma_bytes_at(b: Seq<u8>, p: int, d: Seq<u8>, tail: Seq<u8>)
    requires
        0 <= p <= b.len(),
        b.skip(p) == d + tail,
    ensures
        rfc_bytes(b, p, d.len() as int) == Some((d, p + d.len())),
        p + d.len() <= b.len(),
        b.skip(p + d.len()) == tail,
{
    assert(b.skip(p).len() == b.len() - p);
    assert((d + tail).len() == d.len() + tail.len());
    assert forall|i: int| 0 <= i < d.len() implies b.subrange(p, p + d.len())[i] == d[i] by {
        assert(b.skip(p)[i] == b[p + i]);
    }
    assert(b.subrange(p, p + d.len()) =~= d);
    assert forall|i: int| 0 <= i < tail.len() implies b.skip(p + d.len())[i] == tail[i] by {
        assert(b.skip(p)[d.len() + i] == b[p + d.len() + i]);
    }
    assert(b.skip(p + d.len()) =~= tail);
}

proof fn lemma_skip0(b: Seq<u8>)
    ensures
        b.skip(0) == b,
{
    assert(b.skip(0) =~= b);
}

proof fn lemma_reset_stream_rt(x: u64, y: u64, z: u64, rest: Seq<u8>)
    requires
        x <= VARINT_MAX,
        y <= VARINT_MAX,
        z <= VARINT_MAX,
    ensures
        ({
            let body = spec_varint(x) + (spec_varint(y) + spec_varint(z));
            rfc_reset_stream(body + rest) == Some(
                (SpecFrame::ResetStream { stream_id: x, error_code: y, final_size: z }, body.len() as int),
            )
        }),
{
    hide(rfc_varint_decode);
    let (vx, vy, vz) = (spec_varint(x), spec_varint(y), spec_varint(z));
    let b = vx + (vy + vz) + rest;
    assert(b =~= vx + (vy + (vz + rest)));
    lemma_skip0(b);
    lemma_vint_at(b, 0, x, vy + (vz + rest));
    lemma_vint_at(b, vx.len() as int, y, vz + rest);
    lemma_vint_at(b, (vx.len() + vy.len()) as int, z, rest);
}

proof fn lemma_two_varints_rt(ty: u64, x: u64, y: u64, rest: Seq<u8>)
    requires
        x <= VARINT_MAX,
        y <= VARINT_MAX,
    ensures
        ({
            let body = spec_varint(x) + spec_varint(y);
            &&& rfc_vint(body + rest, 0) == Some((x, spec_varint(x).len() as int))
            &&& rfc_vint(body + rest, spec_varint(x).len() as int) == Some((y, body.len() as int))
        }),
{
    hide(rfc_varint_decode);
    let (vx, vy) = (spec_varint(x), spec_varint(y));
    let b = vx + vy + rest;
    assert(b =~= vx + (vy + rest));
    lemma_skip0(b);
    lemma_vint_at(b, 0, x, vy + rest);
    lemma_vint_at(b, vx.len() as int, y, rest);
}

proof fn lemma_one_varint_rt(x: u64, rest: Seq<u8>)
    requires
        x <= VARINT_MAX,
    ensures
        rfc_vint(spec_varint(x) + rest, 0) == Some((x, spec_varint(x).len() as int)),
{
    hide(rfc_varint_decode);
    let b = spec_varint(x) + rest;
    lemma_skip0(b);
    lemma_vint_at(b, 0, x, rest);
}

proof fn lemma_crypto_rt(offset: u64, data: Seq<u8>, rest: Seq<u8>)
    requires
        offset + data.len() <= VARINT_MAX,
    ensures
        ({
            let body = spec_varint(offset) + (spec_varint(data.len() as u64) + data);
            rfc_crypto(body + rest) == Some((SpecFrame::Crypto { offset, data }, body.len() as int))
        }),
{
    hide(rfc_varint_decode);
    let len = data.len() as u64;
    let (vo, vl) = (spec_varint(offset), spec_varint(len));
    let b = vo + (vl + data) + rest;
    assert(b =~= vo + (vl + (data + rest)));
    lemma_skip0(b);
    lemma_vint_at(b, 0, offset, vl + (data + rest));
    lemma_vint_at(b, vo.len() as int, len, data + rest);
    lemma_bytes_at(b, (vo.len() + vl.len()) as int, data, rest);
}

proof fn lemma_stream_rt(stream_id: u64, offset: u64, data: Seq<u8>, fin: bool, rest: Seq<u8>)
    requires
        stream_id <= VARINT_MAX,
        offset + data.len() <= VARINT_MAX,
    ensures
        ({
            let f = SpecFrame::Stream { stream_id, offset, data, fin };
            let ty = spec_frame_type(f);
            &&& FRAME_STREAM_MIN <= ty <= FRAME_STREAM_MAX
            &&& rfc_stream(ty, spec_frame_body(f) + rest) == Some(
                (f, spec_frame_body(f).len() as int),
            )
        }),
{
    hide(rfc_varint_decode);
    let f = SpecFrame::Stream { stream_id, offset, data, fin };
    let ty = spec_frame_type(f);
    lemma_stream_type_bits(if offset > 0 { 4 } else { 0 }, if fin { 1 } else { 0 });
    let len = data.len() as u64;
    let vi = spec_varint(stream_id);
    let vo: Seq<u8> = if offset > 0 { spec_varint(offset) } else { Seq::empty() };
    let vl = spec_varint(len);
    let b = spec_frame_body(f) + rest;
    assert(b =~= vi + (vo + (vl + (data + rest))));
    lemma_skip0(b);
    lemma_vint_at(b, 0, stream_id, vo + (vl + (data + rest)));
    let p1 = vi.len() as int;
    if offset > 0 {
        lemma_vint_at(b, p1, offset, vl + (data + rest));
    } else {
        assert(vo + (vl + (data + rest)) =~= vl + (data + rest));
    }
    let p2 = p1 + vo.len();
    assert(rfc_stream_offset(ty, b, p1) == Some((offset, p2)));
    lemma_vint_at(b, p2, len, data + rest);
    let p3 = p2 + vl.len();
    assert(rfc_stream_len(ty, b, p2) == Some((len as int, p3)));
    lemma_bytes_at(b, p3, data, rest);
    assert(rfc_stream_data(b, p3, offset, len as int) == Some((data, p3 + data.len())));
}

proof fn lemma_ncid_rt(seq: u64, rpt: u64, cid: Seq<u8>, token: Seq<u8>, rest: Seq<u8>)
    requires
        seq <= VARINT_MAX,
        rpt <= seq,
        1 <= cid.len() <= MAX_CID_LEN,
        token.len() == RESET_TOKEN_LEN,
    ensures
        ({
            let f = SpecFrame::NewConnectionId { seq, retire_prior_to: rpt, cid, reset_token: token };
            rfc_new_connection_id(spec_frame_body(f) + rest) == Some(
                (f, spec_frame_body(f).len() as int),
            )
        }),
{
    hide(rfc_varint_decode);
    let f = SpecFrame::NewConnectionId { seq, retire_prior_to: rpt, cid, reset_token: token };
    let (vs, vr) = (spec_varint(seq), spec_varint(rpt));
    let l = seq![cid.len() as u8];
    let b = spec_frame_body(f) + rest;
    assert(b =~= vs + (vr + (l + (cid + (token + rest)))));
    lemma_skip0(b);
    lemma_vint_at(b, 0, seq, vr + (l + (cid + (token + rest))));
    lemma_vint_at(b, vs.len() as int, rpt, l + (cid + (token + rest)));
    let p2 = (vs.len() + vr.len()) as int;
    lemma_bytes_at(b, p2, l, cid + (token + rest));
    assert(b[p2] == cid.len() as u8) by {
        assert(b.skip(p2)[0] == b[p2]);
    }
    lemma_bytes_at(b, p2 + 1, cid, token + rest);
    lemma_bytes_at(b, p2 + 1 + cid.len(), token, rest);
}

proof fn lemma_path_rt(ty: u64, d: Seq<u8>, rest: Seq<u8>)
    requires
        d.len() == 8,
    ensures
        rfc_bytes(d + rest, 0, 8) == Some((d, 8int)),
{
    lemma_skip0(d + rest);
    lemma_bytes_at(d + rest, 0, d, rest);
}

proof fn lemma_close_rt(app: bool, ec: u64, ft: u64, reason: Seq<u8>, rest: Seq<u8>)
    requires
        ec <= VARINT_MAX,
        ft <= VARINT_MAX,
        reason.len() <= VARINT_MAX,
        app ==> ft == 0,
    ensures
        ({
            let f = SpecFrame::ConnectionClose { app, error_code: ec, frame_type: ft, reason };
            rfc_close(spec_frame_type(f), spec_frame_body(f) + rest) == Some(
                (f, spec_frame_body(f).len() as int),
            )
        }),
{
    hide(rfc_varint_decode);
    let f = SpecFrame::ConnectionClose { app, error_code: ec, frame_type: ft, reason };
    let len = reason.len() as u64;
    let ve = spec_varint(ec);
    let vf: Seq<u8> = if app { Seq::empty() } else { spec_varint(ft) };
    let vl = spec_varint(len);
    let b = spec_frame_body(f) + rest;
    assert(b =~= ve + (vf + (vl + (reason + rest))));
    lemma_skip0(b);
    lemma_vint_at(b, 0, ec, vf + (vl + (reason + rest)));
    let p1 = ve.len() as int;
    if !app {
        lemma_vint_at(b, p1, ft, vl + (reason + rest));
    } else {
        assert(vf + (vl + (reason + rest)) =~= vl + (reason + rest));
    }
    let p2 = p1 + vf.len();
    lemma_vint_at(b, p2, len, reason + rest);
    lemma_bytes_at(b, p2 + vl.len(), reason, rest);
}

/// `lemma_body_roundtrip` for PADDING through STREAM (split for the rlimit).
proof fn lemma_body_roundtrip_a(f: SpecFrame, rest: Seq<u8>)
    requires
        frame_wf(f),
        f is Padding || f is Ping || f is Ack || f is ResetStream || f is StopSending || f is Crypto
            || f is Stream,
    ensures
        rfc_frame_body(spec_frame_type(f), spec_frame_body(f) + rest) == Ok::<(SpecFrame, nat), u64>(
            (f, spec_frame_body(f).len()),
        ),
{
    let body = spec_frame_body(f);
    match f {
        SpecFrame::Padding => {
            assert(body + rest =~= rest);
        },
        SpecFrame::Ping => {
            assert(body + rest =~= rest);
        },
        SpecFrame::Ack(a) => {
            let ty = spec_ack_type(a);
            theorem_ack_roundtrip(a, rest);
            lemma_serialize_bytes::<true>(ty);
            assert(spec_ack_bytes(a).skip(1) =~= spec_ack_body(a));
        },
        SpecFrame::ResetStream { stream_id, error_code, final_size } => {
            lemma_reset_stream_rt(stream_id, error_code, final_size, rest);
        },
        SpecFrame::StopSending { stream_id, error_code } => {
            lemma_two_varints_rt(FRAME_STOP_SENDING, stream_id, error_code, rest);
        },
        SpecFrame::Crypto { offset, data } => {
            lemma_crypto_rt(offset, data, rest);
        },
        SpecFrame::Stream { stream_id, offset, data, fin } => {
            lemma_stream_rt(stream_id, offset, data, fin, rest);
        },
        _ => {},
    }
}

/// `lemma_body_roundtrip` for MAX_DATA through CONNECTION_CLOSE.
proof fn lemma_body_roundtrip_b(f: SpecFrame, rest: Seq<u8>)
    requires
        frame_wf(f),
        !(f is Padding || f is Ping || f is Ack || f is ResetStream || f is StopSending || f is Crypto
            || f is Stream || f is HandshakeDone),
    ensures
        rfc_frame_body(spec_frame_type(f), spec_frame_body(f) + rest) == Ok::<(SpecFrame, nat), u64>(
            (f, spec_frame_body(f).len()),
        ),
{
    match f {
        SpecFrame::MaxData(v) => {
            lemma_one_varint_rt(v, rest);
        },
        SpecFrame::MaxStreamData { stream_id, max } => {
            lemma_two_varints_rt(FRAME_MAX_STREAM_DATA, stream_id, max, rest);
        },
        SpecFrame::MaxStreams { bidi, max } => {
            lemma_streams_limit();
            lemma_one_varint_rt(max, rest);
        },
        SpecFrame::DataBlocked(v) => {
            lemma_one_varint_rt(v, rest);
        },
        SpecFrame::StreamDataBlocked { stream_id, max } => {
            lemma_two_varints_rt(FRAME_STREAM_DATA_BLOCKED, stream_id, max, rest);
        },
        SpecFrame::StreamsBlocked { bidi, max } => {
            lemma_streams_limit();
            lemma_one_varint_rt(max, rest);
        },
        SpecFrame::NewConnectionId { seq, retire_prior_to, cid, reset_token } => {
            lemma_ncid_rt(seq, retire_prior_to, cid, reset_token, rest);
        },
        SpecFrame::RetireConnectionId(v) => {
            lemma_one_varint_rt(v, rest);
        },
        SpecFrame::PathChallenge(d) => {
            lemma_path_rt(FRAME_PATH_CHALLENGE, d, rest);
        },
        SpecFrame::PathResponse(d) => {
            lemma_path_rt(FRAME_PATH_RESPONSE, d, rest);
        },
        SpecFrame::ConnectionClose { app, error_code, frame_type, reason } => {
            lemma_close_rt(app, error_code, frame_type, reason, rest);
        },
        _ => {},
    }
}

/// The body `serialize_frame` writes after the type parses back under that type.
proof fn lemma_body_roundtrip(f: SpecFrame, rest: Seq<u8>)
    requires
        frame_wf(f),
        !(f is HandshakeDone),
    ensures
        rfc_frame_body(spec_frame_type(f), spec_frame_body(f) + rest) == Ok::<(SpecFrame, nat), u64>(
            (f, spec_frame_body(f).len()),
        ),
{
    if f is Padding || f is Ping || f is Ack || f is ResetStream || f is StopSending || f is Crypto
        || f is Stream {
        lemma_body_roundtrip_a(f, rest);
    } else {
        lemma_body_roundtrip_b(f, rest);
    }
}

/// Parsing what `serialize_frame` wrote, followed by anything, recovers the frame and
/// consumes exactly its bytes. HANDSHAKE_DONE is excluded: a server sends it but rejects it.
pub proof fn theorem_frame_roundtrip(f: SpecFrame, rest: Seq<u8>)
    requires
        frame_wf(f),
        !(f is HandshakeDone),
    ensures
        rfc_frame(spec_frame_bytes(f) + rest) == Ok::<(SpecFrame, nat), u64>(
            (f, spec_frame_bytes(f).len()),
        ),
{
    let ty = spec_frame_type(f);
    let body = spec_frame_body(f);
    let b = spec_frame_bytes(f) + rest;
    lemma_frame_type_small(f);
    theorem_serialize_matches_rfc(ty);
    assert(b =~= spec_varint(ty) + (body + rest));
    lemma_skip0(b);
    lemma_varint_at(b, 0, ty, body + rest);
    lemma_body_roundtrip(f, rest);
}

// =============================================================================
// Executable code
// =============================================================================

/// The varint at offset `off`, with the offset after it.
fn vint_at(b: &[u8], off: usize) -> (r: Option<(u64, usize)>)
    requires
        off <= b.len(),
    ensures
        match r {
            Some((v, q)) => {
                &&& rfc_vint(b@, off as int) == Some((v, q as int))
                &&& off < q <= b.len()
                &&& v <= VARINT_MAX
            },
            None => rfc_vint(b@, off as int) is None,
        },
{
    match varint_at(b, off) {
        Some((n, v)) => Some((v, off + n)),
        None => None,
    }
}

/// A copy of the `len` bytes at offset `off`, made only once they are known to be present.
fn bytes_at(b: &[u8], off: usize, len: u64) -> (r: Option<(Vec<u8>, usize)>)
    requires
        off <= b.len(),
    ensures
        match r {
            Some((v, q)) => rfc_bytes(b@, off as int, len as int) == Some((v@, q as int)) && q
                <= b.len(),
            None => rfc_bytes(b@, off as int, len as int) is None,
        },
{
    if len > (b.len() - off) as u64 {
        return None;
    }
    let q = off + len as usize;
    Some((slice_to_vec(slice_subrange(b, off, q)), q))
}

fn stream_data_at(b: &[u8], off: usize, offset: u64, len: u64) -> (r: Option<(Vec<u8>, usize)>)
    requires
        off <= b.len(),
        offset <= VARINT_MAX,
    ensures
        match r {
            Some((v, q)) => rfc_stream_data(b@, off as int, offset, len as int) == Some(
                (v@, q as int),
            ) && q <= b.len(),
            None => rfc_stream_data(b@, off as int, offset, len as int) is None,
        },
{
    if len > VARINT_MAX - offset {
        return None;
    }
    bytes_at(b, off, len)
}

fn parse_reset_stream(b: &[u8]) -> (r: Option<(Frame, usize)>)
    ensures
        match r {
            Some((f, n)) => rfc_reset_stream(b@) == Some((f@, n as int)) && n <= b.len(),
            None => rfc_reset_stream(b@) is None,
        },
{
    let (stream_id, p1) = match vint_at(b, 0) {
        Some(x) => x,
        None => return None,
    };
    let (error_code, p2) = match vint_at(b, p1) {
        Some(x) => x,
        None => return None,
    };
    let (final_size, q) = match vint_at(b, p2) {
        Some(x) => x,
        None => return None,
    };
    Some((Frame::ResetStream { stream_id, error_code, final_size }, q))
}

fn parse_two_varints(ty: u64, b: &[u8]) -> (r: Option<(Frame, usize)>)
    ensures
        match r {
            Some((f, n)) => rfc_two_varints(ty, b@) == Some((f@, n as int)) && n <= b.len(),
            None => rfc_two_varints(ty, b@) is None,
        },
{
    let (x, p1) = match vint_at(b, 0) {
        Some(v) => v,
        None => return None,
    };
    let (y, q) = match vint_at(b, p1) {
        Some(v) => v,
        None => return None,
    };
    let f = if ty == FRAME_STOP_SENDING {
        Frame::StopSending { stream_id: x, error_code: y }
    } else if ty == FRAME_MAX_STREAM_DATA {
        Frame::MaxStreamData { stream_id: x, max: y }
    } else {
        Frame::StreamDataBlocked { stream_id: x, max: y }
    };
    Some((f, q))
}

fn parse_crypto(b: &[u8]) -> (r: Option<(Frame, usize)>)
    ensures
        match r {
            Some((f, n)) => rfc_crypto(b@) == Some((f@, n as int)) && n <= b.len(),
            None => rfc_crypto(b@) is None,
        },
{
    let (offset, p1) = match vint_at(b, 0) {
        Some(x) => x,
        None => return None,
    };
    let (len, p2) = match vint_at(b, p1) {
        Some(x) => x,
        None => return None,
    };
    let (data, q) = match stream_data_at(b, p2, offset, len) {
        Some(x) => x,
        None => return None,
    };
    Some((Frame::Crypto { offset, data }, q))
}

fn parse_stream(ty: u64, b: &[u8]) -> (r: Option<(Frame, usize)>)
    ensures
        match r {
            Some((f, n)) => rfc_stream(ty, b@) == Some((f@, n as int)) && n <= b.len(),
            None => rfc_stream(ty, b@) is None,
        },
{
    let (stream_id, p1) = match vint_at(b, 0) {
        Some(x) => x,
        None => return None,
    };
    let (offset, p2) = if ty & 0x04 != 0 {
        match vint_at(b, p1) {
            Some(x) => x,
            None => return None,
        }
    } else {
        (0, p1)
    };
    let (len, p3) = if ty & 0x02 != 0 {
        match vint_at(b, p2) {
            Some(x) => x,
            None => return None,
        }
    } else {
        ((b.len() - p2) as u64, p2)
    };
    let (data, q) = match stream_data_at(b, p3, offset, len) {
        Some(x) => x,
        None => return None,
    };
    Some((Frame::Stream { stream_id, offset, data, fin: ty & 0x01 != 0 }, q))
}

fn parse_one_varint(ty: u64, b: &[u8]) -> (r: Option<(Frame, usize)>)
    ensures
        match r {
            Some((f, n)) => rfc_one_varint(ty, b@) == Some((f@, n as int)) && n <= b.len(),
            None => rfc_one_varint(ty, b@) is None,
        },
{
    let (v, q) = match vint_at(b, 0) {
        Some(x) => x,
        None => return None,
    };
    let f = if ty == FRAME_MAX_DATA {
        Frame::MaxData(v)
    } else if ty == FRAME_DATA_BLOCKED {
        Frame::DataBlocked(v)
    } else if ty == FRAME_RETIRE_CONNECTION_ID {
        Frame::RetireConnectionId(v)
    } else if v > MAX_STREAMS_LIMIT {
        return None;
    } else if ty == FRAME_MAX_STREAMS_BIDI || ty == FRAME_MAX_STREAMS_UNI {
        Frame::MaxStreams { bidi: ty == FRAME_MAX_STREAMS_BIDI, max: v }
    } else {
        Frame::StreamsBlocked { bidi: ty == FRAME_STREAMS_BLOCKED_BIDI, max: v }
    };
    Some((f, q))
}

fn parse_new_connection_id(b: &[u8]) -> (r: Option<(Frame, usize)>)
    ensures
        match r {
            Some((f, n)) => rfc_new_connection_id(b@) == Some((f@, n as int)) && n <= b.len(),
            None => rfc_new_connection_id(b@) is None,
        },
{
    let (seq, p1) = match vint_at(b, 0) {
        Some(x) => x,
        None => return None,
    };
    let (retire_prior_to, p2) = match vint_at(b, p1) {
        Some(x) => x,
        None => return None,
    };
    if p2 >= b.len() {
        return None;
    }
    let l = b[p2];
    if l < 1 || l as usize > MAX_CID_LEN || retire_prior_to > seq {
        return None;
    }
    let (cid, p3) = match bytes_at(b, p2 + 1, l as u64) {
        Some(x) => x,
        None => return None,
    };
    if RESET_TOKEN_LEN > b.len() - p3 {
        return None;
    }
    let mut reset_token = [0u8; 16];
    reset_token.copy_from_slice(slice_subrange(b, p3, p3 + RESET_TOKEN_LEN));
    Some((Frame::NewConnectionId { seq, retire_prior_to, cid, reset_token }, p3 + RESET_TOKEN_LEN))
}

fn parse_path(ty: u64, b: &[u8]) -> (r: Option<(Frame, usize)>)
    ensures
        match r {
            Some((f, n)) => rfc_path(ty, b@) == Some((f@, n as int)) && n <= b.len(),
            None => rfc_path(ty, b@) is None,
        },
{
    if b.len() < 8 {
        return None;
    }
    let mut d = [0u8; 8];
    d.copy_from_slice(slice_subrange(b, 0, 8));
    let f = if ty == FRAME_PATH_CHALLENGE {
        Frame::PathChallenge(d)
    } else {
        Frame::PathResponse(d)
    };
    Some((f, 8))
}

fn parse_close(ty: u64, b: &[u8]) -> (r: Option<(Frame, usize)>)
    ensures
        match r {
            Some((f, n)) => rfc_close(ty, b@) == Some((f@, n as int)) && n <= b.len(),
            None => rfc_close(ty, b@) is None,
        },
{
    let app = ty == FRAME_CONNECTION_CLOSE_APP;
    let (error_code, p1) = match vint_at(b, 0) {
        Some(x) => x,
        None => return None,
    };
    let (frame_type, p2) = if app {
        (0, p1)
    } else {
        match vint_at(b, p1) {
            Some(x) => x,
            None => return None,
        }
    };
    let (len, p3) = match vint_at(b, p2) {
        Some(x) => x,
        None => return None,
    };
    let (reason, q) = match bytes_at(b, p3, len) {
        Some(x) => x,
        None => return None,
    };
    Some((Frame::ConnectionClose { app, error_code, frame_type, reason }, q))
}

fn parse_frame_fields(ty: u64, b: &[u8]) -> (r: Option<(Frame, usize)>)
    ensures
        match r {
            Some((f, n)) => rfc_frame_fields(ty, b@) == Some((f@, n as int)) && n <= b.len(),
            None => rfc_frame_fields(ty, b@) is None,
        },
{
    if ty == FRAME_PADDING {
        Some((Frame::Padding, 0))
    } else if ty == FRAME_PING {
        Some((Frame::Ping, 0))
    } else if ty == FRAME_RESET_STREAM {
        parse_reset_stream(b)
    } else if ty == FRAME_STOP_SENDING || ty == FRAME_MAX_STREAM_DATA || ty
        == FRAME_STREAM_DATA_BLOCKED {
        parse_two_varints(ty, b)
    } else if ty == FRAME_CRYPTO {
        parse_crypto(b)
    } else if FRAME_STREAM_MIN <= ty && ty <= FRAME_STREAM_MAX {
        parse_stream(ty, b)
    } else if ty == FRAME_MAX_DATA || ty == FRAME_MAX_STREAMS_BIDI || ty == FRAME_MAX_STREAMS_UNI
        || ty == FRAME_DATA_BLOCKED || ty == FRAME_STREAMS_BLOCKED_BIDI || ty
        == FRAME_STREAMS_BLOCKED_UNI || ty == FRAME_RETIRE_CONNECTION_ID {
        parse_one_varint(ty, b)
    } else if ty == FRAME_NEW_CONNECTION_ID {
        parse_new_connection_id(b)
    } else if ty == FRAME_PATH_CHALLENGE || ty == FRAME_PATH_RESPONSE {
        parse_path(ty, b)
    } else if ty == FRAME_CONNECTION_CLOSE || ty == FRAME_CONNECTION_CLOSE_APP {
        parse_close(ty, b)
    } else {
        None
    }
}

/// The frame type at the front of `b` and its encoded length.
pub fn parse_frame_type(b: &[u8]) -> (r: Result<(u64, usize), u64>)
    ensures
        match r {
            Ok((v, n)) => rfc_frame_type(b@) == Ok::<(u64, nat), u64>((v, n as nat)) && n
                <= b.len(),
            Err(e) => rfc_frame_type(b@) == Err::<(u64, nat), u64>(e),
        },
{
    proof {
        lemma_skip0(b@);
    }
    // Lenient parse, then the length check: the minimal parser alone cannot tell a
    // non-minimal type (PROTOCOL_VIOLATION) from a truncated one (FRAME_ENCODING_ERROR).
    match varint_at(b, 0) {
        None => Err(FRAME_ENCODING_ERROR),
        Some((n, v)) => if n == varint_len(v) {
            Ok((v, n))
        } else {
            Err(PROTOCOL_VIOLATION)
        },
    }
}

/// The frame body after type `ty`, as a server receives it, with the bytes consumed.
pub fn parse_frame_body(ty: u64, b: &[u8]) -> (r: Result<(Frame, usize), u64>)
    ensures
        match r {
            Ok((f, n)) => rfc_frame_body(ty, b@) == Ok::<(SpecFrame, nat), u64>((f@, n as nat))
                && n <= b.len(),
            Err(e) => rfc_frame_body(ty, b@) == Err::<(SpecFrame, nat), u64>(e),
        },
{
    if ty == FRAME_NEW_TOKEN || ty == FRAME_HANDSHAKE_DONE {
        return Err(PROTOCOL_VIOLATION);
    }
    if ty == FRAME_ACK || ty == FRAME_ACK_ECN {
        return match parse_ack(ty, b) {
            Ok((a, n)) => Ok((Frame::Ack(a), n)),
            Err(e) => Err(e),
        };
    }
    match parse_frame_fields(ty, b) {
        Some((f, n)) => Ok((f, n)),
        None => Err(FRAME_ENCODING_ERROR),
    }
}

/// One whole frame from the front of `b`, with the bytes consumed.
pub fn parse_frame(b: &[u8]) -> (r: Result<(Frame, usize), u64>)
    ensures
        match r {
            Ok((f, n)) => rfc_frame(b@) == Ok::<(SpecFrame, nat), u64>((f@, n as nat)) && n
                <= b.len(),
            Err(e) => rfc_frame(b@) == Err::<(SpecFrame, nat), u64>(e),
        },
{
    let (ty, n) = match parse_frame_type(b) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    let body = slice_subrange(b, n, b.len());
    proof {
        assert(body@ =~= b@.skip(n as int));
    }
    match parse_frame_body(ty, body) {
        Ok((f, m)) => Ok((f, n + m)),
        Err(e) => Err(e),
    }
}

/// The type byte `serialize_frame` writes for `f`.
pub fn frame_type_of(f: &Frame) -> (r: u64)
    ensures
        r == spec_frame_type(f@),
        r <= FRAME_HANDSHAKE_DONE,
{
    proof {
        lemma_frame_type_small(f@);
    }
    match f {
        Frame::Padding => FRAME_PADDING,
        Frame::Ping => FRAME_PING,
        Frame::Ack(a) => if a.ecn.is_some() {
            FRAME_ACK_ECN
        } else {
            FRAME_ACK
        },
        Frame::ResetStream { .. } => FRAME_RESET_STREAM,
        Frame::StopSending { .. } => FRAME_STOP_SENDING,
        Frame::Crypto { .. } => FRAME_CRYPTO,
        Frame::Stream { offset, fin, .. } => FRAME_STREAM_MIN | (if *offset > 0 {
            0x04u64
        } else {
            0
        }) | 0x02 | (if *fin {
            0x01u64
        } else {
            0
        }),
        Frame::MaxData(_) => FRAME_MAX_DATA,
        Frame::MaxStreamData { .. } => FRAME_MAX_STREAM_DATA,
        Frame::MaxStreams { bidi, .. } => if *bidi {
            FRAME_MAX_STREAMS_BIDI
        } else {
            FRAME_MAX_STREAMS_UNI
        },
        Frame::DataBlocked(_) => FRAME_DATA_BLOCKED,
        Frame::StreamDataBlocked { .. } => FRAME_STREAM_DATA_BLOCKED,
        Frame::StreamsBlocked { bidi, .. } => if *bidi {
            FRAME_STREAMS_BLOCKED_BIDI
        } else {
            FRAME_STREAMS_BLOCKED_UNI
        },
        Frame::NewConnectionId { .. } => FRAME_NEW_CONNECTION_ID,
        Frame::RetireConnectionId(_) => FRAME_RETIRE_CONNECTION_ID,
        Frame::PathChallenge(_) => FRAME_PATH_CHALLENGE,
        Frame::PathResponse(_) => FRAME_PATH_RESPONSE,
        Frame::ConnectionClose { app, .. } => if *app {
            FRAME_CONNECTION_CLOSE_APP
        } else {
            FRAME_CONNECTION_CLOSE
        },
        Frame::HandshakeDone => FRAME_HANDSHAKE_DONE,
    }
}

fn put_bytes(s: &[u8], out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + s@,
{
    out.extend_from_slice(s);
    assert(out@ =~= old(out)@ + s@);
}

fn put_varints2(x: u64, y: u64, out: &mut Vec<u8>)
    requires
        x <= VARINT_MAX,
        y <= VARINT_MAX,
    ensures
        final(out)@ == old(out)@ + (spec_varint(x) + spec_varint(y)),
{
    put_varint(x, out);
    put_varint(y, out);
    assert(out@ =~= old(out)@ + (spec_varint(x) + spec_varint(y)));
}

fn put_varints3(x: u64, y: u64, z: u64, out: &mut Vec<u8>)
    requires
        x <= VARINT_MAX,
        y <= VARINT_MAX,
        z <= VARINT_MAX,
    ensures
        final(out)@ == old(out)@ + (spec_varint(x) + (spec_varint(y) + spec_varint(z))),
{
    put_varint(x, out);
    put_varints2(y, z, out);
    assert(out@ =~= old(out)@ + (spec_varint(x) + (spec_varint(y) + spec_varint(z))));
}

/// The varint `v` when `present`, then a length varint and the bytes: the tail of CRYPTO,
/// STREAM and CONNECTION_CLOSE.
fn put_opt_len_bytes(present: bool, v: u64, data: &[u8], out: &mut Vec<u8>)
    requires
        present ==> v <= VARINT_MAX,
        data.len() <= VARINT_MAX,
    ensures
        final(out)@ == old(out)@ + ((if present {
            spec_varint(v)
        } else {
            Seq::empty()
        }) + (spec_varint(data.len() as u64) + data@)),
{
    let ghost start = old(out)@;
    if present {
        put_varint(v, out);
    }
    put_varint(data.len() as u64, out);
    put_bytes(data, out);
    assert(out@ =~= start + ((if present {
        spec_varint(v)
    } else {
        Seq::empty()
    }) + (spec_varint(data.len() as u64) + data@)));
}

fn put_stream_body(stream_id: u64, offset: u64, data: &[u8], out: &mut Vec<u8>)
    requires
        stream_id <= VARINT_MAX,
        offset + data.len() <= VARINT_MAX,
    ensures
        final(out)@ == old(out)@ + (spec_varint(stream_id) + ((if offset > 0 {
            spec_varint(offset)
        } else {
            Seq::empty()
        }) + (spec_varint(data.len() as u64) + data@))),
{
    let ghost start = old(out)@;
    put_varint(stream_id, out);
    put_opt_len_bytes(offset > 0, offset, data, out);
    assert(out@ =~= start + (spec_varint(stream_id) + ((if offset > 0 {
        spec_varint(offset)
    } else {
        Seq::empty()
    }) + (spec_varint(data.len() as u64) + data@))));
}

fn put_close_body(app: bool, error_code: u64, frame_type: u64, reason: &[u8], out: &mut Vec<u8>)
    requires
        error_code <= VARINT_MAX,
        frame_type <= VARINT_MAX,
        reason.len() <= VARINT_MAX,
    ensures
        final(out)@ == old(out)@ + (spec_varint(error_code) + ((if app {
            Seq::empty()
        } else {
            spec_varint(frame_type)
        }) + (spec_varint(reason.len() as u64) + reason@))),
{
    let ghost start = old(out)@;
    put_varint(error_code, out);
    put_opt_len_bytes(!app, frame_type, reason, out);
    assert(out@ =~= start + (spec_varint(error_code) + ((if app {
        Seq::empty()
    } else {
        spec_varint(frame_type)
    }) + (spec_varint(reason.len() as u64) + reason@))));
}

fn put_ncid_body(seq: u64, retire_prior_to: u64, cid: &[u8], token: &[u8], out: &mut Vec<u8>)
    requires
        seq <= VARINT_MAX,
        retire_prior_to <= VARINT_MAX,
    ensures
        final(out)@ == old(out)@ + (spec_varint(seq) + (spec_varint(retire_prior_to) + (seq![
            cid.len() as u8,
        ] + (cid@ + token@)))),
{
    let ghost start = old(out)@;
    put_varints2(seq, retire_prior_to, out);
    out.push(cid.len() as u8);
    put_bytes(cid, out);
    put_bytes(token, out);
    assert(out@ =~= start + (spec_varint(seq) + (spec_varint(retire_prior_to) + (seq![
        cid.len() as u8,
    ] + (cid@ + token@)))));
}

/// Writes everything after the type.
fn serialize_body(f: &Frame, out: &mut Vec<u8>)
    requires
        frame_wf(f@),
        !(f is Ack),
    ensures
        final(out)@ == old(out)@ + spec_frame_body(f@),
{
    proof {
        lemma_streams_limit();
    }
    match f {
        Frame::ResetStream { stream_id, error_code, final_size } => put_varints3(
            *stream_id,
            *error_code,
            *final_size,
            out,
        ),
        Frame::StopSending { stream_id, error_code } => put_varints2(*stream_id, *error_code, out),
        Frame::Crypto { offset, data } => put_opt_len_bytes(true, *offset, data.as_slice(), out),
        Frame::Stream { stream_id, offset, data, .. } => put_stream_body(
            *stream_id,
            *offset,
            data.as_slice(),
            out,
        ),
        Frame::MaxData(v) => put_varint(*v, out),
        Frame::MaxStreamData { stream_id, max } => put_varints2(*stream_id, *max, out),
        Frame::MaxStreams { max, .. } => put_varint(*max, out),
        Frame::DataBlocked(v) => put_varint(*v, out),
        Frame::StreamDataBlocked { stream_id, max } => put_varints2(*stream_id, *max, out),
        Frame::StreamsBlocked { max, .. } => put_varint(*max, out),
        Frame::NewConnectionId { seq, retire_prior_to, cid, reset_token } => put_ncid_body(
            *seq,
            *retire_prior_to,
            cid.as_slice(),
            reset_token.as_slice(),
            out,
        ),
        Frame::RetireConnectionId(v) => put_varint(*v, out),
        Frame::PathChallenge(d) => put_bytes(d.as_slice(), out),
        Frame::PathResponse(d) => put_bytes(d.as_slice(), out),
        Frame::ConnectionClose { app, error_code, frame_type, reason } => put_close_body(
            *app,
            *error_code,
            *frame_type,
            reason.as_slice(),
            out,
        ),
        _ => {
            assert(old(out)@ + Seq::<u8>::empty() =~= old(out)@);
        },
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-12.4
//# For frame types defined in this document, this
//# means a single-byte encoding, even though it is possible to encode
//# these values as a two-, four-, or eight-byte variable-length integer.
/// Writes the whole frame: its type, minimally encoded, then its body.
pub fn serialize_frame(f: &Frame, out: &mut Vec<u8>)
    requires
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + spec_frame_bytes(f@),
{
    if let Frame::Ack(a) = f {
        serialize_ack(a, out);
        return;
    }
    let ghost start = old(out)@;
    put_varint(frame_type_of(f), out);
    serialize_body(f, out);
    proof {
        assert(out@ =~= start + spec_frame_bytes(f@));
    }
}

} // verus!
