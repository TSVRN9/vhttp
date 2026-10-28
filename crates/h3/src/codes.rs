//! HTTP/3 and QPACK constants: error codes (RFC 9114 §8.1, RFC 9204 §6), frame types
//! (§7.2, §11.2.1), setting identifiers (§7.2.4.1, RFC 9204 §5) and stream types (§6.2).
use vstd::prelude::*;

verus! {

pub const H3_NO_ERROR: u64 = 0x100;
pub const H3_GENERAL_PROTOCOL_ERROR: u64 = 0x101;
pub const H3_INTERNAL_ERROR: u64 = 0x102;
pub const H3_STREAM_CREATION_ERROR: u64 = 0x103;
pub const H3_CLOSED_CRITICAL_STREAM: u64 = 0x104;
pub const H3_FRAME_UNEXPECTED: u64 = 0x105;
pub const H3_FRAME_ERROR: u64 = 0x106;
pub const H3_EXCESSIVE_LOAD: u64 = 0x107;
pub const H3_ID_ERROR: u64 = 0x108;
pub const H3_SETTINGS_ERROR: u64 = 0x109;
pub const H3_MISSING_SETTINGS: u64 = 0x10a;
pub const H3_REQUEST_REJECTED: u64 = 0x10b;
pub const H3_REQUEST_CANCELLED: u64 = 0x10c;
pub const H3_REQUEST_INCOMPLETE: u64 = 0x10d;
pub const H3_MESSAGE_ERROR: u64 = 0x10e;
pub const H3_CONNECT_ERROR: u64 = 0x10f;
pub const H3_VERSION_FALLBACK: u64 = 0x110;
pub const QPACK_DECOMPRESSION_FAILED: u64 = 0x200;
pub const QPACK_ENCODER_STREAM_ERROR: u64 = 0x201;
pub const QPACK_DECODER_STREAM_ERROR: u64 = 0x202;

pub const FRAME_DATA: u64 = 0x00;
pub const FRAME_HEADERS: u64 = 0x01;
pub const FRAME_CANCEL_PUSH: u64 = 0x03;
pub const FRAME_SETTINGS: u64 = 0x04;
pub const FRAME_PUSH_PROMISE: u64 = 0x05;
pub const FRAME_GOAWAY: u64 = 0x07;
pub const FRAME_MAX_PUSH_ID: u64 = 0x0d;

pub const SETTINGS_QPACK_MAX_TABLE_CAPACITY: u64 = 0x01;
pub const SETTINGS_MAX_FIELD_SECTION_SIZE: u64 = 0x06;
pub const SETTINGS_QPACK_BLOCKED_STREAMS: u64 = 0x07;

pub const STREAM_CONTROL: u64 = 0x00;
pub const STREAM_PUSH: u64 = 0x01;
pub const STREAM_QPACK_ENCODER: u64 = 0x02;
pub const STREAM_QPACK_DECODER: u64 = 0x03;

//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.8
//# Frame types of the format 0x1f * N + 0x21 for non-negative integer
//# values of N are reserved to exercise the requirement that unknown
//# types be ignored (Section 9).
pub open spec fn is_grease_spec(v: u64) -> bool {
    v >= 0x21 && (v - 0x21) % 0x1f == 0
}

#[verifier::when_used_as_spec(is_grease_spec)]
pub fn is_grease(v: u64) -> (r: bool)
    ensures
        r == is_grease_spec(v),
{
    v >= 0x21 && (v - 0x21) % 0x1f == 0
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.8
//# Frame types that were used in HTTP/2 where there is no corresponding
//# HTTP/3 frame have also been reserved (Section 11.2.1).
pub open spec fn is_h2_reserved_frame_spec(t: u64) -> bool {
    t == 0x02 || t == 0x06 || t == 0x08 || t == 0x09
}

#[verifier::when_used_as_spec(is_h2_reserved_frame_spec)]
pub fn is_h2_reserved_frame(t: u64) -> (r: bool)
    ensures
        r == is_h2_reserved_frame_spec(t),
{
    t == 0x02 || t == 0x06 || t == 0x08 || t == 0x09
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.4.1
//# Setting identifiers that were defined in [HTTP/2] where there is no
//# corresponding HTTP/3 setting have also been reserved
//# (Section 11.2.2).
pub open spec fn is_h2_reserved_setting_spec(id: u64) -> bool {
    id == 0x02 || id == 0x03 || id == 0x04 || id == 0x05
}

#[verifier::when_used_as_spec(is_h2_reserved_setting_spec)]
pub fn is_h2_reserved_setting(id: u64) -> (r: bool)
    ensures
        r == is_h2_reserved_setting_spec(id),
{
    id == 0x02 || id == 0x03 || id == 0x04 || id == 0x05
}

} // verus!
