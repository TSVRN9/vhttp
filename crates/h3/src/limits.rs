//! Limits we choose (not set by the RFCs).
use vstd::prelude::*;

verus! {

// Bounds the SETTINGS frame and the peer control stream's buffer (`h3::uni::UNI_BUF_CAP`).
/// A larger SETTINGS frame is a connection error H3_EXCESSIVE_LOAD, decided from its header.
pub const MAX_SETTINGS_FRAME: u64 = 1024;

//= https://www.rfc-editor.org/rfc/rfc9114#section-6.2
//# Therefore, the transport parameters sent by both clients
//# and servers MUST allow the peer to create at least three
//# unidirectional streams.
/// Phase 3's transport parameters must allow the peer at least this many unidirectional streams
/// (`initial_max_streams_uni`): a control stream plus the QPACK encoder and decoder streams.
pub const MIN_PEER_UNI_STREAMS: u64 = 3;

/// Advertised as SETTINGS_MAX_FIELD_SECTION_SIZE. A larger HEADERS payload is a stream error
/// H3_EXCESSIVE_LOAD, decided from its frame header. It is also the decoded budget,
/// Σ(name + value + 32), enforced by `decode_field_section_bounded` (and the request stream's
/// buffer bound, `h3::request::REQ_BUF_CAP`).
pub const MAX_FIELD_SECTION_SIZE: u64 = 65536;

} // verus!
