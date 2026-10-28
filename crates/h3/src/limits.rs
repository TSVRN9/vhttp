//! Limits we choose (not set by the RFCs).
use vstd::prelude::*;

verus! {

// ponytail: bounds the O(n^2) duplicate scan in `parse_frame_payload` to 512 pairs, and the
// peer control stream's buffer (`h3::uni::UNI_BUF_CAP`); raise both if peers send larger SETTINGS.
/// A larger SETTINGS frame is a connection error H3_EXCESSIVE_LOAD, decided from its header.
pub const MAX_SETTINGS_FRAME: u64 = 1024;

//= https://www.rfc-editor.org/rfc/rfc9114#section-6.2
//# Therefore, the transport parameters sent by both clients
//# and servers MUST allow the peer to create at least three
//# unidirectional streams.
/// Phase 3's transport parameters must allow the peer at least this many unidirectional streams
/// (`initial_max_streams_uni`): a control stream plus the QPACK encoder and decoder streams.
pub const MIN_PEER_UNI_STREAMS: u64 = 3;

} // verus!
