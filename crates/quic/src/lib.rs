//! QUIC (RFC 9000) wire codecs: codepoints, packet numbers and packet headers (3b); frames
//! and transport parameters follow in later tasks.
pub mod codes;
pub mod header;
pub mod pn;
pub mod stateless;
