//! HTTP/3 (RFC 9114) and QPACK (RFC 9204): error codes, the frame codec and the QPACK codecs.
//! Every `Err(code)` from the 2a codecs is a connection-level code; the HTTP/3 layer classifies it.
pub mod codes;
pub mod frame;
pub mod limits;
pub mod message;
pub mod qpack;
pub mod uni;
