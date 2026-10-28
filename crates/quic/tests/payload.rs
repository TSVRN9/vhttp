use quic::ack::AckFrame;
use quic::codes::{FRAME_ENCODING_ERROR, PROTOCOL_VIOLATION};
use quic::frame::Frame;
use quic::payload::*;

const FEE: u64 = FRAME_ENCODING_ERROR;
const PV: u64 = PROTOCOL_VIOLATION;

fn hex(s: &str) -> Vec<u8> {
    let s: String = s.split_whitespace().collect();
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

/// RFC 9001 §A.3: the server Initial payload (ACK + CRYPTO, no PADDING).
const A3: &str = "02000000000600405a020000560303ee fce7f7b37ba1d1632e96677825ddf739
   88cfc79825df566dc5430b9a045a1200 130100002e00330024001d00209d3c94
   0d89690b84d08a60993c144eca684d10 81287c834d5311bcf32bb9da1a002b00
   020304";

/// RFC 9001 §A.2: the client Initial's CRYPTO frame (before its PADDING).
const A2: &str = "060040f1010000ed0303ebf8fa56f129 39b9584a3896472ec40bb863cfd3e868
   04fe3a47f06a2b69484c000004130113 02010000c000000010000e00000b6578
   616d706c652e636f6dff01000100000a 00080006001d00170018001000070005
   04616c706e0005000501000000000033 00260024001d00209370b2c9caa47fba
   baf4559fedba753de171fa71f50f1ce1 5d43e994ec74d748002b000302030400
   0d0010000e0403050306030203080408 050806002d00020101001c0002400100
   3900320408ffffffffffffffff050480 00ffff07048000ffff08011001048000
   75300901100f088394c8f03e51570806 048000ffff";

#[test]
fn rfc9001_a3_payload() {
    let b = hex(A3);
    assert_eq!(b.len(), 99);
    let ack = AckFrame { largest: 0, delay: 0, first_range: 0, ranges: vec![], ecn: None };
    let want = vec![Frame::Ack(ack), Frame::Crypto { offset: 0, data: b[9..].to_vec() }];
    assert_eq!(want.len(), 2);
    assert_eq!(b[9..].len(), 90);
    assert_eq!(parse_payload(&b, PacketKind::Initial), Ok(want));
    let frames = match parse_payload(&b, PacketKind::Initial) {
        Ok(f) => f,
        Err(e) => panic!("{e}"),
    };
    let mut out = Vec::new();
    serialize_payload(&frames, PacketKind::Initial, &mut out);
    assert_eq!(out, b);
}

#[test]
fn rfc9001_a2_payload() {
    let crypto = hex(A2);
    assert_eq!(crypto.len(), 245);
    let b = [&crypto[..], &[0u8; 917][..]].concat();
    assert_eq!(b.len(), 1162);
    let want = vec![Frame::Crypto { offset: 0, data: crypto[4..].to_vec() }];
    assert_eq!(crypto[4..].len(), 241);
    assert_eq!(crypto[4..8], [0x01, 0x00, 0x00, 0xed]);
    assert_eq!(parse_payload(&b, PacketKind::Initial), Ok(want));
}

#[test]
fn permissions() {
    assert_eq!(parse_payload(&[0x1d, 0x00, 0x00], PacketKind::Initial), Err(PV));
    let close = Frame::ConnectionClose { app: false, error_code: 0, frame_type: 0, reason: vec![] };
    assert_eq!(parse_payload(&[0x1c, 0x00, 0x00, 0x00], PacketKind::Initial), Ok(vec![close]));
    assert_eq!(parse_payload(&[0x10, 0x00], PacketKind::Handshake), Err(PV));
    let b = [0x1a, 1, 2, 3, 4, 5, 6, 7, 8, 0x10, 0x05, 0x08, 0x00, 0x61];
    let want = vec![
        Frame::PathChallenge([1, 2, 3, 4, 5, 6, 7, 8]),
        Frame::MaxData(5),
        Frame::Stream { stream_id: 0, offset: 0, data: b"a".to_vec(), fin: false },
    ];
    assert_eq!(parse_payload(&b, PacketKind::OneRtt), Ok(want));
}

#[test]
fn permission_before_body() {
    assert_eq!(parse_payload(&[0x08], PacketKind::Initial), Err(PV));
    assert_eq!(parse_payload(&[0x08], PacketKind::OneRtt), Err(FEE));
}

#[test]
fn empty_and_padding() {
    assert_eq!(parse_payload(&[], PacketKind::Initial), Err(PV));
    assert_eq!(parse_payload(&[], PacketKind::OneRtt), Err(PV));
    assert_eq!(parse_payload(&[0x00, 0x00, 0x00], PacketKind::Initial), Ok(vec![]));
    let b = [&[0x01u8][..], &[0u8; 1000][..]].concat();
    assert_eq!(parse_payload(&b, PacketKind::Handshake), Ok(vec![Frame::Ping]));
    let b = [0x01, 0x00, 0x00, 0x00, 0x01];
    assert_eq!(parse_payload(&b, PacketKind::Initial), Ok(vec![Frame::Ping, Frame::Ping]));
    let b = [0x01, 0x00, 0x00, 0x10, 0x05, 0x00];
    assert_eq!(parse_payload(&b, PacketKind::OneRtt), Ok(vec![Frame::Ping, Frame::MaxData(5)]));
}

#[test]
fn server_receipt_any_space() {
    assert_eq!(parse_payload(&[0x07, 0x01, 0xaa], PacketKind::OneRtt), Err(PV));
    assert_eq!(parse_payload(&[0x1e], PacketKind::OneRtt), Err(PV));
}

#[test]
fn first_error_wins() {
    // An unknown type is FRAME_ENCODING_ERROR in every packet type, before permissions.
    assert_eq!(parse_payload(&[0x1f], PacketKind::Initial), Err(FEE));
    // Frames before the first bad one parse; the first bad one decides the error.
    assert_eq!(parse_payload(&[0x01, 0x19, 0x10, 0x00], PacketKind::Initial), Err(PV));
    assert_eq!(parse_payload(&[0x01, 0x40, 0x01, 0x1f], PacketKind::OneRtt), Err(PV));
    assert_eq!(parse_payload(&[0x01, 0x10], PacketKind::OneRtt), Err(FEE));
}

#[test]
fn ack_eliciting() {
    let ack =
        || Frame::Ack(AckFrame { largest: 0, delay: 0, first_range: 0, ranges: vec![], ecn: None });
    let close = Frame::ConnectionClose { app: false, error_code: 0, frame_type: 0, reason: vec![] };
    assert!(!is_ack_eliciting(&[ack()]));
    assert!(is_ack_eliciting(&[ack(), Frame::Ping]));
    assert!(!is_ack_eliciting(&[close]));
    assert!(is_ack_eliciting(&[Frame::Crypto { offset: 0, data: vec![1] }]));
    assert!(!is_ack_eliciting(&[]));
}

#[test]
fn permitted_table() {
    for ty in 0..=0x1fu64 {
        let ih = matches!(ty, 0x00 | 0x01 | 0x02 | 0x03 | 0x06 | 0x1c);
        assert_eq!(is_frame_permitted(ty, PacketKind::Initial), ih, "{ty:#x}");
        assert_eq!(is_frame_permitted(ty, PacketKind::Handshake), ih, "{ty:#x}");
        assert_eq!(is_frame_permitted(ty, PacketKind::OneRtt), ty <= 0x1e, "{ty:#x}");
    }
}
