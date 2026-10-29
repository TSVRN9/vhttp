//! Phase 3d datagram lengths (RFC 9000 §12.2, §14, §17.2; RFC 9001 §5.4.2, Appendix A).
use quic::ack::AckFrame;
use quic::datagram::*;
use quic::frame::Frame;
use quic::payload::PacketKind;

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

fn pkt(kind: PacketKind, dcid: &[u8], scid: &[u8], pn: u64, pn_len: u8, frames: Vec<Frame>) -> OutPacket {
    OutPacket {
        kind,
        dcid: dcid.to_vec(),
        scid: scid.to_vec(),
        pn,
        pn_len,
        frames,
        padding: 0,
        spin: false,
    }
}

fn initial43() -> OutPacket {
    pkt(PacketKind::Initial, &[0xc1; 8], &[0x5a; 8], 0, 1, vec![Frame::Ping])
}

fn short29() -> OutPacket {
    let mut p = pkt(PacketKind::OneRtt, &[0x11; 8], &[], 0, 1, vec![Frame::Ping]);
    add_sample_padding(&mut p);
    p
}

#[test]
fn a3_server_initial_len() {
    let crypto90 = hex(A3)[9..].to_vec();
    assert_eq!(crypto90.len(), 90);
    let ack = AckFrame { largest: 0, delay: 0, first_range: 0, ranges: vec![], ecn: None };
    let p = pkt(
        PacketKind::Initial,
        &[],
        &hex("f067a5502a4262b5"),
        1,
        2,
        vec![Frame::Ack(ack), Frame::Crypto { offset: 0, data: crypto90 }],
    );
    assert_eq!(hex("c1000000010008f067a5502a4262b50040750001").len(), 20);
    assert_eq!(packet_len(&p), 20 + 99 + 16);
}

#[test]
fn a2_client_initial_len() {
    let data = hex(A2)[4..].to_vec();
    assert_eq!(data.len(), 241);
    let mut p = pkt(
        PacketKind::Initial,
        &hex("8394c8f03e515708"),
        &[],
        2,
        4,
        vec![Frame::Crypto { offset: 0, data }],
    );
    p.padding = 917;
    assert_eq!(packet_len(&p), 1200);
}

#[test]
fn short_sample_padding() {
    let p = short29();
    assert_eq!(p.padding, 2);
    assert_eq!(packet_len(&p), 29);
    // Already long enough: unchanged.
    let mut q = pkt(PacketKind::OneRtt, &[0x11; 8], &[], 0, 4, vec![Frame::Ping]);
    add_sample_padding(&mut q);
    assert_eq!(q.padding, 0);
}

#[test]
fn pad_single_initial() {
    let p = initial43();
    assert_eq!(packet_len(&p), 43);
    let mut d = OutDatagram { path: 0, packets: vec![p] };
    pad_datagram(&mut d, 1200);
    assert_eq!(d.packets[0].padding, 1156);
    assert_eq!(datagram_len(&d), 1200);
}

#[test]
fn pad_coalesced() {
    let h = pkt(
        PacketKind::Handshake,
        &[0xc1; 8],
        &[0x5a; 8],
        0,
        1,
        vec![Frame::Crypto { offset: 0, data: vec![7; 30] }],
    );
    assert_eq!(packet_len(&h), 74);
    let mut d = OutDatagram { path: 3, packets: vec![initial43(), h] };
    assert_eq!(datagram_len(&d), 117);
    pad_datagram(&mut d, 1200);
    assert_eq!(d.packets[0].padding, 0);
    assert_eq!(d.packets[1].padding, 1082);
    assert_eq!(datagram_len(&d), 1200);
    assert_eq!(d.path, 3);
}

#[test]
fn pad_short() {
    let mut d = OutDatagram { path: 0, packets: vec![short29()] };
    pad_datagram(&mut d, 1200);
    assert_eq!(d.packets[0].padding, 1173);
    assert_eq!(datagram_len(&d), 1200);
}

#[test]
fn pad_already_full() {
    let mut d = OutDatagram { path: 0, packets: vec![short29()] };
    pad_datagram(&mut d, 1200);
    pad_datagram(&mut d, 1200);
    assert_eq!(d.packets[0].padding, 1173);
}
