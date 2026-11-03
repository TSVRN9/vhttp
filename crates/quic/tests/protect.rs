//! Phase 3e Task 3: packet and datagram protection against RFC 9001 Appendix A.2 and A.3.
mod common;
use common::*;
use quic::ack::AckFrame;
use quic::aead::*;
use quic::datagram::*;
use quic::frame::Frame;
use quic::payload::PacketKind;
use quic::protect::*;

fn out(kind: PacketKind, dcid: &[u8], scid: &[u8], pn: u64, pn_len: u8, frames: Vec<Frame>, padding: usize) -> OutPacket {
    OutPacket { kind, dcid: dcid.to_vec(), scid: scid.to_vec(), pn, pn_len, frames, padding, spin: false }
}

fn a2_packet() -> OutPacket {
    out(PacketKind::Initial, &S1, &[], 2, 4, vec![Frame::Crypto { offset: 0, data: A2_CRYPTO.to_vec() }], 917)
}

fn a3_packet() -> OutPacket {
    let ack = AckFrame { largest: 0, delay: 0, first_range: 0, ranges: vec![], ecn: None };
    out(
        PacketKind::Initial,
        &[],
        &hex("f067a5502a4262b5"),
        1,
        2,
        vec![Frame::Ack(ack), Frame::Crypto { offset: 0, data: A3_PAYLOAD[9..].to_vec() }],
        0,
    )
}

fn hs_packet(frames: Vec<Frame>) -> OutPacket {
    out(PacketKind::Handshake, &[], &[0x5a; 8], 0, 1, frames, 0)
}

fn short_packet(spin: bool) -> OutPacket {
    OutPacket { spin, ..out(PacketKind::OneRtt, &[0x11; 8], &[], 0, 1, vec![Frame::Ping], 2) }
}

fn protected(p: &OutPacket, k: &PacketKeys) -> Vec<u8> {
    let mut v = Vec::new();
    protect(p, k, &mut v);
    v
}

/// Server view: Initial (rx CLIENT, tx SERVER) and, as a stand-in, Handshake (tx CLIENT).
fn keys(handshake: bool) -> [Option<KeyPair>; 3] {
    let hs = if handshake { Some(KeyPair { rx: SERVER, tx: CLIENT }) } else { None };
    [Some(KeyPair { rx: CLIENT, tx: SERVER }), hs, None]
}

#[test]
fn a2_protect() {
    let p = a2_packet();
    assert_eq!(protected(&p, &CLIENT), A2);
    assert_eq!(packet_len(&p), 1200);
}

#[test]
fn a3_protect() {
    assert_eq!(protected(&a3_packet(), &SERVER), A3);
}

#[test]
fn protect_appends() {
    let mut v = vec![0xee; 5];
    protect(&a3_packet(), &SERVER, &mut v);
    assert_eq!(v[..5], [0xee; 5]);
    assert_eq!(v[5..], A3);
}

#[test]
fn short_len() {
    let v = protected(&short_packet(false), &CLIENT);
    assert_eq!(v.len(), 29);
    assert_eq!(v[0] & 0xe0, 0x40);
}

#[test]
fn spin_written() {
    let v = protected(&short_packet(true), &CLIENT);
    assert_eq!(v.len(), 29);
    assert_eq!(v[0] & 0xe0, 0x60);
}

#[test]
fn datagram_all_keyed() {
    let hs = hs_packet(vec![Frame::Crypto { offset: 0, data: vec![7; 30] }]);
    let mut want = A3.to_vec();
    want.extend(protected(&hs, &CLIENT));
    let d = OutDatagram { path: 0, packets: vec![a3_packet(), hs] };
    let mut v = Vec::new();
    protect_datagram(&d, &keys(true), &mut v);
    assert_eq!(v, want);
    assert_eq!(v.len(), datagram_len(&d));
}

// The brief's version keeps A.3's Initial, which carries CRYPTO and so is ack-eliciting: with
// Handshake unkeyed, Decision 4 writes nothing (as `datagram_eliciting_initial_unkeyed_peer`
// pins). The skip is shown with an ACK-only Initial; A.3's datagram is checked to write nothing.
#[test]
fn datagram_skip_unkeyed() {
    let ack = AckFrame { largest: 0, delay: 0, first_range: 0, ranges: vec![], ecn: None };
    let ini = out(PacketKind::Initial, &[], &hex("f067a5502a4262b5"), 1, 2, vec![Frame::Ack(ack)], 0);
    let hs = || hs_packet(vec![Frame::Crypto { offset: 0, data: vec![7; 30] }]);
    let want = protected(&ini, &SERVER);
    let d = OutDatagram { path: 0, packets: vec![ini, hs()] };
    let mut v = Vec::new();
    protect_datagram(&d, &keys(false), &mut v);
    assert_eq!(v, want);
    assert!(v.len() < datagram_len(&d));
    let d = OutDatagram { path: 0, packets: vec![a3_packet(), hs()] };
    let mut v = Vec::new();
    protect_datagram(&d, &keys(false), &mut v);
    assert!(v.is_empty());
}

#[test]
fn datagram_eliciting_initial_unkeyed_peer() {
    let d = OutDatagram { path: 0, packets: vec![a3_packet(), hs_packet(vec![Frame::Ping])] };
    let mut v = vec![0xee];
    protect_datagram(&d, &keys(false), &mut v);
    assert_eq!(v, [0xee]);
}
