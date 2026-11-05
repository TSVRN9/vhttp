//! Phase 3e Task 4: removing packet and datagram protection (RFC 9001 §5.3-§5.5), against
//! RFC 9001 Appendix A.2 and A.3 and packets built by `protect`.
mod common;
use common::*;
use quic::ack::AckFrame;
use quic::aead::*;
use quic::codes::PN_MAX;
use quic::datagram::*;
use quic::frame::Frame;
use quic::payload::PacketKind;
use quic::protect::*;

/// Server view: Initial keys only (rx CLIENT).
const KR: [Option<KeyPair>; 3] = [Some(KeyPair { rx: CLIENT, tx: SERVER }), None, None];
/// Client view: Initial keys only (rx SERVER).
const KC: [Option<KeyPair>; 3] = [Some(KeyPair { rx: SERVER, tx: CLIENT }), None, None];
/// Server view with 1-RTT keys only (rx CLIENT).
const K1: [Option<KeyPair>; 3] = [None, None, KR[0]];
const NL: [Option<u64>; 3] = [None; 3];

const A2_HEADER: &str = "c300000001088394c8f03e5157080000449e00000002";

fn plain(kind: PacketKind, dcid: &[u8], scid: &[u8], pn: u64, frames: Vec<Frame>) -> PlainPacket {
    PlainPacket { kind, dcid: dcid.to_vec(), scid: scid.to_vec(), token: vec![], pn, frames }
}

fn a2_plain() -> PlainPacket {
    plain(PacketKind::Initial, &S1, &[], 2, vec![Frame::Crypto { offset: 0, data: A2_CRYPTO.to_vec() }])
}

/// A.2's payload: its CRYPTO frame (`060040f1` and the data), then 917 bytes of PADDING.
fn a2_payload() -> Vec<u8> {
    let mut pt = hex("060040f1");
    pt.extend(A2_CRYPTO);
    pt.extend([0u8; 917]);
    pt
}

fn out(kind: PacketKind, dcid: &[u8], pn: u64, pn_len: u8, frames: Vec<Frame>, padding: usize) -> OutPacket {
    OutPacket { kind, dcid: dcid.to_vec(), scid: vec![], pn, pn_len, frames, padding, spin: false }
}

fn protected(p: &OutPacket, k: &PacketKeys) -> Vec<u8> {
    let mut v = Vec::new();
    protect(p, k, &mut v);
    v
}

/// An Initial to S1 carrying PING, protected with the client's keys.
fn initial(pn: u64) -> Vec<u8> {
    protected(&out(PacketKind::Initial, &S1, pn, 1, vec![Frame::Ping], 40), &CLIENT)
}

fn initial_plain(pn: u64) -> PlainPacket {
    plain(PacketKind::Initial, &S1, &[], pn, vec![Frame::Ping])
}

/// A.2 with its reserved bit 0x08 set before protection: AEAD succeeds over a bad header.
fn reserved_set() -> Vec<u8> {
    build(&hex("cb00000001088394c8f03e5157080000449e00000002"), 18, 2, &a2_payload(), &CLIENT)
}

fn cat(parts: &[&[u8]]) -> Vec<u8> {
    parts.concat()
}

#[test]
fn a2_unprotect() {
    assert_eq!(unprotect(&A2, &KR, &NL), Ok((Some(a2_plain()), 1200)));
}

#[test]
fn a3_unprotect_coalesced() {
    let ack = AckFrame { largest: 0, delay: 0, first_range: 0, ranges: vec![], ecn: None };
    let want = plain(
        PacketKind::Initial,
        &[],
        &hex("f067a5502a4262b5"),
        1,
        vec![Frame::Ack(ack), Frame::Crypto { offset: 0, data: A3_PAYLOAD[9..].to_vec() }],
    );
    let b = cat(&[&A3, &[0xaa; 30]]);
    assert_eq!(unprotect(&b, &KC, &NL), Ok((Some(want), 135)));
}

#[test]
fn drops() {
    let mut bad_tag = A2;
    bad_tag[1199] ^= 1;
    assert_eq!(unprotect(&bad_tag, &KR, &NL), Ok((None, 1200)));
    assert_eq!(unprotect(&A2, &[None; 3], &NL), Ok((None, 1200)));
    assert_eq!(unprotect(&A2, &KR, &[Some(PN_MAX), None, None]), Ok((None, 1200)));
    // 28 bytes: the short header parses (28 >= 21), but 28 < pn_offset 9 + 20.
    let short = cat(&[&[0x40], &[0x11; 8], &[0; 19]]);
    assert_eq!(unprotect(&short, &K1, &NL), Ok((None, 28)));
    assert_eq!(unprotect(&[0x00; 30], &KR, &NL), Ok((None, 30)));
}

#[test]
fn reserved_bits_violation() {
    let want = plain(PacketKind::Initial, &S1, &[], 2, vec![]);
    assert_eq!(unprotect(&reserved_set(), &KR, &NL), Err((0x0a, want)));
}

#[test]
fn reserved_flip_on_wire_drops() {
    let mut b = A2;
    b[0] ^= 0x08;
    assert_eq!(unprotect(&b, &KR, &NL), Ok((None, 1200)));
}

#[test]
fn payload_error() {
    let mut pt = vec![0x10, 0x00];
    pt.extend([0u8; 1160]);
    let r = unprotect(&build(&hex(A2_HEADER), 18, 2, &pt, &CLIENT), &KR, &NL);
    assert!(matches!(r, Err((0x0a, _))), "{r:?}");
}

#[test]
fn decode_with_largest() {
    let p = out(PacketKind::OneRtt, &[0x11; 8], 0x1_0000_0002, 1, vec![Frame::Ping], 2);
    let b = protected(&p, &CLIENT);
    let want = plain(PacketKind::OneRtt, &[0x11; 8], &[], 0x1_0000_0002, vec![Frame::Ping]);
    assert_eq!(unprotect(&b, &K1, &[None, None, Some(0x1_0000_0001)]), Ok((Some(want), b.len())));
}

#[test]
fn coalesced_skip_unkeyed() {
    let hs = OutPacket {
        scid: vec![0x5a; 8],
        ..out(PacketKind::Handshake, &[], 0, 1, vec![Frame::Crypto { offset: 0, data: vec![7; 30] }], 0)
    };
    let d = cat(&[&initial(3), &protected(&hs, &SERVER), &initial(4)]);
    let rx = open_datagram(&d, &KR, &NL);
    assert_eq!(rx.packets, vec![initial_plain(3), initial_plain(4)]);
    assert_eq!(rx.error, None);
    assert_eq!(rx.reset_tail, None);
}

#[test]
fn short_takes_rest() {
    let p = |pn| protected(&out(PacketKind::OneRtt, &[0x11; 8], pn, 1, vec![Frame::Ping], 2), &CLIENT);
    let d = cat(&[&p(0), &p(1)]);
    let rx = open_datagram(&d, &K1, &NL);
    assert_eq!(rx.packets, vec![]);
    assert_eq!(rx.error, None);
    assert_eq!(rx.reset_tail, Some(d[d.len() - 16..].try_into().unwrap()));
}

#[test]
fn zero_rtt_skipped() {
    let d = cat(&[&hex("d000000001088394c8f03e515708001e"), &[0; 30], &A2]);
    let rx = open_datagram(&d, &KR, &NL);
    assert_eq!(rx.packets, vec![a2_plain()]);
    assert_eq!(rx.error, None);
    // The first packet (0-RTT) is not decrypted, so the tail is a reset candidate.
    assert_eq!(rx.reset_tail, Some(A2[1184..].try_into().unwrap()));
}

#[test]
fn error_stops() {
    let d = cat(&[&initial(3), &reserved_set(), &initial(4)]);
    let rx = open_datagram(&d, &KR, &NL);
    assert_eq!(rx.packets, vec![initial_plain(3)]);
    assert!(matches!(rx.error, Some((0x0a, _))), "{:?}", rx.error);
    assert_eq!(rx.reset_tail, None);
}

#[test]
fn reset_tail() {
    let d = cat(&[&[0x40], &[0x11; 8], &[0x33; 15], &[0x77; 16]]);
    let rx = open_datagram(&d, &[None; 3], &NL);
    assert_eq!(rx.packets, vec![]);
    assert_eq!(rx.reset_tail, Some([0x77; 16]));
    assert_eq!(open_datagram(&A2, &KR, &NL).reset_tail, None);
}

#[test]
fn oversized() {
    let rx = open_datagram(&vec![0; 65536], &KR, &NL);
    assert_eq!(rx, Rx { packets: vec![], error: None, reset_tail: None });
}

// A 0-RTT packet (type 0x1) sealed with the Handshake key is still dropped, consuming exactly
// its `packet_end` (54 bytes: header 16 + pn 1, payload 21, tag 16), with Handshake keyed.
#[test]
fn zero_rtt_not_opened_with_handshake_keys() {
    let mut pt = vec![0x01];
    pt.extend([0u8; 20]);
    let b = cat(&[&build(&hex("d000000001088394c8f03e515708002600"), 16, 0, &pt, &CLIENT), &[0xaa; 10]]);
    let hs = [None, Some(KeyPair { rx: CLIENT, tx: SERVER }), None];
    assert_eq!(unprotect(&b, &hs, &NL), Ok((None, 54)));
}

// §5.4.2 on a long header: Length 16 puts `packet_end` (33) below pn_offset 17 + 20, so the
// first packet is dropped consuming only its 33 bytes, and the coalesced Initial after it opens.
#[test]
fn short_long_packet_skipped() {
    let first = cat(&[&hex("c000000001088394c8f03e515708000010"), &[0x55; 16]]);
    assert_eq!(unprotect(&first, &KR, &NL), Ok((None, 33)));
    let d = cat(&[&first, &initial(4)]);
    let rx = open_datagram(&d, &KR, &NL);
    assert_eq!(rx.packets, vec![initial_plain(4)]);
    assert_eq!(rx.error, None);
    assert_eq!(rx.reset_tail, Some(d[d.len() - 16..].try_into().unwrap()));
}

#[test]
fn tiny_datagrams() {
    let none = Rx { packets: vec![], error: None, reset_tail: None };
    assert_eq!(unprotect(&[], &KR, &NL), Ok((None, 0)));
    assert_eq!(open_datagram(&[], &KR, &NL), none);
    assert_eq!(unprotect(&[0xc0], &KR, &NL), Ok((None, 1)));
    assert_eq!(open_datagram(&[0xc0], &KR, &NL), none);
}
