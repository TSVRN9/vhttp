//! Phase 3e Task 5: the receive and send pipelines over `Connection` (RFC 9000 §14, §17.2,
//! §17.3.1; RFC 9001 §5.7).
mod common;
use common::*;
use quic::ack::AckFrame;
use quic::aead::*;
use quic::conn::Connection;
use quic::datagram::*;
use quic::frame::Frame;
use quic::lifecycle::Phase;
use quic::payload::PacketKind;
use quic::pipeline::*;
use quic::protect::*;
use quic::route::CidUpdate;

/// Server view: Initial keys only.
const K: [Option<KeyPair>; 3] = [Some(KeyPair { rx: CLIENT, tx: SERVER }), None, None];
/// Client view: Initial keys only.
const KC: [Option<KeyPair>; 3] = [Some(KeyPair { rx: SERVER, tx: CLIENT }), None, None];
/// Arbitrary 1-RTT keys, the same both ways.
const T: PacketKeys = PacketKeys { key: [7; 16], iv: [8; 12], hp: [9; 16] };
/// Server view with Initial and 1-RTT keys.
const K1: [Option<KeyPair>; 3] = [K[0], None, Some(KeyPair { rx: T, tx: T })];
const NL: [Option<u64>; 3] = [None; 3];

fn crypto() -> Vec<Frame> {
    vec![Frame::Crypto { offset: 0, data: A2_CRYPTO.to_vec() }]
}

fn protected(p: &OutPacket, k: &PacketKeys) -> Vec<u8> {
    let mut v = Vec::new();
    protect(p, k, &mut v);
    v
}

/// A client Initial to S1 with pn length 4.
fn ini(scid: &[u8], pn: u64, frames: Vec<Frame>, padding: usize) -> Vec<u8> {
    let p = OutPacket {
        kind: PacketKind::Initial,
        dcid: S1.to_vec(),
        scid: scid.to_vec(),
        pn,
        pn_len: 4,
        frames,
        padding,
        spin: false,
    };
    protected(&p, &CLIENT)
}

/// SCID C1, which `ptp()`'s `initial_source_connection_id` names: 1200 bytes with A.2's CRYPTO
/// frame and padding 909.
fn ini_c1(pn: u64, frames: Vec<Frame>, padding: usize) -> Vec<u8> {
    ini(&C1, pn, frames, padding)
}

/// A.2 with its reserved bit 0x08 set before protection: AEAD succeeds over a bad header.
fn reserved_set() -> Vec<u8> {
    let mut pt = hex("060040f1");
    pt.extend(A2_CRYPTO);
    pt.extend([0u8; 917]);
    build(&hex("cb00000001088394c8f03e5157080000449e00000002"), 18, 2, &pt, &CLIENT)
}

/// A 42-byte client Initial, pn 4 (4 bytes), reserved bit 0x08 set, `[Ping]` and 3 PADDING:
/// Length 4 + 4 + 16 = 24.
fn reserved_pn4() -> Vec<u8> {
    let b = build(&hex("cb00000001088394c8f03e5157080000401800000004"), 18, 4, &[0x01, 0, 0, 0], &CLIENT);
    assert_eq!(b.len(), 42);
    b
}

fn accepted_a2() -> Connection {
    accept_datagram(&A2, 0, 0, &rnd(1), &ltp(), &K).expect("accepted")
}

/// Decrypts the server's datagram with the client's keys.
fn client_open(out: &[u8]) -> Vec<Frame> {
    match unprotect(out, &KC, &NL) {
        Ok((Some(p), n)) => {
            assert_eq!(n, out.len());
            p.frames
        },
        r => panic!("not decrypted: {:?}", r),
    }
}

fn ack(largest: u64) -> Frame {
    Frame::Ack(AckFrame { largest, delay: 0, first_range: 0, ranges: vec![], ecn: None })
}

#[test]
fn initial_dcid_reads_initials() {
    assert_eq!(initial_dcid(&A2), Some(S1.to_vec()));
    let mut hs = A2;
    hs[0] = 0xe3;
    assert_eq!(initial_dcid(&hs), None);
    assert_eq!(initial_dcid(&[0x43; 30]), None);
}

#[test]
fn accept_transmit_a2() {
    let mut c = accepted_a2();
    let mut out = vec![0xff; 5];
    assert_eq!(transmit(&mut c, 0, &K, &mut out), Some(0));
    // 3d2's 47-byte ACK-only Initial without its 8-byte DCID: A.2's SCID is empty.
    assert_eq!(out.len(), 39);
    let want = PlainPacket {
        kind: PacketKind::Initial,
        dcid: vec![],
        scid: rnd(1)[0..8].to_vec(),
        token: vec![],
        pn: 0,
        frames: vec![ack(2)],
    };
    assert_eq!(unprotect(&out, &KC, &NL), Ok((Some(want), 39)));
    assert_eq!(transmit(&mut c, 0, &K, &mut out), None);
    assert!(out.is_empty());
}

#[test]
fn accept_rejects() {
    let short = ini(&[], 2, crypto(), 916);
    assert_eq!(short.len(), 1199);
    assert!(accept_datagram(&short, 0, 0, &rnd(1), &ltp(), &K).is_none());
    assert!(accept_datagram(&A2, 0, 0, &rnd(1), &ltp(), &[None; 3]).is_none());
    let mut bad = A2;
    bad[1199] ^= 1;
    assert!(accept_datagram(&bad, 0, 0, &rnd(1), &ltp(), &K).is_none());
}

#[test]
fn accept_1350() {
    let d = ini(&[], 2, crypto(), 1067);
    assert_eq!(d.len(), 1350);
    let mut c = accept_datagram(&d, 0, 0, &rnd(1), &ltp(), &K).expect("accepted");
    let mut out = Vec::new();
    assert_eq!(transmit(&mut c, 0, &K, &mut out), Some(0));
    assert_eq!(client_open(&out), vec![ack(2)]);
}

#[test]
fn first_packet_error_closes() {
    let d = reserved_set();
    assert_eq!(d.len(), 1200);
    let mut c = accept_datagram(&d, 0, 0, &rnd(1), &ltp(), &K).expect("accepted");
    assert_eq!(c.phase(), Phase::Closing);
    let mut out = Vec::new();
    assert_eq!(transmit(&mut c, 0, &K, &mut out), Some(0));
    // The Handshake CONNECTION_CLOSE has no keys and is skipped.
    let cc = Frame::ConnectionClose { app: false, error_code: 0x0a, frame_type: 0, reason: vec![] };
    assert_eq!(client_open(&out), vec![cc]);
    assert!(out.len() <= 3 * 1200);
    assert_eq!(c.phase(), Phase::Closing);
}

#[test]
fn receive_then_error() {
    let mut c = accepted_a2();
    let mut out = Vec::new();
    assert_eq!(transmit(&mut c, 0, &K, &mut out), Some(0));
    let bad = reserved_pn4();
    let i3 = ini(&[], 3, vec![Frame::Ping], 1200 - 42 - 39);
    assert_eq!(i3.len() + bad.len(), 1200);
    receive(&mut c, &[i3, bad].concat(), 0, 5, &rnd(2), &K);
    assert_eq!(c.largest_pn(PacketKind::Initial), Some(3));
    assert_eq!(c.phase(), Phase::Closing);
    assert_eq!(c.close_info(), &Some((false, 0x0a, vec![])));
    assert_eq!(transmit(&mut c, 5, &K, &mut out), Some(0));
    let cc = Frame::ConnectionClose { app: false, error_code: 0x0a, frame_type: 0, reason: vec![] };
    assert!(client_open(&out).contains(&cc));
}

#[test]
fn receive_counts_undecryptable() {
    let mut c = accepted_a2();
    let mut out = Vec::new();
    while transmit(&mut c, 0, &K, &mut out).is_some() {}
    let b0 = c.path_budget(0).unwrap();
    // A.2's header with pn length 1 and Length 1182 over zeros: AEAD fails.
    let mut d = vec![0xc0, 0, 0, 0, 1, 8];
    d.extend(S1);
    d.extend([0, 0, 0x44, 0x9e]);
    d.resize(1200, 0);
    assert_eq!(unprotect(&d, &K, &NL), Ok((None, 1200)));
    receive(&mut c, &d, 0, 5, &rnd(2), &K);
    assert_eq!(c.largest_pn(PacketKind::Initial), Some(2));
    assert_eq!(c.phase(), Phase::Open);
    // §8.1: counted although nothing decrypted.
    assert_eq!(c.path_budget(0), Some(b0 + 3600));
}

#[test]
fn one_rtt_gated_until_complete() {
    let d = ini_c1(2, crypto(), 909);
    assert_eq!(d.len(), 1200);
    let mut c = accept_datagram(&d, 0, 0, &rnd(1), &ltp(), &K1).expect("accepted");
    // Short header, reserved bit 0x08 set, pn length 1, DCID L0: valid AEAD under T.
    let mut h = vec![0x48];
    h.extend(L0);
    h.push(0);
    let bad = build(&h, 9, 0, &[0x01, 0, 0, 0], &T);
    receive(&mut c, &bad, 0, 10, &rnd(2), &K1);
    assert_eq!(c.phase(), Phase::Open);
    // Nor in the datagram that creates the connection.
    let c2 = accept_datagram(&[d.clone(), bad.clone()].concat(), 0, 0, &rnd(1), &ltp(), &K1).expect("accepted");
    assert_eq!(c2.phase(), Phase::Open);
    c.on_peer_params(&ptp(), 10);
    c.on_handshake_complete(b"h3", 10, &rnd(3));
    assert!(c.handshake_complete());
    receive(&mut c, &bad, 0, 10, &rnd(2), &K1);
    assert_eq!(c.phase(), Phase::Closing);
    assert_eq!(c.close_info(), &Some((false, 0x0a, vec![])));
}

#[test]
fn timeout_settles() {
    let mut c = accepted_a2();
    let mut out = Vec::new();
    while transmit(&mut c, 0, &K, &mut out).is_some() {}
    let t = c.next_timeout().unwrap();
    c.on_timeout(t, &rnd(4));
    let mut v: Vec<CidUpdate> = Vec::new();
    c.poll_cid_updates(&mut v);
    let mut n = 0;
    while transmit(&mut c, t, &K, &mut out).is_some() {
        n += 1;
        assert!(n < 1024);
    }
    assert!(c.next_timeout().map_or(true, |u| u > t));
}
