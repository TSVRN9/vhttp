//! Phase 3d2 Connection tests: the transmit path (Task 2a-i: frame collection, 1-RTT packets).
// The helpers are the plan's shared set, copied into every 3d2 test file; later tasks use the rest.
#![allow(dead_code, non_snake_case)]
use quic::ack::AckFrame;
use quic::conn::*;
use quic::datagram::*;
use quic::frame::Frame;
use quic::lifecycle::Phase;
use quic::payload::PacketKind;
use quic::route::CidUpdate;
use quic::tp::*;

fn rnd(n: u8) -> [u8; 129] {
    let mut r = [0u8; 129];
    for (j, b) in r.iter_mut().enumerate() {
        *b = n.wrapping_add(j as u8);
    }
    r
}

const S1: [u8; 8] = [0x83, 0x94, 0xc8, 0xf0, 0x3e, 0x51, 0x57, 0x08];
const C1: [u8; 8] = [0xc1; 8];
const L0: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

fn D(x: u8) -> [u8; 8] {
    [x; 8]
}

fn A(l: u64, d: u64, f: u64, r: Vec<(u64, u64)>) -> AckFrame {
    AckFrame { largest: l, delay: d, first_range: f, ranges: r, ecn: None }
}

fn CC(app: bool, c: u64, r: &[u8]) -> Frame {
    Frame::ConnectionClose { app, error_code: c, frame_type: 0, reason: r.to_vec() }
}

fn ltp() -> TransportParams {
    let mut t = default_transport_params();
    t.max_idle_timeout = 30000;
    t.initial_max_data = 1000;
    t.initial_max_stream_data_bidi_remote = 100;
    t.initial_max_stream_data_uni = 100;
    t.initial_max_streams_bidi = 10;
    t.initial_max_streams_uni = 3;
    t.active_connection_id_limit = 2;
    t.disable_active_migration = true;
    t
}

fn ptp() -> TransportParams {
    let mut t = default_transport_params();
    t.initial_source_connection_id = Some(C1.to_vec());
    t.initial_max_data = 1000;
    t.initial_max_stream_data_bidi_local = 100;
    t.initial_max_stream_data_uni = 100;
    t.initial_max_streams_uni = 3;
    t.active_connection_id_limit = 4;
    t
}

fn pkt(kind: PacketKind, dcid: &[u8], scid: &[u8], pn: u64, frames: Vec<Frame>) -> PlainPacket {
    PlainPacket { kind, dcid: dcid.to_vec(), scid: scid.to_vec(), token: vec![], pn, frames }
}

fn ini(pn: u64, f: Vec<Frame>) -> PlainPacket {
    pkt(PacketKind::Initial, &S1, &C1, pn, f)
}

fn ini2(pn: u64, f: Vec<Frame>) -> PlainPacket {
    pkt(PacketKind::Initial, &L0, &C1, pn, f)
}

fn hs(pn: u64, f: Vec<Frame>) -> PlainPacket {
    pkt(PacketKind::Handshake, &L0, &C1, pn, f)
}

fn one(pn: u64, f: Vec<Frame>) -> PlainPacket {
    pkt(PacketKind::OneRtt, &L0, &[], pn, f)
}

fn one_on(pn: u64, dcid: &[u8], f: Vec<Frame>) -> PlainPacket {
    pkt(PacketKind::OneRtt, dcid, &[], pn, f)
}

fn first_frames() -> Vec<Frame> {
    vec![Frame::Crypto { offset: 0, data: vec![1; 100] }]
}

fn conn() -> Connection {
    let mut c = Connection::accept(&ini(2, first_frames()), 1200, 0, 0, &rnd(1), &ltp()).unwrap();
    c.on_datagram(0, 1200, vec![ini(2, first_frames())], 0, &rnd(1));
    c
}

fn established_with(p: TransportParams) -> Connection {
    let mut c = conn();
    c.on_datagram(0, 1200, vec![hs(0, vec![Frame::Ping])], 10, &rnd(9));
    c.on_peer_params(&p, 10);
    c.on_handshake_complete(b"h3", 10, &rnd(2));
    c
}

fn established_rx() -> Connection {
    established_with(ptp())
}

/// Polls until None; a frame left due forever fails here rather than hanging the suite.
fn drain(c: &mut Connection, now: u64) -> Vec<OutDatagram> {
    let mut v = Vec::new();
    while let Some(d) = c.poll_transmit(now) {
        v.push(d);
        assert!(v.len() <= 1024, "poll_transmit never returned None");
    }
    v
}

fn established_tx_with(p: TransportParams) -> Connection {
    let mut c = established_with(p);
    drain(&mut c, 10);
    c
}

fn established() -> Connection {
    established_tx_with(ptp())
}

fn stream(id: u64, off: u64, d: &[u8], fin: bool) -> Frame {
    Frame::Stream { stream_id: id, offset: off, data: d.to_vec(), fin }
}

fn ncid(seq: u64, r: &[u8; 129], at: usize) -> Frame {
    let mut token = [0u8; 16];
    token.copy_from_slice(&r[at + 8..at + 24]);
    Frame::NewConnectionId { seq, retire_prior_to: 0, cid: r[at..at + 8].to_vec(), reset_token: token }
}

#[test]
fn stream_roundtrip() {
    let mut c = established();
    c.on_datagram(0, 50, vec![one(0, vec![stream(0, 0, b"GET", true)])], 30, &rnd(3));
    assert_eq!(c.stream_write(0, b"ok", true), Ok(2));
    let d = c.poll_transmit(30).unwrap();
    assert_eq!(d.path, 0);
    assert_eq!(d.packets.len(), 1);
    let p = &d.packets[0];
    assert_eq!(p.kind, PacketKind::OneRtt);
    assert_eq!(p.frames, vec![Frame::Ack(A(0, 0, 0, vec![])), stream(0, 0, b"ok", true)]);
    assert!(!p.spin);
    assert!(p.scid.is_empty());
    assert_eq!(packet_len(p), datagram_len(&d));
}

#[test]
fn handshake_done_and_cids() {
    let mut c = conn();
    c.on_peer_params(&ptp(), 10);
    c.on_handshake_complete(b"h3", 10, &rnd(2));
    let d = c.poll_transmit(10).unwrap();
    assert_eq!(d.packets.len(), 1);
    let p = &d.packets[0];
    assert_eq!(p.kind, PacketKind::OneRtt);
    assert_eq!(p.pn, 0);
    assert_eq!(p.dcid, C1.to_vec());
    let r = rnd(2);
    assert_eq!(
        p.frames,
        vec![Frame::HandshakeDone, ncid(1, &r, 0), ncid(2, &r, 24), ncid(3, &r, 48)],
    );
    let mut u = Vec::new();
    c.poll_cid_updates(&mut u);
    assert_eq!(
        u,
        vec![
            CidUpdate::Add(S1.to_vec()),
            CidUpdate::Add(L0.to_vec()),
            CidUpdate::Remove(S1.to_vec()),
            CidUpdate::Add(r[0..8].to_vec()),
            CidUpdate::Add(r[24..32].to_vec()),
            CidUpdate::Add(r[48..56].to_vec()),
        ],
    );
    // HANDSHAKE_DONE and the CIDs went once.
    assert!(c.poll_transmit(10).is_none());
}

#[test]
fn ack_only_not_recorded() {
    let mut c = established();
    assert_eq!(c.sent_inflight_len(PacketKind::OneRtt), 1);
    let mut acks = 0;
    for n in 0..100 {
        c.on_datagram(0, 50, vec![one(n, vec![Frame::Ping])], 50, &rnd(3));
        for d in drain(&mut c, 50) {
            assert!(matches!(d.packets[0].frames[0], Frame::Ack(_)));
            assert_eq!(d.packets[0].frames.len(), 1);
            acks += 1;
        }
        assert_eq!(c.sent_inflight_len(PacketKind::OneRtt), 1);
    }
    // The second ack-eliciting packet makes an ACK due at once (§13.2.2).
    assert_eq!(acks, 50);
}

#[test]
fn draining_silent_tx() {
    let mut c = established();
    c.on_datagram(0, 50, vec![one(0, vec![CC(false, 0, &[])])], 20, &rnd(3));
    assert_eq!(c.phase(), Phase::Draining);
    assert_eq!(c.poll_transmit(20), None);
}

#[test]
fn acked_stream_not_resent() {
    let mut c = established();
    c.on_datagram(0, 50, vec![one(0, vec![stream(0, 0, b"GET", true)])], 30, &rnd(3));
    assert_eq!(c.stream_write(0, b"ok", true), Ok(2));
    let d = c.poll_transmit(30).unwrap();
    let pn = d.packets[0].pn;
    assert!(d.packets[0].frames.contains(&stream(0, 0, b"ok", true)));
    c.on_datagram(0, 50, vec![one(1, vec![Frame::Ack(A(pn, 0, 0, vec![]))])], 31, &rnd(3));
    for d in drain(&mut c, 31) {
        assert!(!d.packets[0].frames.iter().any(|f| matches!(f, Frame::Stream { .. })));
    }
}

#[test]
fn ack_timer() {
    let mut c = established();
    c.on_datagram(0, 50, vec![one(0, vec![Frame::Ping])], 100, &rnd(3));
    assert_eq!(c.poll_transmit(100), None);
    assert_eq!(c.poll_transmit(100 + 24_999), None);
    let d = c.poll_transmit(100 + 25_000).unwrap();
    assert_eq!(d.packets.len(), 1);
    assert_eq!(d.packets[0].frames.len(), 1);
    assert!(matches!(d.packets[0].frames[0], Frame::Ack(_)));
}

#[test]
fn retire_cid_sent_once() {
    let mut c = established();
    let f = Frame::NewConnectionId { seq: 1, retire_prior_to: 1, cid: D(0xd1).to_vec(), reset_token: [0xe1; 16] };
    c.on_datagram(0, 50, vec![one(0, vec![f])], 30, &rnd(3));
    let sent = drain(&mut c, 30);
    let n = sent.iter().flat_map(|d| &d.packets).flat_map(|p| &p.frames).filter(|f| **f == Frame::RetireConnectionId(0)).count();
    assert_eq!(n, 1);
}
