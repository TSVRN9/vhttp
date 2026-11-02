//! Phase 3d2 Connection tests: accept, the TLS boundary and (Task 1a-ii, 1b) the receive path.
// The helpers are the plan's shared set, copied into every 3d2 test file; later tasks use the rest.
#![allow(dead_code, non_snake_case)]
use quic::ack::AckFrame;
use quic::conn::*;
use quic::datagram::*;
use quic::frame::Frame;
use quic::lifecycle::Phase;
use quic::path::PathState;
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

#[test]
fn accept_rules() {
    let f = first_frames;
    assert!(Connection::accept(&ini(2, f()), 1199, 0, 0, &rnd(1), &ltp()).is_none());
    assert!(Connection::accept(&hs(0, f()), 1200, 0, 0, &rnd(1), &ltp()).is_none());
    let mut t = ltp();
    t.initial_max_streams_uni = 2;
    assert!(Connection::accept(&ini(2, f()), 1200, 0, 0, &rnd(1), &t).is_none());
    t.initial_max_streams_uni = 101;
    assert!(Connection::accept(&ini(2, f()), 1200, 0, 0, &rnd(1), &t).is_none());
    assert!(Connection::accept(&ini(2, f()), 1200, 0, 0, &rnd(1), &ltp()).is_some());
}

fn peer_params_failed() -> Connection {
    let mut c = conn();
    let mut t = ptp();
    t.initial_source_connection_id = None;
    c.on_peer_params(&t, 1);
    c
}

#[test]
fn peer_params_checked() {
    let c = peer_params_failed();
    assert_eq!(c.phase(), Phase::Closing);
    assert_eq!(c.close_info(), &Some((false, 0x08, vec![])));
}

#[test]
fn tls_calls_after_close() {
    let mut c = peer_params_failed();
    c.on_peer_params(&ptp(), 2);
    c.on_handshake_complete(b"h3", 2, &rnd(2));
    assert!(!c.streams_live());
    assert!(!c.handshake_complete());
    assert_eq!(c.close_info(), &Some((false, 0x08, vec![])));
}

#[test]
fn tls_alert_closes() {
    let mut c = conn();
    c.on_tls_alert(0x78, 1);
    assert_eq!(c.phase(), Phase::Closing);
    assert_eq!(c.close_info(), &Some((false, 0x178, vec![])));
    assert!(!c.streams_live());
}

#[test]
fn complete_without_peer_params() {
    let mut c = conn();
    c.on_handshake_complete(b"h3", 1, &rnd(2));
    assert_eq!(c.phase(), Phase::Closing);
    assert_eq!(c.close_info(), &Some((false, 0x01, vec![])));
    assert!(!c.handshake_complete());
}

#[test]
fn crypto_write_gated() {
    let mut c = conn();
    c.crypto_write(PacketKind::Handshake, &[1; 10]);
    assert!(c.crypto_capacity(PacketKind::Handshake) > 0);
    let mut c = established_rx();
    c.crypto_write(PacketKind::Initial, &[1; 10]);
    assert_eq!(c.crypto_capacity(PacketKind::Initial), 0);
    let mut c = peer_params_failed();
    c.crypto_write(PacketKind::Handshake, &[1; 10]);
    assert_eq!(c.crypto_capacity(PacketKind::Handshake), 0);
}

// The handshake path of `established_with`, which later tasks build on. Peer limit 4 and our cap
// of 4 active CIDs mean three more CIDs, from the first three slices of `rnd(2)`.
#[test]
fn established_state() {
    let mut c = established_rx();
    assert!(c.handshake_complete() && c.streams_live());
    assert_eq!(c.peer_uni_limit(), Some(3));
    assert_eq!(c.active_path(), 0);
    assert!(c.path_state(0).is_some());
    assert_eq!(c.path_dcid(0), Some(C1.to_vec()));
    assert_eq!(c.crypto_capacity(PacketKind::Initial), 0);
    // Absent path 4.
    assert_eq!(c.path_state(4), None);
    assert_eq!(c.path_dcid(4), None);
    assert!(!c.response_owed(4) && !c.challenge_owed(4));

    let r = rnd(2);
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
        ]
    );
    let mut v = Vec::new();
    c.poll_cid_updates(&mut v);
    assert!(v.is_empty());
}

#[test]
fn crypto_delivered() {
    let mut c = conn();
    let mut out = Vec::new();
    c.crypto_read(PacketKind::Initial, &mut out);
    assert_eq!(out, vec![1; 100]);
    let mut u = Vec::new();
    c.poll_cid_updates(&mut u);
    assert_eq!(u, vec![CidUpdate::Add(S1.to_vec()), CidUpdate::Add(L0.to_vec())]);
}

#[test]
fn small_datagram_initial_dropped() {
    let mut c = conn();
    c.on_datagram(0, 1199, vec![ini(3, vec![Frame::Ping])], 1, &rnd(3));
    assert_eq!(c.largest_pn(PacketKind::Initial), Some(2));
    assert_eq!(c.phase(), Phase::Open);
}

#[test]
fn coalesced_dcid_rule() {
    let mut c = conn();
    // `ini` has DCID S1, `hs` has L0: §12.2 ignores the second packet.
    c.on_datagram(0, 1200, vec![ini(3, vec![Frame::Ping]), hs(0, vec![Frame::Ping])], 1, &rnd(3));
    assert_eq!(c.largest_pn(PacketKind::Handshake), None);
    assert_eq!(c.largest_pn(PacketKind::Initial), Some(3));
}

#[test]
fn handshake_validates_and_discards() {
    let mut c = conn();
    c.on_datagram(0, 1100, vec![ini2(3, vec![Frame::Ping]), hs(0, vec![Frame::Ping])], 1, &rnd(3));
    assert_eq!(c.largest_pn(PacketKind::Handshake), Some(0));
    assert_eq!(c.largest_pn(PacketKind::Initial), None);
    assert_eq!(c.path_state(0), Some(PathState::Validated));
    assert_eq!(c.phase(), Phase::Open);
    assert_eq!(c.crypto_capacity(PacketKind::Initial), 0);
}

#[test]
fn later_initial_other_scid() {
    let mut c = conn();
    let p = pkt(PacketKind::Initial, &S1, &[0xc2; 8], 3, vec![Frame::Ping]);
    c.on_datagram(0, 1200, vec![p], 1, &rnd(3));
    assert_eq!(c.largest_pn(PacketKind::Initial), Some(2));
    assert_eq!(c.phase(), Phase::Open);
}

#[test]
fn duplicate_pn() {
    let mut c = conn();
    let mut out = Vec::new();
    c.crypto_read(PacketKind::Initial, &mut out);
    c.on_datagram(0, 1200, vec![ini(2, vec![Frame::Crypto { offset: 100, data: vec![2; 10] }])], 1, &rnd(3));
    let mut out = Vec::new();
    c.crypto_read(PacketKind::Initial, &mut out);
    assert_eq!(out, Vec::<u8>::new());
}

#[test]
fn one_rtt_before_complete() {
    let mut c = conn();
    c.on_datagram(0, 1200, vec![one(0, vec![Frame::Ping])], 1, &rnd(3));
    assert_eq!(c.largest_pn(PacketKind::OneRtt), None);
}

#[test]
fn ack_of_unsent() {
    let mut c = conn();
    c.on_datagram(0, 1200, vec![ini(3, vec![Frame::Ack(A(9, 0, 0, vec![]))])], 1, &rnd(3));
    assert_eq!(c.phase(), Phase::Closing);
    assert_eq!(c.close_info(), &Some((false, 0x0a, vec![])));
}

#[test]
fn connection_close_drains() {
    let mut c = established_rx();
    c.on_datagram(0, 1200, vec![one(0, vec![CC(false, 0, &[])])], 11, &rnd(3));
    assert_eq!(c.phase(), Phase::Draining);
    assert!(!c.streams_live());
}

#[test]
fn long_header_other_path_dropped() {
    let mut c = conn();
    c.on_datagram(1, 1200, vec![ini(3, vec![Frame::Ping])], 1, &rnd(3));
    assert_eq!(c.largest_pn(PacketKind::Initial), Some(2));
}

#[test]
fn challenge_flood_dropped() {
    let mut c = established_rx();
    let f = (1..=5).map(|x| Frame::PathChallenge(D(x))).collect();
    c.on_datagram(0, 1200, vec![one(0, f)], 11, &rnd(3));
    assert_eq!(c.largest_pn(PacketKind::OneRtt), None);
    assert!(!c.response_owed(0));
}

#[test]
fn stream_run_coalesces() {
    let s = |id, offset, data: &[u8], fin| Frame::Stream { stream_id: id, offset, data: data.to_vec(), fin };
    let adj = [s(4, 10, &[1, 2], false), s(4, 12, &[3], false), s(4, 13, &[4], true), Frame::Ping];
    let (run, e) = stream_run(&adj, 0).unwrap();
    assert_eq!(run, s(4, 10, &[1, 2, 3, 4], true));
    assert_eq!(e, 3);
    // A gap, another stream, a frame of another type, and the end of the record end a run.
    assert!(stream_run(&[s(4, 10, &[1], false), s(4, 12, &[2], false)], 0).is_none());
    assert!(stream_run(&[s(4, 10, &[1], false), s(8, 11, &[2], false)], 0).is_none());
    assert!(stream_run(&adj, 2).is_none());
    assert!(stream_run(&[Frame::Ping, s(4, 0, &[1], false)], 0).is_none());
    let (run, e) = stream_run(&[s(4, 0, &[1], false), s(4, 1, &[2], false), s(4, 9, &[3], false)], 0).unwrap();
    assert_eq!(run, s(4, 0, &[1, 2], false));
    assert_eq!(e, 2);
}
