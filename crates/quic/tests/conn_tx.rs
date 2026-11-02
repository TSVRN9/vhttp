//! Phase 3d2 Connection tests: the transmit path (`poll_transmit`).
// The helpers are the plan's shared set, copied into every 3d2 test file; later tasks use the rest.
#![allow(dead_code, non_snake_case)]
use quic::ack::AckFrame;
use quic::codes::PN_MAX;
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

// =============================================================================
// Task 2a-ii: every space, padding, closing, and the gates
// =============================================================================

/// A long-header packet, no padding, PN length 1.
fn long(kind: PacketKind, pn: u64, frames: Vec<Frame>) -> OutPacket {
    OutPacket { kind, dcid: C1.to_vec(), scid: L0.to_vec(), pn, pn_len: 1, frames, padding: 0, spin: false }
}

fn bad_ptp() -> TransportParams {
    let mut t = ptp();
    t.initial_source_connection_id = None;
    t
}

/// The peer has acknowledged everything `established()` sent: nothing is in flight.
fn established_quiet() -> Connection {
    let mut c = established();
    c.on_datagram(0, 50, vec![one(0, vec![Frame::Ack(A(0, 0, 0, vec![]))])], 20, &rnd(3));
    drain(&mut c, 20);
    assert_eq!(c.sent_inflight_len(PacketKind::OneRtt), 0);
    c
}

#[test]
fn pn_unencodable_closes_silently() {
    let mut c = established_quiet();
    c.skip_pns_for_test(PacketKind::OneRtt, 1 << 40);
    assert_eq!(c.poll_transmit(21), None);
    assert_eq!(c.phase(), Phase::Closed);
    assert!(!c.streams_live());
}

#[test]
fn harness_mirror() {
    let mut c = conn();
    let d = c.poll_transmit(0).unwrap();
    assert_eq!(
        d,
        OutDatagram { path: 0, packets: vec![long(PacketKind::Initial, 0, vec![Frame::Ack(A(2, 0, 0, vec![]))])] },
    );
    assert_eq!(datagram_len(&d), 47);
    assert_eq!(c.poll_transmit(0), None);
    assert_eq!(c.sent_inflight_len(PacketKind::Initial), 0);
}

#[test]
fn amp_limit() {
    let mut c = conn();
    c.crypto_write(PacketKind::Initial, &[0xaa; 5000]);
    let v = drain(&mut c, 0);
    assert_eq!(v.len(), 3);
    for d in &v {
        assert_eq!(datagram_len(d), 1200);
    }
    let f = &v[0].packets[0].frames;
    assert_eq!(f[0], Frame::Ack(A(2, 0, 0, vec![])));
    assert!(matches!(f[1], Frame::Crypto { offset: 0, .. }));
    // Bytes count from a datagram with no processed packet.
    c.on_datagram(0, 1200, vec![], 1, &rnd(3));
    assert_eq!(datagram_len(&c.poll_transmit(1).unwrap()), 1200);
}

#[test]
fn padding_counts_toward_amp() {
    let mut c = conn();
    c.crypto_write(PacketKind::Initial, &[0xaa; 10]);
    assert_eq!(datagram_len(&c.poll_transmit(0).unwrap()), 1200);
    assert_eq!(c.path_budget(0), Some(2400));
}

#[test]
fn amp_below_1200() {
    let mut c = conn();
    assert_eq!(datagram_len(&c.poll_transmit(0).unwrap()), 47);
    c.crypto_write(PacketKind::Initial, &[0xaa; 3000]);
    assert_eq!(datagram_len(&c.poll_transmit(0).unwrap()), 1200);
    assert_eq!(datagram_len(&c.poll_transmit(0).unwrap()), 1200);
    // 1153 bytes of budget left: no ack-eliciting Initial, but a Handshake packet fits.
    c.crypto_write(PacketKind::Handshake, &[0xbb; 100]);
    let d = c.poll_transmit(0).unwrap();
    let want = long(PacketKind::Handshake, 0, vec![Frame::Crypto { offset: 0, data: vec![0xbb; 100] }]);
    assert_eq!(d.packets, vec![want]);
    assert_eq!(datagram_len(&d), 146);
    assert_eq!(c.poll_transmit(0), None);
    c.on_datagram(0, 1200, vec![ini(3, vec![Frame::Ping])], 1, &rnd(3));
    let d = c.poll_transmit(1).unwrap();
    assert_eq!(datagram_len(&d), 1200);
    assert_eq!(d.packets[0].kind, PacketKind::Initial);
    assert_eq!(d.packets[0].frames[0], Frame::Ack(A(3, 0, 1, vec![])));
}

#[test]
fn coalesced_small() {
    let mut c = conn();
    c.on_datagram(0, 1100, vec![ini2(3, vec![Frame::Ping]), hs(0, vec![Frame::Ping])], 1, &rnd(3));
    let d = c.poll_transmit(1).unwrap();
    assert_eq!(d.packets, vec![long(PacketKind::Handshake, 0, vec![Frame::Ack(A(0, 0, 0, vec![]))])]);
    // The Handshake packet validated the address.
    c.crypto_write(PacketKind::Handshake, &[0xbb; 10_000]);
    let total: usize = drain(&mut c, 1).iter().map(datagram_len).sum();
    assert!(total > 6900, "{total}");
}

#[test]
fn coalesced_padded() {
    let mut c = conn();
    c.crypto_write(PacketKind::Initial, &[0xaa; 10]);
    c.crypto_write(PacketKind::Handshake, &[0xbb; 10]);
    let d = c.poll_transmit(0).unwrap();
    assert_eq!(datagram_len(&d), 1200);
    assert_eq!(d.packets.len(), 2);
    assert_eq!(d.packets[0].kind, PacketKind::Initial);
    assert_eq!(d.packets[1].kind, PacketKind::Handshake);
    assert_eq!(d.packets[0].dcid, d.packets[1].dcid);
}

#[test]
fn close_in_handshake_spaces() {
    let mut c = conn();
    c.on_peer_params(&bad_ptp(), 1);
    let d = c.poll_transmit(1).unwrap();
    assert_eq!(
        d.packets,
        vec![
            long(PacketKind::Initial, 0, vec![CC(false, 0x08, &[])]),
            long(PacketKind::Handshake, 0, vec![CC(false, 0x08, &[])]),
        ],
    );
    assert_eq!(c.poll_transmit(1), None);
}

#[test]
fn app_close_conversion() {
    let mut c = conn();
    c.close(0x0100, true, b"bye", 1);
    let d = c.poll_transmit(1).unwrap();
    assert_eq!(
        d.packets,
        vec![
            long(PacketKind::Initial, 0, vec![CC(false, 0x0c, &[])]),
            long(PacketKind::Handshake, 0, vec![CC(false, 0x0c, &[])]),
        ],
    );
    let mut c = established();
    c.close(0x0100, true, b"bye", 20);
    let d = c.poll_transmit(20).unwrap();
    assert_eq!(d.packets.len(), 1);
    assert_eq!(d.packets[0].kind, PacketKind::OneRtt);
    assert_eq!(d.packets[0].frames, vec![CC(true, 0x0100, b"bye")]);
}

#[test]
fn alpn_mismatch() {
    let mut c = conn();
    c.on_peer_params(&ptp(), 1);
    c.on_handshake_complete(b"h2", 1, &rnd(2));
    let d = c.poll_transmit(1).unwrap();
    assert_eq!(
        d.packets,
        vec![
            long(PacketKind::Initial, 0, vec![CC(false, 0x178, &[])]),
            long(PacketKind::Handshake, 0, vec![CC(false, 0x178, &[])]),
        ],
    );
}

#[test]
fn closing_capped() {
    let mut c = established();
    c.close(0x0a, false, b"", 20);
    let d = c.poll_transmit(20).unwrap();
    assert_eq!(datagram_len(&d), 30);
    assert_eq!(d.packets.len(), 1);
    assert_eq!(d.packets[0].kind, PacketKind::OneRtt);
    assert_eq!(d.packets[0].frames, vec![CC(false, 0x0a, &[])]);
    assert_eq!(c.poll_transmit(20), None);
    c.on_datagram(0, 9, vec![], 21, &rnd(3));
    assert_eq!(c.poll_transmit(21), None);
    c.on_datagram(0, 9, vec![], 22, &rnd(3));
    let e = c.poll_transmit(22).unwrap();
    assert_eq!(e.packets[0].frames, d.packets[0].frames);
    assert_eq!(e.packets[0].pn, d.packets[0].pn + 1);
    assert_eq!(c.poll_transmit(22), None);
    // An unknown path adds no closing budget and owes no reply.
    c.on_datagram(5, 1200, vec![], 23, &rnd(3));
    assert_eq!(c.poll_transmit(23), None);
}

#[test]
fn pn_max_closes_silently() {
    let mut c = established_quiet();
    c.skip_pns_for_test(PacketKind::OneRtt, PN_MAX);
    assert_eq!(c.poll_transmit(21), None);
    assert_eq!(c.phase(), Phase::Closed);
    assert!(!c.streams_live());
    assert_eq!(c.poll_transmit(22), None);
    assert_eq!(c.poll_transmit(1_000_000), None);
}

#[test]
fn stale_active_silent_close_sends_nothing() {
    // conn_rx's stale_active_no_spare_closes_silently: nothing goes out on that CID, CONNECTION_CLOSE
    // included (§9.5, Task 1b ruling I4).
    let r2 = rnd(2)[0..8].to_vec();
    let id = |seq, rpt| Frame::NewConnectionId {
        seq,
        retire_prior_to: rpt,
        cid: D(0xd1).to_vec(),
        reset_token: [0xe1; 16],
    };
    let mut c = established_rx();
    c.on_datagram(0, 100, vec![one(0, vec![id(1, 0)])], 30, &rnd(3));
    c.on_datagram(1, 100, vec![one_on(1, &r2, vec![Frame::PathChallenge(D(5))])], 30, &rnd(3));
    c.on_datagram(1, 100, vec![one_on(2, &r2, vec![Frame::Ping])], 30, &rnd(3));
    c.on_datagram(2, 100, vec![one_on(3, &r2, vec![Frame::PathChallenge(D(7))])], 30, &rnd(3));
    c.on_datagram(0, 100, vec![one(4, vec![Frame::Ping])], 30, &rnd(3));
    c.on_datagram(0, 100, vec![one(5, vec![id(1, 1)])], 31, &rnd(3));
    assert!(c.is_closed());
    assert_eq!(c.poll_transmit(31), None);
    assert_eq!(c.poll_transmit(1_000_000), None);
}

#[test]
fn close_out_of_pns_is_silent() {
    let mut c = established_quiet();
    c.skip_pns_for_test(PacketKind::OneRtt, PN_MAX);
    c.close(0x0a, false, b"", 21);
    assert_eq!(c.poll_transmit(21), None);
    assert_eq!(c.phase(), Phase::Closed);
    assert!(!c.streams_live());
}

#[test]
fn close_waits_for_path_budget() {
    let mut c = conn();
    c.crypto_write(PacketKind::Initial, &[0xaa; 5000]);
    assert_eq!(drain(&mut c, 0).len(), 3);
    assert_eq!(c.path_budget(0), Some(0));
    c.close(0x0a, false, b"", 1);
    assert_eq!(c.poll_transmit(1), None);
    assert_eq!(c.phase(), Phase::Closing);
    c.on_datagram(0, 100, vec![], 2, &rnd(3));
    let d = c.poll_transmit(2).unwrap();
    assert!(datagram_len(&d) <= 300);
    assert_eq!(c.poll_transmit(2), None);
}

#[test]
fn pn_max_closes_with_no_budget() {
    let mut c = conn();
    c.crypto_write(PacketKind::Initial, &[0xaa; 5000]);
    assert_eq!(drain(&mut c, 0).len(), 3);
    assert_eq!(c.path_budget(0), Some(0));
    c.skip_pns_for_test(PacketKind::Handshake, PN_MAX);
    assert_eq!(c.poll_transmit(0), None);
    assert_eq!(c.phase(), Phase::Closed);
}

// Task 2b: path datagrams.

fn frames_on(d: &OutDatagram) -> Vec<&Frame> {
    d.packets.iter().flat_map(|p| p.frames.iter()).collect()
}

fn has_frame(d: &OutDatagram, f: &Frame) -> bool {
    frames_on(d).iter().any(|g| *g == f)
}

fn has_response(d: &OutDatagram) -> bool {
    frames_on(d).iter().any(|g| matches!(g, Frame::PathResponse(_)))
}

fn has_challenge(d: &OutDatagram) -> bool {
    frames_on(d).iter().any(|g| matches!(g, Frame::PathChallenge(_)))
}

fn slice8(r: &[u8; 129], at: usize) -> [u8; 8] {
    let mut x = [0u8; 8];
    x.copy_from_slice(&r[at..at + 8]);
    x
}

fn new_cid_d1(seq: u64, rpt: u64) -> Frame {
    Frame::NewConnectionId { seq, retire_prior_to: rpt, cid: D(0xd1).to_vec(), reset_token: [0xe1; 16] }
}

/// `established()`, then a non-probing packet from path 1, and the polls that follow it.
fn rebound() -> (Connection, Vec<OutDatagram>) {
    let mut c = established();
    c.on_datagram(1, 100, vec![one(1, vec![stream(0, 0, b"GET", true)])], 30, &rnd(5));
    let v = drain(&mut c, 30);
    (c, v)
}

#[test]
fn path_response_echo() {
    let mut c = established();
    c.on_datagram(0, 100, vec![one(1, vec![Frame::PathChallenge(D(1))])], 30, &rnd(5));
    let d = c.poll_transmit(30).unwrap();
    assert_eq!(d.path, 0);
    assert!(has_frame(&d, &Frame::PathResponse(D(1))));
    assert_eq!(datagram_len(&d), 1200);
    assert!(!drain(&mut c, 30).iter().any(has_response));
    assert!(!drain(&mut c, 1_000_000).iter().any(has_response));
}

#[test]
fn probing_does_not_migrate() {
    let mut c = established();
    c.on_datagram(1, 1200, vec![one(1, vec![Frame::PathChallenge(D(2))])], 30, &rnd(5));
    let d = c.poll_transmit(30).unwrap();
    assert_eq!(d.path, 1);
    assert!(has_frame(&d, &Frame::PathResponse(D(2))));
    assert_eq!(datagram_len(&d), 1200);
    assert_eq!(c.active_path(), 0);
    c.stream_write(3, b"data", false).unwrap();
    let d = c.poll_transmit(31).unwrap();
    assert_eq!(d.path, 0);
    assert!(frames_on(&d).iter().any(|f| matches!(f, Frame::Stream { .. })));
}

#[test]
fn response_not_expanded_past_amp() {
    let mut c = established();
    c.on_datagram(1, 50, vec![one(1, vec![Frame::PathChallenge(D(3))])], 30, &rnd(5));
    let d = c.poll_transmit(30).unwrap();
    assert_eq!(d.path, 1);
    assert_eq!(d.packets.len(), 1);
    let pn = d.packets[0].pn;
    assert_eq!(
        d.packets,
        vec![OutPacket {
            kind: PacketKind::OneRtt,
            dcid: C1.to_vec(),
            scid: vec![],
            pn,
            pn_len: 1,
            frames: vec![Frame::PathResponse(D(3))],
            padding: 0,
            spin: false,
        }]
    );
    assert_eq!(datagram_len(&d), 35);
    assert_eq!(c.path_budget(1), Some(150 - 35));
}

#[test]
fn nat_rebinding() {
    let (mut c, v) = rebound();
    assert_eq!(c.active_path(), 1);
    let r5 = rnd(5);
    let on1: Vec<&OutDatagram> = v.iter().filter(|d| d.path == 1).collect();
    let chal1: Vec<&&OutDatagram> =
        on1.iter().filter(|d| has_frame(d, &Frame::PathChallenge(slice8(&r5, 96)))).collect();
    assert_eq!(chal1.len(), 1);
    assert!(datagram_len(chal1[0]) < 1200);
    assert!(on1.iter().map(|d| datagram_len(d)).sum::<usize>() <= 300);
    let chal0: Vec<&OutDatagram> =
        v.iter().filter(|d| d.path == 0 && has_frame(d, &Frame::PathChallenge(slice8(&r5, 104)))).collect();
    assert_eq!(chal0.len(), 1);
    assert_eq!(datagram_len(chal0[0]), 1200);

    c.on_datagram(1, 1200, vec![one(2, vec![Frame::PathResponse(slice8(&r5, 96))])], 40, &rnd(6));
    let d = c.poll_transmit(40).unwrap();
    assert_eq!(d.path, 1);
    assert!(has_frame(&d, &Frame::PathChallenge(slice8(&rnd(6), 96))));
    assert_eq!(datagram_len(&d), 1200);

    // The expanded probe's answer settles the MTU: no third challenge.
    drain(&mut c, 40);
    c.on_datagram(1, 1200, vec![one(3, vec![Frame::PathResponse(slice8(&rnd(6), 96))])], 40, &rnd(7));
    assert!(!drain(&mut c, 40).iter().any(has_challenge));
    c.stream_write(3, b"data", false).unwrap();
    let d = c.poll_transmit(41).unwrap();
    assert_eq!(d.path, 1);
    assert_eq!(d.packets[0].dcid, C1.to_vec());
}

#[test]
fn fresh_cid_for_new_dcid() {
    let mut c = established();
    c.on_datagram(0, 1200, vec![one(1, vec![new_cid_d1(1, 0)])], 30, &rnd(5));
    drain(&mut c, 30);
    c.on_datagram(1, 1200, vec![one_on(2, &rnd(2)[0..8], vec![stream(0, 0, b"GET", true)])], 31, &rnd(6));
    let v = drain(&mut c, 31);
    assert!(v.iter().any(|d| d.path == 1));
    assert!(v.iter().any(|d| d.path == 0));
    for d in &v {
        let want = if d.path == 1 { D(0xd1) } else { C1 };
        assert!(d.packets.iter().all(|p| p.dcid == want.to_vec()));
    }
}

#[test]
fn probe_new_cid_response() {
    let mut c = established();
    c.on_datagram(0, 1200, vec![one(1, vec![new_cid_d1(1, 0)])], 30, &rnd(5));
    drain(&mut c, 30);
    c.on_datagram(1, 1200, vec![one_on(2, &rnd(2)[0..8], vec![Frame::PathChallenge(D(5))])], 31, &rnd(6));
    let v = drain(&mut c, 31);
    let d = v.iter().find(|d| d.path == 1).unwrap();
    assert!(has_frame(d, &Frame::PathResponse(D(5))));
    assert_eq!(d.packets[0].dcid, D(0xd1).to_vec());
}

#[test]
fn no_fresh_cid_no_send() {
    let mut c = established();
    c.on_datagram(1, 1200, vec![one_on(2, &rnd(2)[0..8], vec![stream(0, 0, b"GET", true)])], 31, &rnd(6));
    assert!(drain(&mut c, 31).iter().all(|d| d.path != 1));
    assert!(drain(&mut c, 1_000_000).iter().all(|d| d.path != 1));
    assert_eq!(c.active_path(), 0);
}

#[test]
fn no_fresh_cid_owed_probe_never_answered() {
    let mut c = established();
    c.on_datagram(1, 1200, vec![one_on(2, &rnd(2)[0..8], vec![Frame::PathChallenge(D(5))])], 31, &rnd(6));
    assert!(c.response_owed(1));
    assert!(drain(&mut c, 31).iter().all(|d| d.path != 1));
    assert!(c.response_owed(1));
}

#[test]
fn stale_cid_not_used() {
    let (mut c, _) = rebound();
    c.on_datagram(1, 100, vec![one(2, vec![new_cid_d1(1, 1)])], 31, &rnd(6));
    c.stream_write(3, b"data", false).unwrap();
    let v = drain(&mut c, 31);
    assert!(!v.is_empty());
    for d in &v {
        for p in &d.packets {
            assert_ne!(p.dcid, C1.to_vec());
            assert_eq!(p.dcid, D(0xd1).to_vec());
        }
    }
}

#[test]
fn path_cap() {
    let mut c = established();
    for q in 1..=3u8 {
        c.on_datagram(q as u64, 1200, vec![one(q as u64, vec![Frame::Ping])], 30, &rnd(3));
    }
    drain(&mut c, 30);
    c.on_datagram(4, 1200, vec![one(5, vec![Frame::PathChallenge(D(4))])], 31, &rnd(3));
    assert!(drain(&mut c, 31).iter().all(|d| d.path != 4));
    assert!(drain(&mut c, 1_000_000).iter().all(|d| d.path != 4));
}

#[test]
fn response_on_other_path_validates() {
    let (mut c, _) = rebound();
    assert_ne!(c.path_state(1), Some(quic::path::PathState::Validated));
    c.on_datagram(0, 100, vec![one(2, vec![Frame::PathResponse(slice8(&rnd(5), 96))])], 31, &rnd(6));
    assert_eq!(c.path_state(1), Some(quic::path::PathState::Validated));
}

#[test]
fn refused_path_burns_no_pn() {
    let mut c = established_with(ptp());
    let before = drain(&mut c, 10);
    let first = before.iter().flat_map(|d| d.packets.iter()).map(|p| p.pn).max().unwrap() + 1;
    c.on_datagram(1, 10, vec![one(1, vec![Frame::PathChallenge(D(3))])], 30, &rnd(5));
    let mut v = drain(&mut c, 30);
    assert!(!v.iter().any(has_response));
    assert_eq!(c.poll_transmit(30), None);
    assert!(c.response_owed(1));
    c.on_datagram(1, 50, vec![], 31, &rnd(5));
    v.extend(drain(&mut c, 31));
    assert_eq!(v.iter().filter(|d| has_frame(d, &Frame::PathResponse(D(3)))).count(), 1);
    let pns: Vec<u64> = v.iter().flat_map(|d| d.packets.iter()).map(|p| p.pn).collect();
    let want: Vec<u64> = (first..first + pns.len() as u64).collect();
    assert_eq!(pns, want);
}

/// A refused path doesn't hold up one later in the table that fits.
#[test]
fn refused_path_skipped() {
    let mut c = established();
    c.on_datagram(1, 10, vec![one(1, vec![Frame::PathChallenge(D(3))])], 30, &rnd(5));
    c.on_datagram(2, 1200, vec![one(2, vec![Frame::PathChallenge(D(4))])], 30, &rnd(5));
    let d = c.poll_transmit(30).unwrap();
    assert_eq!(d.path, 2);
    assert!(has_frame(&d, &Frame::PathResponse(D(4))));
    assert!(c.response_owed(1));
}

#[test]
fn second_migration_keeps_challenge() {
    let (mut c, _) = rebound();
    let r5 = rnd(5);
    c.on_datagram(0, 1200, vec![one(2, vec![Frame::Ping])], 31, &rnd(6));
    assert_eq!(c.active_path(), 0);
    drain(&mut c, 31);
    c.on_datagram(1, 1200, vec![one(3, vec![Frame::Ping])], 32, &rnd(7));
    assert_eq!(c.active_path(), 1);
    assert!(!drain(&mut c, 32).iter().any(|d| d.path == 1 && has_challenge(d)));
    c.on_datagram(1, 100, vec![one(4, vec![Frame::PathResponse(slice8(&r5, 96))])], 33, &rnd(8));
    assert_eq!(c.path_state(1), Some(quic::path::PathState::Validated));
}

/// P12's "at most once": a second copy of a challenge gets its own echo, the first gets one.
#[test]
fn responses_one_per_challenge() {
    let mut c = established();
    c.on_datagram(
        0,
        1200,
        vec![one(1, vec![Frame::PathChallenge(D(1)), Frame::PathChallenge(D(2)), Frame::PathChallenge(D(1))])],
        30,
        &rnd(5),
    );
    let v = drain(&mut c, 30);
    let got: Vec<&Frame> =
        v.iter().flat_map(frames_on).filter(|f| matches!(f, Frame::PathResponse(_))).collect();
    assert_eq!(
        got,
        vec![&Frame::PathResponse(D(1)), &Frame::PathResponse(D(2)), &Frame::PathResponse(D(1))]
    );
}

/// Each path packet takes its own packet number.
#[test]
fn path_packets_take_fresh_pns() {
    let mut c = established();
    c.on_datagram(0, 1200, vec![one(1, vec![Frame::PathChallenge(D(1)), Frame::PathChallenge(D(2))])], 30, &rnd(5));
    let v = drain(&mut c, 30);
    assert!(v.len() >= 2);
    let pns: Vec<u64> = v.iter().flat_map(|d| d.packets.iter()).map(|p| p.pn).collect();
    assert!(pns.windows(2).all(|w| w[0] + 1 == w[1]));
}

/// A response and a challenge together are measured together: 44 bytes don't go in a 39-byte budget.
#[test]
fn both_frames_measured() {
    let mut c = established();
    let f = vec![Frame::PathChallenge(D(3)), stream(0, 0, b"GET", true)];
    c.on_datagram(1, 13, vec![one(1, f)], 30, &rnd(5));
    assert_eq!(c.active_path(), 1);
    assert!(drain(&mut c, 30).iter().all(|d| d.path != 1));
    assert_eq!(c.path_budget(1), Some(39));
    c.on_datagram(1, 50, vec![], 31, &rnd(5));
    let v = drain(&mut c, 31);
    let d = v.iter().find(|d| d.path == 1).unwrap();
    assert!(has_frame(d, &Frame::PathResponse(D(3))));
    assert!(has_challenge(d));
    assert_eq!(datagram_len(d), 44);
}

/// An owed PATH frame with a packet number that can't be encoded ends the connection, sending nothing.
#[test]
fn path_frame_unencodable_pn_closes() {
    let mut c = established_quiet();
    c.on_datagram(0, 1200, vec![one(1, vec![Frame::PathChallenge(D(1))])], 30, &rnd(5));
    c.skip_pns_for_test(PacketKind::OneRtt, 1 << 40);
    assert_eq!(c.poll_transmit(30), None);
    assert_eq!(c.phase(), Phase::Closed);
    assert!(!c.streams_live());
}

/// The close is at the path frame: a tiny active-path budget means `data_datagram` never gets to it.
#[test]
fn path_frame_unencodable_pn_closes_at_the_path() {
    let mut c = established_quiet();
    c.on_datagram(1, 1, vec![one(1, vec![stream(0, 0, b"GET", true)])], 30, &rnd(5));
    assert_eq!(c.active_path(), 1);
    c.skip_pns_for_test(PacketKind::OneRtt, 1 << 40);
    assert_eq!(c.poll_transmit(30), None);
    assert_eq!(c.phase(), Phase::Closed);
}
