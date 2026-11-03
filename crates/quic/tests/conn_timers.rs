//! Phase 3d2 Connection tests: timers (`next_timeout`, `on_timeout`).
// The helpers are the plan's shared set, copied into every 3d2 test file.
#![allow(dead_code, non_snake_case)]
use quic::ack::AckFrame;
use quic::conn::*;
use quic::datagram::*;
use quic::frame::Frame;
use quic::lifecycle::Phase;
use quic::payload::PacketKind;
use quic::tp::*;
use quic::send_stream::MAX_SEND_RANGES;

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


fn frames_on(d: &OutDatagram) -> Vec<&Frame> {
    d.packets.iter().flat_map(|p| p.frames.iter()).collect()
}

fn has_frame(d: &OutDatagram, f: &Frame) -> bool {
    frames_on(d).iter().any(|g| *g == f)
}

fn has_challenge(d: &OutDatagram) -> bool {
    frames_on(d).iter().any(|g| matches!(g, Frame::PathChallenge(_)))
}

fn has_stream(d: &OutDatagram) -> bool {
    frames_on(d).iter().any(|g| matches!(g, Frame::Stream { .. }))
}

fn has_crypto(d: &OutDatagram) -> bool {
    frames_on(d).iter().any(|g| matches!(g, Frame::Crypto { .. }))
}

fn has_close(d: &OutDatagram) -> bool {
    frames_on(d).iter().any(|g| matches!(g, Frame::ConnectionClose { .. }))
}

fn eliciting(d: &OutDatagram) -> bool {
    frames_on(d).iter().any(|g| !matches!(g, Frame::Ack(_)))
}

fn slice8(r: &[u8; 129], at: usize) -> [u8; 8] {
    let mut x = [0u8; 8];
    x.copy_from_slice(&r[at..at + 8]);
    x
}

fn new_cid(seq: u64, rpt: u64, x: u8) -> Frame {
    Frame::NewConnectionId { seq, retire_prior_to: rpt, cid: D(x).to_vec(), reset_token: [x; 16] }
}

/// Drains at `now`; whatever is left must wait for later, or a shell that sleeps until
/// `next_timeout` would spin.
fn settle(c: &mut Connection, now: u64) -> Vec<OutDatagram> {
    let v = drain(c, now);
    if let Some(t) = c.next_timeout() {
        assert!(t > now, "next_timeout {t} is not after {now}: a wake loop");
    }
    v
}

/// `established()`, then a non-probing packet from path 1, and the polls that follow it.
fn rebound() -> (Connection, Vec<OutDatagram>) {
    let mut c = established();
    c.on_datagram(1, 100, vec![one(1, vec![stream(0, 0, b"GET", true)])], 30, &rnd(5));
    let v = drain(&mut c, 30);
    (c, v)
}

const PTO: u64 = 1_024_000;

// =============================================================================
// Closing, draining, idle
// =============================================================================

#[test]
fn close_deadline() {
    let mut c = conn();
    let mut t = ptp();
    t.initial_source_connection_id = None;
    c.on_peer_params(&t, 1);
    drain(&mut c, 1);
    assert_eq!(c.next_timeout(), Some(3_072_001));
    c.on_timeout(3_072_000, &rnd(3));
    assert!(!c.is_closed());
    c.on_timeout(3_072_001, &rnd(3));
    assert!(c.is_closed());
    assert_eq!(c.next_timeout(), None);
}

#[test]
fn draining_deadline() {
    let mut c = established();
    c.on_datagram(0, 50, vec![one(0, vec![CC(false, 0, &[])])], 20, &rnd(3));
    assert_eq!(c.next_timeout(), Some(3_072_020));
    c.on_timeout(3_072_020, &rnd(3));
    assert!(c.is_closed());
    assert_eq!(c.next_timeout(), None);
}

#[test]
fn idle_timeout() {
    let mut c = established();
    c.on_timeout(30_000_009, &rnd(3));
    assert_eq!(c.phase(), Phase::Open);
    c.on_timeout(30_000_010, &rnd(3));
    assert!(c.is_closed());
    assert_eq!(c.poll_transmit(30_000_010), None);
    assert_eq!(c.next_timeout(), None);
}

#[test]
fn idle_refreshed_by_packet() {
    let mut c = established();
    c.on_datagram(0, 50, vec![one(0, vec![Frame::Ping])], 20_000_000, &rnd(3));
    c.on_timeout(30_000_010, &rnd(3));
    assert_eq!(c.phase(), Phase::Open);
}

#[test]
fn idle_refreshed_by_send() {
    let mut c = established();
    c.on_datagram(0, 50, vec![one(0, vec![stream(0, 0, b"GET", true)])], 1_000_000, &rnd(3));
    assert_eq!(c.stream_write(0, b"ok", true), Ok(2));
    assert!(c.poll_transmit(20_000_000).is_some());
    c.on_timeout(31_000_010, &rnd(3));
    assert_eq!(c.phase(), Phase::Open);
}

// =============================================================================
// PTO
// =============================================================================

/// A probe with nothing to retransmit: a STREAM packet in flight, its stream reset, the
/// RESET_STREAM acked; a PTO then finds nothing to resend. One PING goes, and `probe_1` clears,
/// so the next poll has nothing.
#[test]
fn ping_probe() {
    let mut c = established();
    c.on_datagram(0, 50, vec![one(0, vec![Frame::Ack(A(0, 0, 0, vec![]))])], 30, &rnd(3));
    assert_eq!(c.sent_inflight_len(PacketKind::OneRtt), 0);
    assert_eq!(c.stream_write(3, b"x", false), Ok(1));
    let a = c.poll_transmit(40).unwrap();
    assert!(has_stream(&a));
    c.stream_reset(3, 7);
    let b = c.poll_transmit(41).unwrap();
    assert!(frames_on(&b).iter().any(|f| matches!(f, Frame::ResetStream { .. })));
    assert_eq!(c.sent_inflight_len(PacketKind::OneRtt), 2);
    let pn = b.packets[0].pn;
    c.on_datagram(0, 50, vec![one(1, vec![Frame::Ack(A(pn, 0, 0, vec![]))])], 42, &rnd(3));
    assert_eq!(c.sent_inflight_len(PacketKind::OneRtt), 1);

    // The STREAM record's time, not the acked RESET_STREAM's: the last in flight.
    let t = c.next_timeout().unwrap();
    assert_eq!(t, 40 + PTO);
    c.on_timeout(t, &rnd(3));
    assert_eq!(c.sent_inflight_len(PacketKind::OneRtt), 0);
    let p = c.poll_transmit(t).unwrap();
    let only: Vec<&Frame> = frames_on(&p).into_iter().filter(|f| !matches!(f, Frame::Ack(_))).collect();
    assert_eq!(only, vec![&Frame::Ping]);
    assert_eq!(c.poll_transmit(t), None);
    assert_eq!(c.sent_inflight_len(PacketKind::OneRtt), 1);
    assert_eq!(c.next_timeout(), Some(t + 2 * PTO));
}

#[test]
fn acked_crypto_not_resent() {
    let mut c = conn();
    drain(&mut c, 0);
    c.crypto_write(PacketKind::Initial, &[0xaa; 100]);
    let d = c.poll_transmit(0).unwrap();
    assert!(has_crypto(&d));
    let pn = d.packets[0].pn;
    c.crypto_write(PacketKind::Initial, &[0xbb; 10]);
    let d2 = c.poll_transmit(0).unwrap();
    assert!(has_crypto(&d2));
    c.on_datagram(0, 1200, vec![ini(3, vec![Frame::Ack(A(pn, 0, 0, vec![]))])], 1, &rnd(3));
    let t = c.next_timeout().unwrap();
    c.on_timeout(t, &rnd(3));
    let v = drain(&mut c, t);
    let crypto: Vec<&Frame> =
        v.iter().flat_map(frames_on).filter(|f| matches!(f, Frame::Crypto { .. })).collect();
    // Only the unacknowledged write at offset 100 returns.
    assert_eq!(crypto, vec![&Frame::Crypto { offset: 100, data: vec![0xbb; 10] }]);
}

#[test]
fn acked_stream_not_resent_after_pto() {
    let mut c = established();
    c.on_datagram(0, 50, vec![one(0, vec![stream(0, 0, b"GET", true)])], 30, &rnd(3));
    assert_eq!(c.stream_write(0, b"ok", true), Ok(2));
    let d = c.poll_transmit(30).unwrap();
    assert!(d.packets[0].frames.contains(&stream(0, 0, b"ok", true)));
    assert_eq!(c.stream_write(3, b"more", false), Ok(4));
    let d2 = c.poll_transmit(30).unwrap();
    assert!(has_stream(&d2));
    let pn = d.packets[0].pn;
    c.on_datagram(0, 50, vec![one(1, vec![Frame::Ack(A(pn, 0, 0, vec![]))])], 31, &rnd(3));
    let t = c.next_timeout().unwrap();
    c.on_timeout(t, &rnd(3));
    let v = drain(&mut c, t);
    let frames: Vec<&Frame> = v.iter().flat_map(frames_on).collect();
    assert!(!frames.iter().any(|f| matches!(f, Frame::Stream { stream_id: 0, .. })));
    assert!(frames.iter().any(|f| matches!(f, Frame::Stream { stream_id: 3, .. })));
}

#[test]
fn pto_requeue_crypto() {
    let mut c = conn();
    drain(&mut c, 0);
    c.crypto_write(PacketKind::Initial, &[0xaa; 100]);
    let d = c.poll_transmit(0).unwrap();
    assert_eq!(d.packets[0].kind, PacketKind::Initial);
    assert_eq!(d.packets[0].pn, 1);
    assert_eq!(d.packets[0].frames, vec![Frame::Crypto { offset: 0, data: vec![0xaa; 100] }]);
    assert_eq!(datagram_len(&d), 1200);
    assert_eq!(c.next_timeout(), Some(999_000));
    c.on_timeout(999_000, &rnd(3));
    let d = c.poll_transmit(999_000).unwrap();
    assert_eq!(d.packets[0].kind, PacketKind::Initial);
    assert_eq!(d.packets[0].pn, 2);
    assert_eq!(d.packets[0].frames, vec![Frame::Crypto { offset: 0, data: vec![0xaa; 100] }]);
    assert_eq!(datagram_len(&d), 1200);
    assert_eq!(c.next_timeout(), Some(2_997_000));
}

#[test]
fn handshake_done_retransmitted() {
    let mut c = conn();
    c.on_peer_params(&ptp(), 10);
    c.on_handshake_complete(b"h3", 10, &rnd(2));
    let d = c.poll_transmit(10).unwrap();
    assert_eq!(d.packets[0].pn, 0);
    let r = rnd(2);
    let four = || vec![Frame::HandshakeDone, ncid(1, &r, 0), ncid(2, &r, 24), ncid(3, &r, 48)];
    assert_eq!(d.packets[0].frames, four());
    assert_eq!(c.next_timeout(), Some(1_024_010));
    c.on_timeout(1_024_010, &rnd(2));
    let d = c.poll_transmit(1_024_010).unwrap();
    assert_eq!(d.packets[0].pn, 1);
    assert_eq!(d.packets[0].frames, four());
    c.on_datagram(0, 50, vec![one(0, vec![Frame::Ack(A(1, 0, 0, vec![]))])], 1_024_020, &rnd(2));
    assert_eq!(c.poll_transmit(1_024_020), None);
    assert_eq!(c.next_timeout(), Some(1_024_020 + 30_000_000));
}

#[test]
fn pto_halves_cwnd() {
    let mut p = ptp();
    p.initial_max_data = 1 << 30;
    p.initial_max_stream_data_bidi_local = 1 << 30;
    let mut c = established_tx_with(p);
    c.on_datagram(0, 1200, vec![one(0, vec![stream(0, 0, b"GET", true)])], 30, &rnd(3));
    assert_eq!(c.stream_write(0, &[7; 100_000], true), Ok(100_000));
    let v = drain(&mut c, 30);
    assert_eq!(v.iter().filter(|d| eliciting(d)).count(), 9);
    let t = c.next_timeout().unwrap();
    c.on_timeout(t, &rnd(3));
    let v = drain(&mut c, t);
    assert_eq!(v.iter().filter(|d| eliciting(d)).count(), 5);
}

/// RFC 9002 §6.2.2.1: no PTO while the anti-amplification limit blocks sending.
#[test]
fn amp_blocked_no_pto() {
    let mut c = conn();
    c.crypto_write(PacketKind::Initial, &[0xaa; 5000]);
    assert_eq!(drain(&mut c, 0).len(), 3);
    assert_eq!(c.path_budget(0), Some(0));
    assert_eq!(c.next_timeout(), Some(30_000_000));
    let n = c.sent_inflight_len(PacketKind::Initial);
    c.on_timeout(999_000, &rnd(3));
    assert_eq!(c.sent_inflight_len(PacketKind::Initial), n);
    assert_eq!(c.poll_transmit(999_000), None);
}

// =============================================================================
// Path validation
// =============================================================================

#[test]
fn validation_failure_reverts() {
    let (mut c, _) = rebound();
    assert_eq!(c.active_path(), 1);
    c.on_timeout(30 + 3 * PTO, &rnd(6));
    assert_eq!(c.active_path(), 0);
    assert_eq!(c.phase(), Phase::Open);
    assert_eq!(c.path_state(1), Some(quic::path::PathState::Unvalidated));
    c.stream_write(3, b"data", false).unwrap();
    let v = settle(&mut c, 30 + 3 * PTO);
    let d = v.iter().find(|d| has_stream(d)).unwrap();
    assert_eq!(d.path, 0);
}

#[test]
fn no_validated_path_closes() {
    let mut c = conn();
    c.on_peer_params(&ptp(), 10);
    c.on_handshake_complete(b"h3", 10, &rnd(2));
    c.on_datagram(0, 100, vec![one(0, vec![Frame::Ping])], 20, &rnd(3));
    c.on_datagram(1, 100, vec![one(1, vec![Frame::Ping])], 20, &rnd(4));
    assert_eq!(c.active_path(), 1);
    let v = drain(&mut c, 20);
    assert!(v.iter().any(|d| d.path == 1 && has_challenge(d)));
    assert!(!v.iter().any(has_close));
    c.on_timeout(20 + 3 * PTO, &rnd(5));
    assert!(c.is_closed());
    assert_eq!(c.poll_transmit(20 + 3 * PTO), None);
    assert_eq!(c.next_timeout(), None);
}

/// Path 1 is validated, path 2 active, and a retirement leaves path 1 with no CID. Returns with
/// path 2's challenge sent and everything else quiet.
fn fallback_lost_its_cid() -> Connection {
    let mut c = four_cid_conn();
    c.on_datagram(0, 1200, vec![one(1, vec![new_cid(1, 0, 0xd1), new_cid(2, 0, 0xd2)])], 20, &rnd(5));
    drain(&mut c, 20);
    let r = rnd(2);
    c.on_datagram(1, 1200, vec![one_on(2, &r[0..8], vec![Frame::Ping])], 21, &rnd(6));
    drain(&mut c, 21);
    c.on_datagram(1, 1200, vec![one_on(3, &r[0..8], vec![Frame::PathResponse(slice8(&rnd(6), 96))])], 22, &rnd(7));
    assert_eq!(c.path_state(1), Some(quic::path::PathState::Validated));
    drain(&mut c, 22);
    c.on_datagram(2, 1200, vec![one_on(4, &r[24..32], vec![Frame::Ping])], 30, &rnd(8));
    assert_eq!(c.active_path(), 2);
    drain(&mut c, 30);
    // Retires seq 0 and seq 1: path 0 takes d3, the last unused one, and path 1 has none.
    c.on_datagram(2, 1200, vec![one_on(5, &r[24..32], vec![new_cid(3, 2, 0xd3)])], 31, &rnd(9));
    drain(&mut c, 31);
    assert_eq!(c.path_dcid(1), None);
    c
}

/// §9.5: the fallback path takes an unused CID of its own.
#[test]
fn fallback_takes_unused_cid() {
    let mut c = fallback_lost_its_cid();
    c.on_datagram(2, 1200, vec![one_on(6, &rnd(2)[24..32], vec![new_cid(4, 2, 0xd4)])], 32, &rnd(10));
    assert_eq!(c.path_dcid(1), None);
    drain(&mut c, 32);
    c.on_timeout(30 + 3 * PTO, &rnd(11));
    assert_eq!(c.active_path(), 1);
    assert_eq!(c.path_dcid(1), Some(D(0xd4).to_vec()));
    c.stream_write(3, b"data", false).unwrap();
    let v = drain(&mut c, 30 + 3 * PTO);
    let d = v.iter().find(|d| has_stream(d)).unwrap();
    assert_eq!(d.path, 1);
    assert_eq!(d.packets[0].dcid, D(0xd4).to_vec());
}

/// No unused CID either: nothing may be sent there, so the connection closes silently.
#[test]
fn fallback_no_cid_closes() {
    let mut c = fallback_lost_its_cid();
    c.on_timeout(30 + 3 * PTO, &rnd(11));
    assert!(c.is_closed());
    assert_eq!(c.poll_transmit(30 + 3 * PTO), None);
}

/// Step 6: a CID slice that was refused at the handshake is retried with the next `rand`.
#[test]
fn timeout_issues_cids() {
    let mut c = conn();
    c.on_peer_params(&ptp(), 10);
    c.on_handshake_complete(b"h3", 10, &[7u8; 129]);
    let count = |v: &[OutDatagram]| {
        v.iter().flat_map(frames_on).filter(|f| matches!(f, Frame::NewConnectionId { .. })).count()
    };
    assert_eq!(count(&drain(&mut c, 10)), 1);
    c.on_timeout(11, &rnd(3));
    assert_eq!(count(&drain(&mut c, 11)), 2);
}

/// Steps 4 and 5 only while Open: a validation expiring in Closing leaves the active path alone, and
/// the connection closes at its deadline, the only wake `next_timeout` names.
#[test]
fn closing_keeps_path() {
    let (mut c, _) = rebound();
    c.close(0, false, b"", 31);
    let d = c.next_timeout().unwrap();
    assert_eq!(d, 31 + 3 * PTO);
    c.on_timeout(30 + 3 * PTO, &rnd(6));
    assert_eq!(c.phase(), Phase::Closing);
    assert_eq!(c.active_path(), 1);
    assert_eq!(c.next_timeout(), Some(d));
    c.on_timeout(d, &rnd(7));
    assert!(c.is_closed());
    assert_eq!(c.active_path(), 1);
}

/// No validated path either: still nothing before the deadline, where the connection closes.
#[test]
fn closing_no_validated_path_waits() {
    let mut c = conn();
    c.on_peer_params(&ptp(), 10);
    c.on_handshake_complete(b"h3", 10, &rnd(2));
    c.on_datagram(0, 100, vec![one(0, vec![Frame::Ping])], 20, &rnd(3));
    c.on_datagram(1, 100, vec![one(1, vec![Frame::Ping])], 20, &rnd(4));
    drain(&mut c, 20);
    c.close(0, false, b"", 21);
    let d = c.next_timeout().unwrap();
    assert_eq!(d, 21 + 3 * PTO);
    c.on_timeout(20 + 3 * PTO, &rnd(5));
    assert_eq!(c.phase(), Phase::Closing);
    assert_eq!(c.next_timeout(), Some(d));
    c.on_timeout(d, &rnd(6));
    assert!(c.is_closed());
    assert_eq!(c.next_timeout(), None);
}

#[test]
fn mtu_probe_failure_moves_off() {
    let (mut c, _) = rebound();
    let r5 = rnd(5);
    c.on_datagram(1, 1200, vec![one(2, vec![Frame::PathResponse(slice8(&r5, 96))])], 40, &rnd(6));
    let v = drain(&mut c, 40);
    assert!(v.iter().any(|d| d.path == 1 && has_challenge(d)));
    assert_eq!(c.active_path(), 1);

    let t = 40 + 3 * PTO;
    c.on_timeout(t, &rnd(7));
    assert_eq!(c.active_path(), 0);
    assert_eq!(c.phase(), Phase::Open);
    c.stream_write(3, b"data", false).unwrap();
    let v = drain(&mut c, t);
    assert!(v.iter().any(|d| d.path == 0 && has_stream(d)));
    assert!(!v.iter().any(|d| d.path == 1 && has_stream(d)));
    assert!(!v.iter().any(|d| d.path == 1));

    // The peer sends from there: one probe, §14.2's only traffic, and it stays off the path.
    c.on_datagram(1, 1200, vec![one(3, vec![Frame::Ping])], t + 1, &rnd(8));
    assert_eq!(c.active_path(), 0);
    c.stream_write(3, b"more", false).unwrap();
    let v = drain(&mut c, t + 1);
    assert!(!v.iter().any(|d| d.path == 1 && has_stream(d)));
    let probes: Vec<&OutDatagram> = v.iter().filter(|d| d.path == 1).collect();
    assert_eq!(probes.len(), 1);
    assert!(has_frame(probes[0], &Frame::PathChallenge(slice8(&rnd(8), 96))));
    assert_eq!(datagram_len(probes[0]), 1200);
    // Its answer restores the path, and the peer's next packet migrates back.
    c.on_datagram(1, 1200, vec![one(4, vec![Frame::PathResponse(slice8(&rnd(8), 96))])], t + 2, &rnd(9));
    c.on_datagram(1, 1200, vec![one(5, vec![Frame::Ping])], t + 3, &rnd(9));
    assert_eq!(c.active_path(), 1);
}

#[test]
fn validation_resets_recovery() {
    let mut c = established();
    c.on_timeout(10 + PTO, &rnd(3));
    let t = 10 + PTO;
    drain(&mut c, t);
    assert_eq!(c.next_timeout(), Some(t + 2 * PTO));
    c.on_datagram(1, 1200, vec![one(1, vec![stream(0, 0, b"GET", true)])], t + 1, &rnd(5));
    drain(&mut c, t + 1);
    c.on_datagram(1, 1200, vec![one(2, vec![Frame::PathResponse(slice8(&rnd(5), 96))])], t + 2, &rnd(6));
    assert_eq!(c.stream_write(0, b"ok", true), Ok(2));
    let v = drain(&mut c, t + 2);
    assert!(v.iter().any(has_stream));
    assert_eq!(c.next_timeout(), Some(t + 2 + PTO));
}

/// An MTU probe's answer is no new address: §9.4's reset does not apply.
#[test]
fn revalidation_keeps_pto_mtu_probe() {
    let (mut c, _) = rebound();
    c.on_datagram(1, 1200, vec![one(2, vec![Frame::PathResponse(slice8(&rnd(5), 96))])], 40, &rnd(6));
    c.stream_write(0, b"ok", true).unwrap();
    drain(&mut c, 40);
    // on_path_validated left `pto_count` at 0.
    let t = 40 + PTO;
    assert_eq!(c.next_timeout(), Some(t));
    c.on_timeout(t, &rnd(7));
    assert!(drain(&mut c, t).iter().any(has_stream));
    c.on_datagram(1, 1200, vec![one(3, vec![Frame::PathResponse(slice8(&rnd(6), 96))])], t + 1, &rnd(8));
    // Past the ACK timer, so only the PTO is left.
    drain(&mut c, t + 25_001);
    assert_eq!(c.next_timeout(), Some(t + 2 * PTO));
}

/// §9.3.3's recheck of the old path, likewise.
#[test]
fn revalidation_keeps_pto_old_path() {
    let mut c = established();
    c.on_datagram(1, 1200, vec![one(1, vec![stream(0, 0, b"GET", true)])], 30, &rnd(5));
    drain(&mut c, 30);
    drain(&mut c, 25_030);
    let t = 10 + PTO;
    assert_eq!(c.next_timeout(), Some(t));
    c.on_timeout(t, &rnd(7));
    drain(&mut c, t);
    c.on_datagram(0, 1200, vec![one(2, vec![Frame::PathResponse(slice8(&rnd(5), 104))])], t + 1, &rnd(8));
    drain(&mut c, t + 25_001);
    assert_eq!(c.next_timeout(), Some(t + 2 * PTO));
}

fn four_cid_conn() -> Connection {
    let mut l = ltp();
    l.active_connection_id_limit = 4;
    let mut c = Connection::accept(&ini(2, first_frames()), 1200, 0, 0, &rnd(1), &l).unwrap();
    c.on_datagram(0, 1200, vec![ini(2, first_frames())], 0, &rnd(1));
    c.on_datagram(0, 1200, vec![hs(0, vec![Frame::Ping])], 10, &rnd(9));
    c.on_peer_params(&ptp(), 10);
    c.on_handshake_complete(b"h3", 10, &rnd(2));
    drain(&mut c, 10);
    c
}

/// Path 1's challenge is owed when a retirement clears its only CID: nothing can send it, so it
/// adds no timer. The connection does not spin, the active path is unaffected, and once a CID
/// comes back the challenge goes. Returns at that send, with its time.
fn owed_challenge_sent_late() -> (Connection, u64) {
    let mut c = four_cid_conn();
    c.on_datagram(0, 1200, vec![one(1, vec![new_cid(1, 0, 0xd1), new_cid(2, 0, 0xd2)])], 20, &rnd(5));
    drain(&mut c, 20);
    let r = rnd(2);
    // Two migrations, unpolled: path 0's recheck and path 1's challenge are both owed.
    c.on_datagram(1, 1200, vec![one_on(2, &r[0..8], vec![Frame::Ping])], 30, &rnd(6));
    c.on_datagram(2, 1200, vec![one_on(3, &r[24..32], vec![Frame::Ping])], 30, &rnd(7));
    assert_eq!(c.active_path(), 2);
    assert!(c.challenge_owed(1));
    // Retires seq 0 and seq 1: path 0 takes d3, path 1 is left with no CID.
    c.on_datagram(2, 1200, vec![one_on(4, &r[24..32], vec![new_cid(3, 2, 0xd3)])], 30, &rnd(8));
    assert_eq!(c.path_dcid(1), None);
    assert!(c.challenge_owed(1));
    let v = settle(&mut c, 30);
    assert!(v.iter().all(|d| d.path != 1));

    // Path 2 and path 0's sent challenges expire; path 1 is untouched, and nothing repeats.
    let t = 30 + 3 * PTO;
    c.on_timeout(t, &rnd(9));
    assert!(c.challenge_owed(1));
    assert_eq!(c.active_path(), 0);
    let v = settle(&mut c, t);
    assert!(v.iter().all(|d| d.path != 1));

    // A CID for path 1: its challenge goes out now.
    c.on_datagram(0, 1200, vec![one_on(5, &L0, vec![new_cid(4, 2, 0xd4)])], t + 1, &rnd(10));
    assert_eq!(c.path_dcid(1), Some(D(0xd4).to_vec()));
    let v = drain(&mut c, t + 1);
    assert!(v.iter().any(|d| d.path == 1 && has_challenge(d)));
    assert!(!c.challenge_owed(1));
    (c, t + 1)
}

#[test]
fn owed_challenge_cleared_dcid() {
    let (mut c, sent) = owed_challenge_sent_late();
    // The PTO doubled at `t`: 3·2·PTO from the send.
    let e = sent + 6 * PTO;
    c.on_timeout(e, &rnd(11));
    assert_eq!(c.path_state(1), Some(quic::path::PathState::Unvalidated));
    assert_eq!(c.active_path(), 0);
    settle(&mut c, e);
}

/// §8.2.4's timer starts at the send: a start time from when the challenge was drawn would expire
/// it here, before the peer has had its 3·PTO.
#[test]
fn challenge_clock_starts_at_send() {
    let (mut c, _) = owed_challenge_sent_late();
    c.on_timeout(30 + 6 * PTO, &rnd(11));
    assert_eq!(c.path_state(1), Some(quic::path::PathState::Validating));
}

// =============================================================================
// `next_timeout` is later than `now` once settled (3d2 Task 3 review I1, I2)
// =============================================================================

fn has_ack(d: &OutDatagram) -> bool {
    frames_on(d).iter().any(|f| matches!(f, Frame::Ack(_)))
}

/// A rebind on so small a datagram that its challenge spends the budget: no ACK can follow.
fn ack_stalled() -> (Connection, u64) {
    let mut c = established();
    c.on_datagram(1, 15, vec![one(1, vec![stream(0, 0, b"GET", true)])], 30, &rnd(5));
    let v = drain(&mut c, 30);
    assert!(v.iter().any(|d| d.path == 1 && has_challenge(d)));
    assert!(!v.iter().any(has_ack));
    assert!(c.path_budget(1).unwrap() < 30);
    (c, 30)
}

/// §13.2.1: one range fits a small budget, and it goes (review M3).
#[test]
fn ack_placed_within_small_budget() {
    let (mut c, _) = rebound();
    let v = drain(&mut c, 25_030);
    assert!(v.iter().any(|d| d.path == 1 && has_ack(d)));
    assert!(c.path_budget(1).unwrap() < 522);
}

/// An ACK reports every remembered range or does not go: here one range would fit and all do not.
#[test]
fn ack_is_full_or_withheld() {
    let mut c = established();
    for n in (1..=41).step_by(2) {
        c.on_datagram(0, 1200, vec![one(n, vec![Frame::Ping])], 20, &rnd(3));
        drain(&mut c, 20);
    }
    drain(&mut c, 25_020);
    let t = 25_030;
    c.on_datagram(1, 30, vec![one(43, vec![stream(0, 0, b"GET", true)])], t, &rnd(5));
    let v = settle(&mut c, t + 25_000);
    assert!(v.iter().any(|d| d.path == 1 && has_challenge(d)));
    assert!(!v.iter().any(has_ack));
    assert!(c.path_budget(1).unwrap() >= 40);
}

/// The ACK that cannot be placed keeps no deadline, and the peer cannot repeat the stall.
#[test]
fn ack_stalled_by_budget_no_wake_loop() {
    let (mut c, t0) = ack_stalled();
    assert!(!settle(&mut c, t0 + 25_000).iter().any(has_ack));
    let t = 30 + 3 * PTO;
    c.on_timeout(t, &rnd(7));
    assert_eq!(c.active_path(), 0);
    settle(&mut c, t);
    c.on_datagram(1, 1, vec![one(2, vec![Frame::Ping])], t + 1, &rnd(8));
    assert_eq!(c.active_path(), 1);
    settle(&mut c, t + 1 + 25_000);
}

/// A late wake finds two spaces' PTOs passed: both fire, so nothing is left at or before `now`.
#[test]
fn two_spaces_late_wake() {
    let mut c = conn();
    c.crypto_write(PacketKind::Initial, &[0xaa; 100]);
    c.crypto_write(PacketKind::Handshake, &[0xbb; 100]);
    drain(&mut c, 0);
    assert!(c.sent_inflight_len(PacketKind::Initial) > 0);
    assert!(c.sent_inflight_len(PacketKind::Handshake) > 0);
    let now = 5_000_000;
    c.on_timeout(now, &rnd(3));
    assert_eq!(c.sent_inflight_len(PacketKind::Initial), 0);
    assert_eq!(c.sent_inflight_len(PacketKind::Handshake), 0);
    settle(&mut c, now);
}

/// The deadline holds wherever the ACK can go: budget arrives past it, and it goes at once.
#[test]
fn ack_after_budget() {
    let (mut c, t0) = ack_stalled();
    let t = t0 + 25_000;
    settle(&mut c, t);
    c.on_datagram(1, 200, vec![one(2, vec![Frame::Padding])], t + 1, &rnd(7));
    assert!(settle(&mut c, t + 1).iter().any(|d| d.path == 1 && has_ack(d)));
}

/// Validation lifts the budget.
#[test]
fn ack_after_validation() {
    let (mut c, t0) = ack_stalled();
    settle(&mut c, t0);
    c.on_datagram(1, 25, vec![one(2, vec![Frame::PathResponse(slice8(&rnd(5), 96))])], t0 + 1, &rnd(7));
    assert!(settle(&mut c, t0 + 1).iter().any(|d| d.path == 1 && has_ack(d)));
}

/// A revert makes the ACK sendable on the fallback path in the same wake.
#[test]
fn ack_after_revert() {
    let (mut c, t0) = ack_stalled();
    settle(&mut c, t0);
    let t = 30 + 3 * PTO;
    c.on_timeout(t, &rnd(7));
    assert_eq!(c.active_path(), 0);
    assert!(settle(&mut c, t).iter().any(|d| d.path == 0 && has_ack(d)));
}

/// Review I5: a closed connection registers no new CIDs.
#[test]
fn closed_issues_no_cids() {
    let mut c = conn();
    c.on_peer_params(&ptp(), 10);
    c.on_handshake_complete(b"h3", 10, &[7u8; 129]);
    drain(&mut c, 10);
    let mut u = Vec::new();
    c.poll_cid_updates(&mut u);
    c.on_timeout(40_000_000, &rnd(3));
    assert!(c.is_closed());
    let mut u = Vec::new();
    c.poll_cid_updates(&mut u);
    assert!(u.iter().all(|x| !matches!(x, quic::route::CidUpdate::Add(_))));
}

// =============================================================================
// The 1-byte credit-drip adversary (D4)
// =============================================================================

/// The ACK frame for these distinct packet numbers.
fn ack_of(pns: &[u64]) -> AckFrame {
    let mut s = pns.to_vec();
    s.sort_unstable();
    s.reverse();
    let mut ranges = Vec::new();
    let largest = s[0];
    let mut low = s[0];
    let mut first = None;
    let mut top = s[0];
    let mut pending_gap = 0;
    for &p in &s[1..] {
        if p + 1 == low {
            low = p;
            continue;
        }
        match first {
            None => first = Some(top - low),
            Some(_) => ranges.push((pending_gap, top - low)),
        }
        pending_gap = low - p - 2;
        top = p;
        low = p;
    }
    match first {
        None => first = Some(top - low),
        Some(_) => ranges.push((pending_gap, top - low)),
    }
    AckFrame { largest, delay: 0, first_range: first.unwrap(), ranges, ecn: None }
}

#[test]
fn ack_of_shapes() {
    assert_eq!(ack_of(&[5]), A(5, 0, 0, vec![]));
    assert_eq!(ack_of(&[4, 5]), A(5, 0, 1, vec![]));
    // 9; gap: 8, 7; then 6, 5. gap = 9 - 6 - 2 = 1.
    assert_eq!(ack_of(&[9, 6, 5]), A(9, 0, 0, vec![(1, 1)]));
}

#[test]
fn alternate_ack_range_growth() {
    let mut p = ptp();
    p.initial_max_data = 1 << 30;
    p.initial_max_stream_data_bidi_local = 1;
    let mut c = established_tx_with(p);
    let mut t = 1_000u64;
    let mut peer_pn = 0u64;
    c.on_datagram(0, 1200, vec![one(peer_pn, vec![stream(0, 0, b"GET", true)])], t, &rnd(3));
    peer_pn += 1;
    assert_eq!(c.stream_write(0, &[9; 10_000], true), Ok(10_000));
    let cap = 2 * MAX_SEND_RANGES + 1;
    let mut hi = 0u64;
    let mut new_only = 0u32;
    let mut closed_rounds = 0u32;
    let mut stalls = 0u32;
    let mut to_ack: Vec<u64> = Vec::new();
    for r in 0..300u64 {
        // The peer: every other packet of new bytes acked, one more byte of credit.
        let mut f = Vec::new();
        if !to_ack.is_empty() {
            f.push(Frame::Ack(ack_of(&to_ack)));
            to_ack.clear();
        }
        f.push(Frame::MaxStreamData { stream_id: 0, max: r + 2 });
        t += 1_000;
        c.on_datagram(0, 1200, vec![one(peer_pn, f)], t, &rnd(3));
        peer_pn += 1;
        let (a, _) = c.send_range_counts(0).unwrap();
        let closed = a >= MAX_SEND_RANGES;
        if closed {
            closed_rounds += 1;
        }
        let v = drain(&mut c, t);
        for d in &v {
            for pkt in &d.packets {
                let mut carried = false;
                let mut all_new = true;
                for f in &pkt.frames {
                    if let Frame::Stream { offset, data, .. } = f {
                        if data.is_empty() {
                            continue;
                        }
                        carried = true;
                        if *offset >= hi {
                            hi = offset + data.len() as u64;
                            // No new bytes past the stall until a slot frees.
                            assert!(!closed, "round {r}: new bytes with {a} acked ranges");
                        } else {
                            all_new = false;
                        }
                    }
                }
                if carried && all_new {
                    new_only += 1;
                    if new_only % 2 == 0 {
                        to_ack.push(pkt.pn);
                    }
                }
            }
        }
        let (a, l) = c.send_range_counts(0).unwrap();
        assert!(a <= cap && l <= cap, "round {r}: {a} acked, {l} lost ranges");
        assert!(c.sent_inflight_len(PacketKind::OneRtt) <= 64);
        if r % 20 == 19 {
            // Fire timers until the PTO has declared everything lost.
            let mut fired = 0;
            while c.sent_inflight_len(PacketKind::OneRtt) > 0 {
                t = t.max(c.next_timeout().unwrap());
                c.on_timeout(t, &rnd(4));
                fired += 1;
                assert!(fired < 16);
                if c.sent_inflight_len(PacketKind::OneRtt) > 0 {
                    // An ACK timer: answer it, and look again.
                    drain(&mut c, t);
                }
            }
            stalls += 1;
            let (a, l) = c.send_range_counts(0).unwrap();
            assert!(a <= cap && l <= cap, "round {r}: {a} acked, {l} lost ranges");
        }
        assert_eq!(c.phase(), Phase::Open);
    }
    assert!(stalls >= 15);
    assert!(closed_rounds > 0, "the gate never closed");
}
