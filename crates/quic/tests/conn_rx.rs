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
use quic::route::{CidTable, CidUpdate};
use quic::recv_stream::StreamEvent;
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
    c.on_datagram(0, 1200, vec![ini(2, first_frames())], None, 0, &rnd(1));
    c
}

fn established_with(p: TransportParams) -> Connection {
    let mut c = conn();
    c.on_datagram(0, 1200, vec![hs(0, vec![Frame::Ping])], None, 10, &rnd(9));
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

/// No application protocol negotiated closes with 0x0178 even before the peer's transport
/// parameters (RFC 9001 §8.1), not with INTERNAL_ERROR.
#[test]
fn alpn_mismatch_without_params() {
    let mut c = conn();
    c.on_handshake_complete(b"h2", 1, &rnd(2));
    assert_eq!(c.phase(), Phase::Closing);
    assert_eq!(c.close_info(), &Some((false, 0x178, vec![])));
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
fn alert_after_close_keeps_code() {
    let mut c = peer_params_failed();
    c.on_tls_alert(0x28, 2);
    assert_eq!(c.phase(), Phase::Closing);
    assert_eq!(c.close_info(), &Some((false, 0x08, vec![])));
}

#[test]
fn tls_alert_top_of_range() {
    let mut c = conn();
    c.on_tls_alert(0xff, 1);
    assert_eq!(c.close_info(), &Some((false, 0x1ff, vec![])));
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

/// `discard` leaves the Handshake space fresh CRYPTO buffers (TRUSTED.md's capacity paragraph).
#[test]
fn discard_frees_crypto() {
    let mut c = conn();
    c.crypto_write(PacketKind::Handshake, &[1; 10]);
    c.on_datagram(0, 1200, vec![hs(0, vec![Frame::Crypto { offset: 5, data: vec![2; 10] }])], None, 10, &rnd(9));
    assert!(c.crypto_capacity(PacketKind::Handshake) > 10);
    c.on_peer_params(&ptp(), 10);
    c.on_handshake_complete(b"h3", 10, &rnd(2));
    assert!(c.handshake_complete());
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

/// One datagram with in-order and out-of-order CRYPTO data: 500 out-of-order bytes are held, so
/// the §7.5 floor (4096) applies even though 13000 in-order bytes are still unread.
#[test]
fn crypto_in_and_out_of_order_one_datagram_ok() {
    let mut c = conn();
    let f = vec![Frame::Crypto { offset: 100, data: vec![1; 12900] }, Frame::Crypto { offset: 16000, data: vec![2; 500] }];
    c.on_datagram(0, 17000, vec![ini(3, f)], None, 1, &rnd(3));
    assert_eq!(c.phase(), Phase::Open);
    assert_eq!(c.crypto_end(PacketKind::Initial), 16500);
    let mut out = Vec::new();
    c.crypto_read(PacketKind::Initial, &mut out);
    assert_eq!(out, vec![1; 13000]);
}

/// One byte past the window measured from the contiguous end closes with CRYPTO_BUFFER_EXCEEDED.
#[test]
fn crypto_past_contiguous_window_0x0d() {
    let mut c = conn();
    let f = vec![Frame::Crypto { offset: 100, data: vec![1; 12900] }, Frame::Crypto { offset: 13000 + 16384, data: vec![2] }];
    c.on_datagram(0, 17000, vec![ini(3, f)], None, 1, &rnd(3));
    assert_eq!(c.phase(), Phase::Closing);
    assert_eq!(c.close_info(), &Some((false, 0x0d, vec![])));
}

#[test]
fn small_datagram_initial_dropped() {
    let mut c = conn();
    c.on_datagram(0, 1199, vec![ini(3, vec![Frame::Ping])], None, 1, &rnd(3));
    assert_eq!(c.largest_pn(PacketKind::Initial), Some(2));
    assert_eq!(c.phase(), Phase::Open);
}

#[test]
fn coalesced_dcid_rule() {
    let mut c = conn();
    // `ini` has DCID S1, `hs` has L0: §12.2 ignores the second packet.
    c.on_datagram(0, 1200, vec![ini(3, vec![Frame::Ping]), hs(0, vec![Frame::Ping])], None, 1, &rnd(3));
    assert_eq!(c.largest_pn(PacketKind::Handshake), None);
    assert_eq!(c.largest_pn(PacketKind::Initial), Some(3));
}

#[test]
fn handshake_validates_and_discards() {
    let mut c = conn();
    c.on_datagram(0, 1100, vec![ini2(3, vec![Frame::Ping]), hs(0, vec![Frame::Ping])], None, 1, &rnd(3));
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
    c.on_datagram(0, 1200, vec![p], None, 1, &rnd(3));
    assert_eq!(c.largest_pn(PacketKind::Initial), Some(2));
    assert_eq!(c.phase(), Phase::Open);
}

#[test]
fn duplicate_pn() {
    let mut c = conn();
    let mut out = Vec::new();
    c.crypto_read(PacketKind::Initial, &mut out);
    c.on_datagram(0, 1200, vec![ini(2, vec![Frame::Crypto { offset: 100, data: vec![2; 10] }])], None, 1, &rnd(3));
    let mut out = Vec::new();
    c.crypto_read(PacketKind::Initial, &mut out);
    assert_eq!(out, Vec::<u8>::new());
}

#[test]
fn one_rtt_before_complete() {
    let mut c = conn();
    c.on_datagram(0, 1200, vec![one(0, vec![Frame::Ping])], None, 1, &rnd(3));
    assert_eq!(c.largest_pn(PacketKind::OneRtt), None);
}

#[test]
fn ack_of_unsent() {
    let mut c = conn();
    c.on_datagram(0, 1200, vec![ini(3, vec![Frame::Ack(A(9, 0, 0, vec![]))])], None, 1, &rnd(3));
    assert_eq!(c.phase(), Phase::Closing);
    assert_eq!(c.close_info(), &Some((false, 0x0a, vec![])));
}

#[test]
fn connection_close_drains() {
    let mut c = established_rx();
    c.on_datagram(0, 1200, vec![one(0, vec![CC(false, 0, &[])])], None, 11, &rnd(3));
    assert_eq!(c.phase(), Phase::Draining);
    assert!(!c.streams_live());
}

#[test]
fn long_header_other_path_dropped() {
    let mut c = conn();
    c.on_datagram(1, 1200, vec![ini(3, vec![Frame::Ping])], None, 1, &rnd(3));
    assert_eq!(c.largest_pn(PacketKind::Initial), Some(2));
}

#[test]
fn challenge_flood_dropped() {
    let mut c = established_rx();
    let f = (1..=5).map(|x| Frame::PathChallenge(D(x))).collect();
    c.on_datagram(0, 1200, vec![one(0, f)], None, 11, &rnd(3));
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

#[test]
fn spoofed_datagrams_take_no_slot() {
    let mut c = established_rx();
    for q in 1..=3 {
        c.on_datagram(q, 40, vec![], None, 11, &rnd(3));
        assert_eq!(c.path_state(q), None);
    }
    c.on_datagram(9, 40, vec![one(0, vec![Frame::Ping])], None, 12, &rnd(3));
    assert_eq!(c.largest_pn(PacketKind::OneRtt), Some(0));
    assert!(c.path_state(9).is_some());
}

#[test]
fn replay_takes_no_slot() {
    let mut c = established_rx();
    c.on_datagram(0, 40, vec![one(0, vec![Frame::Ping])], None, 11, &rnd(3));
    c.on_datagram(1, 40, vec![one(0, vec![Frame::Ping])], None, 12, &rnd(3));
    assert_eq!(c.path_state(1), None);
    assert_eq!(c.path_budget(1), None);
}

#[test]
fn accepted_datagram_counted_once() {
    let mut c = established_rx();
    c.on_datagram(0, 40, vec![one(0, vec![Frame::Ping])], None, 11, &rnd(3));
    // A replay ahead of two fresh packets: the whole datagram counts, once.
    let d = vec![one(0, vec![Frame::Ping]), one(1, vec![Frame::Ping]), one(2, vec![Frame::Ping])];
    c.on_datagram(7, 100, d, None, 12, &rnd(3));
    assert_eq!(c.largest_pn(PacketKind::OneRtt), Some(2));
    assert_eq!(c.path_budget(7), Some(300));
    // Known now, so a datagram with no accepted packet counts.
    c.on_datagram(7, 40, vec![], None, 13, &rnd(3));
    assert_eq!(c.path_budget(7), Some(420));
}

#[test]
fn closing_unknown_path_uncounted() {
    let mut c = peer_params_failed();
    c.on_datagram(5, 1200, vec![], None, 2, &rnd(3));
    assert_eq!(c.path_state(5), None);
}

#[test]
fn fifth_path_dropped() {
    let mut c = established_rx();
    for q in 1..=3u8 {
        c.on_datagram(q as u64, 40, vec![one(q as u64, vec![Frame::Ping])], None, 11, &rnd(3));
    }
    c.on_datagram(4, 40, vec![one(4, vec![Frame::Ping])], None, 12, &rnd(3));
    assert_eq!(c.largest_pn(PacketKind::OneRtt), Some(3));
    assert_eq!(c.path_state(4), None);
}

fn stream(id: u64, data: &[u8], fin: bool) -> Frame {
    Frame::Stream { stream_id: id, offset: 0, data: data.to_vec(), fin }
}

fn ncid(seq: u64, rpt: u64, x: u8) -> Frame {
    Frame::NewConnectionId { seq, retire_prior_to: rpt, cid: D(x).to_vec(), reset_token: [x.wrapping_add(0x10); 16] }
}

fn r2() -> Vec<u8> {
    rnd(2)[0..8].to_vec()
}

fn updates(c: &mut Connection) -> Vec<CidUpdate> {
    let mut u = Vec::new();
    c.poll_cid_updates(&mut u);
    u
}

#[test]
fn stream_events() {
    let mut c = established_rx();
    c.on_datagram(0, 100, vec![one(0, vec![stream(0, b"GET", true)])], None, 30, &rnd(3));
    let mut ev = Vec::new();
    c.poll_stream_events(&mut ev);
    assert_eq!(ev, vec![StreamEvent::Data { id: 0, data: b"GET".to_vec(), fin: true }]);
    assert_eq!(c.stream_write(0, b"ok", true), Ok(2));
}

/// A 1-RTT packet coalesced with the client's Finished comes before `on_handshake_complete`, so the
/// gate drops it (RFC 9001 §5.7). The Phase 4 binding note's recipe: hand it over again afterwards,
/// with length 0, and it is processed.
#[test]
fn early_one_rtt_refed() {
    let mut c = conn();
    c.on_peer_params(&ptp(), 10);
    let p = || one(0, vec![stream(0, b"GET", true)]);
    c.on_datagram(0, 1200, vec![hs(0, vec![Frame::Ping]), p()], None, 10, &rnd(9));
    assert_eq!(c.largest_pn(PacketKind::Handshake), Some(0));
    assert_eq!(c.largest_pn(PacketKind::OneRtt), None);
    c.on_handshake_complete(b"h3", 10, &rnd(2));
    let mut ev = Vec::new();
    c.poll_stream_events(&mut ev);
    assert!(ev.is_empty());
    c.on_datagram(0, 0, vec![p()], None, 10, &rnd(3));
    assert_eq!(c.largest_pn(PacketKind::OneRtt), Some(0));
    c.poll_stream_events(&mut ev);
    assert_eq!(ev, vec![StreamEvent::Data { id: 0, data: b"GET".to_vec(), fin: true }]);
}

#[test]
fn stream_write_partial() {
    let mut p = ptp();
    p.initial_max_data = 1 << 30;
    p.initial_max_stream_data_bidi_local = 1 << 30;
    let mut c = established_with(p);
    c.on_datagram(0, 100, vec![one(0, vec![stream(0, b"GET", false)])], None, 30, &rnd(3));
    assert_eq!(c.stream_write(0, &vec![7; (1 << 20) + 5], true), Ok(1 << 20));
    assert_eq!(c.stream_write(0, &[7; 5], true), Ok(0));
}

#[test]
fn stream_error_closes() {
    let mut c = established_rx();
    c.on_datagram(0, 100, vec![one(0, vec![stream(3, b"x", false)])], None, 30, &rnd(3));
    assert_eq!(c.phase(), Phase::Closing);
    assert_eq!(c.close_info().as_ref().unwrap().1, 0x05);
    assert!(!c.streams_live());
    c.on_datagram(0, 100, vec![one(1, vec![stream(0, b"GET", true)])], None, 31, &rnd(3));
    let mut ev = Vec::new();
    c.poll_stream_events(&mut ev);
    assert!(ev.is_empty());
}

#[test]
fn reset_candidate() {
    let mut c = established_rx();
    c.on_datagram(0, 100, vec![one(0, vec![ncid(1, 1, 0xd1)])], None, 30, &rnd(3));
    assert!(updates(&mut c).contains(&CidUpdate::AddToken([0xe1; 16])));
    c.on_reset_candidate(&[0xe1; 16], 31);
    assert_eq!(c.phase(), Phase::Draining);
    assert!(!c.streams_live());
    let mut c = established_rx();
    c.on_reset_candidate(&[0xe1; 16], 31);
    assert_eq!(c.phase(), Phase::Open);
}

#[test]
fn retire_replacement() {
    let mut c = established_rx();
    updates(&mut c);
    c.on_datagram(0, 100, vec![one_on(0, &r2(), vec![Frame::RetireConnectionId(0)])], None, 30, &rnd(5));
    let u = updates(&mut c);
    assert_eq!(u, vec![CidUpdate::Remove(L0.to_vec()), CidUpdate::Add(rnd(5)[0..8].to_vec())]);
}

#[test]
fn retire_unsent_seq() {
    let mut c = established_rx();
    c.on_datagram(0, 100, vec![one(0, vec![Frame::RetireConnectionId(1)])], None, 30, &rnd(3));
    assert_eq!(c.phase(), Phase::Closing);
    assert_eq!(c.close_info().as_ref().unwrap().1, 0x0a);
}

#[test]
fn cid_updates_apply_cleanly() {
    fn apply(t: &mut CidTable, c: &mut Connection) -> Vec<CidUpdate> {
        let u = updates(c);
        for x in &u {
            assert!(t.apply(0, x), "{x:?}");
        }
        u
    }
    let mut t = CidTable::new();
    let mut c = conn();
    assert_eq!(apply(&mut t, &mut c), vec![CidUpdate::Add(S1.to_vec()), CidUpdate::Add(L0.to_vec())]);
    c.on_datagram(0, 1200, vec![hs(0, vec![Frame::Ping])], None, 10, &rnd(9));
    c.on_peer_params(&ptp(), 10);
    c.on_handshake_complete(b"h3", 10, &rnd(2));
    apply(&mut t, &mut c);
    c.on_datagram(0, 100, vec![one(0, vec![ncid(1, 0, 0xd1)])], None, 30, &rnd(3));
    apply(&mut t, &mut c);
    c.on_datagram(0, 100, vec![one(1, vec![ncid(2, 1, 0xd2)])], None, 30, &rnd(3));
    assert!(apply(&mut t, &mut c).contains(&CidUpdate::AddToken([0xe1; 16])));
    c.on_datagram(0, 100, vec![one_on(2, &r2(), vec![Frame::RetireConnectionId(0)])], None, 30, &rnd(5));
    assert_eq!(apply(&mut t, &mut c), vec![CidUpdate::Remove(L0.to_vec()), CidUpdate::Add(rnd(5)[0..8].to_vec())]);
    c.on_datagram(0, 100, vec![one_on(3, &r2(), vec![ncid(3, 2, 0xd3)])], None, 30, &rnd(3));
    assert_eq!(apply(&mut t, &mut c), vec![CidUpdate::RemoveToken([0xe1; 16]), CidUpdate::AddToken([0xe2; 16])]);
}

fn challenged() -> Connection {
    let mut c = established_rx();
    c.on_datagram(1, 50, vec![one(1, vec![Frame::PathChallenge(D(1))])], None, 30, &rnd(3));
    c
}

#[test]
fn path_challenge_recorded() {
    let c = challenged();
    assert!(c.response_owed(1));
    assert_eq!(c.active_path(), 0);
    assert_eq!(c.path_dcid(1), Some(C1.to_vec()));
}

#[test]
fn peer_rotation_splits_pair() {
    let mut c = challenged();
    c.on_datagram(1, 100, vec![one_on(2, &r2(), vec![Frame::PathChallenge(D(6))])], None, 31, &rnd(3));
    assert_eq!(c.path_dcid(1), None);
    assert_eq!(c.path_dcid(0), Some(C1.to_vec()));
    assert_eq!(c.active_path(), 0);
    assert!(c.response_owed(1));
}

fn probed_new_cid() -> Connection {
    let mut c = established_rx();
    c.on_datagram(0, 100, vec![one(0, vec![ncid(1, 0, 0xd1)])], None, 30, &rnd(3));
    c.on_datagram(1, 100, vec![one_on(1, &r2(), vec![Frame::PathChallenge(D(5))])], None, 30, &rnd(3));
    c
}

#[test]
fn probe_new_cid_assigned() {
    let c = probed_new_cid();
    assert_eq!(c.path_dcid(1), Some(D(0xd1).to_vec()));
    assert_eq!(c.active_path(), 0);
}

#[test]
fn rpt_switch_to_used_cid() {
    let mut c = probed_new_cid();
    c.on_datagram(0, 100, vec![one(2, vec![ncid(2, 1, 0xd2)])], None, 31, &rnd(3));
    assert_eq!(c.path_dcid(0), Some(D(0xd2).to_vec()));
    assert_eq!(c.path_dcid(1), Some(D(0xd1).to_vec()));
}

#[test]
fn probe_no_spare_cid() {
    let mut c = established_rx();
    c.on_datagram(1, 100, vec![one_on(1, &r2(), vec![Frame::PathChallenge(D(5))])], None, 30, &rnd(3));
    assert_eq!(c.path_dcid(1), None);
    assert!(c.response_owed(1));
}

fn rebound() -> Connection {
    let mut c = established_rx();
    c.on_datagram(1, 100, vec![one(1, vec![stream(0, b"GET", true)])], None, 30, &rnd(5));
    c
}

#[test]
fn nat_rebinding_rx() {
    let c = rebound();
    assert_eq!(c.active_path(), 1);
    assert!(c.challenge_owed(1));
    assert!(c.challenge_owed(0));
}

#[test]
fn stale_dcid_rewritten() {
    let mut c = rebound();
    c.on_datagram(1, 100, vec![one(2, vec![ncid(1, 1, 0xd1)])], None, 31, &rnd(6));
    assert_eq!(c.path_dcid(1), Some(D(0xd1).to_vec()));
    assert_eq!(c.path_dcid(0), Some(D(0xd1).to_vec()));
}

#[test]
fn stale_active_no_spare_closes_silently() {
    // Paths 1 and 2 share D1 (the peer uses one CID on both). Path 0 is active again when an exact
    // repeat retires C1, with no unused CID left: D1 cannot go to a second destination.
    let mut c = established_rx();
    c.on_datagram(0, 100, vec![one(0, vec![ncid(1, 0, 0xd1)])], None, 30, &rnd(3));
    c.on_datagram(1, 100, vec![one_on(1, &r2(), vec![Frame::PathChallenge(D(5))])], None, 30, &rnd(3));
    c.on_datagram(1, 100, vec![one_on(2, &r2(), vec![Frame::Ping])], None, 30, &rnd(3));
    assert_eq!(c.active_path(), 1);
    c.on_datagram(2, 100, vec![one_on(3, &r2(), vec![Frame::PathChallenge(D(7))])], None, 30, &rnd(3));
    assert_eq!(c.path_dcid(2), Some(D(0xd1).to_vec()));
    c.on_datagram(0, 100, vec![one(4, vec![Frame::Ping])], None, 30, &rnd(3));
    assert_eq!(c.active_path(), 0);
    c.on_datagram(0, 100, vec![one(5, vec![ncid(1, 1, 0xd1)])], None, 31, &rnd(3));
    assert!(c.is_closed());
    assert!(!c.streams_live());
    assert!(c.close_info().is_none());
}

#[test]
fn repeat_raise_no_holder_stays_open() {
    // The same exact repeat, but nothing else holds D1: the active path just takes it.
    let mut c = established_rx();
    c.on_datagram(0, 100, vec![one(0, vec![ncid(1, 0, 0xd1)])], None, 30, &rnd(3));
    c.on_datagram(0, 100, vec![one(1, vec![ncid(1, 1, 0xd1)])], None, 31, &rnd(3));
    assert_eq!(c.phase(), Phase::Open);
    assert_eq!(c.path_dcid(0), Some(D(0xd1).to_vec()));
}

#[test]
fn owed_response_gets_late_cid() {
    // A full response queue drops the retransmitted probe at the gate, so the CID has to arrive
    // without one.
    let mut c = established_rx();
    for pn in 0..4 {
        c.on_datagram(1, 100, vec![one_on(pn, &r2(), vec![Frame::PathChallenge(D(pn as u8))])], None, 30, &rnd(3));
    }
    assert_eq!(c.path_dcid(1), None);
    c.on_datagram(0, 100, vec![one(4, vec![ncid(1, 0, 0xd1)])], None, 31, &rnd(3));
    assert_eq!(c.path_dcid(1), Some(D(0xd1).to_vec()));
    c.on_datagram(1, 100, vec![one_on(5, &r2(), vec![Frame::PathChallenge(D(9))])], None, 32, &rnd(3));
    assert_eq!(c.largest_pn(PacketKind::OneRtt), Some(4));
}

#[test]
fn owed_challenge_gets_late_cid() {
    // Migrated to and away from path 1, then split from path 0 with its challenge still owed.
    let mut c = established_rx();
    c.on_datagram(1, 100, vec![one(0, vec![Frame::Ping])], None, 30, &rnd(3));
    assert!(c.challenge_owed(1));
    c.on_datagram(0, 100, vec![one(1, vec![Frame::Ping])], None, 30, &rnd(3));
    c.on_datagram(1, 100, vec![one_on(2, &r2(), vec![Frame::Padding])], None, 30, &rnd(3));
    assert_eq!(c.path_dcid(1), None);
    c.on_datagram(0, 100, vec![one(3, vec![ncid(1, 0, 0xd1)])], None, 31, &rnd(3));
    assert_eq!(c.path_dcid(1), Some(D(0xd1).to_vec()));
}

#[test]
fn rebound_probe_keeps_spare_cid() {
    // M1: the same CID from a new address shares the active DCID; the spare stays unused.
    let mut c = established_rx();
    c.on_datagram(0, 100, vec![one(0, vec![ncid(1, 0, 0xd1)])], None, 30, &rnd(3));
    c.on_datagram(1, 100, vec![one(1, vec![Frame::PathChallenge(D(5))])], None, 31, &rnd(3));
    assert_eq!(c.path_dcid(1), Some(C1.to_vec()));
}

#[test]
fn reordered_packet_no_migration() {
    let mut c = established_rx();
    c.on_datagram(0, 100, vec![one(5, vec![Frame::Ping])], None, 30, &rnd(3));
    c.on_datagram(1, 100, vec![one(3, vec![stream(0, b"GET", true)])], None, 31, &rnd(3));
    assert_eq!(c.active_path(), 0);
}

#[test]
fn no_fresh_cid_no_migration() {
    let mut c = established_rx();
    c.on_datagram(1, 100, vec![one_on(1, &r2(), vec![stream(0, b"GET", true)])], None, 30, &rnd(3));
    assert_eq!(c.active_path(), 0);
}

#[test]
fn path_cap_rx() {
    let mut c = established_rx();
    for q in 1..=3u8 {
        c.on_datagram(q as u64, 1200, vec![one(q as u64, vec![Frame::Ping])], None, 30, &rnd(3));
        assert!(c.path_state(q as u64).is_some());
    }
    c.on_datagram(4, 1200, vec![one(5, vec![Frame::PathChallenge(D(4))])], None, 30, &rnd(3));
    assert!(!c.response_owed(4));
}
