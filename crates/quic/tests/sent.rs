//! Phase 3d sent packets: packet number allocation, eliciting-only records, incoming ACKs with
//! the 64-range read cap, and the placeholder recovery hook (PTO and packet-count AIMD).
use quic::ack::AckFrame;
use quic::codes::{PN_MAX, PROTOCOL_VIOLATION};
use quic::frame::Frame;
use quic::payload::PacketKind;
use quic::recovery::*;
use quic::sent::*;

#[allow(non_snake_case)]
fn A(largest: u64, delay: u64, first_range: u64, ranges: Vec<(u64, u64)>) -> AckFrame {
    AckFrame { largest, delay, first_range, ranges, ecn: None }
}

fn rec(pn: u64) -> SentPacket {
    SentPacket {
        pn,
        time: 0,
        size: 50,
        ack_eliciting: true,
        frames: vec![Frame::Crypto { offset: 0, data: vec![pn as u8] }],
    }
}

/// Takes and records packet numbers `0..n`.
fn sent(n: u64) -> SentPackets {
    let mut s = SentPackets::new();
    for i in 0..n {
        assert_eq!(s.take_pn(), Some(i));
        s.on_sent(rec(i));
    }
    s
}

fn pns(v: &[SentPacket]) -> Vec<u64> {
    v.iter().map(|p| p.pn).collect()
}

#[test]
fn pn_monotonic() {
    let mut s = SentPackets::new();
    assert_eq!(s.take_pn(), Some(0));
    assert_eq!(s.take_pn(), Some(1));
    assert_eq!(s.next_pn(), 2);
}

#[test]
fn pn_exhaustion() {
    let mut s = SentPackets::new_at(PN_MAX - 1);
    assert_eq!(s.take_pn(), Some(PN_MAX - 1));
    assert_eq!(s.take_pn(), None);
    assert_eq!(s.take_pn(), None);
}

#[test]
fn ack_removes() {
    let mut s = sent(4);
    let mut out = Vec::new();
    assert_eq!(s.on_ack(&A(2, 0, 0, vec![(0, 0)]), &mut out), Ok(()));
    assert_eq!(pns(&out), vec![0, 2]);
    assert_eq!(s.largest_acked(), Some(2));
    assert_eq!(s.inflight_len(), 2);
}

#[test]
fn ack_unsent() {
    let mut s = sent(4);
    assert_eq!(s.next_pn(), 4);
    let mut out = Vec::new();
    assert_eq!(s.on_ack(&A(4, 0, 0, vec![]), &mut out), Err(PROTOCOL_VIOLATION));
    assert!(out.is_empty());
    assert_eq!(s.inflight_len(), 4);
    assert_eq!(s.largest_acked(), None);
}

#[test]
fn ack_repeat() {
    let mut s = sent(4);
    let a = A(2, 0, 0, vec![(0, 0)]);
    let mut out = Vec::new();
    assert_eq!(s.on_ack(&a, &mut out), Ok(()));
    let mut out = Vec::new();
    assert_eq!(s.on_ack(&a, &mut out), Ok(()));
    assert!(out.is_empty());
    assert_eq!(s.on_ack(&A(1, 0, 0, vec![]), &mut out), Ok(()));
    assert_eq!(pns(&out), vec![1]);
    assert_eq!(s.largest_acked(), Some(2));
}

#[test]
fn ack_of_unrecorded_pn() {
    let mut s = SentPackets::new();
    assert_eq!(s.take_pn(), Some(0));
    assert_eq!(s.take_pn(), Some(1));
    s.on_sent(rec(1));
    let mut out = Vec::new();
    assert_eq!(s.on_ack(&A(1, 0, 1, vec![]), &mut out), Ok(()));
    assert_eq!(out, vec![rec(1)]);
    assert_eq!(s.inflight_len(), 0);
}

#[test]
fn ack_range_cap_in() {
    let mut s = sent(201);
    let mut out = Vec::new();
    assert_eq!(s.on_ack(&A(200, 0, 0, vec![(0, 0); 70]), &mut out), Ok(()));
    assert_eq!(pns(&out), (36..=100).map(|i| 2 * i).collect::<Vec<u64>>());
    assert_eq!(out.len(), 65);
    assert_eq!(s.on_packet_lost(70), Some(rec(70)));
    assert_eq!(s.on_packet_lost(60), Some(rec(60)));
}

#[test]
fn lost_once() {
    let mut s = sent(3);
    assert_eq!(s.on_packet_lost(1), Some(rec(1)));
    assert_eq!(s.on_packet_lost(1), None);
    assert_eq!(s.inflight_len(), 2);
}

#[test]
fn drain_frees() {
    let mut s = sent(3);
    let mut out = Vec::new();
    s.drain_inflight(&mut out);
    assert_eq!(pns(&out), vec![0, 1, 2]);
    assert_eq!(s.inflight_len(), 0);
    assert_eq!(s.inflight_capacity(), 0);
    assert_eq!(s.last_sent_time(), None);
}

/// `on_ack` rebuilds the list into a fresh `Vec`, so acknowledged records free their slots.
#[test]
fn ack_frees() {
    let mut s = sent(64);
    let mut out = Vec::new();
    assert_eq!(s.on_ack(&A(62, 0, 62, vec![]), &mut out), Ok(()));
    assert_eq!(s.inflight_len(), 1);
    assert!(s.inflight_capacity() <= 4);
    assert_eq!(s.on_ack(&A(63, 0, 0, vec![]), &mut out), Ok(()));
    assert_eq!(out.len(), 64);
    assert_eq!(s.inflight_capacity(), 0);
}

#[test]
fn last_sent_time_newest() {
    let mut s = SentPackets::new();
    assert_eq!(s.last_sent_time(), None);
    for (i, t) in [(0, 10), (1, 20)] {
        assert_eq!(s.take_pn(), Some(i));
        s.on_sent(SentPacket { time: t, ..rec(i) });
    }
    assert_eq!(s.last_sent_time(), Some(20));
}

#[test]
fn placeholder_pto() {
    let mut r = Recovery::new();
    assert_eq!(r.pto_us(PacketKind::Initial, 25_000), 999_000);
    assert_eq!(r.pto_us(PacketKind::OneRtt, 25_000), 1_024_000);
    r.on_pto_fired();
    assert_eq!(r.pto_us(PacketKind::Initial, 25_000), 1_998_000);
    for _ in 0..10 {
        r.on_pto_fired();
    }
    assert_eq!(r.pto_us(PacketKind::Initial, 25_000), 999_000 << 6);
    assert_eq!(r.pto_us(PacketKind::Initial, 25_000), 63_936_000);
    assert_eq!(r.pto_us(PacketKind::OneRtt, u64::MAX), u64::MAX);
    r.on_ack_received(PacketKind::Initial, 1, 0, 0);
    assert_eq!(r.pto_us(PacketKind::Initial, 25_000), 999_000);
}

#[test]
fn pto_not_armed_amp_blocked() {
    let r = Recovery::new();
    assert_eq!(r.pto_deadline(PacketKind::Initial, Some(5), 0, true), None);
    assert_eq!(r.pto_deadline(PacketKind::Initial, Some(5), 0, false), Some(999_005));
    assert_eq!(r.pto_deadline(PacketKind::Initial, None, 0, false), None);
    assert_eq!(r.pto_deadline(PacketKind::Initial, Some(u64::MAX), 0, false), Some(u64::MAX));
}

#[test]
fn aimd() {
    let mut r = Recovery::new();
    assert!(r.can_send(9));
    assert!(!r.can_send(10));
    r.on_packets_lost(PacketKind::OneRtt, 1, 0);
    assert!(r.can_send(4));
    assert!(!r.can_send(5));
    r.on_packets_lost(PacketKind::OneRtt, 1, 0);
    r.on_packets_lost(PacketKind::OneRtt, 1, 0);
    assert!(r.can_send(1));
    assert!(!r.can_send(2));
    r.on_packets_lost(PacketKind::OneRtt, 0, 0);
    assert!(r.can_send(1));
    r.on_ack_received(PacketKind::OneRtt, 100, 0, 0);
    assert!(r.can_send(63));
    assert!(!r.can_send(64));
    r.on_path_validated();
    assert!(r.can_send(9));
    assert!(!r.can_send(10));
}
