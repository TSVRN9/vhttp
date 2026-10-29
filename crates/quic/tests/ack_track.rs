//! Phase 3d received packet numbers: duplicate suppression, the 32-range cap, ACK scheduling
//! and ACK frame generation.
use quic::ack::{serialize_ack, AckFrame};
use quic::ack_track::*;
use quic::payload::PacketKind;

#[allow(non_snake_case)]
fn A(largest: u64, delay: u64, first_range: u64, ranges: Vec<(u64, u64)>) -> AckFrame {
    AckFrame { largest, delay, first_range, ranges, ecn: None }
}

fn with(kind: PacketKind, pns: &[u64]) -> RecvPns {
    let mut r = RecvPns::new(kind);
    for &pn in pns {
        r.on_packet(pn, true, 0);
    }
    r
}

/// The smallest packet number the frame acknowledges.
fn smallest(a: &AckFrame) -> u64 {
    let mut s = a.largest - a.first_range;
    for &(gap, len) in &a.ranges {
        s = s - gap - 2 - len;
    }
    s
}

#[test]
fn dup_suppression() {
    let mut r = RecvPns::new(PacketKind::OneRtt);
    r.on_packet(5, true, 0);
    assert!(r.is_duplicate(5));
    assert!(!r.is_duplicate(4));
    r.on_packet(4, true, 0);
    r.on_packet(7, true, 0);
    assert_eq!(r.build_ack(0, 3, 1200), Some(A(7, 0, 0, vec![(0, 1)])));
}

#[test]
fn ack_matches_received() {
    let r = with(PacketKind::Initial, &[0, 1, 2, 5, 9, 10]);
    assert_eq!(r.build_ack(0, 3, 1200), Some(A(10, 0, 1, vec![(2, 0), (1, 2)])));
}

/// The 33rd range drops the lowest, once an ACK has reported it. With the list full, a
/// number below the lowest range is refused (Fix round 1: `is_duplicate(1)` is now true).
#[test]
fn range_cap() {
    let mut r = RecvPns::new(PacketKind::OneRtt);
    for k in 0..32u64 {
        r.on_packet(2 * k, true, 0);
    }
    r.on_ack_sent(false);
    assert!(!r.is_duplicate(64));
    r.on_packet(64, true, 0);
    assert!(r.is_duplicate(0));
    assert!(r.is_duplicate(1));
    assert!(!r.is_duplicate(3));
    let a = r.build_ack(0, 3, 1200).unwrap();
    assert_eq!(a.ranges.len(), 31);
    assert_eq!(smallest(&a), 2);
    assert_eq!(r.largest(), Some(64));
}

#[test]
fn ack_scheduling() {
    for kind in [PacketKind::Initial, PacketKind::Handshake] {
        let mut r = RecvPns::new(kind);
        r.on_packet(0, true, 100);
        assert_eq!(r.ack_deadline(25_000), Some(100));
    }
    let mut r = RecvPns::new(PacketKind::OneRtt);
    r.on_packet(0, true, 100);
    assert_eq!(r.ack_deadline(25_000), Some(25_100));
    r.on_packet(1, true, 200);
    assert_eq!(r.ack_deadline(25_000), Some(100));
    r.on_ack_sent(false);
    assert_eq!(r.ack_deadline(25_000), None);
}

#[test]
fn non_eliciting() {
    let mut r = RecvPns::new(PacketKind::OneRtt);
    r.on_packet(0, false, 100);
    assert_eq!(r.ack_deadline(25_000), None);
    assert!(!r.ack_only_allowed());
    assert!(r.has_new());
}

#[test]
fn ack_delay_field() {
    let mut r = RecvPns::new(PacketKind::OneRtt);
    r.on_packet(7, true, 1000);
    assert_eq!(r.build_ack(9000, 3, 1200).unwrap().delay, 1000);
    let mut r = RecvPns::new(PacketKind::Initial);
    r.on_packet(7, true, 1000);
    assert_eq!(r.build_ack(9000, 3, 1200).unwrap().delay, 0);
}

#[test]
fn build_ack_max_len() {
    let r = with(PacketKind::Initial, &[0, 1, 2, 5, 9, 10]);
    let a = r.build_ack(0, 3, 7).unwrap();
    assert_eq!(a, A(10, 0, 1, vec![(2, 0)]));
    let mut out = Vec::new();
    serialize_ack(&a, &mut out);
    assert_eq!(out, [0x02, 0x0a, 0x00, 0x01, 0x01, 0x02, 0x00]);
    assert_eq!(r.build_ack(0, 3, 5), Some(A(10, 0, 1, vec![])));
    assert_eq!(r.build_ack(0, 3, 4), None);
}

/// Attacker-chosen gaps never grow the range list's allocation past a small constant:
/// the lowest range is popped, never re-allocated.
#[test]
fn ranges_capacity_bounded() {
    let mut r = RecvPns::new(PacketKind::OneRtt);
    for k in 0..5000u64 {
        assert!(!r.is_duplicate(2 * k));
        r.on_packet(2 * k, k % 3 == 0, k);
        r.on_ack_sent(false);
        assert!(r.ranges_capacity() <= 64, "pn {}: capacity {}", 2 * k, r.ranges_capacity());
    }
    // Filling the gaps that are still above the floor merges ranges back together.
    for k in 4968..4999u64 {
        assert!(!r.is_duplicate(2 * k + 1));
        r.on_packet(2 * k + 1, false, 0);
    }
    assert_eq!(r.build_ack(0, 3, 1200), Some(A(9998, 0, 9998 - 9936, vec![])));
    assert!(r.ranges_capacity() <= 64);
}

/// No range holding an ack-eliciting packet number is dropped before an ACK was sent after
/// it: the packet that would force it out is refused, and taken once the ACK goes out.
#[test]
fn unreported_never_dropped() {
    let mut r = RecvPns::new(PacketKind::OneRtt);
    for k in 0..32u64 {
        r.on_packet(2 * k, true, 0);
    }
    // Full, and the lowest range (PN 0) is unreported.
    assert!(r.is_duplicate(64));
    assert!(r.is_duplicate(100));
    // Extending a range does not drop one, but the list is still full: refused all the same.
    assert!(r.is_duplicate(63));
    let a = r.build_ack(0, 3, 1200).unwrap();
    assert_eq!((a.ranges.len(), smallest(&a)), (31, 0));
    r.on_ack_sent(false);
    assert!(!r.is_duplicate(64));
    r.on_packet(64, true, 0);
    // PN 0 went only after an ACK reported it; 64 is unreported, but above the lowest range.
    assert!(r.is_duplicate(0));
    assert!(!r.is_duplicate(66));

    // A non-eliciting lowest range may go without an ACK.
    let mut r = RecvPns::new(PacketKind::OneRtt);
    r.on_packet(0, false, 0);
    for k in 1..32u64 {
        r.on_packet(2 * k, true, 0);
    }
    assert!(!r.is_duplicate(64));
    r.on_packet(64, true, 0);
    assert!(r.is_duplicate(0));
    let a = r.build_ack(0, 3, 1200).unwrap();
    assert_eq!((a.ranges.len(), smallest(&a)), (31, 2));
}
