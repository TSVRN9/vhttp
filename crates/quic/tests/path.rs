//! Phase 3d path table (RFC 9000 §8.2, §19.17).
use quic::path::*;

#[allow(non_snake_case)]
fn D(x: u8) -> [u8; 8] {
    [x; 8]
}

/// Path 0 validated, path 1 inserted and challenged with D(9) at `t`, the challenge sent.
fn challenged(t: u64, padded: bool) -> Paths {
    let mut p = Paths::new(0);
    p.set_validated(0);
    assert!(p.insert(1));
    p.start_challenge(1, D(9), t);
    assert_eq!(p.take_challenge(1, padded), Some(D(9)));
    p
}

#[test]
fn respond_echo() {
    let mut p = Paths::new(0);
    p.on_challenge(0, D(1));
    assert!(p.has_response(0));
    assert_eq!(p.take_response(0), Some(D(1)));
    assert_eq!(p.take_response(0), None);
    assert!(!p.has_response(0));
}

#[test]
fn two_challenges() {
    let mut p = Paths::new(0);
    p.on_challenge(0, D(1));
    p.on_challenge(0, D(2));
    assert_eq!(p.take_response(0), Some(D(1)));
    assert_eq!(p.take_response(0), Some(D(2)));
    assert_eq!(p.take_response(0), None);
}

#[test]
fn response_cap() {
    let mut p = Paths::new(0);
    for x in 1..=5 {
        p.on_challenge(0, D(x));
    }
    for x in 1..=4 {
        assert_eq!(p.take_response(0), Some(D(x)));
    }
    assert_eq!(p.take_response(0), None);
}

#[test]
fn response_any_path() {
    let mut p = challenged(100, true);
    assert_eq!(p.on_response(D(9)), Some(1));
    assert_eq!(p.state(1), PathState::Validated);
    assert_eq!(p.budget(1), u64::MAX);
    assert_eq!(p.last_validated(), Some(1));
    assert!(!p.needs_mtu_probe(1));
}

#[test]
fn wrong_response_ignored() {
    let mut p = challenged(100, true);
    assert_eq!(p.on_response(D(8)), None);
    assert_eq!(p.state(1), PathState::Validating);
    assert_eq!(p.last_validated(), Some(0));
}

#[test]
fn unsent_challenge_not_answered() {
    let mut p = Paths::new(0);
    p.start_challenge(0, D(9), 0);
    assert!(p.challenge_owed(0));
    assert_eq!(p.on_response(D(9)), None);
    assert_eq!(p.take_challenge(0, true), Some(D(9)));
    assert!(!p.challenge_owed(0));
    assert_eq!(p.take_challenge(0, true), None);
}

#[test]
fn mtu_second_validation() {
    let mut p = challenged(0, false);
    assert_eq!(p.on_response(D(9)), Some(1));
    assert!(p.needs_mtu_probe(1));
    p.start_challenge(1, D(10), 10);
    assert!(!p.needs_mtu_probe(1));
    assert_eq!(p.take_challenge(1, true), Some(D(10)));
    assert_eq!(p.on_response(D(10)), Some(1));
    assert!(!p.needs_mtu_probe(1));
    assert_eq!(p.state(1), PathState::Validated);
}

#[test]
fn validation_timeout() {
    let mut p = challenged(100, true);
    assert_eq!(p.deadline(999_000), Some(2_997_100));
    assert_eq!(p.on_timeout(2_997_099, 999_000), None);
    assert_eq!(p.on_timeout(2_997_100, 999_000), Some(1));
    assert_eq!(p.state(1), PathState::Unvalidated);
    assert_eq!(p.deadline(999_000), None);
    assert_eq!(p.on_timeout(u64::MAX, 999_000), None);
}

#[test]
fn failed_mtu_probe_keeps_validated() {
    let mut p = challenged(0, false);
    assert_eq!(p.on_response(D(9)), Some(1));
    p.start_challenge(1, D(10), 10);
    assert_eq!(p.deadline(1), None);
    assert_eq!(p.take_challenge(1, true), Some(D(10)));
    assert_eq!(p.deadline(1), Some(13));
    assert_eq!(p.on_timeout(13, 1), Some(1));
    assert_eq!(p.state(1), PathState::Validated);
    assert!(p.needs_mtu_probe(1));
}

#[test]
fn timeout_lowest_first() {
    let mut p = Paths::new(0);
    assert!(p.insert(1));
    p.start_challenge(1, D(1), 0);
    p.take_challenge(1, true);
    p.start_challenge(0, D(2), 5);
    p.take_challenge(0, true);
    assert_eq!(p.deadline(1), Some(3));
    assert_eq!(p.on_timeout(100, 1), Some(0));
    assert_eq!(p.on_timeout(100, 1), Some(1));
    assert_eq!(p.on_timeout(100, 1), None);
}

#[test]
fn path_cap() {
    let mut p = Paths::new(0);
    assert!(p.insert(1));
    assert!(p.insert(2));
    assert!(p.insert(3));
    assert!(!p.insert(4));
    assert_eq!(p.index(3), Some(3));
    assert_eq!(p.index(4), None);
}

#[test]
fn per_path_amp() {
    let mut p = Paths::new(0);
    assert!(p.insert(1));
    p.on_recv(1, 100);
    assert_eq!(p.budget(1), 300);
    assert_eq!(p.budget(0), 0);
    p.on_sent(1, 300);
    assert_eq!(p.budget(1), 0);
}

#[test]
fn cids_and_active() {
    let mut p = Paths::new(0);
    assert!(p.insert(7));
    assert_eq!(p.dcid(7), None);
    p.set_dcid(7, Some(&[1, 2, 3]));
    assert_eq!(p.dcid(7), Some(&[1u8, 2, 3][..]));
    p.set_dcid(7, None);
    assert_eq!(p.dcid(7), None);
    p.set_peer_used(7, &[4, 5]);
    assert_eq!(p.peer_used(7), Some(&[4u8, 5][..]));
    assert_eq!(p.peer_used(0), None);
    assert_eq!(p.active(), 0);
    p.set_active(7);
    assert_eq!(p.active(), 7);
    assert_eq!(p.last_validated(), None);
}

#[test]
fn capacity_bounded() {
    let mut p = Paths::new(0);
    for i in 1..100u64 {
        p.insert(i);
    }
    for r in 0..1000u32 {
        for x in 0..10u8 {
            p.on_challenge(0, D(x ^ r as u8));
        }
        while p.take_response(0).is_some() {}
    }
    assert!(p.capacities(0).0 <= MAX_PATHS);
    assert!(p.capacities(0).1 <= MAX_RESPONSES);
}

#[test]
fn handshake_path_mtu_ok() {
    let mut p = Paths::new(0);
    assert!(!p.mtu_ok(0));
    p.set_validated(0);
    assert!(p.mtu_ok(0));
    assert!(!p.needs_mtu_probe(0));
}

#[test]
fn rechallenge_keeps_clock() {
    let mut p = challenged(100, true);
    p.start_challenge(1, D(10), 5_000);
    assert_eq!(p.take_challenge(1, true), Some(D(10)));
    assert_eq!(p.deadline(999_000), Some(2_997_100));
    assert_eq!(p.on_response(D(9)), None);
    assert_eq!(p.on_timeout(2_997_100, 999_000), Some(1));
    assert_eq!(p.state(1), PathState::Unvalidated);
}

#[test]
fn unpadded_response_keeps_mtu_ok() {
    let mut p = challenged(0, true);
    assert_eq!(p.on_response(D(9)), Some(1));
    p.start_challenge(1, D(10), 10);
    assert_eq!(p.take_challenge(1, false), Some(D(10)));
    assert_eq!(p.on_response(D(10)), Some(1));
    assert!(p.mtu_ok(1));
    assert!(!p.needs_mtu_probe(1));
}
