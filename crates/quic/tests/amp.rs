//! Phase 3d anti-amplification budget (RFC 9000 §8.1).
use quic::amp::*;

#[test]
fn amp_budget() {
    let mut a = AmpBudget::new();
    assert_eq!(a.budget(), 0);
    a.on_recv(1200);
    assert_eq!(a.budget(), 3600);
    a.on_sent(3600);
    assert_eq!(a.budget(), 0);
    a.on_recv(1);
    assert_eq!(a.budget(), 3);
    assert!(!a.is_validated());
    a.validate();
    assert!(a.is_validated());
    assert_eq!(a.budget(), u64::MAX - 3600);
    a.on_sent(10_000);
    assert_eq!(a.budget(), u64::MAX - 13_600);
}

#[test]
fn amp_saturating() {
    let mut a = AmpBudget::new();
    a.on_recv(u64::MAX);
    a.on_recv(5);
    assert_eq!(a.budget(), u64::MAX);
    a.on_sent(7);
    assert_eq!(a.budget(), u64::MAX - 7);
}
