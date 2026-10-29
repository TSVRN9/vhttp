use quic::flow::*;
use wire::varint::VARINT_MAX;

#[test]
fn recv_credit_half_window() {
    let mut c = RecvCredit::new(100, VARINT_MAX);
    assert_eq!(c.limit(), 100);
    c.on_consumed(49);
    assert_eq!(c.pending(), None);
    c.on_consumed(2);
    assert_eq!(c.pending(), Some(151));
    c.commit();
    assert_eq!(c.limit(), 151);
    assert_eq!(c.pending(), None);
    c.on_lost();
    assert_eq!(c.pending(), Some(151));
}

#[test]
fn recv_credit_cap() {
    let mut c = RecvCredit::new(4, 6);
    c.on_consumed(3);
    assert_eq!(c.pending(), Some(6));
    c.commit();
    c.on_consumed(3);
    // The target of 6 is not above the limit of 6.
    assert_eq!(c.pending(), None);
}

#[test]
fn recv_credit_zero_window() {
    let mut c = RecvCredit::new(0, VARINT_MAX);
    c.on_consumed(0);
    assert_eq!(c.pending(), None);
}

#[test]
fn send_credit() {
    let mut c = SendCredit::new(10);
    c.on_max(5);
    assert_eq!(c.max(), 10);
    c.on_max(12);
    assert_eq!(c.available(), 12);
    c.consume(12);
    assert_eq!(c.available(), 0);
    c.on_max(12);
    assert_eq!(c.max(), 12);
}

#[test]
fn recv_credit_lost_keeps_larger_pending() {
    let mut c = RecvCredit::new(100, VARINT_MAX);
    c.on_consumed(51);
    assert_eq!(c.pending(), Some(151));
    c.on_lost();
    assert_eq!(c.pending(), Some(151));
    assert_eq!(c.limit(), 100);
}
