//! Phase 3d idle timeout, close and draining (RFC 9000 §10.1, §10.2).
use quic::codes::*;
use quic::frame::*;
use quic::lifecycle::*;
use quic::payload::PacketKind;
use wire::varint::VARINT_MAX;

#[test]
fn idle_effective() {
    assert_eq!(effective_idle_us(30000, Some(0), 999_000), Some(30_000_000));
    assert_eq!(effective_idle_us(30000, Some(10000), 1), Some(10_000_000));
    assert_eq!(effective_idle_us(0, Some(5000), 1), Some(5_000_000));
    assert_eq!(effective_idle_us(1, Some(0), 999_000), Some(2_997_000));
    assert_eq!(effective_idle_us(0, Some(0), 1), None);
    assert_eq!(effective_idle_us(0, None, 1), None);
    assert_eq!(effective_idle_us(VARINT_MAX, Some(0), 999_000), Some(u64::MAX));
    assert_eq!(effective_idle_us(1, None, u64::MAX), Some(u64::MAX));
    assert_eq!(ms_to_us(u64::MAX), u64::MAX);
}

#[test]
fn idle_restart() {
    let mut t = IdleTimer::new(0);
    t.on_packet_processed(100);
    assert_eq!(t.deadline(10), 110);
    t.on_eliciting_sent(200);
    assert_eq!(t.deadline(10), 210);
    t.on_eliciting_sent(300);
    assert_eq!(t.deadline(10), 210);
    t.on_packet_processed(400);
    assert_eq!(t.deadline(10), 410);
    assert_eq!(t.deadline(u64::MAX), u64::MAX);
}

#[test]
fn close_frame_conversion() {
    let cc = |app, error_code, reason: &[u8]| Frame::ConnectionClose {
        app,
        error_code,
        frame_type: 0,
        reason: reason.to_vec(),
    };
    for k in [PacketKind::Initial, PacketKind::Handshake] {
        assert_eq!(close_frame(true, 0x0100, b"bye", k), cc(false, 0x0c, b""));
    }
    assert_eq!(close_frame(true, 0x0100, b"bye", PacketKind::OneRtt), cc(true, 0x0100, b"bye"));
    assert_eq!(close_frame(false, 0x0a, b"x", PacketKind::Handshake), cc(false, 0x0a, b"x"));
}

#[test]
fn close_spaces_order() {
    use PacketKind::*;
    assert_eq!(close_spaces(true, false, false, true), vec![OneRtt]);
    assert_eq!(close_spaces(true, true, true, true), vec![OneRtt]);
    assert_eq!(close_spaces(false, true, true, false), vec![Initial, Handshake]);
    assert_eq!(close_spaces(false, false, true, true), vec![Handshake, OneRtt]);
}

#[test]
fn closing_budget() {
    let mut l = Lifecycle::new();
    assert_eq!(l.phase(), Phase::Open);
    assert!(!l.may_send_close(1));
    l.enter_closing(0, 1000, false, 0x0a, b"");
    assert_eq!(l.phase(), Phase::Closing);
    assert_eq!(l.deadline(), Some(3000));
    assert!(l.may_send_close(30));
    l.on_close_sent(30);
    assert!(!l.may_send_close(30));
    l.on_recv_closing(9);
    assert!(!l.may_send_close(30));
    l.on_recv_closing(9);
    assert!(l.may_send_close(30));
    l.on_close_sent(30);
    l.on_timeout(2999);
    assert_eq!(l.phase(), Phase::Closing);
    l.on_timeout(3000);
    assert_eq!(l.phase(), Phase::Closed);
}

#[test]
fn first_error_wins_and_reason_cap() {
    let mut l = Lifecycle::new();
    l.enter_closing(0, 10, true, 5, &[7; 100]);
    l.enter_closing(1, 10, false, 6, b"later");
    assert_eq!(l.close_info(), &Some((true, 5, vec![7; 64])));
    assert_eq!(l.deadline(), Some(30));
    let _ = APPLICATION_ERROR;
}

#[test]
fn draining_silent() {
    let mut l = Lifecycle::new();
    l.enter_draining(10, 1000);
    assert_eq!(l.phase(), Phase::Draining);
    assert!(!l.may_send_close(1));
    assert_eq!(l.deadline(), Some(3010));
    l.enter_closing(11, 1000, false, 1, b"");
    assert_eq!(l.phase(), Phase::Draining);
    l.on_timeout(3010);
    assert_eq!(l.phase(), Phase::Closed);
    l.enter_draining(4000, 1000);
    assert_eq!(l.phase(), Phase::Closed);

    let mut l = Lifecycle::new();
    l.enter_closing(0, 1000, false, 1, b"");
    l.enter_draining(5, 1000);
    assert_eq!(l.phase(), Phase::Draining);
    assert_eq!(l.deadline(), Some(3005));
    let mut l = Lifecycle::new();
    l.close_silently();
    assert_eq!(l.phase(), Phase::Closed);
}
