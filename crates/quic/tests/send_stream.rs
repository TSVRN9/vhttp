use quic::send_stream::*;

#[allow(non_snake_case)]
fn C(off: u64, data: &[u8], fin: bool, new_bytes: u64) -> Chunk {
    Chunk { off, data: data.to_vec(), fin, new_bytes }
}

#[test]
fn send_flow() {
    let mut s = SendStream::new(5);
    assert_eq!(s.write(b"abcdefgh", true), Ok(()));
    assert_eq!(s.state_exec(), SendState::Ready);
    assert_eq!(s.poll_data(100, 100), Some(C(0, b"abcde", false, 5)));
    assert_eq!(s.state_exec(), SendState::Send);
    assert_eq!(s.poll_data(100, 100), None);
    s.on_max_stream_data(4);
    assert_eq!(s.max(), 5);
    s.on_max_stream_data(8);
    assert_eq!(s.poll_data(100, 100), Some(C(5, b"fgh", true, 3)));
    assert_eq!(s.state_exec(), SendState::DataSent);
    assert_eq!(s.sent_end(), 8);
}

#[test]
fn conn_limited() {
    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"abcdef", false), Ok(()));
    assert_eq!(s.poll_data(100, 2), Some(C(0, b"ab", false, 2)));
    assert_eq!(s.poll_data(100, 0), None);
}

#[test]
fn fin_only() {
    let mut s = SendStream::new(0);
    assert_eq!(s.write(b"", true), Ok(()));
    assert_eq!(s.poll_data(100, 0), Some(C(0, b"", true, 0)));
    assert_eq!(s.state_exec(), SendState::DataSent);
}

#[test]
fn max_len_split() {
    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"abcdef", true), Ok(()));
    assert_eq!(s.poll_data(4, 100), Some(C(0, b"abcd", false, 4)));
    assert_eq!(s.poll_data(4, 100), Some(C(4, b"ef", true, 2)));
}

#[test]
fn retransmit_same_bytes() {
    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"abcdef", true), Ok(()));
    assert_eq!(s.poll_data(100, 100), Some(C(0, b"abcdef", true, 6)));
    s.on_data_lost(2, 3, false);
    assert_eq!(s.poll_data(100, 0), Some(C(2, b"cde", false, 0)));
    s.on_data_lost(0, 6, true);
    assert_eq!(s.poll_data(4, 0), Some(C(0, b"abcd", false, 0)));
    assert_eq!(s.poll_data(4, 0), Some(C(4, b"ef", true, 0)));
    s.on_data_acked(0, 6, true);
    assert_eq!(s.state_exec(), SendState::DataRecvd);
    assert_eq!(s.poll_data(100, 100), None);
}

#[test]
fn all_acks_required() {
    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"abcd", true), Ok(()));
    assert!(s.poll_data(100, 100).is_some());
    s.on_data_acked(2, 2, true);
    assert_eq!(s.state_exec(), SendState::DataSent);
    s.on_data_acked(0, 2, false);
    assert_eq!(s.state_exec(), SendState::DataRecvd);
}

#[test]
fn reset_stops_stream() {
    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"abcdef", false), Ok(()));
    assert!(s.poll_data(3, 100).is_some());
    assert!(s.reset(9));
    assert_eq!(s.state_exec(), SendState::ResetSent);
    assert_eq!(s.poll_data(100, 100), None);
    assert_eq!(s.pending_reset(), Some((9, 3)));
    s.commit_reset();
    assert_eq!(s.pending_reset(), None);
    s.on_data_lost(0, 3, false);
    assert_eq!(s.poll_data(100, 100), None);
    assert_eq!(s.write(b"x", false), Err(()));
    s.on_reset_lost();
    assert_eq!(s.pending_reset(), Some((9, 3)));
    s.commit_reset();
    s.on_reset_acked();
    assert_eq!(s.state_exec(), SendState::ResetRecvd);
    assert!(!s.reset(1));
}

#[test]
fn stop_sending_forces_reset() {
    let mut s = SendStream::new(100);
    assert!(s.on_stop_sending(5));
    assert_eq!(s.pending_reset(), Some((5, 0)));

    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"ab", true), Ok(()));
    assert!(s.poll_data(100, 100).is_some());
    assert_eq!(s.state_exec(), SendState::DataSent);
    assert!(s.on_stop_sending(6));
    assert_eq!(s.pending_reset(), Some((6, 2)));

    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"ab", true), Ok(()));
    assert!(s.poll_data(100, 100).is_some());
    s.on_data_acked(0, 2, true);
    assert_eq!(s.state_exec(), SendState::DataRecvd);
    assert!(!s.on_stop_sending(7));
    assert_eq!(s.pending_reset(), None);

    let mut s = SendStream::new(100);
    assert!(s.reset(1));
    assert!(!s.on_stop_sending(8));
}

#[test]
fn write_rules() {
    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"a", true), Ok(()));
    assert_eq!(s.write(b"b", false), Err(()));
    assert_eq!(s.write(b"", true), Err(()));
}

#[test]
fn next_off_tracks_poll() {
    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"abcdef", true), Ok(()));
    assert_eq!(s.next_off(), Some(0));
    assert!(s.poll_data(4, 100).is_some());
    assert_eq!(s.next_off(), Some(4));
    s.on_data_lost(1, 2, false);
    assert_eq!(s.next_off(), Some(1));
    assert_eq!(s.poll_data(100, 100), Some(C(1, b"bc", false, 0)));
    assert_eq!(s.poll_data(100, 100), Some(C(4, b"ef", true, 2)));
    assert_eq!(s.next_off(), None);
    assert!(s.reset(0));
    assert_eq!(s.next_off(), None);
}

#[test]
fn ack_releases_capacity() {
    // Everything written is acked: the send buffer keeps no allocation.
    const W: usize = 1 << 16;
    let mut s = SendStream::new(W as u64);
    assert_eq!(s.write(&vec![7u8; W], true), Ok(()));
    assert!(s.buf_capacity() >= W);
    while s.poll_data(1200, u64::MAX).is_some() {}
    s.on_data_acked(W as u64 / 2, W as u64 / 2, true);
    assert!(s.buf_capacity() >= W / 2);
    s.on_data_acked(0, W as u64 / 2, false);
    assert_eq!(s.state_exec(), SendState::DataRecvd);
    assert_eq!(s.buf_capacity(), 0);
}
