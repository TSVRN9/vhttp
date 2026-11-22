use quic::codes::*;
use quic::recv_stream::*;

#[allow(non_snake_case)]
fn D(d: &[u8], fin: bool) -> StreamEvent {
    StreamEvent::Data { id: 0, data: d.to_vec(), fin }
}

type Out = (Result<u64, u64>, Vec<StreamEvent>);

/// A STREAM frame as the frame path takes it: `on_data`, then a delivery of at most its length.
fn data(s: &mut RecvStream, off: u64, d: &[u8], fin: bool, room: u64) -> Out {
    let mut ev = Vec::new();
    let (r, _) = s.on_data(off, d, fin, room);
    if r.is_ok() {
        let _ = s.deliver(d.len() as u64, &mut ev);
    }
    (r, ev)
}

/// A delivery of at most `max` bytes (`pump_backlog`'s).
fn deliver(s: &mut RecvStream, max: u64) -> Vec<StreamEvent> {
    let mut ev = Vec::new();
    let _ = s.deliver(max, &mut ev);
    ev
}

fn reset(s: &mut RecvStream, code: u64, fs: u64, room: u64) -> Out {
    let mut ev = Vec::new();
    let (r, _) = s.on_reset(code, fs, room, &mut ev);
    (r, ev)
}

#[test]
fn ordered_delivery() {
    let mut s = RecvStream::new(0, 100);
    assert_eq!(data(&mut s, 3, b"def", false, 1000), (Ok(6), vec![]));
    // A frame delivers at most its own length; the rest waits for `deliver`.
    assert_eq!(data(&mut s, 0, b"abc", false, 1000), (Ok(0), vec![D(b"abc", false)]));
    assert!(s.has_ready());
    assert_eq!(data(&mut s, 6, b"", true, 1000), (Ok(0), vec![]));
    assert_eq!(s.state(), RecvState::DataRecvd);
    assert_eq!(deliver(&mut s, 100), vec![D(b"def", true)]);
    assert_eq!(s.state(), RecvState::DataRead);
    assert!(!s.has_ready());
}

#[test]
fn fin_out_of_order() {
    let mut s = RecvStream::new(0, 100);
    assert_eq!(data(&mut s, 3, b"de", true, 1000).1, vec![]);
    assert_eq!(s.state(), RecvState::SizeKnown);
    assert_eq!(data(&mut s, 0, b"abc", false, 1000).1, vec![D(b"abc", false)]);
    assert_eq!(s.state(), RecvState::DataRecvd);
    assert_eq!(deliver(&mut s, 1), vec![D(b"d", false)]);
    assert_eq!(deliver(&mut s, 1), vec![D(b"e", true)]);
    assert_eq!(s.state(), RecvState::DataRead);
    assert_eq!(deliver(&mut s, 1), vec![]);
}

/// Review Focus 1: 100 bytes delivered, then a 0-byte FIN frame at 100: "Data Recvd" to "Data
/// Read" in that call, one `Data { fin: true }` event.
#[test]
fn fin_only_frame_after_delivery_completes() {
    let mut s = RecvStream::new(0, 1000);
    assert_eq!(data(&mut s, 0, &[7; 100], false, 1000).1, vec![D(&[7; 100], false)]);
    assert_eq!(s.state(), RecvState::Recv);
    assert_eq!(data(&mut s, 100, b"", true, 1000), (Ok(0), vec![D(b"", true)]));
    assert_eq!(s.state(), RecvState::DataRead);
}

/// RFC 9000 §3.2: a RESET_STREAM in "Data Recvd" is ignored (with the right final size) and the
/// data is still delivered; a wrong final size is still FINAL_SIZE_ERROR.
#[test]
fn reset_in_data_recvd_still_delivers() {
    let mut s = RecvStream::new(0, 100);
    let (r, _) = s.on_data(0, b"hello", true, 1000);
    assert_eq!(r, Ok(5));
    assert_eq!(s.state(), RecvState::DataRecvd);
    assert_eq!(reset(&mut s, 9, 5, 1000), (Ok(0), vec![]));
    assert_eq!(s.state(), RecvState::DataRecvd);
    assert_eq!(reset(&mut s, 9, 6, 1000).0, Err(FINAL_SIZE_ERROR));
    assert_eq!(deliver(&mut s, 100), vec![D(b"hello", true)]);
    assert_eq!(s.state(), RecvState::DataRead);
}

/// D12: a 1-byte frame that fills a 16 KiB gap delivers at most 1 byte; `deliver` hands over the
/// rest.
#[test]
fn on_data_delivers_at_most_d() {
    const N: usize = 16 << 10;
    let mut s = RecvStream::new(0, 1 << 16);
    assert!(data(&mut s, 1, &vec![5; N], false, 1 << 20).1.is_empty());
    let ev = data(&mut s, 0, b"x", false, 1 << 20).1;
    assert_eq!(ev, vec![D(b"x", false)]);
    assert!(s.has_ready());
    let mut got = 0;
    while s.has_ready() {
        for e in deliver(&mut s, 4096) {
            if let StreamEvent::Data { data, .. } = e {
                assert!(data.len() <= 4096);
                got += data.len();
            }
        }
    }
    assert_eq!(got, N);
}

#[test]
fn final_size_rules() {
    let fse = Err(FINAL_SIZE_ERROR);
    // (a)
    let mut s = RecvStream::new(0, 100);
    assert!(data(&mut s, 0, b"abcdefghij", true, 1000).0.is_ok());
    assert_eq!(data(&mut s, 0, b"abcdefghijkl", true, 1000).0, fse);
    // (b)
    let mut s = RecvStream::new(0, 100);
    assert!(data(&mut s, 10, b"", true, 1000).0.is_ok());
    assert_eq!(data(&mut s, 10, b"x", false, 1000).0, fse);
    // (c)
    let mut s = RecvStream::new(0, 100);
    assert!(data(&mut s, 0, &[0; 8], false, 1000).0.is_ok());
    assert_eq!(data(&mut s, 5, b"", true, 1000).0, fse);
    // (d)
    let mut s = RecvStream::new(0, 100);
    assert!(data(&mut s, 10, b"", true, 1000).0.is_ok());
    assert_eq!(reset(&mut s, 0, 9, 1000).0, fse);
    // (e)
    let mut s = RecvStream::new(0, 100);
    assert!(data(&mut s, 10, b"", true, 1000).0.is_ok());
    assert_eq!(reset(&mut s, 7, 10, 1000), (Ok(0), vec![StreamEvent::Reset { id: 0, code: 7 }]));
    assert_eq!(s.state(), RecvState::ResetRead);
    // (f)
    let mut s = RecvStream::new(0, 100);
    assert!(data(&mut s, 0, &[0; 8], false, 1000).0.is_ok());
    assert_eq!(reset(&mut s, 0, 5, 1000).0, fse);
    // (g)
    let mut s = RecvStream::new(0, 100);
    assert!(data(&mut s, 0, b"abc", true, 1000).0.is_ok());
    assert_eq!(s.state(), RecvState::DataRead);
    assert_eq!(data(&mut s, 0, b"abc", true, 1000), (Ok(0), vec![]));
    assert_eq!(reset(&mut s, 0, 3, 1000), (Ok(0), vec![]));
    assert_eq!(reset(&mut s, 0, 4, 1000).0, fse);
    // (h)
    let mut s = RecvStream::new(0, 100);
    assert!(data(&mut s, 10, b"", true, 1000).0.is_ok());
    assert_eq!(data(&mut s, 0, b"abcde", true, 1000).0, fse);
}

#[test]
fn flow_control() {
    let mut s = RecvStream::new(0, 10);
    assert_eq!(data(&mut s, 5, b"abcde", false, 1000).0, Ok(10));
    assert_eq!(data(&mut s, 10, b"x", false, 1000).0, Err(FLOW_CONTROL_ERROR));
    let mut s = RecvStream::new(0, 10);
    assert_eq!(reset(&mut s, 0, 11, 1000).0, Err(FLOW_CONTROL_ERROR));
    let mut s = RecvStream::new(0, 10);
    assert_eq!(data(&mut s, 0, b"abcde", false, 4), (Err(FLOW_CONTROL_ERROR), vec![]));
    assert_eq!(data(&mut s, 0, b"abcd", false, 4), (Ok(4), vec![D(b"abcd", false)]));
}

#[test]
fn error_precedence() {
    let mut s = RecvStream::new(0, 10);
    assert!(data(&mut s, 10, b"", true, 1000).0.is_ok());
    assert_eq!(data(&mut s, 10, b"x", false, 0).0, Err(FINAL_SIZE_ERROR));
}

#[test]
fn duplicates_not_recounted() {
    let mut s = RecvStream::new(0, 100);
    assert_eq!(data(&mut s, 0, b"abcd", false, 1000).0, Ok(4));
    assert_eq!(data(&mut s, 0, b"abcd", false, 1000).0, Ok(0));
    assert_eq!(data(&mut s, 2, b"cdef", false, 1000).0, Ok(2));
}

#[test]
fn conflicting_retransmit() {
    let mut s = RecvStream::new(0, 100);
    assert!(data(&mut s, 0, b"abc", false, 1000).0.is_ok());
    assert_eq!(data(&mut s, 0, b"xyz", false, 1000), (Ok(0), vec![]));
    assert_eq!(data(&mut s, 2, b"QR", true, 1000).1, vec![D(b"R", true)]);
}

#[test]
fn credit() {
    let mut s = RecvStream::new(0, 10);
    assert!(data(&mut s, 0, &[0; 6], false, 1000).0.is_ok());
    assert_eq!(s.pending_credit(), Some(16));
    assert_eq!(data(&mut s, 6, &[0; 5], false, 1000).0, Err(FLOW_CONTROL_ERROR));
    s.commit_credit();
    assert_eq!(s.pending_credit(), None);
    assert_eq!(data(&mut s, 6, &[0; 10], true, 1000).0, Ok(10));
    assert_eq!(s.state(), RecvState::DataRead);
    assert_eq!(s.pending_credit(), None);

    let mut s = RecvStream::new(0, 10);
    assert!(data(&mut s, 0, &[0; 6], false, 1000).0.is_ok());
    s.commit_credit();
    s.credit_lost();
    assert_eq!(s.pending_credit(), Some(16));
}

#[test]
fn stop_keeps_events() {
    let mut s = RecvStream::new(0, 100);
    assert_eq!(data(&mut s, 0, b"ab", false, 1000).1, vec![D(b"ab", false)]);
    assert!(s.stop(0));
    assert_eq!(s.pending_stop(), Some(0));
    s.commit_stop();
    assert!(!s.stop(0));
    assert_eq!(data(&mut s, 2, b"cd", true, 1000), (Ok(2), vec![D(b"cd", true)]));
    assert_eq!(s.state(), RecvState::DataRead);
    assert_eq!(s.retired_exec(), 4);

    let mut s = RecvStream::new(0, 100);
    assert!(s.stop(0));
    assert_eq!(reset(&mut s, 3, 0, 1000), (Ok(0), vec![StreamEvent::Reset { id: 0, code: 3 }]));
    assert_eq!(s.state(), RecvState::ResetRead);

    let mut s = RecvStream::new(0, 100);
    assert!(s.stop(0));
    assert!(data(&mut s, 0, &[0; 60], false, 1000).0.is_ok());
    assert_eq!(s.pending_credit(), None);
}

#[test]
fn reset_counts() {
    let mut s = RecvStream::new(0, 100);
    assert!(data(&mut s, 0, b"abc", false, 1000).0.is_ok());
    assert_eq!(reset(&mut s, 1, 10, 1000).0, Ok(7));
    assert_eq!(s.retired_exec(), 10);
    assert_eq!(s.buffered_len(), 0);
}

#[test]
fn buffer_bound() {
    let mut s = RecvStream::new(0, 10);
    assert!(data(&mut s, 9, b"z", false, 1000).0.is_ok());
    // Exactly limit - delivered, and one byte past it is refused with nothing buffered.
    assert_eq!(s.buffered_len(), 10);
    assert_eq!(data(&mut s, 10, b"y", false, 1000).0, Err(FLOW_CONTROL_ERROR));
    assert_eq!(s.buffered_len(), 10);
    assert_eq!(data(&mut s, 0, b"a", false, 1000), (Ok(0), vec![D(b"a", false)]));
    assert_eq!(s.buffered_len(), 9);
}

#[test]
fn no_stop_sending_after_reset() {
    // Peer reset first: stop() queues nothing.
    let mut s = RecvStream::new(0, 100);
    assert!(reset(&mut s, 3, 0, 1000).0.is_ok());
    assert!(!s.stop(0));
    assert_eq!(s.pending_stop(), None);
    // Stopped, then the peer's reset arrives before the STOP_SENDING is sent.
    let mut s = RecvStream::new(0, 100);
    assert!(s.stop(5));
    assert!(reset(&mut s, 3, 0, 1000).0.is_ok());
    assert_eq!(s.pending_stop(), None);
    s.stop_lost();
    assert_eq!(s.pending_stop(), None);
}

/// An empty STREAM frame inside the window buffers nothing (no unreceived slots).
#[test]
fn empty_stream_frame_keeps_window() {
    let mut s = RecvStream::new(0, 100);
    assert_eq!(data(&mut s, 0, &[1; 10], false, 1000).0, Ok(10));
    assert_eq!(s.page_count(), 0);
    assert_eq!(data(&mut s, 90, &[], false, 1000).0, Ok(80));
    assert_eq!(s.page_count(), 0);
    assert_eq!(s.buffered_len(), 0);
}

/// An empty STREAM frame's offset is the next byte its sender would send (RFC 9000 §19.8), so a
/// later FIN below it lowers the final size under the largest received offset.
#[test]
fn empty_frame_offset_bounds_final_size() {
    let mut s = RecvStream::new(0, 100);
    assert_eq!(data(&mut s, 90, &[], false, 1000).0, Ok(90));
    assert_eq!(data(&mut s, 0, &[1; 50], true, 1000).0, Err(FINAL_SIZE_ERROR));
}
