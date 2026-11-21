//! Phase 3d stream-layer bounds: the own-uni cap, the connection send-buffer cap (on the send
//! queues' `max(128, 6·peak)` reservations since 9b2 Task 8) and the new-data gate on acked + lost
//! ranges.
use quic::frame::Frame;
use quic::send_stream::MAX_SEND_RANGES;
use quic::streams::*;
use quic::tp::*;

fn local() -> TransportParams {
    let mut t = default_transport_params();
    t.initial_max_data = 1000;
    t.initial_max_stream_data_bidi_remote = 100;
    t.initial_max_stream_data_uni = 100;
    t.initial_max_streams_bidi = 10;
    t.initial_max_streams_uni = 3;
    t
}

fn peer() -> TransportParams {
    let mut t = default_transport_params();
    t.initial_max_data = 1000;
    t.initial_max_stream_data_bidi_local = 100;
    t.initial_max_stream_data_uni = 100;
    t.initial_max_streams_uni = 3;
    t
}

#[allow(non_snake_case)]
fn S(stream_id: u64, offset: u64, d: &[u8], fin: bool) -> Frame {
    Frame::Stream { stream_id, offset, data: d.to_vec(), fin }
}

fn feed(s: &mut Streams, f: Frame) -> Result<(), u64> {
    let mut ev = Vec::new();
    s.on_frame(&f, &mut ev)
}

fn poll(s: &mut Streams, budget: usize) -> Vec<Frame> {
    let mut out = Vec::new();
    s.poll_frames(budget, &mut out);
    out
}

#[test]
fn own_uni_cap() {
    let mut p = peer();
    p.initial_max_streams_uni = 100;
    let mut s = Streams::new(&local(), &p);
    assert_eq!(s.write(3, b"a", false), Ok(()));
    assert_eq!(s.write(7, b"a", false), Ok(()));
    assert_eq!(s.write(11, b"a", false), Ok(()));
    assert_eq!(s.write(15, b"a", false), Err(()));
    assert_eq!(s.local_uni_limit(), 100);
}

/// A client request on stream 0 with its send queue full: a queue of peak P reserves `6·P`, so an
/// empty queue takes `MAX_SEND_BUFFER/6`.
fn full_buffer() -> Streams {
    let mut p = peer();
    p.initial_max_data = 1 << 30;
    p.initial_max_stream_data_bidi_local = 1 << 30;
    let mut s = Streams::new(&local(), &p);
    assert_eq!(feed(&mut s, S(0, 0, b"GET", true)), Ok(()));
    assert_eq!(s.send_room(0), 174_762);
    assert_eq!(s.write(0, &vec![7u8; 174_763], false), Err(()));
    assert_eq!(s.write(0, &vec![7u8; 174_762], false), Ok(()));
    assert_eq!(s.send_room(0), 0);
    assert_eq!(s.send_capacity(), 3 * 174_762);
    s
}

#[test]
fn send_buffer_cap() {
    let mut s = full_buffer();
    assert_eq!(s.write(0, &[7], false), Err(()));
    assert_eq!(s.write(0, &[], true), Ok(()));
}

#[test]
fn room_after_ack() {
    let mut s = full_buffer();
    assert_eq!(s.write(0, &[], true), Ok(()));
    loop {
        let out = poll(&mut s, 1 << 21);
        if out.is_empty() {
            break;
        }
        for f in &out {
            s.on_frame_acked(f);
        }
    }
    assert_eq!(s.send_room(0), 174_762);
    assert_eq!(s.send_capacity(), 0);
    assert_eq!(s.open_streams(), 0);
}

#[test]
fn room_after_reset() {
    let mut s = Streams::new(&local(), &peer());
    assert_eq!(feed(&mut s, S(0, 0, b"GET", false)), Ok(()));
    assert_eq!(s.write(0, &[1; 1000], false), Ok(()));
    assert_eq!(s.send_room(0), 174_762 - 1000);
    s.reset(0, 1);
    assert_eq!(s.send_room(0), 174_762);
    assert_eq!(s.send_capacity(), 0);
}

/// The credit-drip adversary with simulated PTOs: one byte of stream credit per round, every
/// other packet that carried only new data acked, retransmissions never acked, and everything
/// outstanding declared lost every 20 rounds. After every round the sending part's acked, lost
/// and in-flight sets hold at most `sent/256 + 4` entries and at most `buffered/256 + 4`
/// (D10 (d), proved in `SendStream::wf`). Here the `MAX_SEND_RANGES` gate cannot close: the drip
/// sends about 400 bytes, so the sets hold at most 5 items against a gate of 64; its `closed`
/// check stays as a guard, and `send_stream::range_gate_closes` closes the gate for real.
#[test]
fn range_gate_pto_cycles() {
    let mut p = peer();
    p.initial_max_data = 1 << 30;
    p.initial_max_stream_data_bidi_local = 1;
    let mut s = Streams::new(&local(), &p);
    assert_eq!(feed(&mut s, S(0, 0, b"GET", true)), Ok(()));
    assert_eq!(s.write(0, &[9; 10_000], true), Ok(()));
    let mut outstanding: Vec<Frame> = Vec::new();
    let mut hi = 0u64; // end of the highest byte sent: new data starts here
    let mut new_only = 0u32;
    for r in 0..400u64 {
        assert_eq!(feed(&mut s, Frame::MaxStreamData { stream_id: 0, max: r + 2 }), Ok(()));
        let (a, l, _) = s.send_range_counts(0).unwrap();
        // A poll retransmits every lost range before any new data, so the gate it meets is
        // closed exactly when the acked ranges alone fill it.
        let closed = a >= MAX_SEND_RANGES;
        let pkt = poll(&mut s, 1200);
        let mut any_new = false;
        let mut all_new = !pkt.is_empty();
        let mut end = hi;
        for f in &pkt {
            if let Frame::Stream { offset, data, .. } = f {
                let new = *offset >= hi && !data.is_empty();
                any_new |= new;
                all_new &= new;
                end = end.max(offset + data.len() as u64);
            }
        }
        hi = end;
        if closed {
            assert!(!any_new, "round {r}: new data with {a} acked + {l} lost ranges");
        }
        if all_new {
            new_only += 1;
        }
        if all_new && new_only % 2 == 0 {
            for f in &pkt {
                s.on_frame_acked(f);
            }
        } else {
            outstanding.extend(pkt);
        }
        if r % 20 == 19 {
            for f in std::mem::take(&mut outstanding) {
                s.on_frame_lost(&f);
            }
        }
        let (a, l, f) = s.send_range_counts(0).unwrap();
        let b = s.send_buffered(0).unwrap();
        assert!(a + l + f <= b / 256 + 4, "round {r}: {a} acked, {l} lost, {f} in flight, {b} buffered");
        assert!(a + l + f <= hi as usize / 256 + 4, "round {r}: {a} acked, {l} lost, {f} in flight, {hi} sent");
    }
}

/// Carryover mem-9b2-send-cap: a send queue keeps its capacity until it is empty, so withheld ACKs
/// keep memory held. Several streams each write 64 KiB with the FIN, sent in 1 KiB pieces, every
/// piece acknowledged but the last: after every call the queues' capacity (the allocator's sizes)
/// stays within `MAX_SEND_BUFFER` (each queue holds `6·64 KiB` reserved until it empties, so two
/// fit), and a write past a stream's room is refused.
#[test]
fn held_capacity_within_cap() {
    const W: usize = 64 << 10;
    let mut p = peer();
    p.initial_max_data = 1 << 30;
    p.initial_max_stream_data_bidi_local = 1 << 30;
    let mut l = local();
    l.initial_max_streams_bidi = 100;
    let mut s = Streams::new(&l, &p);
    let mut refused = 0;
    let mut written = Vec::new();
    for k in 0..40u64 {
        let id = 4 * k;
        assert_eq!(feed(&mut s, S(id, 0, b"GET", true)), Ok(()));
        let room = s.send_room(id) as usize;
        if room < W {
            assert_eq!(s.write(id, &vec![1u8; room + 1], true), Err(()));
            assert!(s.send_capacity() <= 1 << 20);
            refused += 1;
            continue;
        }
        assert_eq!(s.write(id, &vec![1u8; W], true), Ok(()));
        assert!(s.send_capacity() <= 1 << 20);
        written.push(id);
        let mut held_back = None;
        loop {
            let out = poll(&mut s, 1024 + 32);
            assert!(s.send_capacity() <= 1 << 20);
            if out.is_empty() {
                break;
            }
            for f in out {
                match &f {
                    Frame::Stream { offset, data, .. } if *offset as usize + data.len() == W => held_back = Some(f),
                    _ => s.on_frame_acked(&f),
                }
                assert!(s.send_capacity() <= 1 << 20);
            }
        }
        assert!(held_back.is_some());
    }
    assert!(written.len() == 2 && refused > 0, "written {} refused {refused}", written.len());
}

/// The reservation's steady window (owner decision 2026-11-17, option (b)): a stream whose queue
/// peaked at `MAX_SEND_BUFFER/6` has its room back byte for byte as its pieces are acknowledged,
/// while the others wait until it empties (its reservation stays `6·peak` until then).
#[test]
fn room_refills_as_acks_arrive() {
    let mut p = peer();
    p.initial_max_data = 1 << 30;
    p.initial_max_stream_data_bidi_local = 1 << 30;
    let mut s = Streams::new(&local(), &p);
    assert_eq!(feed(&mut s, S(0, 0, b"GET", true)), Ok(()));
    assert_eq!(feed(&mut s, S(4, 0, b"GET", true)), Ok(()));
    assert_eq!(s.write(0, &vec![7u8; 174_762], false), Ok(()));
    assert_eq!((s.send_room(0), s.send_room(4)), (0, 0));
    let mut sent = Vec::new();
    loop {
        let out = poll(&mut s, 1024 + 32);
        if out.is_empty() {
            break;
        }
        sent.extend(out);
    }
    let len = |f: &Frame| match f {
        Frame::Stream { data, .. } => data.len() as u64,
        _ => panic!("only STREAM frames"),
    };
    assert_eq!(sent.iter().map(len).sum::<u64>(), 174_762);
    let (last, rest) = sent.split_last().unwrap();
    let mut acked = 0;
    for f in rest {
        s.on_frame_acked(f);
        acked += len(f);
        assert_eq!((s.send_room(0), s.send_room(4)), (acked, 0));
        assert!(s.send_capacity() <= 6 * 174_762);
    }
    s.on_frame_acked(last);
    assert_eq!((s.send_room(0), s.send_room(4)), (174_762, 174_762));
    assert_eq!(s.send_capacity(), 0);
}

/// Review Focus 7 (D10 (e), D13): STOP_SENDING on a stream holding hundreds of ranges resets it in O(1): its sets move
/// to its teardown slot, whose window stays charged against `MAX_SEND_BUFFER`, so another stream's room stays below
/// `MAX_SEND_BUFFER/6` while the slot holds nodes. The part is queued; `deliver_some` (the pump's STREAM half) frees
/// the slot a budget at a time, and only then does the room come back whole and the finished entry go.
#[test]
fn stop_sending_reaps_by_pump() {
    let mut p = peer();
    p.initial_max_data = 1 << 30;
    p.initial_max_stream_data_bidi_local = 1 << 30;
    let mut s = Streams::new(&local(), &p);
    assert_eq!(feed(&mut s, S(0, 0, b"GET", true)), Ok(()));
    assert_eq!(s.write(0, &vec![7u8; 174_762], false), Ok(()));
    let mut sent = Vec::new();
    loop {
        let out = poll(&mut s, 280);
        if out.is_empty() {
            break;
        }
        sent.extend(out);
    }
    for (i, f) in sent.iter().enumerate() {
        if i % 2 == 1 {
            s.on_frame_acked(f);
        } else {
            s.on_frame_lost(f);
        }
    }
    let (a, l, f) = s.send_range_counts(0).unwrap();
    assert!(a + l >= 600 && f == 0, "{a} acked, {l} lost, {f} in flight");
    assert!(!s.stream_backlog());
    assert_eq!(feed(&mut s, Frame::StopSending { stream_id: 0, error_code: 5 }), Ok(()));
    assert_eq!(s.send_range_counts(0), Some((0, 0, 0)));
    assert_eq!(s.send_td_len(0), Some(a + l));
    assert!(s.stream_backlog());
    // The RESET_STREAM goes and is acknowledged: both parts are terminal, but the slot keeps the entry.
    let out = poll(&mut s, 1200);
    assert!(out.iter().any(|f| matches!(f, Frame::ResetStream { stream_id: 0, .. })));
    for f in &out {
        s.on_frame_acked(f);
    }
    assert_eq!(s.open_streams(), 1);
    let mut ev = Vec::new();
    let mut steps = 0;
    while s.stream_backlog() {
        assert!(steps < 1000, "still backlog after {steps} steps");
        assert!(s.send_room(4) < 174_762);
        assert_eq!(s.open_streams(), 1);
        let _ = s.deliver_some(4096, &mut ev);
        steps += 1;
    }
    assert!(steps >= 2, "{steps} steps");
    assert_eq!(s.send_room(4), 174_762);
    assert_eq!(s.open_streams(), 0);
}
