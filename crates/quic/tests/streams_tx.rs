use quic::codes::*;
use quic::frame::{parse_frame, serialize_frame, Frame};
use quic::recv_stream::StreamEvent;
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

#[allow(non_snake_case)]
fn D(id: u64, d: &[u8], fin: bool) -> StreamEvent {
    StreamEvent::Data { id, data: d.to_vec(), fin }
}

fn fresh() -> Streams {
    Streams::new(&local(), &peer())
}

fn with(l: &TransportParams, p: &TransportParams) -> Streams {
    Streams::new(l, p)
}

/// One frame into `s`, returning the result and the events it pushed.
fn feed(s: &mut Streams, f: Frame) -> (Result<(), u64>, Vec<StreamEvent>) {
    let mut ev = Vec::new();
    let r = s.on_frame(&f, &mut ev);
    (r, ev)
}

fn poll(s: &mut Streams, budget: usize) -> Vec<Frame> {
    let mut out = Vec::new();
    s.poll_frames(budget, &mut out);
    out
}

fn enc(f: &Frame) -> Vec<u8> {
    let mut b = Vec::new();
    serialize_frame(f, &mut b);
    b
}

#[test]
fn write_and_poll() {
    let mut s = fresh();
    assert_eq!(feed(&mut s, S(0, 0, b"GET", true)).0, Ok(()));
    assert_eq!(s.write(0, b"hello", true), Ok(()));
    assert_eq!(poll(&mut s, 1200), vec![S(0, 0, b"hello", true)]);
}

fn local_uni_open_frames() -> Vec<Frame> {
    let mut p = peer();
    p.initial_max_streams_uni = 1;
    let mut s = with(&local(), &p);
    assert_eq!(s.write(3, &[0x00, 0x04, 0x00], false), Ok(()));
    for id in [7, 2, 1, 4, 11] {
        assert_eq!(s.write(id, b"x", false), Err(()));
    }
    let out = poll(&mut s, 1200);
    assert_eq!(out, vec![S(3, 0, &[0, 4, 0], false)]);
    assert_eq!(feed(&mut s, Frame::MaxStreams { bidi: false, max: 3 }).0, Ok(()));
    assert_eq!(s.write(11, b"x", false), Err(()));
    assert_eq!(s.write(7, b"x", false), Ok(()));
    out
}

#[test]
fn local_uni_open() {
    local_uni_open_frames();
}

#[test]
fn tp_direction_mapping_tx() {
    let mut p = peer();
    p.initial_max_stream_data_bidi_local = 4;
    p.initial_max_stream_data_bidi_remote = 1000;
    p.initial_max_stream_data_uni = 6;
    let mut s = with(&local(), &p);
    assert_eq!(feed(&mut s, S(0, 0, b"GET", true)).0, Ok(()));
    assert_eq!(s.write(0, b"0123456789", true), Ok(()));
    assert_eq!(s.write(3, b"abcdefghij", false), Ok(()));
    assert_eq!(poll(&mut s, 1200), vec![S(0, 0, b"0123", false), S(3, 0, b"abcdef", false)]);
    assert_eq!(feed(&mut s, Frame::MaxStreamData { stream_id: 0, max: 10 }).0, Ok(()));
    assert_eq!(poll(&mut s, 1200), vec![S(0, 4, b"456789", true)]);
}

#[test]
fn conn_send_limit() {
    let mut p = peer();
    p.initial_max_data = 5;
    let mut s = with(&local(), &p);
    assert_eq!(feed(&mut s, S(0, 0, b"GET", true)).0, Ok(()));
    assert_eq!(s.write(0, b"0123456789", true), Ok(()));
    assert_eq!(poll(&mut s, 1200), vec![S(0, 0, b"01234", false)]);
    assert_eq!(feed(&mut s, Frame::MaxData(3)).0, Ok(()));
    assert_eq!(poll(&mut s, 1200), vec![]);
    assert_eq!(feed(&mut s, Frame::MaxData(8)).0, Ok(()));
    assert_eq!(poll(&mut s, 1200), vec![S(0, 5, b"567", false)]);
}

#[test]
fn budget() {
    let bytes: Vec<u8> = (0..100).collect();
    let mut s = fresh();
    assert_eq!(feed(&mut s, S(0, 0, b"GET", true)).0, Ok(()));
    assert_eq!(s.write(0, &bytes, false), Ok(()));
    let out = poll(&mut s, 20);
    assert_eq!(out, vec![S(0, 0, &bytes[0..17], false)]);
    let e = enc(&out[0]);
    assert_eq!((&e[..3], e.len()), (&[0x0a, 0x00, 0x11][..], 20));
    let out = poll(&mut s, 20);
    assert_eq!(out, vec![S(0, 17, &bytes[17..33], false)]);
    let e = enc(&out[0]);
    assert_eq!((&e[..4], e.len()), (&[0x0e, 0x00, 0x11, 0x10][..], 20));
    assert_eq!(poll(&mut s, 4), vec![]);
    let out = poll(&mut s, 70);
    assert_eq!(out, vec![S(0, 33, &bytes[33..98], false)]);
    assert_eq!(enc(&out[0]).len(), 70);
    assert_eq!(poll(&mut s, 1200), vec![S(0, 98, &bytes[98..100], false)]);
}

#[test]
fn control_frame_budget() {
    let mut s = fresh();
    assert_eq!(feed(&mut s, S(0, 0, b"GET", true)).0, Ok(()));
    assert_eq!(feed(&mut s, Frame::StopSending { stream_id: 0, error_code: 7 }).0, Ok(()));
    assert_eq!(poll(&mut s, 3), vec![]);
    assert_eq!(
        poll(&mut s, 4),
        vec![Frame::ResetStream { stream_id: 0, error_code: 7, final_size: 0 }]
    );
}

fn credit_streams() -> (Streams, Vec<Frame>) {
    let mut l = local();
    l.initial_max_data = 10;
    l.initial_max_stream_data_bidi_remote = 10;
    let mut s = with(&l, &peer());
    assert_eq!(feed(&mut s, S(0, 0, &[0; 6], false)).0, Ok(()));
    let out = poll(&mut s, 1200);
    assert_eq!(out, vec![Frame::MaxData(16), Frame::MaxStreamData { stream_id: 0, max: 16 }]);
    (s, out)
}

#[test]
fn credit_updates_emitted() {
    let (mut s, _) = credit_streams();
    assert_eq!(poll(&mut s, 1200), vec![]);
    assert_eq!(feed(&mut s, S(0, 6, &[0; 10], false)).0, Ok(()));
    assert_eq!(feed(&mut s, S(4, 0, &[0], false)).0, Err(FLOW_CONTROL_ERROR));
}

#[test]
fn lost_credit_resent() {
    let (mut s, _) = credit_streams();
    s.on_frame_lost(&Frame::MaxData(16));
    assert_eq!(poll(&mut s, 1200), vec![Frame::MaxData(16)]);
}

#[test]
fn stop_sending_resets() {
    let mut s = fresh();
    assert_eq!(feed(&mut s, S(0, 0, b"GET", true)).0, Ok(()));
    let (r, ev) = feed(&mut s, Frame::StopSending { stream_id: 0, error_code: 7 });
    assert_eq!(r, Ok(()));
    assert_eq!(ev.last(), Some(&StreamEvent::StopSending { id: 0, code: 7 }));
    assert_eq!(
        poll(&mut s, 1200),
        vec![Frame::ResetStream { stream_id: 0, error_code: 7, final_size: 0 }]
    );
    assert_eq!(s.write(0, b"x", true), Err(()));
}

fn stop_after_partial_frames() -> Vec<Frame> {
    let mut s = fresh();
    let mut all = Vec::new();
    assert_eq!(feed(&mut s, S(0, 0, b"GET", true)).0, Ok(()));
    assert_eq!(s.write(0, b"hello", false), Ok(()));
    let out = poll(&mut s, 1200);
    assert_eq!(out, vec![S(0, 0, b"hello", false)]);
    all.extend(out);
    assert_eq!(feed(&mut s, Frame::StopSending { stream_id: 0, error_code: 9 }).0, Ok(()));
    let out = poll(&mut s, 1200);
    assert_eq!(out, vec![Frame::ResetStream { stream_id: 0, error_code: 9, final_size: 5 }]);
    all.extend(out);
    s.on_frame_lost(&S(0, 0, b"hello", false));
    assert_eq!(poll(&mut s, 1200), vec![]);
    all
}

#[test]
fn stop_sending_after_partial() {
    stop_after_partial_frames();
}

#[test]
fn app_reset_and_stop() {
    let mut s = fresh();
    let mut ev = Vec::new();
    assert_eq!(s.on_frame(&S(0, 0, b"GET", false), &mut ev), Ok(()));
    s.reset(0, 0x10c);
    s.stop_sending(0, 0x10c);
    assert_eq!(
        poll(&mut s, 1200),
        vec![
            Frame::ResetStream { stream_id: 0, error_code: 0x10c, final_size: 0 },
            Frame::StopSending { stream_id: 0, error_code: 0x10c },
        ]
    );
    assert_eq!(s.on_frame(&S(0, 3, b"x", true), &mut ev), Ok(()));
    assert_eq!(ev, vec![D(0, b"GET", false), D(0, b"x", true)]);
    assert_eq!(s.open_streams(), 1);
    s.on_frame_acked(&Frame::ResetStream { stream_id: 0, error_code: 0x10c, final_size: 0 });
    assert_eq!(s.open_streams(), 0);
}

#[test]
fn reset_one_direction() {
    let mut s = fresh();
    let mut ev = Vec::new();
    assert_eq!(s.on_frame(&S(0, 0, b"GET", false), &mut ev), Ok(()));
    let f = Frame::ResetStream { stream_id: 0, error_code: 1, final_size: 3 };
    assert_eq!(s.on_frame(&f, &mut ev), Ok(()));
    assert_eq!(ev, vec![D(0, b"GET", false), StreamEvent::Reset { id: 0, code: 1 }]);
    assert_eq!(s.write(0, b"resp", true), Ok(()));
    assert_eq!(feed(&mut s, Frame::MaxStreamData { stream_id: 0, max: 200 }).0, Ok(()));
    assert_eq!(poll(&mut s, 1200), vec![S(0, 0, b"resp", true)]);
}

#[test]
fn max_streams_credit() {
    let mut s = fresh();
    assert_eq!(feed(&mut s, S(2, 0, b"a", true)).0, Ok(()));
    assert_eq!(feed(&mut s, S(6, 0, b"b", true)).0, Ok(()));
    assert_eq!(poll(&mut s, 1200), vec![Frame::MaxStreams { bidi: false, max: 5 }]);
    assert_eq!(feed(&mut s, S(10, 0, b"c", true)).0, Ok(()));
    assert_eq!(feed(&mut s, S(14, 0, b"d", true)).0, Ok(()));
    assert_eq!(feed(&mut s, S(18, 0, b"e", false)).0, Ok(()));
    assert_eq!(feed(&mut s, S(22, 0, b"f", false)).0, Err(STREAM_LIMIT_ERROR));
}

#[test]
fn ack_frees_stream() {
    let mut s = fresh();
    assert_eq!(feed(&mut s, S(0, 0, b"GET", true)).0, Ok(()));
    assert_eq!(s.write(0, b"ok", true), Ok(()));
    let out = poll(&mut s, 1200);
    assert_eq!(out.len(), 1);
    s.on_frame_acked(&out[0]);
    assert_eq!(s.open_streams(), 0);
    assert_eq!(feed(&mut s, S(0, 0, b"GET", true)), (Ok(()), vec![]));
}

#[test]
fn emitted_frames_roundtrip() {
    let mut all = credit_streams().1;
    all.extend(stop_after_partial_frames());
    all.extend(local_uni_open_frames());
    assert_eq!(all.len(), 5);
    for f in &all {
        let b = enc(f);
        let (g, n) = parse_frame(&b).expect("parses");
        assert_eq!((&g, n), (f, b.len()));
    }
}
