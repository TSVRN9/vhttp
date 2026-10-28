use quic::codes::*;
use quic::frame::Frame;
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

#[test]
fn stream_data_to_events() {
    let mut s = fresh();
    assert_eq!(feed(&mut s, S(0, 0, b"GET", true)), (Ok(()), vec![D(0, b"GET", true)]));
}

#[test]
fn out_of_order_frames() {
    let mut s = fresh();
    let mut ev = Vec::new();
    assert_eq!(s.on_frame(&S(4, 3, b"lo", true), &mut ev), Ok(()));
    assert_eq!(s.on_frame(&S(4, 0, b"hel", false), &mut ev), Ok(()));
    assert_eq!(ev, vec![D(4, b"hello", true)]);
}

#[test]
fn state_errors() {
    let cases = [
        S(3, 0, b"x", false),
        Frame::ResetStream { stream_id: 3, error_code: 0, final_size: 0 },
        Frame::StreamDataBlocked { stream_id: 3, max: 0 },
        Frame::MaxStreamData { stream_id: 2, max: 10 },
        Frame::StopSending { stream_id: 2, error_code: 0 },
        S(1, 0, b"x", false),
        Frame::ResetStream { stream_id: 1, error_code: 0, final_size: 0 },
        Frame::MaxStreamData { stream_id: 3, max: 10 },
        Frame::StopSending { stream_id: 7, error_code: 0 },
    ];
    for f in cases {
        let mut s = fresh();
        assert_eq!(feed(&mut s, f), (Err(STREAM_STATE_ERROR), vec![]));
        assert!(s.failed());
    }
}

#[test]
fn stream_limit() {
    let mut s = fresh();
    assert_eq!(feed(&mut s, S(10, 0, b"x", false)).0, Ok(()));
    assert_eq!(feed(&mut s, S(14, 0, b"x", false)).0, Err(STREAM_LIMIT_ERROR));
    let mut s = fresh();
    assert_eq!(
        feed(&mut s, Frame::MaxStreamData { stream_id: 14, max: 5 }).0,
        Err(STREAM_STATE_ERROR)
    );
    let mut s = fresh();
    assert_eq!(feed(&mut s, S(40, 0, b"x", false)).0, Err(STREAM_LIMIT_ERROR));
}

#[test]
fn implicit_open() {
    let mut s = fresh();
    let mut ev = Vec::new();
    assert_eq!(s.on_frame(&S(8, 0, b"x", false), &mut ev), Ok(()));
    let f = Frame::ResetStream { stream_id: 0, error_code: 5, final_size: 0 };
    assert_eq!(s.on_frame(&f, &mut ev), Ok(()));
    assert_eq!(ev, vec![D(8, b"x", false), StreamEvent::Reset { id: 0, code: 5 }]);
}

#[test]
fn closed_stream_ignored() {
    let mut s = fresh();
    assert_eq!(feed(&mut s, S(2, 0, b"a", true)), (Ok(()), vec![D(2, b"a", true)]));
    assert_eq!(s.open_streams(), 0);
    assert_eq!(feed(&mut s, S(2, 0, b"a", true)), (Ok(()), vec![]));
    assert_eq!(feed(&mut s, S(2, 0, b"ab", true)), (Ok(()), vec![]));
    let f = Frame::ResetStream { stream_id: 2, error_code: 0, final_size: 9 };
    assert_eq!(feed(&mut s, f), (Ok(()), vec![]));
}

#[test]
fn conn_flow_counts_high_water() {
    let mut l = local();
    l.initial_max_data = 10;
    let mut s = with(&l, &peer());
    assert_eq!(feed(&mut s, S(0, 0, &[0; 8], false)).0, Ok(()));
    assert_eq!(feed(&mut s, S(0, 0, &[0; 8], false)).0, Ok(()));
    assert_eq!(feed(&mut s, S(0, 8, &[0; 2], false)).0, Ok(()));
    assert_eq!(feed(&mut s, S(4, 0, &[0], false)).0, Err(FLOW_CONTROL_ERROR));
}

#[test]
fn reset_final_size_counts() {
    let mut l = local();
    l.initial_max_data = 10;
    let rst = || Frame::ResetStream { stream_id: 0, error_code: 1, final_size: 6 };
    let mut s = with(&l, &peer());
    assert_eq!(feed(&mut s, rst()), (Ok(()), vec![StreamEvent::Reset { id: 0, code: 1 }]));
    assert_eq!(feed(&mut s, S(4, 0, &[0; 5], false)).0, Err(FLOW_CONTROL_ERROR));
    let mut s = with(&l, &peer());
    assert_eq!(feed(&mut s, rst()).0, Ok(()));
    assert_eq!(feed(&mut s, S(4, 0, &[0; 4], false)).0, Ok(()));
}

#[test]
fn stop_sending_unopened() {
    let mut s = fresh();
    let f = Frame::StopSending { stream_id: 3, error_code: 0 };
    assert_eq!(feed(&mut s, f).0, Err(STREAM_STATE_ERROR));
    let mut s = fresh();
    let f = Frame::StopSending { stream_id: 1, error_code: 0 };
    assert_eq!(feed(&mut s, f).0, Err(STREAM_STATE_ERROR));
    let mut s = fresh();
    let mut ev = Vec::new();
    assert_eq!(s.on_frame(&Frame::StopSending { stream_id: 0, error_code: 7 }, &mut ev), Ok(()));
    assert_eq!(ev, vec![StreamEvent::StopSending { id: 0, code: 7 }]);
    assert_eq!(s.on_frame(&S(0, 0, b"GET", true), &mut ev), Ok(()));
    assert_eq!(ev, vec![StreamEvent::StopSending { id: 0, code: 7 }, D(0, b"GET", true)]);
}

#[test]
fn max_data_non_increasing() {
    let mut p = peer();
    p.initial_max_data = 100;
    let mut s = with(&local(), &p);
    assert_eq!(feed(&mut s, Frame::MaxData(50)).0, Ok(()));
    assert_eq!(s.peer_max_data(), 100);
    assert_eq!(feed(&mut s, Frame::MaxData(200)).0, Ok(()));
    assert_eq!(s.peer_max_data(), 200);
}

#[test]
fn max_streams_2_60() {
    let mut s = fresh();
    assert_eq!(feed(&mut s, Frame::MaxStreams { bidi: false, max: 1 << 60 }).0, Ok(()));
    assert_eq!(s.local_uni_limit(), 1 << 60);
    assert_eq!(feed(&mut s, Frame::MaxStreams { bidi: false, max: 5 }).0, Ok(()));
    assert_eq!(s.local_uni_limit(), 1 << 60);
    assert_eq!(feed(&mut s, Frame::MaxStreams { bidi: true, max: 7 }).0, Ok(()));
}

#[test]
fn blocked_frames_ignored() {
    let mut s = fresh();
    for f in [
        Frame::DataBlocked(5),
        Frame::StreamsBlocked { bidi: true, max: 3 },
        Frame::StreamsBlocked { bidi: false, max: 3 },
    ] {
        assert_eq!(feed(&mut s, f), (Ok(()), vec![]));
        assert_eq!(s.open_streams(), 0);
    }
    assert_eq!(feed(&mut s, Frame::StreamDataBlocked { stream_id: 0, max: 5 }), (Ok(()), vec![]));
    assert_eq!(s.open_streams(), 1);
}

#[test]
fn tp_direction_mapping_rx() {
    let mut l = local();
    l.initial_max_stream_data_bidi_remote = 5;
    l.initial_max_stream_data_bidi_local = 1000;
    l.initial_max_stream_data_uni = 7;
    let cases = [
        (S(0, 0, &[0; 6], false), Err(FLOW_CONTROL_ERROR)),
        (S(0, 0, &[0; 5], false), Ok(())),
        (S(2, 0, &[0; 7], false), Ok(())),
        (S(6, 0, &[0; 8], false), Err(FLOW_CONTROL_ERROR)),
    ];
    for (f, want) in cases {
        let mut s = with(&l, &peer());
        assert_eq!(feed(&mut s, f).0, want);
    }
}
