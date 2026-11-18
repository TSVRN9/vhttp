//! Phase 3d2 Task 4: the HTTP/3 adapter over `Connection`.
// The helpers are the plan's shared set, copied into every 3d2 test file.
#![allow(dead_code, non_snake_case)]
use h3::conn::Output;
use h3::frame::{parse_frame_header, serialize_frame_header, FrameHeader};
use h3::message::Response;
use h3::qpack::field_section::{decode_field_section, encode_field_section, FieldLine};
use quic::ack::AckFrame;
use quic::conn::*;
use quic::datagram::*;
use quic::frame::Frame;
use quic::h3_server::*;
use quic::lifecycle::Phase;
use quic::payload::PacketKind;
use quic::tp::*;

fn rnd(n: u8) -> [u8; 129] {
    let mut r = [0u8; 129];
    for (j, b) in r.iter_mut().enumerate() {
        *b = n.wrapping_add(j as u8);
    }
    r
}

const S1: [u8; 8] = [0x83, 0x94, 0xc8, 0xf0, 0x3e, 0x51, 0x57, 0x08];
const C1: [u8; 8] = [0xc1; 8];
const L0: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

fn D(x: u8) -> [u8; 8] {
    [x; 8]
}

fn A(l: u64, d: u64, f: u64, r: Vec<(u64, u64)>) -> AckFrame {
    AckFrame { largest: l, delay: d, first_range: f, ranges: r, ecn: None }
}

fn CC(app: bool, c: u64, r: &[u8]) -> Frame {
    Frame::ConnectionClose { app, error_code: c, frame_type: 0, reason: r.to_vec() }
}

fn ltp() -> TransportParams {
    let mut t = default_transport_params();
    t.max_idle_timeout = 30000;
    t.initial_max_data = 1000;
    t.initial_max_stream_data_bidi_remote = 100;
    t.initial_max_stream_data_uni = 100;
    t.initial_max_streams_bidi = 10;
    t.initial_max_streams_uni = 3;
    t.active_connection_id_limit = 2;
    t.disable_active_migration = true;
    t
}

fn ptp() -> TransportParams {
    let mut t = default_transport_params();
    t.initial_source_connection_id = Some(C1.to_vec());
    t.initial_max_data = 1000;
    t.initial_max_stream_data_bidi_local = 100;
    t.initial_max_stream_data_uni = 100;
    t.initial_max_streams_uni = 3;
    t.active_connection_id_limit = 4;
    t
}

fn pkt(kind: PacketKind, dcid: &[u8], scid: &[u8], pn: u64, frames: Vec<Frame>) -> PlainPacket {
    PlainPacket { kind, dcid: dcid.to_vec(), scid: scid.to_vec(), token: vec![], pn, frames }
}

fn ini(pn: u64, f: Vec<Frame>) -> PlainPacket {
    pkt(PacketKind::Initial, &S1, &C1, pn, f)
}

fn ini2(pn: u64, f: Vec<Frame>) -> PlainPacket {
    pkt(PacketKind::Initial, &L0, &C1, pn, f)
}

fn hs(pn: u64, f: Vec<Frame>) -> PlainPacket {
    pkt(PacketKind::Handshake, &L0, &C1, pn, f)
}

fn one(pn: u64, f: Vec<Frame>) -> PlainPacket {
    pkt(PacketKind::OneRtt, &L0, &[], pn, f)
}

fn one_on(pn: u64, dcid: &[u8], f: Vec<Frame>) -> PlainPacket {
    pkt(PacketKind::OneRtt, dcid, &[], pn, f)
}

fn first_frames() -> Vec<Frame> {
    vec![Frame::Crypto { offset: 0, data: vec![1; 100] }]
}

fn conn() -> Connection {
    let mut c = Connection::accept(&ini(2, first_frames()), 1200, 0, 0, &rnd(1), &ltp()).unwrap();
    c.on_datagram(0, 1200, vec![ini(2, first_frames())], None, 0, &rnd(1));
    c
}

fn established_with(p: TransportParams) -> Connection {
    let mut c = conn();
    c.on_datagram(0, 1200, vec![hs(0, vec![Frame::Ping])], None, 10, &rnd(9));
    c.on_peer_params(&p, 10);
    c.on_handshake_complete(b"h3", 10, &rnd(2));
    c
}

fn established_rx() -> Connection {
    established_with(ptp())
}

/// Polls until None; a frame left due forever fails here rather than hanging the suite.
fn drain(c: &mut Connection, now: u64) -> Vec<OutDatagram> {
    let mut v = Vec::new();
    while let Some(d) = c.poll_transmit(now) {
        v.push(d);
        assert!(v.len() <= 1024, "poll_transmit never returned None");
    }
    v
}

fn established_tx_with(p: TransportParams) -> Connection {
    let mut c = established_with(p);
    drain(&mut c, 10);
    c
}

fn established() -> Connection {
    established_tx_with(ptp())
}


/// The ACK frame for these distinct packet numbers.
fn ack_of(pns: &[u64]) -> AckFrame {
    let mut s = pns.to_vec();
    s.sort_unstable();
    s.reverse();
    let mut ranges = Vec::new();
    let largest = s[0];
    let mut low = s[0];
    let mut first = None;
    let mut top = s[0];
    let mut pending_gap = 0;
    for &p in &s[1..] {
        if p + 1 == low {
            low = p;
            continue;
        }
        match first {
            None => first = Some(top - low),
            Some(_) => ranges.push((pending_gap, top - low)),
        }
        pending_gap = low - p - 2;
        top = p;
        low = p;
    }
    match first {
        None => first = Some(top - low),
        Some(_) => ranges.push((pending_gap, top - low)),
    }
    AckFrame { largest, delay: 0, first_range: first.unwrap(), ranges, ecn: None }
}

fn stream(id: u64, off: u64, d: &[u8], fin: bool) -> Frame {
    Frame::Stream { stream_id: id, offset: off, data: d.to_vec(), fin }
}

fn fl(n: &[u8], v: &[u8]) -> FieldLine {
    FieldLine { name: n.to_vec(), value: v.to_vec() }
}

/// A HEADERS frame of these fields.
fn headers(f: &[FieldLine]) -> Vec<u8> {
    let mut b = Vec::new();
    encode_field_section(f, &mut b);
    let mut out = Vec::new();
    serialize_frame_header(0x01, b.len() as u64, &mut out);
    out.extend_from_slice(&b);
    out
}

fn get() -> Vec<u8> {
    headers(&[fl(b":method", b"GET"), fl(b":scheme", b"https"), fl(b":authority", b"example.com"), fl(b":path", b"/")])
}

/// A CONNECT, which h3 answers 501 by itself.
fn connect() -> Vec<u8> {
    headers(&[fl(b":method", b"CONNECT"), fl(b":authority", b"example.com:443")])
}

fn resp(body: &[u8]) -> Response {
    Response { status: 200, headers: vec![], body: body.to_vec() }
}

fn est_with(p: TransportParams) -> H3Server {
    let mut s = H3Server::new(established_with(p));
    let mut app = Vec::new();
    s.pump(&mut app);
    assert!(app.is_empty());
    s
}

fn est() -> H3Server {
    est_with(ptp())
}

fn big_ptp() -> TransportParams {
    let mut p = ptp();
    p.initial_max_data = 1 << 30;
    p.initial_max_stream_data_bidi_local = 1 << 30;
    p
}

fn dgram(s: &mut H3Server, pn: u64, f: Vec<Frame>, now: u64, app: &mut Vec<AppEvent>) {
    s.on_datagram(0, 300, vec![one(pn, f)], None, now, &rnd(pn as u8), app);
}

fn poll_all(s: &mut H3Server, now: u64) -> Vec<OutDatagram> {
    drain(s.conn_mut(), now)
}

fn polled_frames(v: &[OutDatagram]) -> Vec<&Frame> {
    v.iter().flat_map(|d| d.packets.iter()).flat_map(|p| p.frames.iter()).collect()
}

fn any_frame(v: &[OutDatagram], f: &Frame) -> bool {
    polled_frames(v).iter().any(|g| *g == f)
}

fn stream3(v: &[OutDatagram]) -> bool {
    polled_frames(v).iter().any(|g| matches!(g, Frame::Stream { stream_id: 3, .. }))
}

fn one_rtt_pns(v: &[OutDatagram]) -> Vec<u64> {
    v.iter().flat_map(|d| d.packets.iter()).filter(|p| p.kind == PacketKind::OneRtt).map(|p| p.pn).collect()
}

/// Copies every polled `Stream{id, ..}` payload into `buf` by offset, and returns whether a FIN was seen.
fn collect(v: &[OutDatagram], id: u64, buf: &mut Vec<u8>) -> bool {
    let mut fin_seen = false;
    for f in polled_frames(v) {
        if let Frame::Stream { stream_id, offset, data, fin } = f {
            if *stream_id == id {
                let end = *offset as usize + data.len();
                if buf.len() < end {
                    buf.resize(end, 0);
                }
                buf[*offset as usize..end].copy_from_slice(data);
                fin_seen |= *fin;
            }
        }
    }
    fin_seen
}

/// A server with a GET answered by 3 MiB, most of it deferred. The next peer PN is 1.
fn deferred() -> H3Server {
    let mut s = est_with(big_ptp());
    let mut app = Vec::new();
    dgram(&mut s, 0, vec![stream(0, 0, &get(), true)], 40, &mut app);
    assert_eq!(app.len(), 2);
    let body = vec![0x5a; 3 << 20];
    let r = Response { status: 200, headers: vec![], body };
    assert_eq!(s.send_response(0, &r, &mut app), Ok(()));
    assert!(!s.can_send());
    s
}

/// Rounds of poll, ack everything, until nothing is deferred; every polled datagram goes to `all`.
fn drain_deferred(s: &mut H3Server, mut pn: u64, all: &mut Vec<OutDatagram>) -> u64 {
    let mut app = Vec::new();
    let mut rounds = 0;
    while !s.can_send() {
        rounds += 1;
        assert!(rounds <= 200, "deferred response did not drain");
        let v = poll_all(s, 50 + rounds);
        let pns = one_rtt_pns(&v);
        all.extend(v);
        assert!(!pns.is_empty());
        dgram(s, pn, vec![Frame::Ack(ack_of(&pns))], 50 + rounds, &mut app);
        pn += 1;
        assert_eq!(s.conn().phase(), Phase::Open);
    }
    pn
}

/// Rounds of poll, ack everything, until nothing more is polled: the send buffer's last bytes.
fn drain_buffered(s: &mut H3Server, mut pn: u64, all: &mut Vec<OutDatagram>) {
    let mut app = Vec::new();
    for round in 0..200 {
        let v = poll_all(s, 400 + round);
        let pns = one_rtt_pns(&v);
        all.extend(v);
        if pns.is_empty() {
            return;
        }
        dgram(s, pn, vec![Frame::Ack(ack_of(&pns))], 400 + round, &mut app);
        pn += 1;
    }
    panic!("the send buffer did not drain");
}

#[test]
fn min_uni_literal() {
    assert_eq!(h3::limits::MIN_PEER_UNI_STREAMS, 3);
    assert_eq!(quic::stream_id::MAX_OWN_UNI, 3);
    let mut t = ltp();
    t.initial_max_streams_uni = 2;
    assert!(Connection::accept(&ini(2, first_frames()), 1200, 0, 0, &rnd(1), &t).is_none());
}

#[test]
fn control_stream_opened() {
    let mut s = est();
    let v = poll_all(&mut s, 20);
    let want = stream(3, 0, &[0x00, 0x04, 0x07, 0x06, 0x80, 0x01, 0x00, 0x00, 0x21, 0x00], false);
    assert!(any_frame(&v, &want));
}

#[test]
fn drain_gated_on_started() {
    let mut s = H3Server::new(conn());
    let mut app = Vec::new();
    s.pump(&mut app);
    assert!(app.is_empty());
    assert!(!stream3(&poll_all(&mut s, 5)));
}

#[test]
fn get_end_to_end() {
    let mut s = est();
    poll_all(&mut s, 20);
    let mut app = Vec::new();
    dgram(&mut s, 0, vec![stream(2, 0, &[0x00, 0x04, 0x00], false), stream(0, 0, &get(), true)], 40, &mut app);
    assert_eq!(app.len(), 2);
    match &app[0] {
        AppEvent::H3(Output::Request { stream_id: 0, head }) => {
            assert_eq!(head.method, b"GET");
            assert_eq!(head.scheme, b"https");
            assert_eq!(head.authority, b"example.com");
            assert_eq!(head.path, b"/");
        }
        _ => panic!("expected the request"),
    }
    match &app[1] {
        AppEvent::H3(Output::RequestEnd { stream_id: 0, trailers }) => assert!(trailers.is_empty()),
        _ => panic!("expected the request's end"),
    }
    let r = Response { status: 200, headers: vec![fl(b"content-type", b"text/plain")], body: b"hi".to_vec() };
    assert_eq!(s.send_response(0, &r, &mut app), Ok(()));
    let v = poll_all(&mut s, 41);
    let mut w = Vec::new();
    assert!(collect(&v, 0, &mut w));
    let FrameHeader::Complete { ty: 1, len, hdr_len } = parse_frame_header(&w) else { panic!("no HEADERS") };
    let end = hdr_len + len as usize;
    let fields = decode_field_section(&w[hdr_len..end]).unwrap();
    assert_eq!(fields.len(), 2);
    assert_eq!((&fields[0].name[..], &fields[0].value[..]), (&b":status"[..], &b"200"[..]));
    assert_eq!((&fields[1].name[..], &fields[1].value[..]), (&b"content-type"[..], &b"text/plain"[..]));
    assert_eq!(&w[end..], &[0x00, 0x02, b'h', b'i']);
}

#[test]
fn stop_sending_forwarded() {
    let mut s = est();
    poll_all(&mut s, 20);
    let mut app = Vec::new();
    dgram(&mut s, 0, vec![Frame::StopSending { stream_id: 3, error_code: 0 }], 40, &mut app);
    assert!(any_frame(&poll_all(&mut s, 41), &CC(true, 0x104, &[])));

    let mut s = est();
    poll_all(&mut s, 20);
    let mut app = Vec::new();
    dgram(&mut s, 0, vec![stream(0, 0, &get(), false)], 40, &mut app);
    dgram(&mut s, 1, vec![Frame::StopSending { stream_id: 0, error_code: 0x10c }], 41, &mut app);
    assert!(matches!(s.send_response(0, &resp(b"x"), &mut app), Err(SendError::Rejected)));
    let v = poll_all(&mut s, 42);
    assert!(any_frame(&v, &Frame::ResetStream { stream_id: 0, error_code: 0x10c, final_size: 0 }));
    assert!(!polled_frames(&v).iter().any(|g| matches!(g, Frame::Stream { stream_id: 0, .. })));
}

#[test]
fn reset_forwarded() {
    let mut s = est();
    let g = get();
    let mut app = Vec::new();
    dgram(&mut s, 0, vec![stream(0, 0, &g, false)], 40, &mut app);
    dgram(&mut s, 1, vec![Frame::ResetStream { stream_id: 0, error_code: 0x10c, final_size: g.len() as u64 }], 41, &mut app);
    assert_eq!(app.len(), 2);
    assert!(matches!(&app[0], AppEvent::H3(Output::Request { stream_id: 0, .. })));
    assert!(matches!(&app[1], AppEvent::Aborted(0)));
}

#[test]
fn h3_conn_error_closes() {
    let mut s = est();
    poll_all(&mut s, 20);
    let mut app = Vec::new();
    dgram(&mut s, 0, vec![stream(2, 0, &[0x00, 0x07, 0x01, 0x00], false)], 40, &mut app);
    assert!(any_frame(&poll_all(&mut s, 41), &CC(true, 0x10a, &[])));
}

/// RFC 9114 §6.2.1: the peer resetting its control stream closes the connection.
#[test]
fn peer_control_reset_closes() {
    let mut s = est();
    poll_all(&mut s, 20);
    let mut app = Vec::new();
    dgram(&mut s, 0, vec![stream(2, 0, &[0x00, 0x04, 0x00], false)], 40, &mut app);
    dgram(&mut s, 1, vec![Frame::ResetStream { stream_id: 2, error_code: 0, final_size: 3 }], 41, &mut app);
    assert!(any_frame(&poll_all(&mut s, 42), &CC(true, 0x104, &[])));
}

#[test]
fn peer_uni_too_small() {
    for n in [2, 0] {
        let mut p = ptp();
        p.initial_max_streams_uni = n;
        let mut s = est_with(p);
        let v = poll_all(&mut s, 20);
        assert!(any_frame(&v, &CC(true, 0x101, &[])));
        assert!(!stream3(&v));
    }
}

/// The close leaves events queued by the same datagram; h3 never started, so none may reach it.
#[test]
fn too_small_never_drains() {
    let mut p = ptp();
    p.initial_max_streams_uni = 2;
    let mut c = established_with(p);
    c.on_datagram(0, 300, vec![one(0, vec![stream(0, 0, &get(), true)])], None, 40, &rnd(3));
    let mut s = H3Server::new(c);
    let mut app = Vec::new();
    s.pump(&mut app);
    s.pump(&mut app);
    s.on_timeout(41, &rnd(4), &mut app);
    assert!(app.is_empty());
}

/// `shutdown` before the transport can write must not lose SETTINGS, which h3 emits only once.
#[test]
fn shutdown_before_started_keeps_settings() {
    let mut s = H3Server::new(conn());
    let mut app = Vec::new();
    s.shutdown(&mut app);
    assert!(s.can_send());
    s.conn_mut().on_datagram(0, 1200, vec![hs(0, vec![Frame::Ping])], None, 10, &rnd(9));
    s.conn_mut().on_peer_params(&ptp(), 10);
    s.conn_mut().on_handshake_complete(b"h3", 10, &rnd(2));
    s.pump(&mut app);
    let want = stream(3, 0, &[0x00, 0x04, 0x07, 0x06, 0x80, 0x01, 0x00, 0x00, 0x21, 0x00], false);
    assert!(any_frame(&poll_all(&mut s, 20), &want));
}

#[test]
fn deferred_large_response() {
    let mut s = deferred();
    let mut all = Vec::new();
    let pn = drain_deferred(&mut s, 1, &mut all);
    assert_eq!(s.pending_bytes(), 0);
    drain_buffered(&mut s, pn, &mut all);
    assert_eq!(s.conn().phase(), Phase::Open);
    let mut w = Vec::new();
    assert!(collect(&all, 0, &mut w));
    let FrameHeader::Complete { ty: 1, len, hdr_len } = parse_frame_header(&w) else { panic!("no HEADERS") };
    let f = hdr_len + len as usize;
    let fields = decode_field_section(&w[hdr_len..f]).unwrap();
    assert_eq!(fields.len(), 1);
    assert_eq!((&fields[0].name[..], &fields[0].value[..]), (&b":status"[..], &b"200"[..]));
    let FrameHeader::Complete { ty: 0, len, hdr_len } = parse_frame_header(&w[f..]) else { panic!("no DATA") };
    assert_eq!(len as usize, 3 << 20);
    assert_eq!(w.len(), f + hdr_len + (3 << 20));
    assert!(w[f + hdr_len..].iter().all(|b| *b == 0x5a));
}

#[test]
fn busy_while_pending() {
    let mut s = deferred();
    let mut app = Vec::new();
    dgram(&mut s, 1, vec![stream(4, 0, &get(), true)], 41, &mut app);
    let r = resp(b"x");
    assert_eq!(s.send_response(4, &r, &mut app), Err(SendError::Busy));
    let mut all = Vec::new();
    drain_deferred(&mut s, 2, &mut all);
    assert_eq!(s.send_response(4, &r, &mut app), Ok(()));
}

#[test]
fn stop_sending_drops_pending() {
    let mut s = deferred();
    let mut app = Vec::new();
    dgram(&mut s, 1, vec![Frame::StopSending { stream_id: 0, error_code: 0x10c }], 41, &mut app);
    assert!(s.can_send());
    assert_eq!(s.pending_bytes(), 0);
    assert_eq!(s.conn().phase(), Phase::Open);
}

/// Behind a stalled head, a CONNECT is answered by h3 and queues without `send_response`. STOP_SENDING
/// resets that part, so QUIC can forget the stream and re-credit it: nothing in the queue may outlive
/// that, or the peer grows it forever while withholding the head's ACKs.
#[test]
fn stopped_answers_do_not_pile_up() {
    let mut s = deferred();
    let base = s.pending_bytes();
    let c = connect();
    let mut app = Vec::new();
    for k in 0..8u64 {
        let id = 4 + k * 4;
        dgram(&mut s, 1 + k * 2, vec![stream(id, 0, &c, true)], 41 + k, &mut app);
        assert!(s.pending_bytes() > base, "h3 did not answer the CONNECT");
        dgram(&mut s, 2 + k * 2, vec![Frame::StopSending { stream_id: id, error_code: 0 }], 41 + k, &mut app);
        assert_eq!(s.pending_bytes(), base);
    }
    // Answered by h3, so never shown to the application.
    assert!(app.is_empty());
}

/// A peer reset of an answered request leaves our sending part alone, so its bytes still go out.
#[test]
fn reset_keeps_a_committed_answer() {
    let mut s = deferred();
    let base = s.pending_bytes();
    let c = connect();
    let mut app = Vec::new();
    dgram(&mut s, 1, vec![stream(4, 0, &c, false)], 41, &mut app);
    assert!(s.pending_bytes() > base);
    let n = s.pending_bytes();
    dgram(&mut s, 2, vec![Frame::ResetStream { stream_id: 4, error_code: 0, final_size: c.len() as u64 }], 42, &mut app);
    assert_eq!(s.pending_bytes(), n);
    let mut all = Vec::new();
    let pn = drain_deferred(&mut s, 3, &mut all);
    drain_buffered(&mut s, pn, &mut all);
    let mut w = Vec::new();
    assert!(collect(&all, 4, &mut w));
    assert!(!w.is_empty());
}

/// Nothing queued survives the close.
#[test]
fn close_frees_pending() {
    let mut s = deferred();
    s.conn_mut().close(0, true, &[], 41);
    let mut app = Vec::new();
    s.pump(&mut app);
    assert!(s.can_send());
    assert_eq!(s.pending_bytes(), 0);
}

/// Phase 4c Task 2 (preflight C8): the clock reaches `now`.
#[test]
fn h3_on_timeout_now() {
    let mut s = H3Server::new(established());
    let mut app = Vec::new();
    s.on_timeout(50, &rnd(4), &mut app);
    assert!(s.conn().now() >= 50);
}

/// A connection error alone closes (RFC 9000 §17.2, §17.3.1).
#[test]
fn h3_on_datagram_passes_error() {
    let mut s = H3Server::new(established());
    let mut app = Vec::new();
    s.on_datagram(0, 100, vec![], Some((0x0a, one(5, vec![]))), 30, &rnd(3), &mut app);
    assert_eq!(s.conn().phase(), Phase::Closing);
}
