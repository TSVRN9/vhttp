use h3::codes::*;
use h3::conn::*;
use h3::frame::{parse_frame_header, parse_frame_payload, serialize_frame_header, Frame, FrameHeader};
use h3::message::Response;
use h3::qpack::field_section::{decode_field_section, encode_field_section, FieldLine};

fn fl(n: &str, v: &str) -> FieldLine {
    FieldLine { name: n.as_bytes().to_vec(), value: v.as_bytes().to_vec() }
}

fn frame(ty: u64, payload: &[u8]) -> Vec<u8> {
    let mut o = Vec::new();
    serialize_frame_header(ty, payload.len() as u64, &mut o);
    o.extend_from_slice(payload);
    o
}

fn headers(fields: &[FieldLine]) -> Vec<u8> {
    let mut p = Vec::new();
    encode_field_section(fields, &mut p);
    frame(0x01, &p)
}

fn get(path: &str) -> Vec<u8> {
    headers(&[
        fl(":method", "GET"),
        fl(":scheme", "https"),
        fl(":authority", "example.com"),
        fl(":path", path),
    ])
}

/// The client's control stream: type 0x00, then SETTINGS with `pairs` (single-byte varints).
fn client_control(pairs: &[(u8, u8)]) -> Vec<u8> {
    let p: Vec<u8> = pairs.iter().flat_map(|(k, v)| [*k, *v]).collect();
    let mut b = vec![0x00];
    b.extend(frame(0x04, &p));
    b
}

fn resp(status: u16, h: &[(&str, &str)], body: &str) -> Response {
    Response { status, headers: h.iter().map(|(n, v)| fl(n, v)).collect(), body: body.as_bytes().to_vec() }
}

/// Splits `b` into frames: (type, payload).
fn frames(mut b: &[u8]) -> Vec<(u64, Vec<u8>)> {
    let mut v = Vec::new();
    while !b.is_empty() {
        let FrameHeader::Complete { ty, len, hdr_len } = parse_frame_header(b) else {
            panic!("incomplete frame header")
        };
        let end = hdr_len + len as usize;
        v.push((ty, b[hdr_len..end].to_vec()));
        b = &b[end..];
    }
    v
}

/// The one write on `id`: its frames and FIN flag.
fn write_on(out: &[Output], id: u64) -> (Vec<(u64, Vec<u8>)>, bool) {
    let w: Vec<_> = out
        .iter()
        .filter_map(|o| match o {
            Output::StreamWrite { stream_id, data, fin } if *stream_id == id => Some((data, *fin)),
            _ => None,
        })
        .collect();
    assert_eq!(w.len(), 1, "expected one write on stream {id}");
    (frames(w[0].0), w[0].1)
}

fn status_of(fr: &[(u64, Vec<u8>)]) -> Vec<u8> {
    assert_eq!(fr[0].0, 0x01);
    let f = decode_field_section(&fr[0].1).unwrap();
    assert_eq!(f[0].name, b":status");
    f[0].value.clone()
}

fn is_close(o: &Output, c: u64) -> bool {
    matches!(o, Output::CloseConnection { code } if *code == c)
}

fn is_reset(o: &Output, id: u64, c: u64) -> bool {
    matches!(o, Output::ResetStream { stream_id, code } if *stream_id == id && *code == c)
}

fn is_stop(o: &Output, id: u64, c: u64) -> bool {
    matches!(o, Output::StopSending { stream_id, code } if *stream_id == id && *code == c)
}

/// A started connection whose peer control stream (2) has sent `pairs`.
fn ready(pairs: &[(u8, u8)]) -> H3Conn {
    let mut c = H3Conn::new();
    let mut out = Vec::new();
    c.start(&mut out);
    c.on_stream_data(2, &client_control(pairs), false, &mut out);
    assert_eq!(out.len(), 1);
    c
}

#[test]
fn start_sends_settings() {
    let mut c = H3Conn::new();
    let mut out = Vec::new();
    c.start(&mut out);
    assert_eq!(out.len(), 1);
    let Output::StreamWrite { stream_id: 3, data, fin: false } = &out[0] else { panic!() };
    assert_eq!(&data[..2], &[0x00, 0x04]);
    let fr = frames(&data[1..]);
    assert_eq!(fr.len(), 1);
    assert_eq!(
        parse_frame_payload(fr[0].0, &fr[0].1),
        Ok(Frame::Settings(vec![(6, 65536), (0x21, 0)]))
    );
    // A second start writes nothing (a second SETTINGS is H3_FRAME_UNEXPECTED at the peer).
    c.start(&mut out);
    assert_eq!(out.len(), 1);
}

#[test]
fn end_to_end_get() {
    let mut c = ready(&[]);
    let mut out = Vec::new();
    c.on_stream_data(0, &get("/index.html"), true, &mut out);
    assert_eq!(out.len(), 2);
    let Output::Request { stream_id: 0, head } = &out[0] else { panic!() };
    assert_eq!(head.method, b"GET");
    assert_eq!(head.scheme, b"https");
    assert_eq!(head.authority, b"example.com");
    assert_eq!(head.path, b"/index.html");
    let Output::RequestEnd { stream_id: 0, trailers } = &out[1] else { panic!() };
    assert!(trailers.is_empty());

    let mut out = Vec::new();
    assert_eq!(c.send_response(0, &resp(200, &[("content-type", "text/plain")], "hi"), &mut out), Ok(()));
    let (fr, fin) = write_on(&out, 0);
    assert!(fin);
    assert_eq!(fr.len(), 2);
    let f = decode_field_section(&fr[0].1).unwrap();
    assert_eq!(f.len(), 2);
    assert_eq!((f[0].name.as_slice(), f[0].value.as_slice()), (&b":status"[..], &b"200"[..]));
    assert_eq!((f[1].name.as_slice(), f[1].value.as_slice()), (&b"content-type"[..], &b"text/plain"[..]));
    assert_eq!(fr[1], (0x00, b"hi".to_vec()));
    // One response per request.
    let mut out = Vec::new();
    assert_eq!(c.send_response(0, &resp(200, &[], ""), &mut out), Err(()));
    assert!(out.is_empty());
}

/// Outputs with body chunks concatenated, for comparing chunkings.
fn summary(out: &[Output]) -> Vec<String> {
    let mut v: Vec<String> = Vec::new();
    for o in out {
        let s = match o {
            Output::Request { stream_id, head } => format!("req {stream_id} {:?}", head.method),
            Output::RequestBody { stream_id, data } => {
                if let Some(last) = v.last_mut() {
                    if last.starts_with(&format!("body {stream_id} ")) {
                        last.push_str(&String::from_utf8_lossy(data));
                        continue;
                    }
                }
                format!("body {stream_id} {}", String::from_utf8_lossy(data))
            }
            Output::RequestEnd { stream_id, trailers } => format!("end {stream_id} {}", trailers.len()),
            _ => "other".to_string(),
        };
        v.push(s);
    }
    v
}

#[test]
fn chunked_request_with_body_and_trailers() {
    let mut b = headers(&[
        fl(":method", "POST"),
        fl(":scheme", "https"),
        fl(":authority", "example.com"),
        fl(":path", "/"),
        fl("content-length", "5"),
    ]);
    b.extend(frame(0x00, b"he"));
    b.extend(frame(0x00, b"llo"));
    b.extend(headers(&[fl("x-t", "1")]));
    let mut c = ready(&[]);
    let mut out = Vec::new();
    for x in &b {
        c.on_stream_data(4, &[*x], false, &mut out);
    }
    c.on_stream_data(4, &[], true, &mut out);
    let mut whole = ready(&[]);
    let mut out_whole = Vec::new();
    whole.on_stream_data(4, &b, true, &mut out_whole);
    assert_eq!(summary(&out), summary(&out_whole));
    let mut body = Vec::new();
    let mut ended = false;
    for o in &out {
        match o {
            Output::Request { stream_id: 4, head } => assert_eq!(head.method, b"POST"),
            Output::RequestBody { stream_id: 4, data } => body.extend_from_slice(data),
            Output::RequestEnd { stream_id: 4, trailers } => {
                assert_eq!(trailers.len(), 1);
                assert_eq!(trailers[0].name, b"x-t");
                ended = true;
            }
            _ => panic!("unexpected output"),
        }
    }
    assert_eq!(body, b"hello");
    assert!(ended);
}

#[test]
fn bad_response_rejected() {
    for r in [
        resp(200, &[("X-Up", "1")], ""),
        resp(200, &[("connection", "close")], ""),
        resp(200, &[(":path", "/")], ""),
        resp(600, &[], ""),
        // Interim statuses are never a whole response; HTTP/3 has no 101.
        resp(100, &[], ""),
        resp(101, &[], ""),
        resp(199, &[], ""),
        // content-length must equal the body length; 204 and 304 carry no content.
        resp(200, &[("content-length", "3")], "hi"),
        resp(200, &[("content-length", "x")], "hi"),
        resp(204, &[], "hi"),
        resp(304, &[], "hi"),
    ] {
        let mut c = ready(&[]);
        let mut out = Vec::new();
        c.on_stream_data(0, &get("/"), true, &mut out);
        let mut out = Vec::new();
        assert_eq!(c.send_response(0, &r, &mut out), Err(()));
        assert!(out.is_empty());
        // The stream is still answerable.
        assert_eq!(c.send_response(0, &resp(204, &[], ""), &mut out), Ok(()));
    }
    // An accepted 200 with a matching content-length.
    let mut c = ready(&[]);
    let mut out = Vec::new();
    c.on_stream_data(0, &get("/"), true, &mut out);
    let mut out = Vec::new();
    assert_eq!(c.send_response(0, &resp(200, &[("content-length", "2")], "hi"), &mut out), Ok(()));
    assert_eq!(out.len(), 1);
    // No Head delivered on that stream: Err.
    let mut c = ready(&[]);
    let mut out = Vec::new();
    assert_eq!(c.send_response(8, &resp(200, &[], ""), &mut out), Err(()));
    assert!(out.is_empty());
}

#[test]
fn peer_field_section_limit() {
    // Peer MAX_FIELD_SECTION_SIZE = 50: :status alone is 7 + 3 + 32 = 42.
    let mut c = ready(&[(0x06, 50)]);
    let mut out = Vec::new();
    c.on_stream_data(0, &get("/"), true, &mut out);
    let mut out = Vec::new();
    assert_eq!(c.send_response(0, &resp(200, &[("a", "b")], ""), &mut out), Err(()));
    assert!(out.is_empty());
    assert_eq!(c.send_response(0, &resp(200, &[], "x"), &mut out), Ok(()));
}

#[test]
fn connect_gets_501() {
    let mut c = ready(&[]);
    let mut out = Vec::new();
    let b = headers(&[fl(":method", "CONNECT"), fl(":authority", "example.com:443")]);
    c.on_stream_data(0, &b, false, &mut out);
    let (fr, fin) = write_on(&out, 0);
    assert!(fin);
    assert_eq!(status_of(&fr), b"501");
    assert!(out.iter().any(|o| is_stop(o, 0, H3_NO_ERROR)));
    assert!(!out.iter().any(|o| matches!(o, Output::Request { .. })));
    // The rest of the CONNECT stream is ignored.
    let mut out = Vec::new();
    c.on_stream_data(0, &frame(0x00, b"tunnel"), false, &mut out);
    assert!(out.is_empty());
}

#[test]
fn non_http_scheme_gets_421() {
    let mut c = ready(&[]);
    let mut out = Vec::new();
    let b = headers(&[
        fl(":method", "GET"),
        fl(":scheme", "ftp"),
        fl(":authority", "example.com"),
        fl(":path", "/"),
    ]);
    c.on_stream_data(0, &b, true, &mut out);
    assert_eq!(out.len(), 1);
    let (fr, _) = write_on(&out, 0);
    assert_eq!(status_of(&fr), b"421");
}

#[test]
fn stream_error_resets() {
    let mut c = ready(&[]);
    let mut out = Vec::new();
    let b = headers(&[
        fl(":method", "GET"),
        fl(":scheme", "https"),
        fl(":authority", "example.com"),
        fl(":path", "/"),
        fl("Accept", "*/*"),
    ]);
    c.on_stream_data(0, &b, false, &mut out);
    assert_eq!(out.len(), 2);
    assert!(is_reset(&out[0], 0, H3_MESSAGE_ERROR) && is_stop(&out[1], 0, H3_MESSAGE_ERROR));
    // Data still in flight on the reset stream is ignored, not a new request.
    let mut out = Vec::new();
    c.on_stream_data(0, &frame(0x00, b"x"), false, &mut out);
    assert!(out.is_empty());
    // Other streams are unaffected.
    c.on_stream_data(4, &get("/"), true, &mut out);
    assert!(matches!(out[0], Output::Request { stream_id: 4, .. }));
}

#[test]
fn goaway() {
    let mut c = ready(&[]);
    let mut out = Vec::new();
    c.on_stream_data(0, &get("/"), true, &mut out);
    let mut out = Vec::new();
    c.shutdown(&mut out);
    let (fr, fin) = write_on(&out, 3);
    assert!(!fin);
    assert_eq!(fr.len(), 1);
    assert_eq!(parse_frame_payload(fr[0].0, &fr[0].1), Ok(Frame::Goaway(4)));
    let mut out = Vec::new();
    c.on_stream_data(4, &get("/"), true, &mut out);
    assert!(out.iter().any(|o| is_reset(o, 4, H3_REQUEST_REJECTED)));
    assert!(!out.iter().any(|o| matches!(o, Output::Request { .. })));
    // Stream 0 was accepted before the GOAWAY: it can still be answered.
    let mut out = Vec::new();
    assert_eq!(c.send_response(0, &resp(200, &[], ""), &mut out), Ok(()));
    // A second GOAWAY never carries a larger ID.
    let mut out = Vec::new();
    c.shutdown(&mut out);
    let (fr, _) = write_on(&out, 3);
    assert_eq!(parse_frame_payload(fr[0].0, &fr[0].1), Ok(Frame::Goaway(4)));
}

#[test]
fn goaway_before_start_and_without_requests() {
    let mut c = H3Conn::new();
    let mut out = Vec::new();
    c.shutdown(&mut out);
    let w: Vec<u8> = out
        .iter()
        .flat_map(|o| match o {
            Output::StreamWrite { stream_id: 3, data, .. } => data.clone(),
            _ => panic!("unexpected output"),
        })
        .collect();
    assert_eq!(w[0], 0x00);
    let fr = frames(&w[1..]);
    assert_eq!(fr.len(), 2);
    assert!(matches!(parse_frame_payload(fr[0].0, &fr[0].1), Ok(Frame::Settings(_))));
    assert_eq!(parse_frame_payload(fr[1].0, &fr[1].1), Ok(Frame::Goaway(0)));
}

#[test]
fn latch() {
    let mut c = H3Conn::new();
    let mut out = Vec::new();
    c.start(&mut out);
    let mut out = Vec::new();
    // A control stream whose first frame is not SETTINGS.
    c.on_stream_data(2, &[0x00, 0x07, 0x01, 0x00], false, &mut out);
    assert_eq!(out.len(), 1);
    assert!(is_close(&out[0], H3_MISSING_SETTINGS));
    let mut out = Vec::new();
    c.on_stream_data(0, &get("/"), true, &mut out);
    c.on_stream_data(6, &[0x00], false, &mut out);
    c.on_stream_data(1, &[0x00], false, &mut out);
    c.on_stream_reset(2, 0, &mut out);
    c.on_stop_sending(3, 0, &mut out);
    c.shutdown(&mut out);
    c.start(&mut out);
    assert!(out.is_empty());
    assert_eq!(c.send_response(0, &resp(200, &[], ""), &mut out), Err(()));
    assert!(out.is_empty());
}

#[test]
fn bad_stream_id() {
    for id in [1u64, 3, 7] {
        let mut c = ready(&[]);
        let mut out = Vec::new();
        c.on_stream_data(id, &[0x00], false, &mut out);
        assert_eq!(out.len(), 1);
        assert!(is_close(&out[0], H3_STREAM_CREATION_ERROR));
    }
}

#[test]
fn stop_sending_control() {
    let mut c = ready(&[]);
    let mut out = Vec::new();
    c.on_stop_sending(3, H3_NO_ERROR, &mut out);
    assert_eq!(out.len(), 1);
    assert!(is_close(&out[0], H3_CLOSED_CRITICAL_STREAM));
}

#[test]
fn stop_sending_request() {
    let mut c = ready(&[]);
    let mut out = Vec::new();
    c.on_stream_data(0, &get("/"), false, &mut out);
    let mut out = Vec::new();
    c.on_stop_sending(0, H3_REQUEST_CANCELLED, &mut out);
    assert!(out.is_empty());
    assert_eq!(c.send_response(0, &resp(200, &[], ""), &mut out), Err(()));
    assert!(out.is_empty());
}

#[test]
fn stream_resets() {
    // A critical stream reset closes the connection; the error code doesn't matter.
    let mut c = ready(&[]);
    let mut out = Vec::new();
    c.on_stream_reset(2, 0x1234, &mut out);
    assert_eq!(out.len(), 1);
    assert!(is_close(&out[0], H3_CLOSED_CRITICAL_STREAM));
    // The encoder and decoder streams are critical too.
    for ty in [0x02u8, 0x03] {
        let mut c = ready(&[]);
        let mut out = Vec::new();
        c.on_stream_data(6, &[ty], false, &mut out);
        assert!(out.is_empty());
        c.on_stream_reset(6, 0, &mut out);
        assert_eq!(out.len(), 1);
        assert!(is_close(&out[0], H3_CLOSED_CRITICAL_STREAM));
    }
    // An unknown-type uni stream reset is silent.
    let mut c = ready(&[]);
    let mut out = Vec::new();
    c.on_stream_data(6, &[0x21], false, &mut out);
    c.on_stream_reset(6, 0, &mut out);
    assert!(out.is_empty());
    // A request stream reset mid-request: our sending part is reset with H3_REQUEST_INCOMPLETE.
    let mut c = ready(&[]);
    let mut out = Vec::new();
    c.on_stream_data(0, &get("/"), false, &mut out);
    let mut out = Vec::new();
    c.on_stream_reset(0, H3_REQUEST_CANCELLED, &mut out);
    assert_eq!(out.len(), 1);
    assert!(is_reset(&out[0], 0, H3_REQUEST_INCOMPLETE));
    let mut out = Vec::new();
    assert_eq!(c.send_response(0, &resp(200, &[], ""), &mut out), Err(()));
    // After the request ended, unanswered: H3_REQUEST_CANCELLED.
    c.on_stream_data(4, &get("/"), true, &mut out);
    let mut out = Vec::new();
    c.on_stream_reset(4, 0, &mut out);
    assert_eq!(out.len(), 1);
    assert!(is_reset(&out[0], 4, H3_REQUEST_CANCELLED));
    // Already answered: nothing to reset.
    let mut out = Vec::new();
    c.on_stream_data(8, &get("/"), false, &mut out);
    assert_eq!(c.send_response(8, &resp(200, &[], ""), &mut out), Ok(()));
    let mut out = Vec::new();
    c.on_stream_reset(8, 0, &mut out);
    assert!(out.is_empty());
}

#[test]
fn critical_stream_fin() {
    // The control stream (2, already open), then a new encoder or decoder stream (6).
    for (id, b) in [(2u64, vec![]), (6, vec![0x02u8]), (6, vec![0x03])] {
        let mut c = ready(&[]);
        let mut out = Vec::new();
        c.on_stream_data(id, &b, true, &mut out);
        assert_eq!(out.len(), 1);
        assert!(is_close(&out[0], H3_CLOSED_CRITICAL_STREAM));
    }
}

#[test]
fn only_open_directions_aborted() {
    // Rejected with the request complete: no STOP_SENDING.
    let mut c = ready(&[]);
    let mut out = Vec::new();
    c.on_stream_data(0, &get("/"), true, &mut out);
    c.shutdown(&mut out);
    let mut out = Vec::new();
    c.on_stream_data(4, &get("/"), true, &mut out);
    assert_eq!(out.len(), 1);
    assert!(is_reset(&out[0], 4, H3_REQUEST_REJECTED));
    // Answered early, then the rest of the request is malformed: the sent response is not reset.
    let mut c = ready(&[]);
    let mut out = Vec::new();
    c.on_stream_data(0, &get("/"), false, &mut out);
    assert_eq!(c.send_response(0, &resp(200, &[], ""), &mut out), Ok(()));
    let mut out = Vec::new();
    c.on_stream_data(0, &headers(&[fl(":path", "/")]), false, &mut out);
    assert_eq!(out.len(), 1);
    assert!(is_stop(&out[0], 0, H3_MESSAGE_ERROR));
}

fn head_req() -> Vec<u8> {
    headers(&[
        fl(":method", "HEAD"),
        fl(":scheme", "https"),
        fl(":authority", "example.com"),
        fl(":path", "/"),
    ])
}

/// RFC 9110 §8.6, §9.3.2, §15.3.5, §15.4.5.
#[test]
fn head_and_bodiless_statuses() {
    let cases: [(Vec<u8>, Response, bool); 4] = [
        // HEAD: the GET's content-length, no content.
        (head_req(), resp(200, &[("content-length", "5")], ""), true),
        (head_req(), resp(200, &[], "hi"), false),
        // 304: content-length allowed, no content.
        (get("/"), resp(304, &[("content-length", "5")], ""), true),
        // 204: no content-length at all.
        (get("/"), resp(204, &[("content-length", "0")], ""), false),
    ];
    for (req, r, ok) in cases {
        let mut c = ready(&[]);
        let mut out = Vec::new();
        c.on_stream_data(0, &req, true, &mut out);
        let mut out = Vec::new();
        assert_eq!(c.send_response(0, &r, &mut out), if ok { Ok(()) } else { Err(()) });
        assert_eq!(out.len(), if ok { 1 } else { 0 });
    }
}
