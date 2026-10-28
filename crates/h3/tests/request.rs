use h3::codes::*;
use h3::frame::serialize_frame_header;
use h3::message::RequestHead;
use h3::qpack::field_section::{encode_field_section, FieldLine};
use h3::request::*;

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

fn req(method: &str, extra: &[(&str, &str)]) -> Vec<u8> {
    let mut f = vec![
        fl(":method", method),
        fl(":scheme", "https"),
        fl(":authority", "example.com"),
        fl(":path", "/"),
    ];
    f.extend(extra.iter().map(|(n, v)| fl(n, v)));
    headers(&f)
}

/// Comparable events: the method for a head, body chunks concatenated, the trailer count.
#[derive(Debug, PartialEq)]
enum Ev {
    Head(Vec<u8>),
    Body(Vec<u8>),
    Trailers(usize),
    End,
}

fn summary(ev: Vec<ReqEvent>) -> Vec<Ev> {
    let mut out: Vec<Ev> = Vec::new();
    for e in ev {
        match e {
            ReqEvent::Head(RequestHead::Request(r)) => out.push(Ev::Head(r.method)),
            ReqEvent::Head(RequestHead::Connect { .. }) => out.push(Ev::Head(b"CONNECT".to_vec())),
            ReqEvent::Body(b) => {
                assert!(!b.is_empty(), "empty Body chunk");
                if let Some(Ev::Body(prev)) = out.last_mut() {
                    prev.extend_from_slice(&b);
                } else {
                    out.push(Ev::Body(b));
                }
            }
            ReqEvent::Trailers(t) => out.push(Ev::Trailers(t.len())),
            ReqEvent::End => out.push(Ev::End),
        }
    }
    out
}

fn run(bytes: &[u8], fin: bool) -> (Result<(), ReqError>, Vec<Ev>) {
    let mut s = RequestStream::new();
    let mut ev = Vec::new();
    let r = s.on_data(bytes, fin, &mut ev);
    (r, summary(ev))
}

/// One byte per call, then an empty call carrying the FIN.
fn run_bytewise(bytes: &[u8], fin: bool) -> (Result<(), ReqError>, Vec<Ev>) {
    let mut s = RequestStream::new();
    let mut ev = Vec::new();
    for b in bytes {
        if let Err(e) = s.on_data(&[*b], false, &mut ev) {
            return (Err(e), summary(ev));
        }
    }
    let r = s.on_data(&[], fin, &mut ev);
    (r, summary(ev))
}

fn cat(parts: &[&[u8]]) -> Vec<u8> {
    parts.concat()
}

fn post_body_bytes() -> Vec<u8> {
    cat(&[&req("POST", &[("content-length", "5")]), &frame(0x00, b"he"), &frame(0x00, b"llo")])
}

fn get_events() -> Vec<Ev> {
    vec![Ev::Head(b"GET".to_vec()), Ev::End]
}

fn post_events() -> Vec<Ev> {
    vec![Ev::Head(b"POST".to_vec()), Ev::Body(b"hello".to_vec()), Ev::End]
}

#[test]
fn simple_get() {
    assert_eq!(run(&req("GET", &[]), true), (Ok(()), get_events()));
    // Without the FIN the head is delivered and the stream stays open.
    assert_eq!(run(&req("GET", &[]), false), (Ok(()), vec![Ev::Head(b"GET".to_vec())]));
}

#[test]
fn post_body() {
    assert_eq!(run(&post_body_bytes(), true), (Ok(()), post_events()));
}

#[test]
fn content_length() {
    let short = cat(&[&req("POST", &[("content-length", "5")]), &frame(0x00, b"hell")]);
    assert_eq!(run(&short, true).0, Err(ReqError::Stream(H3_MESSAGE_ERROR)));
    // Too many bytes: an error as soon as the sixth byte arrives, after the first five.
    let long = cat(&[&req("POST", &[("content-length", "5")]), &frame(0x00, b"hello!")]);
    assert_eq!(
        run(&long, false),
        (
            Err(ReqError::Stream(H3_MESSAGE_ERROR)),
            vec![Ev::Head(b"POST".to_vec()), Ev::Body(b"hello".to_vec())]
        )
    );
    assert_eq!(run_bytewise(&long, false), run(&long, false));
}

#[test]
fn frame_order() {
    assert_eq!(run(&frame(0x00, b"x"), false).0, Err(ReqError::Connection(H3_FRAME_UNEXPECTED)));
    let after_trailers =
        cat(&[&req("GET", &[]), &headers(&[fl("x-t", "1")]), &frame(0x00, b"x")]);
    assert_eq!(run(&after_trailers, false).0, Err(ReqError::Connection(H3_FRAME_UNEXPECTED)));
    let settings = cat(&[&req("GET", &[]), &frame(0x04, &[])]);
    assert_eq!(run(&settings, false).0, Err(ReqError::Connection(H3_FRAME_UNEXPECTED)));
    // CANCEL_PUSH, GOAWAY, MAX_PUSH_ID and HTTP/2-reserved 0x02, from the header alone.
    for ty in [0x03u8, 0x07, 0x0d, 0x02] {
        let b = cat(&[&req("GET", &[]), &[ty, 0x05]]);
        assert_eq!(run(&b, false).0, Err(ReqError::Connection(H3_FRAME_UNEXPECTED)));
    }
}

#[test]
fn trailers() {
    let b = cat(&[&post_body_bytes(), &headers(&[fl("x-t", "1")]), &frame(0x21, b"zz")]);
    assert_eq!(
        run(&b, true),
        (
            Ok(()),
            vec![Ev::Head(b"POST".to_vec()), Ev::Body(b"hello".to_vec()), Ev::Trailers(1), Ev::End]
        )
    );
    let bad = cat(&[&req("GET", &[]), &headers(&[fl(":path", "/")])]);
    assert_eq!(run(&bad, false).0, Err(ReqError::Stream(H3_MESSAGE_ERROR)));
}

#[test]
fn truncation() {
    let b = [0x01u8, 0x0a, 0x00, 0x00, 0xd1];
    assert_eq!(run(&b, true).0, Err(ReqError::Connection(H3_FRAME_ERROR)));
    assert_eq!(run(&b, false).0, Ok(()));
    assert_eq!(run(&[], true).0, Err(ReqError::Stream(H3_REQUEST_INCOMPLETE)));
    // A partial frame header, or a partial DATA payload, then FIN.
    assert_eq!(run(&[0x40], true).0, Err(ReqError::Connection(H3_FRAME_ERROR)));
    let partial_data = cat(&[&req("GET", &[]), &[0x00, 0x05], b"he"]);
    assert_eq!(
        run(&partial_data, true),
        (
            Err(ReqError::Connection(H3_FRAME_ERROR)),
            vec![Ev::Head(b"GET".to_vec()), Ev::Body(b"he".to_vec())]
        )
    );
    // Only unknown frames, then FIN: no request.
    assert_eq!(run(&frame(0x21, b"abc"), true).0, Err(ReqError::Stream(H3_REQUEST_INCOMPLETE)));
}

#[test]
fn qpack_failure() {
    let b = frame(0x01, &[0x03, 0x81, 0x10, 0x11]);
    assert_eq!(run(&b, false).0, Err(ReqError::Connection(QPACK_DECOMPRESSION_FAILED)));
}

#[test]
fn decoded_budget() {
    // Static entry 31 is accept-encoding: gzip, deflate, br (15 + 17 + 32 = 64 bytes decoded).
    let mut p = vec![0x00u8, 0x00];
    p.extend(std::iter::repeat(0xc0u8 | 31).take(2000));
    assert_eq!(run(&frame(0x01, &p), false).0, Err(ReqError::Stream(H3_EXCESSIVE_LOAD)));
    // A HEADERS frame announcing more than MAX_FIELD_SECTION_SIZE: rejected from its header.
    let mut h = Vec::new();
    serialize_frame_header(0x01, 65537, &mut h);
    assert_eq!(run(&h, false).0, Err(ReqError::Stream(H3_EXCESSIVE_LOAD)));
}

#[test]
fn push_promise_rejected_by_type() {
    assert_eq!(run(&frame(0x05, &[0xff]), false).0, Err(ReqError::Connection(H3_FRAME_UNEXPECTED)));
}

#[test]
fn malformed_request() {
    assert_eq!(
        run(&req("GET", &[("Accept", "*/*")]), false).0,
        Err(ReqError::Stream(H3_MESSAGE_ERROR))
    );
}

#[test]
fn unknown_frames_ignored() {
    let b = cat(&[
        &frame(0x21, b"xyz"),
        &req("POST", &[("content-length", "5")]),
        &frame(0x00, b"he"),
        &frame(0x21, &[0u8; 300]),
        &frame(0x00, b"llo"),
    ]);
    assert_eq!(run(&b, true), (Ok(()), post_events()));
    assert_eq!(run_bytewise(&b, true), (Ok(()), post_events()));
}

#[test]
fn chunking() {
    assert_eq!(run_bytewise(&post_body_bytes(), true), (Ok(()), post_events()));
    assert_eq!(run_bytewise(&req("GET", &[]), true), (Ok(()), get_events()));
    // Two calls split inside the HEADERS payload.
    let b = post_body_bytes();
    let mut s = RequestStream::new();
    let mut ev = Vec::new();
    assert_eq!(s.on_data(&b[..7], false, &mut ev), Ok(()));
    assert_eq!(s.on_data(&b[7..], true, &mut ev), Ok(()));
    assert_eq!(summary(ev), post_events());
}
