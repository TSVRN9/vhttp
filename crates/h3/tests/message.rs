use h3::codes::H3_MESSAGE_ERROR;
use h3::message::*;
use h3::qpack::field_section::FieldLine;

fn fl(n: &str, v: &str) -> FieldLine {
    FieldLine { name: n.as_bytes().to_vec(), value: v.as_bytes().to_vec() }
}

fn pairs(v: &[FieldLine]) -> Vec<(Vec<u8>, Vec<u8>)> {
    v.iter().map(|f| (f.name.clone(), f.value.clone())).collect()
}

fn base() -> Vec<FieldLine> {
    vec![fl(":method", "GET"), fl(":scheme", "https"), fl(":authority", "example.com"), fl(":path", "/")]
}

fn with(extra: Vec<FieldLine>) -> Vec<FieldLine> {
    let mut v = base();
    v.extend(extra);
    v
}

#[test]
fn valid_get() {
    let f = with(vec![fl("accept", "*/*")]);
    match validate_request(&f) {
        Ok(RequestHead::Request(r)) => {
            assert_eq!(r.method, b"GET");
            assert_eq!(r.scheme, b"https");
            assert_eq!(r.authority, b"example.com");
            assert_eq!(r.path, b"/");
            assert_eq!(pairs(&r.headers), pairs(&[fl("accept", "*/*")]));
        }
        _ => panic!("expected Request"),
    }
}

fn err(f: Vec<FieldLine>) {
    assert!(matches!(validate_request(&f), Err(H3_MESSAGE_ERROR)));
}

#[test]
fn malformed_cases() {
    err(with(vec![fl("Accept", "x")]));
    err(with(vec![fl("accept", "x ")]));
    err(with(vec![fl("accept", "x\ry")]));
    err(with(vec![fl("accept", "*/*"), fl(":path", "/")]));
    err(with(vec![]).into_iter().chain([fl(":path", "/b")]).collect());
    err(vec![fl(":method", "GET"), fl(":scheme", "https"), fl(":authority", "a"), fl(":path", "/"), fl(":protocol", "x")]);
    err(vec![fl(":method", "GET"), fl(":authority", "a"), fl(":path", "/")]);
    err(vec![fl(":method", "GET"), fl(":scheme", "https"), fl(":authority", "a"), fl(":path", "")]);
    err(vec![fl(":method", "GET"), fl(":scheme", "https"), fl(":authority", "user@host"), fl(":path", "/")]);
    err(with(vec![fl("connection", "close")]));
    err(with(vec![fl("te", "gzip")]));
    err(vec![fl(":method", "GET"), fl(":scheme", "https"), fl(":authority", "a"), fl(":path", "/"), fl("host", "b")]);
    err(with(vec![fl("content-length", "12a")]));
    err(with(vec![fl("content-length", "3"), fl("content-length", "4")]));
    err(with(vec![fl("content-length", "99999999999999999999")]));
    err(with(vec![fl("content-length", "")]));
    err(vec![fl(":method", "GET"), fl(":scheme", "https"), fl(":path", "/")]);
    err(with(vec![fl("host", "a"), fl("host", "a")]));
}

#[test]
fn accepted_variants() {
    assert!(validate_request(&with(vec![fl("te", "trailers"), fl("content-length", "3"), fl("content-length", "3")])).is_ok());
    let f = vec![fl(":method", "GET"), fl(":scheme", "https"), fl(":path", "/"), fl("host", "h")];
    match validate_request(&f) {
        Ok(RequestHead::Request(r)) => assert_eq!(r.authority, b"h"),
        _ => panic!(),
    }
    assert_eq!(content_length(&with(vec![fl("content-length", "0042")])), Some(42));
    assert_eq!(content_length(&base()), None);
    assert!(validate_trailers(&[fl("x-sum", "1")]));
    assert!(!validate_trailers(&[fl(":path", "/")]));
    assert!(!validate_trailers(&[fl("X", "1")]));
}

#[test]
fn connect() {
    let f = vec![fl(":method", "CONNECT"), fl(":authority", "example.com:443")];
    match validate_request(&f) {
        Ok(RequestHead::Connect { authority }) => assert_eq!(authority, b"example.com:443"),
        _ => panic!("expected Connect"),
    }
    let mut g = f;
    g.push(fl(":path", "/"));
    err(g);
    // RFC 9114 §4.4, RFC 9110 §9.3.6: authority-form, host ":" port, no userinfo.
    for a in ["[::1]:443", "h:1", "example.com:443"] {
        let f = vec![fl(":method", "CONNECT"), fl(":authority", a)];
        assert!(matches!(validate_request(&f), Ok(RequestHead::Connect { .. })), "{a}");
    }
    for a in ["u@h:443", "h", "h:", ":443", "h:4a", "h:44 ", ""] {
        err(vec![fl(":method", "CONNECT"), fl(":authority", a)]);
    }
}

#[test]
fn cookie_merge() {
    let f = with(vec![fl("cookie", "a=1"), fl("accept", "x"), fl("cookie", "b=2")]);
    match validate_request(&f) {
        Ok(RequestHead::Request(r)) => {
            assert_eq!(pairs(&r.headers), pairs(&[fl("cookie", "a=1; b=2"), fl("accept", "x")]))
        }
        _ => panic!(),
    }
}

#[test]
fn response_check() {
    let r = |s: u16, n: &str, v: &str| Response { status: s, headers: vec![fl(n, v)], body: vec![] };
    assert!(check_response(&r(200, "content-type", "text/plain"), false));
    assert!(!check_response(&r(99, "content-type", "text/plain"), false));
    assert!(!check_response(&r(600, "content-type", "text/plain"), false));
    assert!(!check_response(&r(200, "Content-Type", "text/plain"), false));
    assert!(!check_response(&r(200, "connection", "x"), false));
    assert!(!check_response(&r(200, ":status", "200"), false));
    // RFC 9114 §4.2: TE is allowed only in a request header.
    assert!(!check_response(&r(200, "te", "trailers"), false));
    assert!(!check_response(&r(200, "te", "gzip"), false));
}

#[test]
fn hardening() {
    err(vec![fl(":method", "GET"), fl(":scheme", "https"), fl(":path", "/"), fl("host", "user@h")]);
    err(vec![fl(":method", "GET"), fl(":scheme", "HTTPS"), fl(":path", "/")]);
    err(vec![fl(":method", "GET"), fl(":scheme", "HtTp"), fl(":path", "/")]);
    assert!(!validate_trailers(&[fl("connection", "x")]));
    assert!(!validate_trailers(&[fl("te", "trailers")]));
    assert!(validate_trailers(&[fl("x-t", "1")]));
    err(vec![fl(":method", ""), fl(":scheme", "https"), fl(":authority", "a"), fl(":path", "/")]);
    err(vec![fl(":method", "CONNECT"), fl(":scheme", "https"), fl(":authority", "a:1")]);
}
