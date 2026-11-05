//! The static response through `Server`, with rustls as a real QUIC client (the quictls
//! harness, included as is: its own tests run here too).
#![allow(dead_code)]
#[path = "../../quictls/tests/e2e.rs"]
mod e2e;
use e2e::Client;
use h3::frame::{parse_frame_header, serialize_frame_header, FrameHeader};
use h3::qpack::field_section::{decode_field_section, encode_field_section, FieldLine};
use quic::frame::Frame;
use quic::payload::PacketKind;
use server::*;
use std::io;
use std::net::SocketAddr;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

static CALLS: AtomicU64 = AtomicU64::new(0);
static FILLS: Mutex<Vec<Vec<u8>>> = Mutex::new(Vec::new());

/// Every call fills `b` with bytes no other call gets, so a reused array shows as equal arrays.
fn rng(b: &mut [u8]) -> io::Result<()> {
    let n = CALLS.fetch_add(1, Ordering::SeqCst) + 1;
    for (i, x) in b.iter_mut().enumerate() {
        *x = (n.wrapping_mul(37) as u8).wrapping_add((i as u8).wrapping_mul(11)) ^ (n >> 8) as u8;
    }
    FILLS.lock().unwrap().push(b.to_vec());
    Ok(())
}

fn get() -> Vec<u8> {
    let fl = |n: &[u8], v: &[u8]| FieldLine { name: n.to_vec(), value: v.to_vec() };
    let mut b = Vec::new();
    encode_field_section(&[fl(b":method", b"GET"), fl(b":scheme", b"https"), fl(b":authority", b"localhost"), fl(b":path", b"/")], &mut b);
    let mut out = Vec::new();
    serialize_frame_header(0x01, b.len() as u64, &mut out);
    out.extend_from_slice(&b);
    out
}

fn stream(id: u64, off: u64, d: &[u8], fin: bool) -> Frame {
    Frame::Stream { stream_id: id, offset: off, data: d.to_vec(), fin }
}

/// Feeds the client's datagrams to the server and the server's replies to the client; returns the
/// 1-RTT STREAM bytes by stream id.
fn exchange(s: &mut Server, c: &mut Client, from: SocketAddr, now: u64, ds: Vec<Vec<u8>>, got: &mut Vec<(u64, Vec<u8>)>) {
    for d in ds {
        let mut send = Vec::new();
        s.on_datagram(&d, from, now, &mut send).unwrap();
        for (r, to) in send {
            assert_eq!(to, from);
            for (k, frames) in c.absorb(&r) {
                for f in frames {
                    if let (PacketKind::OneRtt, Frame::Stream { stream_id, offset, data, .. }) = (k, f) {
                        let i = got.iter().position(|(id, _)| *id == stream_id);
                        let v = match i {
                            Some(i) => &mut got[i].1,
                            None => {
                                got.push((stream_id, Vec::new()));
                                &mut got.last_mut().unwrap().1
                            }
                        };
                        assert_eq!(v.len() as u64, offset);
                        v.extend_from_slice(&data);
                    }
                }
            }
        }
    }
}

fn check_response(w: &[u8]) {
    let FrameHeader::Complete { ty: 1, len, hdr_len } = parse_frame_header(w) else { panic!("no HEADERS") };
    let end = hdr_len + len as usize;
    let fields = decode_field_section(&w[hdr_len..end]).unwrap();
    assert_eq!(fields.len(), 2);
    assert_eq!((&fields[0].name[..], &fields[0].value[..]), (&b":status"[..], &b"200"[..]));
    assert_eq!((&fields[1].name[..], &fields[1].value[..]), (&b"content-type"[..], &b"text/plain"[..]));
    let mut data = vec![0x00, RESPONSE_BODY.len() as u8];
    data.extend_from_slice(RESPONSE_BODY);
    assert_eq!(&w[end..], &data[..]);
}

/// A completed handshake through `Server`, then `requests` GETs on streams 0, 4, ... in one
/// datagram. Returns the stream data the client received.
fn serve(requests: u64) -> Vec<(u64, Vec<u8>)> {
    let cfg: &'static _ = Box::leak(Box::new(
        load_config(include_bytes!("data/cert.pem"), include_bytes!("data/key.pem"), vec![]).unwrap(),
    ));
    let mut s = Server::new(cfg, rng);
    let mut c = Client::new();
    let from: SocketAddr = "127.0.0.1:50000".parse().unwrap();
    let mut got = Vec::new();
    for round in 0..8u64 {
        if !c.handshaking() && round > 1 {
            break;
        }
        let ds = c.datagrams(None);
        exchange(&mut s, &mut c, from, 10 + round, ds, &mut got);
    }
    assert!(!c.handshaking());
    assert_eq!(s.conn_count(), 1);
    let mut frames = vec![stream(2, 0, &[0x00, 0x04, 0x00], false)];
    for i in 0..requests {
        frames.push(stream(4 * i, 0, &get(), true));
    }
    let ds = c.datagrams(Some(frames));
    exchange(&mut s, &mut c, from, 30, ds, &mut got);
    // A later datagram lets a response that waited for room go out.
    for r in 0..4 {
        let ds = c.datagrams(Some(vec![Frame::Ping]));
        exchange(&mut s, &mut c, from, 40 + r, ds, &mut got);
    }
    // No two of the server's random fills were equal (no array reused).
    let fills = FILLS.lock().unwrap();
    for (i, a) in fills.iter().enumerate() {
        for b in &fills[i + 1..] {
            assert_ne!(a, b);
        }
    }
    got
}

#[test]
fn get_gets_the_static_response() {
    let got = serve(1);
    let r = got.iter().find(|(id, _)| *id == 0).expect("a response on stream 0");
    check_response(&r.1);
}

#[test]
fn two_requests_answered_in_order() {
    let got = serve(2);
    for id in [0, 4] {
        let r = got.iter().find(|(i, _)| *i == id).unwrap_or_else(|| panic!("no response on stream {id}"));
        check_response(&r.1);
    }
}
