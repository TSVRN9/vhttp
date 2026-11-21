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
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

/// Counts this thread's frees (per thread: tests run in parallel), so a test can bound one call's.
struct Counting;

thread_local! {
    static FREES: Cell<usize> = const { Cell::new(0) };
}

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        unsafe { System.alloc(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        let _ = FREES.try_with(|f| f.set(f.get() + 1));
        unsafe { System.dealloc(p, l) }
    }
}

#[global_allocator]
static ALLOC: Counting = Counting;

fn frees() -> usize {
    FREES.with(|f| f.get())
}

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

/// D13 through the shell: an inflated ClientHello whose bytes `[1, N)` came first, then the 1-byte gap fill.
/// `Server::on_datagram` pumps the backlog that datagram leaves, so its replies already hold the server's Initial
/// and Handshake flight; the exchange then completes and the static response arrives, with no other datagram
/// needed to move the handshake on.
#[test]
fn gap_filled_client_hello_completes_without_another_datagram() {
    let cfg: &'static _ = Box::leak(Box::new(
        load_config(include_bytes!("data/cert.pem"), include_bytes!("data/key.pem"), vec![]).unwrap(),
    ));
    let mut s = Server::new(cfg, rng);
    let mut c = Client::with_alpn_pad(200);
    let from: SocketAddr = "127.0.0.1:50001".parse().unwrap();
    let mut got = Vec::new();
    let (ch, ds) = e2e::big_ch(&mut c, 1);
    exchange(&mut s, &mut c, from, 10, ds, &mut got);
    assert!(!s.has_backlog());
    let gap = c.ch_dgram(&ch, 0, 1);
    let mut send = Vec::new();
    s.on_datagram(&gap, from, 11, &mut send).unwrap();
    assert!(!s.has_backlog());
    let mut kinds = Vec::new();
    for (r, to) in send {
        assert_eq!(to, from);
        kinds.extend(c.absorb(&r).into_iter().map(|(k, _)| k));
    }
    assert!(kinds.contains(&PacketKind::Initial) && kinds.contains(&PacketKind::Handshake), "{kinds:?}");
    for round in 0..8u64 {
        if !c.handshaking() && round > 1 {
            break;
        }
        let ds = c.datagrams(None);
        exchange(&mut s, &mut c, from, 12 + round, ds, &mut got);
    }
    assert!(!c.handshaking());
    let ds = c.datagrams(Some(vec![stream(2, 0, &[0x00, 0x04, 0x00], false), stream(0, 0, &get(), true)]));
    exchange(&mut s, &mut c, from, 30, ds, &mut got);
    for r in 0..4 {
        let ds = c.datagrams(Some(vec![Frame::Ping]));
        exchange(&mut s, &mut c, from, 40 + r, ds, &mut got);
    }
    let r = got.iter().find(|(id, _)| *id == 0).expect("a response on stream 0");
    check_response(&r.1);
}

/// A server with one connection, handshake complete, then `open` request streams left open (no FIN) and `answered`
/// GETs whose responses the client takes; it acknowledges only the even 1-RTT packet numbers, so the other responses'
/// sending parts keep their pieces in flight (tree nodes) at a close.
fn busy_server(open: u64, answered: u64, from: SocketAddr) -> (Server<'static>, Client) {
    let cfg: &'static _ = Box::leak(Box::new(
        load_config(include_bytes!("data/cert.pem"), include_bytes!("data/key.pem"), vec![]).unwrap(),
    ));
    let mut s = Server::new(cfg, rng);
    let mut c = Client::new();
    let mut got = Vec::new();
    for round in 0..8u64 {
        if !c.handshaking() && round > 1 {
            break;
        }
        let ds = c.datagrams(None);
        exchange(&mut s, &mut c, from, 10 + round, ds, &mut got);
    }
    assert!(!c.handshaking());
    let mut frames = vec![stream(2, 0, &[0x00, 0x04, 0x00], false)];
    for i in 0..open + answered {
        frames.push(stream(4 * i, 0, &get(), i >= open));
    }
    let ds = c.datagrams(Some(frames));
    exchange(&mut s, &mut c, from, 30, ds, &mut got);
    let l = c.largest_one_rtt().expect("1-RTT packets");
    let top = l - l % 2;
    let ack = quic::ack::AckFrame { largest: top, delay: 0, first_range: 0, ranges: vec![(0, 0); (top / 2) as usize], ecn: None };
    let ds = c.datagrams(Some(vec![Frame::Ack(ack)]));
    exchange(&mut s, &mut c, from, 31, ds, &mut got);
    (s, c)
}

/// D13 (9b2 Task 10b fix rounds 1 and 2): a connection closed silently by its idle timeout, holding open streams and
/// answered ones whose responses are acknowledged only in part (sending parts with pieces in flight), is kept until its
/// backlog is freed. Its streams go to the dead slot at the close, its stores and send contexts to their slots at
/// `retire_closed`, and `pump` frees them a bounded `backlog_step` at a time, at most `MAX_PUMPS` per wake: so while it
/// is kept nothing is held outside the slots, the dead entries fall by at most `MAX_PUMPS` per wake (one per step at
/// most), and the wake that removes it frees at most `REMOVAL_FREES`, the last steps and the Connection's own drop.
/// Under the old rule (removal at Closed) the whole teardown happens in one wake and this test fails.
#[test]
fn idle_closed_connection_kept_until_drained() {
    use quic::payload::PacketKind;
    // The removing wake frees 146 here (fix round 2); the Connection's own drop is about 100 of them.
    const REMOVAL_FREES: usize = 250;
    let from: SocketAddr = "127.0.0.1:50002".parse().unwrap();
    let (mut s, _c) = busy_server(24, 12, from);
    let mut send = Vec::new();
    s.on_wake(32, &mut send).unwrap();
    assert_eq!(s.conn_count(), 1);
    let held: usize = (0..36u64).filter_map(|i| s.quic(0).conn().send_range_counts(4 * i)).map(|(a, l, f)| a + l + f).sum();
    assert!(held > 0, "no sending part holds a piece");
    // Past the idle timeout (30 s): closed silently, its streams buried.
    let mut now = 100_000_000;
    let mut wakes = 0;
    let mut dead: Option<usize> = None;
    loop {
        let f0 = frees();
        let mut send = Vec::new();
        s.on_wake(now, &mut send).unwrap();
        let f = frees() - f0;
        wakes += 1;
        if s.conn_count() == 0 {
            assert!(f <= REMOVAL_FREES, "the removing wake freed {f}");
            break;
        }
        let q = s.quic(0).conn();
        assert!(s.has_backlog(), "kept without backlog after wake {wakes}");
        assert!(!q.streams_live());
        for k in [PacketKind::Initial, PacketKind::Handshake] {
            assert_eq!(q.crypto_send_ranges(k), 0, "{k:?}'s send context not retired");
        }
        for k in [PacketKind::Initial, PacketKind::Handshake, PacketKind::OneRtt] {
            assert_eq!(q.crypto_unread(k), 0);
        }
        let d = q.dead_entries().unwrap_or(0);
        if let Some(p) = dead {
            assert!(p - d <= MAX_PUMPS, "dead entries {p} -> {d} in one wake");
        }
        dead = Some(d);
        assert!(wakes < 100, "still kept after {wakes} wakes");
        now += 1;
    }
    assert!(wakes >= 2, "the teardown took {wakes} wake(s): not kept across a wake");
    assert!(!s.has_backlog());
}

/// m6 (9b2 Task 10b fix round 2): admission counts every connection held, so `conns` stays within MAX_CONNS while a
/// Closed connection drains: one connection closed and draining, then MAX_CONNS + 4 new Initials.
#[test]
fn conns_capped_while_closed_drain() {
    use quic::route::MAX_CONNS;
    let from: SocketAddr = "127.0.0.1:50003".parse().unwrap();
    let (mut s, _c) = busy_server(24, 12, from);
    let mut send = Vec::new();
    s.on_wake(100_000_000, &mut send).unwrap();
    assert_eq!(s.conn_count(), 1);
    assert!(s.has_backlog(), "the closed connection drained in one wake");
    for n in 0..MAX_CONNS + 4 {
        let mut odcid = [0xd0u8; 8];
        odcid[6] = (n >> 8) as u8;
        odcid[7] = n as u8;
        let mut c = Client::with_odcid(odcid);
        let d = c.datagrams(None);
        let mut send = Vec::new();
        s.on_datagram(&d[0], from, 100_000_001, &mut send).unwrap();
        assert!(s.conn_count() <= MAX_CONNS, "{} connections after {} Initials", s.conn_count(), n + 1);
    }
    assert_eq!(s.conn_count(), MAX_CONNS);
}
