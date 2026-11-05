//! Phase 3d2 Task 4: `flush` must not copy the queued tail. A peer paces `pump` (any 1-RTT packet
//! will do), so a copy there costs up to a whole deferred response per packet.
// One test in this binary; the counter is per thread anyway, since libtest runs tests on threads.
#![allow(dead_code)]
use h3::message::Response;
use h3::qpack::field_section::{encode_field_section, FieldLine};
use h3::frame::serialize_frame_header;
use quic::conn::*;
use quic::datagram::*;
use quic::frame::Frame;
use quic::h3_server::*;
use quic::payload::PacketKind;
use quic::tp::*;
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

/// Calibrated at 7d4d174 plus fix round 1: 16 bytes around the PING. A tail copy allocates about 2 MiB.
const LIMIT: usize = 64 << 10;

struct Counting;

thread_local! {
    static BYTES: Cell<usize> = const { Cell::new(0) };
}

fn count(n: usize) {
    let _ = BYTES.try_with(|b| b.set(b.get() + n));
}

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        count(l.size());
        System.alloc(l)
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        count(l.size());
        System.alloc_zeroed(l)
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        count(n);
        System.realloc(p, l, n)
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        System.dealloc(p, l)
    }
}

#[global_allocator]
static ALLOC: Counting = Counting;

fn allocated() -> usize {
    BYTES.with(|b| b.get())
}

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

fn big_ptp() -> TransportParams {
    let mut t = default_transport_params();
    t.initial_source_connection_id = Some(C1.to_vec());
    t.initial_max_data = 1 << 30;
    t.initial_max_stream_data_bidi_local = 1 << 30;
    t.initial_max_stream_data_uni = 100;
    t.initial_max_streams_uni = 3;
    t.active_connection_id_limit = 4;
    t
}

fn pkt(kind: PacketKind, dcid: &[u8], scid: &[u8], pn: u64, frames: Vec<Frame>) -> PlainPacket {
    PlainPacket { kind, dcid: dcid.to_vec(), scid: scid.to_vec(), token: vec![], pn, frames }
}

fn one(pn: u64, f: Vec<Frame>) -> PlainPacket {
    pkt(PacketKind::OneRtt, &L0, &[], pn, f)
}

fn established() -> Connection {
    let first = vec![Frame::Crypto { offset: 0, data: vec![1; 100] }];
    let ini = pkt(PacketKind::Initial, &S1, &C1, 2, first);
    let mut c = Connection::accept(&ini, 1200, 0, 0, &rnd(1), &ltp()).unwrap();
    c.on_datagram(0, 1200, vec![ini], None, 0, &rnd(1));
    c.on_datagram(0, 1200, vec![pkt(PacketKind::Handshake, &L0, &C1, 0, vec![Frame::Ping])], None, 10, &rnd(9));
    c.on_peer_params(&big_ptp(), 10);
    c.on_handshake_complete(b"h3", 10, &rnd(2));
    c
}

fn fl(n: &[u8], v: &[u8]) -> FieldLine {
    FieldLine { name: n.to_vec(), value: v.to_vec() }
}

fn get() -> Vec<u8> {
    let f = [fl(b":method", b"GET"), fl(b":scheme", b"https"), fl(b":authority", b"example.com"), fl(b":path", b"/")];
    let mut b = Vec::new();
    encode_field_section(&f, &mut b);
    let mut out = Vec::new();
    serialize_frame_header(0x01, b.len() as u64, &mut out);
    out.extend_from_slice(&b);
    out
}

/// A GET answered by 3 MiB: the send buffer is full and nothing has been polled, so there is no room.
fn deferred() -> H3Server {
    let mut s = H3Server::new(established());
    let mut app = Vec::new();
    s.pump(&mut app);
    let f = vec![Frame::Stream { stream_id: 0, offset: 0, data: get(), fin: true }];
    s.on_datagram(0, 300, vec![one(0, f)], 40, &rnd(0), &mut app);
    assert_eq!(app.len(), 2);
    let r = Response { status: 200, headers: vec![], body: vec![0x5a; 3 << 20] };
    assert_eq!(s.send_response(0, &r, &mut app), Ok(()));
    assert!(s.pending_bytes() > 1 << 20);
    s
}

#[test]
fn zero_room_ping_copies_nothing() {
    let mut s = deferred();
    let queued = s.pending_bytes();
    let mut app = Vec::new();
    let p = vec![one(1, vec![Frame::Ping])];
    let r = rnd(1);
    let before = allocated();
    s.on_datagram(0, 300, p, 41, &r, &mut app);
    let n = allocated() - before;
    assert_eq!(s.pending_bytes(), queued);
    assert!(n < LIMIT, "{n} bytes allocated around one PING");
}
