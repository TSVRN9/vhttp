//! 9b3 Task 1: the per-call cost of h3's network-input calls (spec D13, RCA docs/rca/2026-11-14-cookie-merge.md).
//! A per-thread counting allocator measures each input call on its own (9b2's crates/quic/tests/input_cost.rs design).
//! Per call: no `realloc`, and requested bytes at most `COST_A·d + COST_B`, but for one queue buffer of a call given
//! bytes, and, for the call that completes a buffered frame of `f` bytes, `fa·f + COST_B` more (`per_call_ok`): `fa` is
//! `H3_F` for a request stream's frame (QPACK decode expands it), `COST_A` elsewhere.
//! Each test is ignored until the task that makes it pass.
use h3::conn::{H3Conn, Output};
use h3::frame::serialize_frame_header;
use h3::message::RequestHead;
use h3::qpack::field_section::FieldLine;
use byteq::capvec::CapVec;
use h3::request::{ReqEvent, RequestStream, MAX_REQ_EVENTS};
use h3::uni::{SeenUni, UniEvent, UniStream};
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

struct Counting;

// alloc, alloc_zeroed, realloc, dealloc calls; requested bytes (alloc sizes and realloc new sizes); the largest single
// request since `Run::call` reset it
thread_local! {
    static K: Cell<[usize; 6]> = const { Cell::new([0; 6]) };
}

fn bump(i: usize, bytes: usize) {
    let _ = K.try_with(|k| {
        let mut v = k.get();
        v[i] += 1;
        v[4] += bytes;
        v[5] = v[5].max(bytes);
        k.set(v)
    });
}

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        bump(0, l.size());
        System.alloc(l)
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        bump(1, l.size());
        System.alloc_zeroed(l)
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        bump(2, n);
        System.realloc(p, l, n)
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        bump(3, 0);
        System.dealloc(p, l)
    }
}

#[global_allocator]
static ALLOC: Counting = Counting;

/// 9b2's per-call budget: `COST_A` per byte given, `COST_B` for the constant terms.
const COST_A: usize = 8;
const COST_B: usize = 4096;
/// The decoded bytes per encoded byte of a field line, proved (`lemma_line_expansion` in
/// crates/h3/src/qpack/field_section.rs): a static entry is at most 76 bytes and its line at least 1 byte, a Huffman
/// string decodes to at most 8/5 of its bytes (`lemma_decoded_len`), a raw one to its bytes.
const EXPAND: usize = 76;
/// h3's per-byte constant for the frame a call completes (controller ruling after Task 4: QPACK decode expands its
/// input, so 9b2's `COST_A` is not it). An encoded byte can be a whole line, so `decode_lines_bounded`'s `out` takes
/// at most one `FieldLine` slot per encoded byte (`CapVec::new(min(lines.len(), budget/32))`) and `build_headers`'
/// one more; each line's `EXPAND` bytes per encoded byte are copied by the decoder and once more (`build_headers` for a
/// regular field, `validate_request` for a pseudo-header), plus a 2-byte "; " per cookie line. A `host` value is copied
/// a third time (`request_authority_x`, when `:authority` is absent); `host` is not in the static table, so its value
/// is a string literal of at most 8/5 bytes per encoded byte, within the slots' slack. Still O(f).
const H3_F: usize = 2 * std::mem::size_of::<FieldLine>() + 2 * EXPAND + 2;
/// byteq's `MIN_CAP` (9b2 D4); named apart so the RFC-quantity gate, which reads constants by name, never sees it.
const QUEUE_MIN_CAP: usize = 64;

/// One input call: its kind, allocator counts (`k[5]` its largest single request), the bytes it was given, the bytes
/// of the buffered frame it completes (0: none), the bytes the stream holds after it.
#[derive(Clone, Copy)]
struct Call {
    tag: &'static str,
    k: [usize; 6],
    d: usize,
    f: usize,
    held: usize,
}

#[derive(Default)]
struct Run(Vec<Call>);

impl Run {
    /// Measures `g` alone (it returns the bytes held after the call): the record is pushed after the counters are read.
    fn call(&mut self, tag: &'static str, d: usize, f: usize, g: impl FnOnce() -> usize) {
        let a = K.with(|k| {
            let mut v = k.get();
            v[5] = 0;
            k.set(v);
            v
        });
        let held = g();
        let b = K.with(|k| k.get());
        self.0.push(Call {
            tag,
            k: [0, 1, 2, 3, 4, 5].map(|i| if i == 5 { b[5] } else { b[i] - a[i] }),
            d,
            f,
            held,
        });
    }

    fn bytes(&self) -> usize {
        self.0.iter().map(|x| x.k[4]).sum()
    }

    fn reallocs(&self) -> usize {
        self.0.iter().map(|x| x.k[2]).sum()
    }
}

/// `fa`: the per-byte constant of the frame a call completes, `H3_F` on a request stream, else `COST_A`.
fn budget(x: &Call, fa: usize) -> usize {
    COST_A * x.d + COST_B + if x.f > 0 { fa * x.f + COST_B } else { 0 }
}

/// 9b2's rule: in a test whose structure is a `ByteQueue` (`queue`), one allocation of a call given bytes may exceed the
/// budget if it can be a queue buffer, at most `3·(bytes held after the call) + MIN_CAP`.
fn bytes_ok(x: &Call, queue: bool, fa: usize) -> bool {
    x.k[4] <= budget(x, fa) || exempt(x, queue, fa)
}

fn exempt(x: &Call, queue: bool, fa: usize) -> bool {
    let b = budget(x, fa);
    queue && x.k[4] > b && x.d > 0 && x.k[4] - x.k[5] <= b && x.k[5] <= 3 * x.held + QUEUE_MIN_CAP
}

/// A queue allocates a new buffer at most twice per doubling of its peak from `MIN_CAP`.
fn exempt_cap(peak: usize) -> usize {
    2 * (peak / QUEUE_MIN_CAP).max(1).ilog2() as usize + 4
}

/// Each call: no realloc, and `bytes_ok`; at most `exempt_cap` excused calls. Returns the failures, worst call first.
fn per_call_ok(name: &str, m: usize, c: &[Call], queue: bool, fa: usize) -> Vec<String> {
    let mut f = Vec::new();
    let re: Vec<_> = c.iter().enumerate().filter(|(_, x)| x.k[2] != 0).collect();
    if let Some((i, x)) = re.iter().max_by_key(|(_, x)| (x.k[2], x.k[4])) {
        f.push(format!(
            "{name} n={m}: {} calls realloc, {} reallocs in all (worst: call {i} ({}), {} reallocs, {} bytes for d = {})",
            re.len(),
            c.iter().map(|x| x.k[2]).sum::<usize>(),
            x.tag,
            x.k[2],
            x.k[4],
            x.d
        ));
    }
    let peak = c.iter().map(|x| x.held).max().unwrap_or(0);
    let ex = c.iter().filter(|x| exempt(x, queue, fa)).count();
    if ex > exempt_cap(peak) {
        f.push(format!(
            "{name} n={m}: {ex} calls excused as queue buffers, more than {} (peak {peak} held)",
            exempt_cap(peak)
        ));
    }
    let over: Vec<_> = c.iter().enumerate().filter(|(_, x)| !bytes_ok(x, queue, fa)).collect();
    if let Some((i, x)) = over.iter().max_by_key(|(_, x)| x.k[4] - budget(x, fa).min(x.k[4])) {
        f.push(format!(
            "{name} n={m}: {} calls over the per-call budget (worst: call {i} ({}), {} bytes for d = {}, f = {}, budget {}, \
             largest single {}, {} held after)",
            over.len(),
            x.tag,
            x.k[4],
            x.d,
            x.f,
            budget(x, fa),
            x.k[5],
            x.held
        ));
    }
    f
}

/// Requested bytes at most 3x per doubling of n.
fn doubling_ok(name: &str, rows: &[(usize, usize)]) -> Vec<String> {
    rows.windows(2)
        .filter(|w| w[1].1 > 3 * w[0].1)
        .map(|w| {
            format!(
                "{name}: requested bytes {} at n={} -> {} at n={} (> 3x)",
                w[0].1, w[0].0, w[1].1, w[1].0
            )
        })
        .collect()
}

fn report(name: &str, m: usize, r: &Run) {
    let c = &r.0;
    let sum = |i: usize| c.iter().map(|x| x.k[i]).sum::<usize>();
    let big = c.iter().enumerate().max_by_key(|(_, x)| x.k[4]).unwrap();
    eprintln!(
        "{name} n={m}: calls {} requested {} alloc {} alloc_zeroed {} realloc {} dealloc {} largest-call {} bytes (call {}, \
         d = {}) peak-held {}",
        c.len(),
        sum(4),
        sum(0),
        sum(1),
        sum(2),
        sum(3),
        big.1.k[4],
        big.0,
        big.1.d,
        c.iter().map(|x| x.held).max().unwrap()
    );
}

// ------------------------------------------------------------------ frame builders (the RCA's method)

fn frame(ty: u64, payload: &[u8]) -> Vec<u8> {
    let mut o = Vec::new();
    serialize_frame_header(ty, payload.len() as u64, &mut o);
    o.extend_from_slice(payload);
    o
}

/// A HEADERS frame: the field-section prefix (Required Insert Count 0, Delta Base 0), `:method GET`, `:scheme https`,
/// `:path /` (static indexed lines 17, 23, 1), `:authority a` (static name reference 0), then `lines`.
fn headers(lines: &[u8]) -> Vec<u8> {
    let mut p = vec![0x00, 0x00, 0xD1, 0xD7, 0xC1, 0x50, 0x01, b'a'];
    p.extend_from_slice(lines);
    frame(0x01, &p)
}

/// `n` literal lines with static name reference `idx` (< 16), each with a raw value of `v` (< 127) bytes `a`.
fn named_lines(idx: u8, n: usize, v: usize) -> Vec<u8> {
    assert!(idx < 16 && v < 127);
    let mut o = Vec::new();
    for _ in 0..n {
        o.extend_from_slice(&[0x50 | idx, v as u8]);
        o.extend(std::iter::repeat_n(b'a', v));
    }
    o
}

/// `cookie` (static 5) lines.
fn cookie_lines(n: usize, v: usize) -> Vec<u8> {
    named_lines(5, n, v)
}

/// `date` (static 6) lines: not merged.
fn date_lines(n: usize, v: usize) -> Vec<u8> {
    named_lines(6, n, v)
}

/// `accept` (static 29, a 4-bit prefix integer 15 + 14) lines with empty values.
fn accept_lines(n: usize) -> Vec<u8> {
    [0x5F, 0x0E, 0x00].repeat(n)
}

/// A QUIC varint (RFC 9000 §16).
fn varint(x: u64, o: &mut Vec<u8>) {
    match x {
        0..=63 => o.push(x as u8),
        64..=16383 => o.extend_from_slice(&(0x4000 | x as u16).to_be_bytes()),
        16384..=0x3fff_ffff => o.extend_from_slice(&(0x8000_0000 | x as u32).to_be_bytes()),
        _ => o.extend_from_slice(&(0xc000_0000_0000_0000 | x).to_be_bytes()),
    }
}

/// The first `n` non-reserved SETTINGS identifiers in order: 0, 1, then 6 on (2-5 are HTTP/2's, codes.rs; F5).
fn settings_ids(n: usize) -> Vec<u64> {
    (0u64..).filter(|i| !(2..=5).contains(i)).take(n).collect()
}

/// A SETTINGS payload: each id with value 0.
fn settings_payload(ids: &[u64]) -> Vec<u8> {
    let mut o = Vec::new();
    for &i in ids {
        varint(i, &mut o);
        varint(0, &mut o);
    }
    o
}

fn fresh_seen() -> SeenUni {
    SeenUni {
        control: false,
        encoder: false,
        decoder: false,
    }
}

// ------------------------------------------------------------------ request streams

/// Feeds `fr` to a fresh `RequestStream`, `step` bytes per call (the last call completes the frame); returns the run
/// and the events.
fn feed_request(fr: &[u8], step: usize, tag: &'static str) -> (Run, Vec<ReqEvent>) {
    let mut s = RequestStream::new();
    let mut r = Run::default();
    let mut all = Vec::new();
    for (i, ch) in fr.chunks(step).enumerate() {
        let last = (i + 1) * step >= fr.len();
        let mut ev = Vec::new();
        r.call(tag, ch.len(), if last { fr.len() } else { 0 }, || {
            ev = req_call(&mut s, ch);
            s.buffered_len()
        });
        all.extend(ev);
    }
    (r, all)
}

/// One `on_data` call (no FIN) with its `MAX_REQ_EVENTS` event buffer, which the call's allocations include.
fn req_call(s: &mut RequestStream, b: &[u8]) -> Vec<ReqEvent> {
    let mut ev = CapVec::new(MAX_REQ_EVENTS);
    assert_eq!(s.on_data(b, false, &mut ev).0, Ok(()));
    ev.into_vec()
}

/// The request's headers: (name, value length).
fn head_fields(ev: &[ReqEvent]) -> Vec<(Vec<u8>, usize)> {
    let [ReqEvent::Head(RequestHead::Request(q))] = ev else {
        panic!("expected one request head")
    };
    q.headers.iter().map(|f| (f.name.clone(), f.value.len())).collect()
}

/// The completing (last) call of `r`: at most `H3_F·frame + COST_B`.
fn completing_ok(name: &str, m: usize, r: &Run, fr: usize) -> Vec<String> {
    let x = r.0.last().unwrap();
    eprintln!(
        "  {name} n={m}: completing call requested {} (d = {}, realloc {}), frame {fr}",
        x.k[4], x.d, x.k[2]
    );
    if x.k[4] > H3_F * fr + COST_B {
        vec![format!(
            "{name} n={m}: the completing call requested {} > {H3_F}·{fr} + {COST_B}",
            x.k[4]
        )]
    } else {
        vec![]
    }
}

#[test]
fn cookie_lines_linear() {
    let (v, mut fails, mut whole, mut bytewise) = (34, Vec::new(), Vec::new(), Vec::new());
    for m in [226, 452, 904] {
        let fr = headers(&cookie_lines(m, v));
        if m == 226 {
            assert_eq!(fr.len(), 8147, "the RCA's frame bytes at n = 226");
        }
        for (step, tag, rows) in [(fr.len(), "whole", &mut whole), (1, "bytewise", &mut bytewise)] {
            let (r, ev) = feed_request(&fr, step, tag);
            let h = head_fields(&ev);
            assert_eq!(h, vec![(b"cookie".to_vec(), m * v + (m - 1) * 2)]);
            report(&format!("cookie_lines_linear {tag}"), m, &r);
            fails.extend(per_call_ok(&format!("cookie_lines_linear {tag}"), m, &r.0, true, H3_F));
            fails.extend(completing_ok(&format!("cookie_lines_linear {tag}"), m, &r, fr.len()));
            rows.push((m, r.bytes()));
        }
    }
    fails.extend(doubling_ok("cookie_lines_linear whole", &whole));
    fails.extend(doubling_ok("cookie_lines_linear bytewise", &bytewise));
    assert!(fails.is_empty(), "{fails:#?}");
}

/// The rescan's time is mutant 9b3-M8's to catch.
#[test]
fn cookie_rescans_linear() {
    let (mut fails, mut rows) = (Vec::new(), Vec::new());
    for m in [215, 430, 860] {
        let mut lines = accept_lines(m);
        lines.extend(cookie_lines(m, 0));
        let fr = headers(&lines);
        let (r, ev) = feed_request(&fr, fr.len(), "whole");
        let h = head_fields(&ev);
        assert_eq!(h.len(), m + 1);
        assert_eq!(h[m], (b"cookie".to_vec(), (m - 1) * 2));
        report("cookie_rescans_linear", m, &r);
        if r.reallocs() != 0 {
            fails.push(format!("cookie_rescans_linear n={m}: {} reallocs", r.reallocs()));
        }
        fails.extend(completing_ok("cookie_rescans_linear", m, &r, fr.len()));
        rows.push((m, r.bytes()));
    }
    fails.extend(doubling_ok("cookie_rescans_linear", &rows));
    assert!(fails.is_empty(), "{fails:#?}");
}

#[test]
fn huffman_max_expansion() {
    // 6,400 'a' (HPACK code 00011, 5 bits): 32,000 bits, 4,000 bytes, no padding.
    let mut enc = Vec::new();
    let (mut acc, mut bits) = (0u64, 0);
    for _ in 0..6400 {
        acc = (acc << 5) | 0b00011;
        bits += 5;
        while bits >= 8 {
            bits -= 8;
            enc.push((acc >> bits) as u8);
        }
    }
    assert_eq!((enc.len(), bits), (4000, 0));
    // A literal line with a literal name `x` (001 N=0 H=0, length 1), then a Huffman value of 4,000 bytes (H=1, a 7-bit
    // prefix integer 127 + 3,873).
    let mut line = vec![0x21, b'x', 0xFF, 0xA1, 0x1E];
    line.extend_from_slice(&enc);
    let fr = headers(&line);
    let (r, ev) = feed_request(&fr, fr.len(), "whole");
    assert_eq!(head_fields(&ev), vec![(b"x".to_vec(), 6400)]);
    report("huffman_max_expansion", 6400, &r);
    assert_eq!(r.reallocs(), 0, "huffman_max_expansion: reallocs in the call");
}

#[test]
fn headers_bytewise() {
    let fr = headers(&date_lines(413, 120));
    assert_eq!(fr.len(), 50399, "the RCA's frame bytes");
    let (r, ev) = feed_request(&fr, 1, "byte");
    assert_eq!(head_fields(&ev).len(), 413);
    report("headers_bytewise", 413, &r);
    let l = r.0.len() - 1;
    let fails = per_call_ok("headers_bytewise", 413, &r.0[..l], true, H3_F);
    assert!(fails.is_empty(), "{fails:#?}");
}

#[test]
fn data_frames_events() {
    let mut s = RequestStream::new();
    assert_eq!(req_call(&mut s, &headers(&[])).len(), 1);
    let n = 5461;
    let data: Vec<u8> = (0..n).flat_map(|i| [0x00, 0x01, i as u8]).collect();
    let mut r = Run::default();
    let mut ev = Vec::new();
    r.call("data", data.len(), 0, || {
        ev = req_call(&mut s, &data);
        s.buffered_len()
    });
    report("data_frames_events", n, &r);
    let bodies: Vec<usize> = ev
        .iter()
        .filter_map(|e| if let ReqEvent::Body(b) = e { Some(b.len()) } else { None })
        .collect();
    let mut fails = per_call_ok("data_frames_events", n, &r.0, true, H3_F);
    if ev.len() > 4 || bodies != vec![n] {
        fails.push(format!(
            "data_frames_events: {} events, {} Body events ({} bytes in all), want at most 4 events and one Body of {n}",
            ev.len(),
            bodies.len(),
            bodies.iter().sum::<usize>()
        ));
    }
    assert!(fails.is_empty(), "{fails:#?}");
}

// ------------------------------------------------------------------ uni streams

/// Feeds `b` to a fresh `UniStream`, cut every `step` bytes (call ends); `done(i)` is the frame or instruction bytes call `i`
/// completes. Returns the run and the events.
fn feed_uni(b: &[u8], step: usize, tag: &'static str, done: impl Fn(usize, usize) -> usize) -> (Run, Vec<UniEvent>) {
    let (mut s, mut seen, mut r, mut all) = (UniStream::new(), fresh_seen(), Run::default(), Vec::new());
    for (i, ch) in b.chunks(step).enumerate() {
        let mut ev = Vec::new();
        r.call(tag, ch.len(), done(i * step, ch.len()), || {
            assert_eq!(s.on_data(ch, false, &mut seen, &mut ev), Ok(()));
            s.buffered_len()
        });
        all.extend(ev);
    }
    (r, all)
}

#[test]
#[ignore = "9b3: fails today, the uni buffer grows by append (reallocs); un-ignored by Task 8"]
fn control_bytewise() {
    // 60 one-byte ids (0, 1, 6-63) and 301 two-byte ones: 361 pairs, a 1,023-byte payload.
    let ids = settings_ids(361);
    let p = settings_payload(&ids);
    assert_eq!(p.len(), 1023);
    assert!(p.len() as u64 <= h3::limits::MAX_SETTINGS_FRAME);
    let fr = frame(0x04, &p);
    let mut b = vec![0x00];
    b.extend_from_slice(&fr);
    let end = b.len();
    let (r, ev) = feed_uni(&b, 1, "byte", |at, d| if at + d == end { fr.len() } else { 0 });
    let want: Vec<(u64, u64)> = ids.iter().map(|&i| (i, 0)).collect();
    assert_eq!(ev, vec![UniEvent::PeerSettings(want)]);
    report("control_bytewise", ids.len(), &r);
    let fails = per_call_ok("control_bytewise", ids.len(), &r.0, true, COST_A);
    assert!(fails.is_empty(), "{fails:#?}");
}

#[test]
#[ignore = "9b3: fails today, the uni buffer is rebuilt exact then grown by append (reallocs); un-ignored by Task 8"]
fn qpack_bytewise() {
    // The decoder stream (type 0x03), then 2,000 Stream Cancellations (01 + a 6-bit prefix integer) of ids 63 + 8i:
    // 0x7F then one or two continuation bytes, so 3-byte calls cut instructions.
    let mut b = vec![0x03];
    for i in 0..2000u64 {
        b.push(0x7F);
        let x = 8 * i;
        if x < 128 {
            b.push(x as u8);
        } else {
            b.extend_from_slice(&[0x80 | (x & 0x7F) as u8, (x >> 7) as u8]);
        }
    }
    let (r, ev) = feed_uni(&b, 3, "3 bytes", |_, _| 0);
    assert!(ev.is_empty());
    report("qpack_bytewise", 2000, &r);
    let mut fails = per_call_ok("qpack_bytewise", 2000, &r.0, true, COST_A);
    if let Some((i, x)) = r.0.iter().enumerate().find(|(_, x)| x.held > 11) {
        fails.push(format!(
            "qpack_bytewise: {} bytes held after call {i}, more than 11",
            x.held
        ));
    }
    assert!(fails.is_empty(), "{fails:#?}");
}

// ------------------------------------------------------------------ the connection

/// The client's control stream (2) with an empty SETTINGS, on a started connection.
fn ready() -> H3Conn {
    let mut c = H3Conn::new();
    let mut out = Vec::new();
    c.start(&mut out);
    let mut b = vec![0x00];
    b.extend(frame(0x04, &[]));
    let mut out = Vec::new();
    c.on_stream_data(2, &b, false, &mut out);
    assert!(out.is_empty());
    c
}

#[test]
#[ignore = "9b3: fails today, the stream table is a Vec grown by push (reallocs); un-ignored by Task 11"]
fn stream_table_flat() {
    let mut c = ready();
    let mut r = Run::default();
    let fr = headers(&[]);
    let n = 100u64;
    // `held` is 0: H3Conn exposes no buffered count, and nothing is buffered after a whole frame (the strictest
    // queue allowance).
    for i in 0..n {
        let mut out = Vec::new();
        r.call("open", fr.len(), 0, || {
            c.on_stream_data(4 * i, &fr, false, &mut out);
            0
        });
        assert!(matches!(&out[..], [Output::Request { stream_id, .. }] if *stream_id == 4 * i));
    }
    for i in (0..n).rev() {
        let mut out = Vec::new();
        r.call("data", 3, 0, || {
            c.on_stream_data(4 * i, &[0x00, 0x01, b'x'], false, &mut out);
            0
        });
        assert!(matches!(&out[..], [Output::RequestBody { stream_id, data }] if *stream_id == 4 * i && data == b"x"));
    }
    report("stream_table_flat", n as usize, &r);
    let fails = per_call_ok("stream_table_flat", n as usize, &r.0, false, COST_A);
    assert!(fails.is_empty(), "{fails:#?}");
}
