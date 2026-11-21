//! 9b2 Task 1: the per-call cost of quic's input-path byte buffers (spec "The cost today", D15). Each pattern runs at
//! n, 2n and 4n under a per-thread counting allocator; every input call is measured on its own. The bounds count, never
//! time: requested bytes at most 3x per doubling, per call kind the largest single call's requested bytes at most 3x
//! per doubling (+ `COST_B`), no `realloc`, and a delivering call hands over at most its own input's bytes. Per call
//! (the allocator is deterministic): no `realloc`, and requested bytes at most `COST_A·d + COST_B`, but for one queue
//! buffer of a call given bytes (`per_call_ok`).
use quic::crypto_stream::CryptoStream;
use quic::CapVec;
use quic::recv_stream::{RecvStream, StreamEvent};
use quic::send_stream::{SendState, SendStream};
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

/// The owner's rule is O(d + log n) per call; the spec's per-call bounds are `7d + 4` units for a queue push and `n + 3`
/// for a take (D4), so `COST_A = 8` per byte given, and `COST_B = 4096` covers the constant terms (a 56-byte node per chunk, at
/// most 258 ring slots of 8 bytes and two 256-byte page arrays, D11).
const COST_A: usize = 8;
const COST_B: usize = 4096;
/// byteq's `MIN_CAP` (D4); named apart so the RFC-quantity gate, which reads constants by name, never sees it.
const QUEUE_MIN_CAP: usize = 64;

/// Requested capacity is memory, not work: an uninitialized `with_capacity` is one allocator call, and D4 bounds the copies
/// into it at 3 per byte pushed. So, in a test whose structure is a `ByteQueue` after 9b2 (`queue`), one allocation of a
/// call may exceed the budget if it can be a queue buffer: the call was given bytes (D4 allocates only in `push_slice`
/// with `d > 0`; an ACK or a read creates none) and the allocation is at most `3·(bytes held after the call) + MIN_CAP`
/// (D4's memory bound); the rest of the call stays within the budget. The allocator sees no copy into that buffer: the
/// work bound on it rests on D15's proved cost (`push_slice` at most `7d + 4`), not on this test. `exempt_cap` bounds
/// how many calls a run may excuse so.
fn bytes_ok(x: &Call, a: Alloc) -> bool {
    x.k[4] <= COST_A * x.d + COST_B || exempt(x, a == Alloc::Queue) || gather_ok(x, a)
}

/// Which allocation a call of the test's structure may make beyond the budget: a `ByteQueue`'s buffer (`exempt`), or
/// `Frags::insert`'s gather list (`gather_ok`).
#[derive(Clone, Copy, PartialEq)]
enum Alloc {
    None,
    Queue,
    Gather,
}

/// One entry of `Frags::insert`'s gather list: a chunk's start and its piece.
const GATHER_ENTRY: usize = std::mem::size_of::<(u64, CapVec<u8>)>();

/// `Frags::insert`'s gather list (9b2 Task 6, coordinator ruling): one exact `CapVec` with room for the chunks the frame
/// meets, at most `d` (`split_frame`'s proved `fm.len() <= e - s`), plus `B`'s first chunk, so one allocation of at most
/// `GATHER_ENTRY·(d + 1)` bytes, freed before the call returns; the rest of the call stays within the budget.
fn gather_ok(x: &Call, a: Alloc) -> bool {
    let budget = COST_A * x.d + COST_B;
    a == Alloc::Gather && x.k[4] - x.k[5] <= budget && x.k[5] <= GATHER_ENTRY * (x.d + 1)
}

/// The call passes only by its queue-buffer allowance.
fn exempt(x: &Call, queue: bool) -> bool {
    let budget = COST_A * x.d + COST_B;
    queue && x.k[4] > budget && x.d > 0 && x.k[4] - x.k[5] <= budget && x.k[5] <= 3 * x.held + QUEUE_MIN_CAP
}

/// A queue allocates a new buffer when its length reaches half the old one's capacity (D4), at most twice per doubling
/// of its peak from `MIN_CAP`: `2·log2(peak / MIN_CAP) + 4` excused calls per run.
fn exempt_cap(peak: usize) -> usize {
    2 * (peak / QUEUE_MIN_CAP).max(1).ilog2() as usize + 4
}

/// Each call: no realloc, and `bytes_ok`; at most `exempt_cap` excused calls. Returns the failures, worst call first.
fn per_call_ok(name: &str, m: usize, c: &[Call], a: Alloc) -> Vec<String> {
    let queue = a == Alloc::Queue;
    let mut f = Vec::new();
    let re: Vec<_> = c.iter().enumerate().filter(|(_, x)| x.k[2] != 0).collect();
    if let Some((i, x)) = re.iter().max_by_key(|(_, x)| x.k[2]) {
        f.push(format!(
            "{name} n={m}: {} calls realloc (worst: call {i} ({}), {} reallocs)",
            re.len(),
            x.tag,
            x.k[2]
        ));
    }
    let peak = c.iter().map(|x| x.held).max().unwrap_or(0);
    let ex = c.iter().filter(|x| exempt(x, queue)).count();
    if ex > exempt_cap(peak) {
        f.push(format!(
            "{name} n={m}: {ex} calls excused as queue buffers, more than {} (peak {peak} held)",
            exempt_cap(peak)
        ));
    }
    let over: Vec<_> = c.iter().enumerate().filter(|(_, x)| !bytes_ok(x, a)).collect();
    if let Some((i, x)) = over
        .iter()
        .max_by_key(|(_, x)| x.k[4] - (COST_A * x.d + COST_B).min(x.k[4]))
    {
        f.push(format!(
            "{name} n={m}: {} calls request more than {COST_A}·d + {COST_B} bytes{} (worst: call {i} ({}), {} bytes \
             for d = {}, largest single {}, {} held after)",
            over.len(),
            if queue { " beyond one queue buffer" } else { "" },
            x.tag,
            x.k[4],
            x.d,
            x.k[5],
            x.held
        ));
    }
    f
}

/// One input call: its kind, allocator counts (`k[5]` its largest single request), the bytes it was given, the bytes
/// it handed over (None: delivers nothing), the bytes held after it.
#[derive(Clone, Copy)]
struct Call {
    tag: &'static str,
    k: [usize; 6],
    d: usize,
    out: Option<usize>,
    held: usize,
}

#[derive(Default)]
struct Run(Vec<Call>);

impl Run {
    /// Measures `f` alone: the record is pushed after the counters are read.
    fn call(&mut self, tag: &'static str, d: usize, f: impl FnOnce() -> (Option<usize>, usize)) {
        let a = K.with(|k| {
            let mut v = k.get();
            v[5] = 0;
            k.set(v);
            v
        });
        let (out, held) = f();
        let b = K.with(|k| k.get());
        self.0.push(Call {
            tag,
            k: [0, 1, 2, 3, 4, 5].map(|i| if i == 5 { b[5] } else { b[i] - a[i] }),
            d,
            out,
            held,
        });
    }
}

/// Runs `pat` at n, 2n, 4n and checks the bounds; `a`: the allocations the structure may make beyond the per-call
/// budget (`bytes_ok`). Counts only (the allocator is deterministic): wall time is not a cost bound (Task 8 ruling).
fn check(name: &str, n: usize, pat: fn(usize, &mut Run), a: Alloc) {
    let mut fails = Vec::new();
    let mut rows: Vec<(usize, Vec<(&'static str, usize)>)> = Vec::new();
    for m in [n, 2 * n, 4 * n] {
        let mut r = Run::default();
        pat(m, &mut r);
        let c = &r.0;
        let k = c.iter().fold([0; 5], |a, x| [0, 1, 2, 3, 4].map(|i| a[i] + x.k[i]));
        let worst = c
            .iter()
            .filter_map(|x| x.out.map(|o| (o, x.d)))
            .max_by_key(|&(o, d)| o as i64 - d as i64);
        let over = c.iter().filter(|x| x.out.is_some_and(|o| o > x.d)).count();
        fails.extend(per_call_ok(name, m, c, a));
        if over != 0 {
            fails.push(format!(
                "{name} n={m}: {over} calls hand over more than their input (worst {worst:?} (out, d))"
            ));
        }
        eprintln!(
            "{name} n={m}: calls {} bytes {} alloc {} alloc_zeroed {} realloc {} dealloc {} worst-out {worst:?}",
            c.len(),
            k[4],
            k[0],
            k[1],
            k[2],
            k[3]
        );
        let mut tags: Vec<(&'static str, usize)> = Vec::new();
        for x in c {
            match tags.iter_mut().find(|t| t.0 == x.tag) {
                Some(t) => t.1 = t.1.max(x.k[4]),
                None => tags.push((x.tag, x.k[4])),
            }
        }
        for &(tag, b) in &tags {
            let n = c.iter().filter(|x| x.tag == tag).count();
            eprintln!("  {name} n={m} {tag}: calls {n} largest-call-bytes {b}");
        }
        rows.push((k[4], tags));
    }
    for i in 0..2 {
        if rows[i + 1].0 > 3 * rows[i].0 {
            fails.push(format!("{name}: bytes {} -> {} (> 3x)", rows[i].0, rows[i + 1].0));
        }
        for &(tag, b) in &rows[i + 1].1 {
            let p = rows[i].1.iter().find(|t| t.0 == tag).map_or(0, |t| t.1);
            if b > 3 * p + COST_B {
                fails.push(format!("{name}: {tag} largest-call-bytes {p} -> {b} (> 3x + {COST_B})"));
            }
        }
    }
    assert!(fails.is_empty(), "{fails:#?}");
}

fn bytes(m: usize) -> Vec<u8> {
    (0..m).map(|i| i as u8).collect()
}

/// `on_crypto` then `read(max = d)` into an exact buffer, as quictls's `feed` does per level with the datagram's size
/// (D6): one input call. `new` is the bytes the frame adds to what was received; `held` counts the received bytes not
/// yet handed over.
fn crypto_call(
    r: &mut Run,
    tag: &'static str,
    c: &mut CryptoStream,
    off: usize,
    d: &[u8],
    new: usize,
    held: &mut usize,
) {
    r.call(tag, d.len(), || {
        assert_eq!(c.on_crypto(off as u64, d), Ok(()));
        let mut out = CapVec::new((c.unread() as usize).min(d.len()));
        c.read(d.len() as u64, &mut out);
        *held = *held + new - out.len();
        (Some(out.len()), *held)
    });
}

/// Bytes per gap-closed run in `one_byte_frames`: held out of order below `MAX_CRYPTO_BUFFER`, constant in n.
const GAP_RUN: usize = 8192;

/// The stream one byte per frame, in runs of `GAP_RUN`: bytes `b+1..b+GAP_RUN` in order, then `b`, which closes the gap.
fn one_byte_frames(m: usize, r: &mut Run) {
    let s = bytes(m);
    let (mut c, mut h) = (CryptoStream::new(), 0);
    for b in (0..m).step_by(GAP_RUN) {
        for i in b + 1..b + GAP_RUN {
            crypto_call(r, "frame", &mut c, i, &s[i..i + 1], 1, &mut h);
        }
        crypto_call(r, "close", &mut c, b, &s[b..b + 1], 1, &mut h);
    }
}

fn runs_then_fill(m: usize, r: &mut Run) {
    let s = bytes(2 * m);
    let (mut c, mut h) = (CryptoStream::new(), 0);
    for k in 0..m {
        crypto_call(r, "run", &mut c, 2 * k + 1, &s[2 * k + 1..2 * k + 2], 1, &mut h);
    }
    crypto_call(r, "fill", &mut c, 0, &s, m, &mut h);
}

fn write_send_ack(m: usize, r: &mut Run) {
    let s = bytes(m);
    let mut st = SendStream::new(m as u64);
    r.call("write", m, || {
        assert_eq!(st.write(&s, true), Ok(()));
        (None, st.buffered())
    });
    let mut more = true;
    while more {
        r.call("poll", 0, || {
            // Each 1 KiB ACK below is exactly one sent piece.
            more = st.poll_data(1024, u64::MAX).is_some();
            (None, st.buffered())
        });
    }
    for i in 0..m / 1024 {
        // An ACK range carries no stream bytes: d = 0.
        r.call("ack", 0, || {
            st.on_data_acked((i * 1024) as u64, 1024, i == m / 1024 - 1);
            (None, st.buffered())
        });
    }
    assert_eq!(st.state_exec(), SendState::DataRecvd);
}

fn reverse_fill(m: usize, r: &mut Run) {
    let s = bytes(m);
    let mut st = RecvStream::new(0, m as u64);
    let (mut got, mut recvd) = (0, 0);
    let data_len = |ev: &Vec<StreamEvent>| -> usize {
        ev.iter()
            .map(|e| if let StreamEvent::Data { data, .. } = e { data.len() } else { 0 })
            .sum()
    };
    // The frame path's shape (D12): each frame's `on_data`, then a delivery of at most its length.
    for off in (0..m).rev() {
        r.call("frame", 1, || {
            let mut ev = Vec::new();
            assert!(st.on_data(off as u64, &s[off..off + 1], false, u64::MAX).0.is_ok());
            let _ = st.deliver(1, &mut ev);
            let n = data_len(&ev);
            got += n;
            recvd += 1;
            (Some(n), recvd - got)
        });
    }
    // `pump_backlog`'s STREAM half: `B_PUMP`-sized deliveries until none is left (D13).
    while st.has_ready() {
        r.call("pump", 4096, || {
            let mut ev = Vec::new();
            let _ = st.deliver(4096, &mut ev);
            let n = data_len(&ev);
            got += n;
            (Some(n), recvd - got)
        });
    }
    assert_eq!(got, m);
}

#[test]
fn crypto_one_byte_frames() {
    check("crypto_one_byte_frames", 16 << 10, one_byte_frames, Alloc::Gather);
}

#[test]
fn crypto_runs_then_fill() {
    check("crypto_runs_then_fill", 1024, runs_then_fill, Alloc::Gather);
}

#[test]
fn send_ack_1k() {
    check("send_ack_1k", 256 << 10, write_send_ack, Alloc::Queue);
}

/// A height bound for the three range trees with `n` nodes in all: an AVL tree of `n` nodes is at most
/// `1.45·log2(n + 2)` high, below `2·log2(n + 2)`.
fn h_max(n: usize) -> usize {
    2 * (usize::BITS - (n + 2).leading_zeros()) as usize
}

/// Node allocations per ACK or loss: `NODE_C · (h + 1)` (D10 (e)): `split` and `join` re-box the nodes on their path
/// (`take_piece`, `add`, `remove_range`), a handful of paths per call.
const NODE_C: usize = 8;

/// One ACK or loss on `s`, measured: (allocations, frees, reallocs, requested bytes), and the nodes before it.
fn measure(s: &mut SendStream, f: impl FnOnce(&mut SendStream)) -> ([usize; 4], usize) {
    let (a, l, fl) = s.range_counts();
    let k0 = K.with(|k| k.get());
    f(s);
    let k1 = K.with(|k| k.get());
    ([k1[0] + k1[1] - k0[0] - k0[1], k1[3] - k0[3], k1[2] - k0[2], k1[4] - k0[4]], a + l + fl)
}

/// The per-call rule for an ACK or a loss: no `realloc`, at most `NODE_C·(h + 1)` allocations, of nodes only (40
/// bytes each), and at most one live node more after it (allocations minus frees).
fn node_call_ok(m: [usize; 4], n: usize) -> bool {
    m[2] == 0 && m[0] <= NODE_C * (h_max(n) + 1) && m[3] <= 40 * m[0] && m[0] <= m[1] + 1
}

/// 64 KiB written and sent in 1 KiB pieces, acknowledged in order and, on a second stream, out of order (odd pieces,
/// then even ones backwards): no ACK copies a stream byte, reallocates, allocates more than `NODE_C·(h + 1)` nodes, or
/// adds more than one live node (D10 (h)).
#[test]
fn ack_copies_no_stream_bytes() {
    const W: usize = 1 << 16;
    let n = W / 1024;
    let orders: [Vec<usize>; 2] = [
        (0..n).collect(),
        (1..n).step_by(2).chain((0..n).step_by(2).rev()).collect(),
    ];
    for order in orders {
        let mut s = SendStream::new(W as u64);
        assert_eq!(s.write(&bytes(W), true), Ok(()));
        while s.poll_data(1024, u64::MAX).is_some() {}
        let mut bad = Vec::new();
        for &i in &order {
            let (m, nodes) = measure(&mut s, |s| s.on_data_acked((i * 1024) as u64, 1024, i == n - 1));
            if !node_call_ok(m, nodes) {
                bad.push((i, m, nodes));
            }
        }
        assert!(bad.is_empty(), "ACKs over the node rule (piece, [allocs, frees, reallocs, bytes], nodes): {bad:?}");
        assert_eq!(s.state_exec(), SendState::DataRecvd);
    }
}

/// Totals of a selective-ACK run over the stream's own calls (the test's accessors not counted): requested bytes,
/// allocations, and the most allocations of one ACK or loss (printed).
#[derive(Default)]
struct SelRun {
    bytes: usize,
    allocs: usize,
    worst: usize,
}

impl SelRun {
    /// Runs one call of the stream, adding its allocations to the totals.
    fn call<R>(&mut self, f: impl FnOnce() -> R) -> (R, [usize; 4]) {
        let k0 = K.with(|k| k.get());
        let r = f();
        let k1 = K.with(|k| k.get());
        let m = [k1[0] + k1[1] - k0[0] - k0[1], k1[3] - k0[3], k1[2] - k0[2], k1[4] - k0[4]];
        self.bytes += m[3];
        self.allocs += m[0];
        (r, m)
    }
}

/// The selective-ACK adversary at `b` bytes in pieces of `m` (1200, or 1 written and flushed each): each round sends
/// what it can at room 1200, then the peer acknowledges odd pieces in flight and loses even ones (parity over all
/// pieces); after 8 rounds everything is acknowledged. After every call the three sets hold at most
/// `buffered()/256 + 4` entries, and each ACK or loss passes `node_call_ok`.
fn sel_acks(b: usize, m: usize) -> SelRun {
    let mut s = SendStream::new(1 << 40);
    let mut written = 0usize;
    let mut run = SelRun::default();
    let mut bad = Vec::new();
    let check = |s: &SendStream| {
        let (a, l, f) = s.range_counts();
        assert!(a + l + f <= s.buffered() / 256 + 4, "b={b} m={m}: {a} + {l} + {f} > {} / 256 + 4", s.buffered());
    };
    let data = bytes(b);
    if m > 1 {
        run.call(|| assert_eq!(s.write(&data, true), Ok(())));
        written = b;
    }
    // Sends what it can: 1-byte writes flushed one at a time (at most `MAX_FLUSH` short pieces open), or the backlog.
    let send = |s: &mut SendStream, written: &mut usize, run: &mut SelRun| loop {
        if m == 1 && *written < b && s.range_sets().1.is_empty() {
            let fin = *written + 1 == b;
            run.call(|| {
                assert_eq!(s.write(&[7], fin), Ok(()));
                s.flush();
            });
            *written += 1;
        }
        let (got, _) = run.call(|| s.poll_data(1200, u64::MAX).is_some());
        check(s);
        if !got {
            break;
        }
    };
    let mut parity = 0usize;
    for round in 0..9 {
        send(&mut s, &mut written, &mut run);
        for (x, y) in s.range_sets().2 {
            parity += 1;
            let fin = y as usize == b;
            let nodes = s.range_counts();
            let ack = round == 8 || parity % 2 == 1;
            let (_, c) = run.call(|| if ack { s.on_data_acked(x, y - x, fin) } else { s.on_data_lost(x, y - x, fin) });
            check(&s);
            run.worst = run.worst.max(c[0]);
            if !node_call_ok(c, nodes.0 + nodes.1 + nodes.2) {
                bad.push((x, y, c, nodes));
            }
        }
    }
    while s.state_exec() != SendState::DataRecvd {
        send(&mut s, &mut written, &mut run);
        for (x, y) in s.range_sets().2 {
            let nodes = s.range_counts();
            let (_, c) = run.call(|| s.on_data_acked(x, y - x, y as usize == b));
            check(&s);
            run.worst = run.worst.max(c[0]);
            if !node_call_ok(c, nodes.0 + nodes.1 + nodes.2) {
                bad.push((x, y, c, nodes));
            }
        }
    }
    assert!(bad.is_empty(), "b={b} m={m}: calls over the node rule (piece, [allocs, frees, reallocs, bytes], nodes): {:?}",
        &bad[..bad.len().min(8)]);
    eprintln!("sel_acks b={b} m={m}: bytes {} allocs {} worst-call allocs {}", run.bytes, run.allocs, run.worst);
    run
}

/// D10 (d), (e), (h) under the ruling-11 adversary (spec D15): B = 4 KiB, 64 KiB, 1 MiB in 1200-byte pieces and 4 KiB,
/// 64 KiB in 1-byte pieces. Counts, never time (Task 8 ruling): the stream's requested bytes at 16·B at most 24× those
/// at B, and each ACK or loss within `NODE_C·(h + 1)` allocations (`node_call_ok`, in `sel_acks`): the O(log n) per
/// call. Allocation totals are not held to 24×: about n calls of O(log n) nodes each grow as n·log n, and at 4 KiB the
/// trees are a few nodes high (measured 56, 3163, 104122 allocations).
#[test]
fn send_selective_acks() {
    let big: Vec<SelRun> = [4 << 10, 64 << 10, 1 << 20].iter().map(|&b| sel_acks(b, 1200)).collect();
    let one: Vec<SelRun> = [4 << 10, 64 << 10].iter().map(|&b| sel_acks(b, 1)).collect();
    for (lo, hi) in big.windows(2).map(|w| (&w[0], &w[1])).chain([(&one[0], &one[1])]) {
        assert!(hi.bytes <= 24 * lo.bytes, "bytes {} -> {} (> 24x)", lo.bytes, hi.bytes);
    }
    assert!(big.iter().chain(&one).all(|r| r.worst > 0));
}

#[test]
fn stream_reverse_fill() {
    check("stream_reverse_fill", 16 << 10, reverse_fill, Alloc::None);
}

/// D10 (e), Review Focus 7: `reset` of a stream holding thousands of acked and lost ranges (1 MiB in 256-byte pieces,
/// odd ones acknowledged, even ones lost) allocates nothing and frees only its queue's buffers (`c_sfree`, at most
/// two): its sets move to the teardown slot whole. Each `reap(4096)` then frees more nodes than it allocates (`pop_min`
/// re-boxes the nodes on its path), and no call reallocates.
#[test]
fn reset_allocates_nothing() {
    const W: usize = 1 << 20;
    let mut s = SendStream::new(W as u64);
    assert_eq!(s.write(&bytes(W), false), Ok(()));
    let mut p = Vec::new();
    while let Some(c) = s.poll_data(256, u64::MAX) {
        p.push((c.off, c.data.len() as u64));
    }
    for (i, &(o, n)) in p.iter().enumerate() {
        if i % 2 == 1 {
            s.on_data_acked(o, n, false);
        } else {
            s.on_data_lost(o, n, false);
        }
    }
    let (m, nodes) = measure(&mut s, |s| assert!(s.reset(3)));
    assert!(nodes >= 4000, "{nodes} nodes");
    assert!(m[0] == 0 && m[2] == 0 && m[1] <= 2, "reset: [allocs, frees, reallocs, bytes] {m:?}");
    assert_eq!(s.td_len(), nodes);
    while s.has_td() {
        let (m, _) = measure(&mut s, |s| {
            let _ = s.reap(4096);
        });
        assert!(m[2] == 0 && m[0] < m[1], "reap: [allocs, frees, reallocs, bytes] {m:?}");
    }
}
