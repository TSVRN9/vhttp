//! 9b2 Task 1: the per-call cost of quic's input-path byte buffers (spec "The cost today", D15). Each pattern runs at
//! n, 2n and 4n under a per-thread counting allocator; every input call is measured on its own. The bounds: requested
//! bytes at most 3x per doubling, total time at most 8x (+ 20 ms) from n to 4n, no `realloc`, a delivering call hands
//! over at most its own input's bytes, and the slowest call at 4n at most 4x the slowest at n (+ 1 ms). Per call
//! (the allocator is deterministic): no `realloc`, and requested bytes at most `COST_A·d + COST_B` (`per_call_ok`).
use quic::crypto_stream::CryptoStream;
use quic::recv_stream::{RecvStream, StreamEvent};
use quic::send_stream::{SendState, SendStream};
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::time::{Duration, Instant};

struct Counting;

// alloc, alloc_zeroed, realloc, dealloc calls; requested bytes (alloc sizes and realloc new sizes)
thread_local! {
    static K: Cell<[usize; 5]> = const { Cell::new([0; 5]) };
}

fn bump(i: usize, bytes: usize) {
    let _ = K.try_with(|k| {
        let mut v = k.get();
        v[i] += 1;
        v[4] += bytes;
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

/// Each call: no realloc, and at most `COST_A·d + COST_B` requested bytes. Returns the failures, worst call first.
fn per_call_ok(name: &str, m: usize, c: &[Call]) -> Vec<String> {
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
    let over: Vec<_> = c
        .iter()
        .enumerate()
        .filter(|(_, x)| x.k[4] > COST_A * x.d + COST_B)
        .collect();
    if let Some((i, x)) = over.iter().max_by_key(|(_, x)| x.k[4] - (COST_A * x.d + COST_B)) {
        f.push(format!(
            "{name} n={m}: {} calls request more than {COST_A}·d + {COST_B} bytes (worst: call {i} ({}), {} bytes for d = {})",
            over.len(),
            x.tag,
            x.k[4],
            x.d
        ));
    }
    f
}

/// One input call: its kind, allocator counts, wall time, the bytes it was given, the bytes it handed over (None:
/// delivers nothing).
#[derive(Clone, Copy)]
struct Call {
    tag: &'static str,
    k: [usize; 5],
    t: Duration,
    d: usize,
    out: Option<usize>,
}

#[derive(Default)]
struct Run(Vec<Call>);

impl Run {
    /// Measures `f` alone: the record is pushed after the counters are read.
    fn call(&mut self, tag: &'static str, d: usize, f: impl FnOnce() -> Option<usize>) {
        let a = K.with(|k| k.get());
        let t = Instant::now();
        let out = f();
        let t = t.elapsed();
        let b = K.with(|k| k.get());
        self.0.push(Call {
            tag,
            k: [0, 1, 2, 3, 4].map(|i| b[i] - a[i]),
            t,
            d,
            out,
        });
    }
}

/// Runs `pat` at n, 2n, 4n (three times each; times are the fastest run's) and checks the bounds. With `fill`, the
/// last call is the gap fill and must take at most 8x the slowest other call + 1 ms.
fn check(name: &str, n: usize, pat: fn(usize, &mut Run), fill: bool) {
    let mut fails = Vec::new();
    let mut rows = Vec::new();
    for m in [n, 2 * n, 4 * n] {
        let runs: Vec<Run> = (0..3)
            .map(|_| {
                let mut r = Run::default();
                pat(m, &mut r);
                r
            })
            .collect();
        let c = &runs[0].0;
        let k = c.iter().fold([0; 5], |a, x| [0, 1, 2, 3, 4].map(|i| a[i] + x.k[i]));
        let total = runs
            .iter()
            .map(|r| r.0.iter().map(|x| x.t).sum::<Duration>())
            .min()
            .unwrap();
        let slow = runs
            .iter()
            .map(|r| r.0.iter().map(|x| x.t).max().unwrap())
            .min()
            .unwrap();
        let big = c.iter().map(|x| x.k[4]).max().unwrap();
        let worst = c
            .iter()
            .filter_map(|x| x.out.map(|o| (o, x.d)))
            .max_by_key(|&(o, d)| o as i64 - d as i64);
        let over = c.iter().filter(|x| x.out.is_some_and(|o| o > x.d)).count();
        fails.extend(per_call_ok(name, m, c));
        if over != 0 {
            fails.push(format!(
                "{name} n={m}: {over} calls hand over more than their input (worst {worst:?} (out, d))"
            ));
        }
        let (tf, tmax) = if fill {
            let tf = runs.iter().map(|r| r.0.last().unwrap().t).min().unwrap();
            let l = c.len() - 1;
            let tmax = runs
                .iter()
                .map(|r| r.0[..l].iter().map(|x| x.t).max().unwrap())
                .min()
                .unwrap();
            if tf > 8 * tmax + Duration::from_millis(1) {
                fails.push(format!("{name} n={m}: fill call {tf:?} > 8 x {tmax:?} + 1 ms"));
            }
            (Some(tf), Some(tmax))
        } else {
            (None, None)
        };
        eprintln!(
            "{name} n={m}: calls {} bytes {} alloc {} alloc_zeroed {} realloc {} dealloc {} time {total:?} \
             slowest {slow:?} largest-call-bytes {big} worst-out {worst:?} fill {tf:?} other-max {tmax:?}",
            c.len(),
            k[4],
            k[0],
            k[1],
            k[2],
            k[3]
        );
        let mut tags: Vec<&str> = Vec::new();
        for x in c {
            if !tags.contains(&x.tag) {
                tags.push(x.tag);
            }
        }
        for tag in tags {
            let of = |r: &Run| r.0.iter().filter(|x| x.tag == tag).map(|x| x.t).max().unwrap();
            let b = c.iter().filter(|x| x.tag == tag).map(|x| x.k[4]).max().unwrap();
            let n = c.iter().filter(|x| x.tag == tag).count();
            let t = runs.iter().map(of).min().unwrap();
            eprintln!("  {name} n={m} {tag}: calls {n} largest-call-bytes {b} slowest {t:?}");
        }
        rows.push((k[4], total, slow));
    }
    for i in 0..2 {
        if rows[i + 1].0 > 3 * rows[i].0 {
            fails.push(format!("{name}: bytes {} -> {} (> 3x)", rows[i].0, rows[i + 1].0));
        }
    }
    if rows[2].1 > 8 * rows[0].1 + Duration::from_millis(20) {
        fails.push(format!(
            "{name}: time {:?} -> {:?} (> 8x + 20 ms)",
            rows[0].1, rows[2].1
        ));
    }
    if rows[2].2 > 4 * rows[0].2 + Duration::from_millis(1) {
        fails.push(format!(
            "{name}: slowest call {:?} -> {:?} (> 4x + 1 ms)",
            rows[0].2, rows[2].2
        ));
    }
    assert!(fails.is_empty(), "{fails:#?}");
}

fn bytes(m: usize) -> Vec<u8> {
    (0..m).map(|i| i as u8).collect()
}

/// `on_crypto` then `read` into a fresh `Vec`, as quictls's `feed` does per level: one input call.
fn crypto_call(r: &mut Run, tag: &'static str, c: &mut CryptoStream, off: usize, d: &[u8]) {
    r.call(tag, d.len(), || {
        assert_eq!(c.on_crypto(off as u64, d), Ok(()));
        let mut out = Vec::new();
        c.read(&mut out);
        Some(out.len())
    });
}

/// Bytes per gap-closed run in `one_byte_frames`: held out of order below `MAX_CRYPTO_BUFFER`, constant in n.
const GAP_RUN: usize = 8192;

/// The stream one byte per frame, in runs of `GAP_RUN`: bytes `b+1..b+GAP_RUN` in order, then `b`, which closes the gap.
fn one_byte_frames(m: usize, r: &mut Run) {
    let s = bytes(m);
    let mut c = CryptoStream::new();
    for b in (0..m).step_by(GAP_RUN) {
        for i in b + 1..b + GAP_RUN {
            crypto_call(r, "frame", &mut c, i, &s[i..i + 1]);
        }
        crypto_call(r, "close", &mut c, b, &s[b..b + 1]);
    }
}

fn runs_then_fill(m: usize, r: &mut Run) {
    let s = bytes(2 * m);
    let mut c = CryptoStream::new();
    for k in 0..m {
        crypto_call(r, "run", &mut c, 2 * k + 1, &s[2 * k + 1..2 * k + 2]);
    }
    crypto_call(r, "fill", &mut c, 0, &s);
}

fn write_send_ack(m: usize, r: &mut Run) {
    let s = bytes(m);
    let mut st = SendStream::new(m as u64);
    r.call("write", m, || {
        assert_eq!(st.write(&s, true), Ok(()));
        None
    });
    let mut more = true;
    while more {
        r.call("poll", 0, || {
            more = st.poll_data(1200, u64::MAX).is_some();
            None
        });
    }
    for i in 0..m / 1024 {
        // An ACK range carries no stream bytes: d = 0.
        r.call("ack", 0, || {
            st.on_data_acked((i * 1024) as u64, 1024, i == m / 1024 - 1);
            None
        });
    }
    assert_eq!(st.state_exec(), SendState::DataRecvd);
}

fn reverse_fill(m: usize, r: &mut Run) {
    let s = bytes(m);
    let mut st = RecvStream::new(0, m as u64);
    let mut got = 0;
    for off in (0..m).rev() {
        r.call("frame", 1, || {
            let mut ev = Vec::new();
            assert!(st
                .on_data(off as u64, &s[off..off + 1], false, u64::MAX, &mut ev)
                .is_ok());
            let n: usize = ev
                .iter()
                .map(|e| {
                    if let StreamEvent::Data { data, .. } = e {
                        data.len()
                    } else {
                        0
                    }
                })
                .sum();
            got += n;
            Some(n)
        });
    }
    assert_eq!(got, m);
}

#[test]
#[ignore = "9b2: fails today, a 1-byte frame closing a gap copies and hands over the whole run (Q4, Q5); un-ignored by Task 6"]
fn crypto_one_byte_frames() {
    check("crypto_one_byte_frames", 16 << 10, one_byte_frames, false);
}

#[test]
#[ignore = "9b2: fails today, the fill's take_front grows buf by realloc (Q5); un-ignored by Task 6"]
fn crypto_runs_then_fill() {
    check("crypto_runs_then_fill", 1024, runs_then_fill, true);
}

#[test]
#[ignore = "9b2: fails today, one ACK's split_off copies up to half the stream (Q7); un-ignored by Task 8"]
fn send_ack_1k() {
    check("send_ack_1k", 256 << 10, write_send_ack, false);
}

#[test]
#[ignore = "9b2: fails today, zero-fill reallocs and eager whole-run delivery (Q1, Q3); un-ignored by Task 10"]
fn stream_reverse_fill() {
    check("stream_reverse_fill", 16 << 10, reverse_fill, false);
}
