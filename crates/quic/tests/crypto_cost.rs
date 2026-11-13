//! 9b1: the CRYPTO reassembly store's cost must grow linearly in the number of frames.
use quic::crypto_stream::CryptoStream;
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::time::{Duration, Instant};

struct Counting;

thread_local! {
    static BYTES: Cell<usize> = const { Cell::new(0) };
    static REALLOCS: Cell<usize> = const { Cell::new(0) };
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
        let _ = REALLOCS.try_with(|r| r.set(r.get() + 1));
        System.realloc(p, l, n)
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        System.dealloc(p, l)
    }
}

#[global_allocator]
static ALLOC: Counting = Counting;

fn allocated() -> (usize, usize) {
    (BYTES.with(|b| b.get()), REALLOCS.with(|r| r.get()))
}

type Frames = Vec<(u64, Vec<u8>)>;

/// Bytes allocated, `realloc` calls and wall time for the frames.
fn cost(frames: &Frames) -> (usize, usize, Duration) {
    let mut c = CryptoStream::new();
    let (b0, r0) = allocated();
    let t = Instant::now();
    for (o, d) in frames {
        assert_eq!(c.on_crypto(*o, d), Ok(()));
    }
    let took = t.elapsed();
    let (b1, r1) = allocated();
    (b1 - b0, r1 - r0, took)
}

fn descending(n: u64) -> Frames {
    (0..n).rev().map(|k| (2 + 2 * k, vec![1])).collect()
}
fn runs_then_fill(n: u64) -> Frames {
    let mut v: Frames = (0..n).map(|k| (2 + 2 * k, vec![1])).collect();
    v.extend((0..n - 1).map(|k| (3 + 2 * k, vec![1])));
    v
}
fn grow_down(n: u64) -> Frames {
    (1..4 * n).rev().map(|o| (o, vec![1])).collect()
}
fn grow_down_full(n: u64) -> Frames {
    (1..4 * n).rev().map(|o| (o, vec![1; (4 * n - o) as usize])).collect()
}

/// The target store costs O(log n + d) per frame, and grow-down-full's input is itself quadratic,
/// so the bounds are per unit of input w = frames + input bytes, not absolute.
fn w(f: &Frames) -> u128 {
    f.len() as u128 + f.iter().map(|(_, d)| d.len() as u128).sum::<u128>()
}

/// No pattern fills from offset 0, so CryptoStream's in-order buffer stays empty and every `realloc` would be a
/// `Frags` chunk grown past its `with_capacity` (spec "The bound": none is).
#[test]
fn crypto_ooo_cost_linear() {
    let patterns: [(&str, fn(u64) -> Frames); 4] = [
        ("descending", descending),
        ("runs then fill", runs_then_fill),
        ("grow-down", grow_down),
        ("grow-down-full", grow_down_full),
    ];
    let mut fails = Vec::new();
    for (name, f) in patterns {
        let m: Vec<_> = [1024, 2048, 4096]
            .iter()
            .map(|&n| {
                let fr = f(n);
                let (b, r, t) = cost(&fr);
                if r != 0 {
                    fails.push(format!("{name} n={n}: {r} reallocs"));
                }
                (b as u128, t, w(&fr))
            })
            .collect();
        eprintln!("{name}: {:?}", m);
        for i in 0..2 {
            let (b0, _, w0) = m[i];
            let (b1, _, w1) = m[i + 1];
            if b1 * w0 > 3 * b0 * w1 / 2 {
                fails.push(format!("{name}: bytes {b0} -> {b1} (w {w0} -> {w1})"));
            }
        }
        let (_, t0, w0) = m[0];
        let (_, t2, w2) = m[2];
        if t2.as_nanos() > 2 * t0.as_nanos() * w2 / w0 + 20_000_000 {
            fails.push(format!("{name}: time {t0:?} -> {t2:?} (w {w0} -> {w2})"));
        }
    }
    assert!(fails.is_empty(), "{fails:#?}");
}
