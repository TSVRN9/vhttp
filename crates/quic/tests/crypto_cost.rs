//! 9b1: the CRYPTO reassembly store's cost must grow linearly in the number of frames.
use quic::crypto_stream::CryptoStream;
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::time::{Duration, Instant};

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


type Frames = Vec<(u64, Vec<u8>)>;

fn cost(frames: &Frames) -> (usize, Duration) {
    let mut c = CryptoStream::new();
    let before = allocated();
    let t = Instant::now();
    for (o, d) in frames {
        assert_eq!(c.on_crypto(*o, d), Ok(()));
    }
    (allocated() - before, t.elapsed())
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

/// Bytes allocated and time must grow linearly in the scale (n, 2n, 4n).
#[test]
#[ignore = "9b1: quadratic on the Vec store; un-ignored by Task 7"]
fn crypto_ooo_cost_linear() {
    let patterns: [(&str, fn(u64) -> Frames); 4] = [
        ("descending", descending),
        ("runs then fill", runs_then_fill),
        ("grow-down", grow_down),
        ("grow-down-full", grow_down_full),
    ];
    let mut fails = Vec::new();
    for (name, f) in patterns {
        let m: Vec<_> = [1024, 2048, 4096].iter().map(|&n| cost(&f(n))).collect();
        eprintln!("{name}: {:?}", m);
        if m[1].0 > 3 * m[0].0 || m[2].0 > 3 * m[1].0 {
            fails.push(format!("{name}: bytes {} -> {} -> {}", m[0].0, m[1].0, m[2].0));
        }
        if m[2].1 > 8 * m[0].1 + Duration::from_millis(20) {
            fails.push(format!("{name}: time {:?} -> {:?}", m[0].1, m[2].1));
        }
    }
    assert!(fails.is_empty(), "{fails:#?}");
}
