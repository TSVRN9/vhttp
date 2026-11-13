//! 9b2 Task 1: the per-call cost of `HsReader` (spec "The cost today" T1, T2; D15). The pattern runs at n, 2n and 4n
//! under a per-thread counting allocator; every call is measured on its own. The bounds: requested bytes at most 3x per
//! doubling, total time at most 8x (+ 20 ms) from n to 4n, no `realloc`, and the slowest call at 4n at most 4x the
//! slowest at n (+ 1 ms). `next_message` hands over a whole message, which stays O(message) until 9b5 (D14), so no call
//! here is held to its input's size.
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::time::{Duration, Instant};
use tls::handshake::HsReader;

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

/// One call's allocator counts and wall time; the record is pushed after the counters are read.
fn call(r: &mut Vec<([usize; 5], Duration)>, f: impl FnOnce()) {
    let a = K.with(|k| k.get());
    let t = Instant::now();
    f();
    let t = t.elapsed();
    let b = K.with(|k| k.get());
    r.push(([0, 1, 2, 3, 4].map(|i| b[i] - a[i]), t));
}

/// One ClientHello-typed message of `m` bytes, header included, pushed one byte per call; `next_message` once it is
/// complete.
fn one_byte_push(m: usize) -> Vec<([usize; 5], Duration)> {
    let body = m - 4;
    let mut s = vec![1u8, (body >> 16) as u8, (body >> 8) as u8, body as u8];
    s.extend((0..body).map(|i| i as u8));
    let mut h = HsReader::new();
    let mut r = Vec::new();
    for i in 0..m {
        call(&mut r, || h.push(&s[i..i + 1]));
    }
    let mut got = None;
    call(&mut r, || got = Some(h.next_message(1)));
    assert!(matches!(got, Some(Ok(Some(ref v))) if v.len() == m));
    assert!(h.is_empty());
    r
}

#[test]
#[ignore = "9b2: fails today, per-byte push grows the reader by realloc (T1); un-ignored by Task 7"]
fn reader_one_byte_push() {
    let mut fails = Vec::new();
    let mut rows = Vec::new();
    for m in [16 << 10, 32 << 10, 64 << 10] {
        let runs: Vec<_> = (0..3).map(|_| one_byte_push(m)).collect();
        let c = &runs[0];
        let k = c.iter().fold([0; 5], |a, x| [0, 1, 2, 3, 4].map(|i| a[i] + x.0[i]));
        let total = runs
            .iter()
            .map(|r| r.iter().map(|x| x.1).sum::<Duration>())
            .min()
            .unwrap();
        let slow = runs.iter().map(|r| r.iter().map(|x| x.1).max().unwrap()).min().unwrap();
        let big = c.iter().map(|x| x.0[4]).max().unwrap();
        if k[2] != 0 {
            fails.push(format!("n={m}: {} reallocs", k[2]));
        }
        eprintln!(
            "reader_one_byte_push n={m}: calls {} bytes {} alloc {} alloc_zeroed {} realloc {} dealloc {} \
             time {total:?} slowest {slow:?} largest-call-bytes {big}",
            c.len(),
            k[4],
            k[0],
            k[1],
            k[2],
            k[3]
        );
        rows.push((k[4], total, slow));
    }
    for i in 0..2 {
        if rows[i + 1].0 > 3 * rows[i].0 {
            fails.push(format!("bytes {} -> {} (> 3x)", rows[i].0, rows[i + 1].0));
        }
    }
    if rows[2].1 > 8 * rows[0].1 + Duration::from_millis(20) {
        fails.push(format!("time {:?} -> {:?} (> 8x + 20 ms)", rows[0].1, rows[2].1));
    }
    if rows[2].2 > 4 * rows[0].2 + Duration::from_millis(1) {
        fails.push(format!("slowest call {:?} -> {:?} (> 4x + 1 ms)", rows[0].2, rows[2].2));
    }
    assert!(fails.is_empty(), "{fails:#?}");
}
