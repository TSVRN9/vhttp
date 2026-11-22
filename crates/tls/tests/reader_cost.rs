//! 9b2 Task 1: the per-call cost of `HsReader` (spec "The cost today" T1, T2; D15). The pattern runs at n, 2n and 4n
//! under a per-thread counting allocator; every call is measured on its own. The bounds count, never time (9b2 Task 8
//! ruling): requested bytes at most 3x per doubling, per call kind (push, next_message) the largest single call's
//! requested bytes at most 3x per doubling (+ `COST_B`), and no `realloc`. Per call (the allocator is deterministic):
//! no `realloc`, and requested bytes at most `COST_A·d + COST_B`,
//! `d` the bytes the call was given; `next_message` is given none and hands over a whole message, one copy of the
//! completed unit that stays O(message) until 9b5 (D14), so it is held to `COST_A·message + COST_B`.
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use tls::handshake::HsReader;

struct Counting;

// alloc, alloc_zeroed, realloc, dealloc calls; requested bytes (alloc sizes and realloc new sizes); the largest single
// request since `call` reset it
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
/// for a take (D4), so `COST_A = 8` per byte, and `COST_B = 4096` covers the constant terms.
const COST_A: usize = 8;
const COST_B: usize = 4096;
/// byteq's `MIN_CAP` (D4); named apart so the RFC-quantity gate, which reads constants by name, never sees it.
const QUEUE_MIN_CAP: usize = 64;

/// (allocator counts with `.0[5]` the largest single request, byte allowance `d`, bytes held after)
type Rec = ([usize; 6], usize, usize);

/// Requested capacity is memory, not work: an uninitialized `with_capacity` is one allocator call, and D4 bounds the copies
/// into it at 3 per byte pushed. So one allocation of a push may exceed the budget if it can be a queue buffer: the call
/// was given bytes (D4 allocates only in `push_slice` with `d > 0`) and the allocation is at most `3·(bytes held after the
/// call) + MIN_CAP` (D4's memory bound); the rest of the call stays within the budget. The allocator sees no copy into
/// that buffer: the work bound on it rests on D15's proved cost (`push_slice` at most `7d + 4`), not on this test.
/// `exempt_cap` bounds how many calls a run may excuse so.
fn bytes_ok(x: &Rec, push: bool) -> bool {
    x.0[4] <= COST_A * x.1 + COST_B || exempt(x, push)
}

/// The call passes only by its queue-buffer allowance.
fn exempt(x: &Rec, push: bool) -> bool {
    let budget = COST_A * x.1 + COST_B;
    push && x.0[4] > budget && x.0[4] - x.0[5] <= budget && x.0[5] <= 3 * x.2 + QUEUE_MIN_CAP
}

/// A queue allocates a new buffer when its length reaches half the old one's capacity (D4), at most twice per doubling
/// of its peak from `MIN_CAP`: `2·log2(peak / MIN_CAP) + 4` excused calls per run.
fn exempt_cap(peak: usize) -> usize {
    2 * (peak / QUEUE_MIN_CAP).max(1).ilog2() as usize + 4
}

/// One call's allocator counts, byte allowance `d` and the bytes `f` reports held after it; the record is pushed after
/// the counters are read.
fn call(r: &mut Vec<Rec>, d: usize, f: impl FnOnce() -> usize) {
    let a = K.with(|k| {
        let mut v = k.get();
        v[5] = 0;
        k.set(v);
        v
    });
    let held = f();
    let b = K.with(|k| k.get());
    r.push(([0, 1, 2, 3, 4, 5].map(|i| if i == 5 { b[5] } else { b[i] - a[i] }), d, held));
}

/// One ClientHello-typed message of `m` bytes, header included, pushed one byte per call; `next_message` once it is
/// complete.
fn one_byte_push(m: usize) -> Vec<Rec> {
    let body = m - 4;
    let mut s = vec![1u8, (body >> 16) as u8, (body >> 8) as u8, body as u8];
    s.extend((0..body).map(|i| i as u8));
    let mut h = HsReader::new();
    let mut r = Vec::new();
    for i in 0..m {
        call(&mut r, 1, || {
            h.push(&s[i..i + 1]);
            i + 1
        });
    }
    let mut got = None;
    call(&mut r, m, || {
        got = Some(h.next_message(1));
        0
    });
    assert!(matches!(got, Some(Ok(Some(ref v))) if v.len() == m));
    assert!(h.is_empty());
    r
}

#[test]
fn reader_one_byte_push() {
    let mut fails = Vec::new();
    let mut rows = Vec::new();
    for m in [16 << 10, 32 << 10, 64 << 10] {
        let c = &one_byte_push(m);
        let k = c.iter().fold([0; 5], |a, x| [0, 1, 2, 3, 4].map(|i| a[i] + x.0[i]));
        let big = c.iter().map(|x| x.0[4]).max().unwrap();
        let re: Vec<_> = c.iter().enumerate().filter(|(_, x)| x.0[2] != 0).collect();
        if let Some((i, x)) = re.iter().max_by_key(|(_, x)| x.0[2]) {
            fails.push(format!(
                "n={m}: {} calls realloc (worst: call {i}, {} reallocs)",
                re.len(),
                x.0[2]
            ));
        }
        let peak = c.iter().map(|x| x.2).max().unwrap_or(0);
        let ex = c
            .iter()
            .enumerate()
            .filter(|(i, x)| exempt(x, *i + 1 < c.len()))
            .count();
        if ex > exempt_cap(peak) {
            fails.push(format!(
                "n={m}: {ex} calls excused as queue buffers, more than {} (peak {peak} held)",
                exempt_cap(peak)
            ));
        }
        let over: Vec<_> = c
            .iter()
            .enumerate()
            .filter(|(i, x)| !bytes_ok(x, *i + 1 < c.len()))
            .collect();
        if let Some((i, x)) = over
            .iter()
            .max_by_key(|(_, x)| x.0[4] - (COST_A * x.1 + COST_B).min(x.0[4]))
        {
            fails.push(format!(
                "n={m}: {} calls request more than {COST_A}·d + {COST_B} bytes beyond one queue buffer (worst: call {i}, \
                 {} bytes for d = {}, largest single {}, {} held after)",
                over.len(),
                x.0[4],
                x.1,
                x.0[5],
                x.2
            ));
        }
        eprintln!(
            "reader_one_byte_push n={m}: calls {} bytes {} alloc {} alloc_zeroed {} realloc {} dealloc {} \
             largest-call-bytes {big}",
            c.len(),
            k[4],
            k[0],
            k[1],
            k[2],
            k[3]
        );
        // Per call kind: the pushes, then the one `next_message`.
        let (push, next) = c.split_at(c.len() - 1);
        let kinds = [push.iter().map(|x| x.0[4]).max().unwrap(), next[0].0[4]];
        rows.push((k[4], kinds));
    }
    for i in 0..2 {
        if rows[i + 1].0 > 3 * rows[i].0 {
            fails.push(format!("bytes {} -> {} (> 3x)", rows[i].0, rows[i + 1].0));
        }
    }
    for i in 0..2 {
        for (k, kind) in ["push", "next_message"].iter().enumerate() {
            let (p, b) = (rows[i].1[k], rows[i + 1].1[k]);
            if b > 3 * p + COST_B {
                fails.push(format!("{kind} largest-call-bytes {p} -> {b} (> 3x + {COST_B})"));
            }
        }
    }
    assert!(fails.is_empty(), "{fails:#?}");
}

/// One ClientHello-typed message of `m` bytes, header included, its body bytes starting at `seed`.
fn msg(m: usize, seed: u8) -> Vec<u8> {
    let body = m - 4;
    let mut s = vec![1u8, (body >> 16) as u8, (body >> 8) as u8, body as u8];
    s.extend((0..body).map(|i| (i as u8).wrapping_add(seed)));
    s
}

/// D8 (T2): three complete 1000-byte messages and 4 bytes of a fourth in one push; each `next_message` makes exactly one
/// allocation, of its message's `4 + len` bytes (the tail is never copied), and the bytes left are the fourth's.
#[test]
fn reader_never_copies_tail() {
    let ms: Vec<Vec<u8>> = (0..4).map(|k| msg(1000, k as u8)).collect();
    let mut first = [&ms[0][..], &ms[1][..], &ms[2][..]].concat();
    first.extend_from_slice(&ms[3][..4]);
    let mut h = HsReader::new();
    h.push(&first);
    for m in &ms[..3] {
        let mut got = None;
        let mut r = Vec::new();
        call(&mut r, 0, || {
            got = Some(h.next_message(1));
            0
        });
        let k = r[0].0;
        assert_eq!((k[0], k[1], k[2], k[4]), (1, 0, 0, 1000), "allocs, zeroed, reallocs, bytes: {k:?}");
        assert_eq!(got, Some(Ok(Some(m.clone()))));
    }
    assert_eq!(h.next_message(1), Ok(None));
    h.push(&ms[3][4..]);
    assert_eq!(h.next_message(1), Ok(Some(ms[3].clone())));
    assert!(h.is_empty());
}
