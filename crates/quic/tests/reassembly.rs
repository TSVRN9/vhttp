use quic::reassembly::*;

/// Requested bytes, per thread: the cost tests below count, never time (9b2 Task 8 ruling).
struct Counting;

thread_local! {
    static BYTES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

unsafe impl std::alloc::GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: std::alloc::Layout) -> *mut u8 {
        let _ = BYTES.try_with(|b| b.set(b.get() + l.size()));
        std::alloc::System.alloc(l)
    }
    unsafe fn realloc(&self, p: *mut u8, l: std::alloc::Layout, n: usize) -> *mut u8 {
        let _ = BYTES.try_with(|b| b.set(b.get() + n));
        std::alloc::System.realloc(p, l, n)
    }
    unsafe fn dealloc(&self, p: *mut u8, l: std::alloc::Layout) {
        std::alloc::System.dealloc(p, l)
    }
}

#[global_allocator]
static ALLOC: Counting = Counting;

fn allocated() -> usize {
    BYTES.with(|b| b.get())
}

fn pop(r: &mut Reassembly) -> Vec<u8> {
    let mut out = Vec::new();
    r.pop(&mut out);
    out
}

#[test]
fn in_order() {
    let mut r = Reassembly::new();
    r.insert(0, b"ab");
    assert_eq!(pop(&mut r), b"ab");
    r.insert(2, b"cd");
    assert_eq!(pop(&mut r), b"cd");
    assert_eq!(r.base_exec(), 4);
}

#[test]
fn out_of_order() {
    let mut r = Reassembly::new();
    r.insert(3, b"de");
    assert_eq!(pop(&mut r), b"");
    r.insert(0, b"abc");
    assert_eq!(pop(&mut r), b"abcde");
}

#[test]
fn first_writer_wins() {
    let mut r = Reassembly::new();
    r.insert(0, b"abc");
    assert_eq!(pop(&mut r), b"abc");
    // X and Y lose to the delivered b and c; W is new at offset 3.
    r.insert(1, b"XYW");
    assert_eq!(pop(&mut r), b"W");
    r.insert(5, b"pq");
    // Y and Z lose to the buffered p and q.
    r.insert(4, b"XYZ");
    assert_eq!(pop(&mut r), b"Xpq");
}

#[test]
fn buffer_bound() {
    let mut r = Reassembly::new();
    r.insert(9, b"z");
    assert_eq!(r.buf_len(), 10);
    r.insert(0, b"abcdefghi");
    assert_eq!(pop(&mut r), b"abcdefghiz");
    assert_eq!(r.buf_len(), 0);
}

#[test]
fn duplicate_below_base() {
    let mut r = Reassembly::new();
    r.insert(0, b"abcde");
    pop(&mut r);
    r.insert(0, b"abcde");
    assert_eq!(pop(&mut r), b"");
    assert_eq!(r.buf_len(), 0);
    r.insert(2, b"cdefg");
    assert_eq!(pop(&mut r), b"fg");
}

#[test]
fn pop_cost_independent_of_tail() {
    // The CRYPTO pattern at 1 MiB. Copying the tail on every pop moves ~512 GiB here; amortized
    // compaction moves under 2 MiB. Each compaction is a `split_off`, one tail-sized allocation, so
    // the bytes requested count the bytes compaction copies (plus `out`'s doubling, under 2N).
    const N: u64 = 1 << 20;
    let a0 = allocated();
    let mut r = Reassembly::new();
    r.insert(N - 1, b"z");
    let mut out = Vec::new();
    for off in 0..N - 2 {
        r.insert(off, &[off as u8]);
        r.pop(&mut out);
        assert_eq!(r.base_exec(), off + 1);
        assert_eq!(r.buf_len() as u64, N - 1 - off);
    }
    r.insert(N - 2, b"y");
    r.pop(&mut out);
    assert_eq!(r.base_exec(), N);
    assert_eq!(r.buf_len(), 0);
    assert_eq!(out.len() as u64, N);
    let req = allocated() - a0;
    assert!(req <= 8 * N as usize, "{req} bytes requested for {N} bytes popped");
}

#[test]
fn drain_releases_capacity() {
    // A peer fills [1, W), then sends byte 0: everything drains, and nothing stays allocated.
    const W: usize = 1 << 16;
    let mut r = Reassembly::new();
    r.insert(1, &vec![7u8; W - 1]);
    assert!(r.capacities().0 >= W && r.capacities().1 >= W);
    r.insert(0, b"x");
    let out = pop(&mut r);
    assert_eq!(out.len(), W);
    assert_eq!(r.buf_len(), 0);
    assert_eq!(r.capacities(), (0, 0));
}
