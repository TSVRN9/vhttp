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

/// Everything contiguous (at most a window).
fn pop(r: &mut Reassembly) -> Vec<u8> {
    r.pop(u64::MAX).0
}

const W: u64 = 1 << 16;

#[test]
fn in_order() {
    let mut r = Reassembly::new(W);
    r.insert(0, b"ab");
    assert_eq!(pop(&mut r), b"ab");
    r.insert(2, b"cd");
    assert_eq!(pop(&mut r), b"cd");
    assert_eq!(r.base_exec(), 4);
}

#[test]
fn out_of_order() {
    let mut r = Reassembly::new(W);
    r.insert(3, b"de");
    assert_eq!(pop(&mut r), b"");
    r.insert(0, b"abc");
    assert_eq!(pop(&mut r), b"abcde");
}

#[test]
fn pop_stops_at_max() {
    let mut r = Reassembly::new(W);
    r.insert(0, b"abcdef");
    assert_eq!(r.pop(2).0, b"ab");
    assert_eq!(r.pop(3).0, b"cde");
    assert_eq!(r.pop(0).0, b"");
    assert_eq!(pop(&mut r), b"f");
    assert_eq!(r.base_exec(), 6);
}

#[test]
fn first_writer_wins() {
    let mut r = Reassembly::new(W);
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
    let mut r = Reassembly::new(W);
    r.insert(9, b"z");
    assert_eq!(r.buf_len(), 10);
    r.insert(0, b"abcdefghi");
    assert_eq!(pop(&mut r), b"abcdefghiz");
    assert_eq!(r.buf_len(), 0);
}

#[test]
fn duplicate_below_base() {
    let mut r = Reassembly::new(W);
    r.insert(0, b"abcde");
    pop(&mut r);
    r.insert(0, b"abcde");
    assert_eq!(pop(&mut r), b"");
    assert_eq!(r.buf_len(), 0);
    r.insert(2, b"cdefg");
    assert_eq!(pop(&mut r), b"fg");
}

#[test]
fn complete_to_counts_received() {
    let mut r = Reassembly::new(W);
    r.insert(5, b"fgh");
    assert!(!r.complete_to(8));
    r.insert(0, b"abc");
    assert!(!r.complete_to(8));
    r.insert(2, b"cde");
    assert!(r.complete_to(8));
    assert_eq!(r.pop(4).0, b"abcd");
    assert!(r.complete_to(8));
}

#[test]
fn pop_cost_independent_of_tail() {
    // A window's last byte, then every other byte one at a time, each delivered at once: a pop hands over one byte in
    // one exact allocation, whatever is buffered behind it (9b2 Task 8 ruling C4; `pop`'s cost is proved, at most
    // `c_rd · (max + max/PAGE + 2)`). Counted, never timed.
    let mut r = Reassembly::new(W);
    r.insert(W - 1, b"z");
    for off in 0..W - 2 {
        r.insert(off, &[off as u8]);
        let a0 = allocated();
        let (out, _) = r.pop(1);
        assert_eq!(out.len(), 1);
        assert!(allocated() - a0 <= 1, "pop of one byte requested {} bytes", allocated() - a0);
        assert_eq!(r.base_exec(), off + 1);
        assert_eq!(r.buf_len() as u64, W - 1 - off);
    }
    r.insert(W - 2, b"y");
    assert_eq!(pop(&mut r), b"yz");
    assert_eq!(r.buf_len(), 0);
    assert_eq!(r.page_count(), 0);
}

#[test]
fn drain_releases_capacity() {
    // A peer fills [1, W), then sends byte 0: everything drains, and no page stays allocated.
    let mut r = Reassembly::new(W);
    r.insert(1, &vec![7u8; W as usize - 1]);
    assert_eq!(r.page_count(), 256);
    r.insert(0, b"x");
    let out = pop(&mut r);
    assert_eq!(out.len(), W as usize);
    assert_eq!(r.buf_len(), 0);
    assert_eq!(r.page_count(), 0);
}
