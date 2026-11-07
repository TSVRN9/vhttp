//! 9a T7 fix round 1 (review I1): an out-of-order CRYPTO frame whose bytes are all held already
//! must not copy or allocate. CRYPTO has no flow control, so a peer may send such frames without
//! limit; at edeca5c each one copied the whole fragment it touched.
// One test in this binary; the counter is per thread anyway, since libtest runs tests on threads.
use quic::crypto_stream::CryptoStream;
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

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

#[test]
fn duplicate_ooo_frames_allocate_nothing() {
    // One held 16 KiB fragment, 10,000 one-byte duplicates inside it.
    let mut c = CryptoStream::new();
    assert_eq!(c.on_crypto(1, &[7; 16384]), Ok(()));
    let before = allocated();
    for k in 0..10_000u64 {
        assert_eq!(c.on_crypto(1 + k % 16384, &[7]), Ok(()));
    }
    assert_eq!(allocated() - before, 0);
    // 4096 one-byte fragments, 10,000 duplicates spread over them.
    let mut c = CryptoStream::new();
    for k in 0..4096u64 {
        assert_eq!(c.on_crypto(2 + 2 * k, &[1]), Ok(()));
    }
    let before = allocated();
    for k in 0..10_000u64 {
        assert_eq!(c.on_crypto(2 + 2 * (k % 4096), &[1]), Ok(()));
    }
    assert_eq!(allocated() - before, 0);
}
