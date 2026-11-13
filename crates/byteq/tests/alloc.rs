//! 9b2 D3: a `CapVec` allocates once, at `new`, with the capacity it was asked for, and never reallocates.
use byteq::capvec::CapVec;
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

struct Counting;

thread_local! {
    static ALLOCS: Cell<usize> = const { Cell::new(0) };
    static BYTES: Cell<usize> = const { Cell::new(0) };
    static REALLOCS: Cell<usize> = const { Cell::new(0) };
    static DEALLOCS: Cell<usize> = const { Cell::new(0) };
}

fn bump(c: &'static std::thread::LocalKey<Cell<usize>>, n: usize) {
    let _ = c.try_with(|x| x.set(x.get() + n));
}

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        bump(&ALLOCS, 1);
        bump(&BYTES, l.size());
        System.alloc(l)
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        bump(&ALLOCS, 1);
        bump(&BYTES, l.size());
        System.alloc_zeroed(l)
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        bump(&REALLOCS, 1);
        bump(&BYTES, n);
        System.realloc(p, l, n)
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        bump(&DEALLOCS, 1);
        System.dealloc(p, l)
    }
}

#[global_allocator]
static ALLOC: Counting = Counting;

/// (allocs, bytes, reallocs, deallocs) on this thread so far.
fn counts() -> [usize; 4] {
    [ALLOCS.with(|c| c.get()), BYTES.with(|c| c.get()), REALLOCS.with(|c| c.get()), DEALLOCS.with(|c| c.get())]
}

#[test]
fn capvec_allocs_exact() {
    let src: [u8; 64] = core::array::from_fn(|i| i as u8);
    let c0 = counts();
    let e = CapVec::<u8>::new(0);
    let mut a = CapVec::<u8>::new(5);
    let mut b = CapVec::<u8>::new(64);
    let mut f = CapVec::<bool>::new(3);
    for i in 0..5u8 {
        a.push(10 + i);
    }
    let _ = b.push_slice(&src[..40]);
    let _ = b.push_slice(&src[40..]);
    f.push(true);
    f.push(false);
    f.push(true);
    a.set(2, 99);
    f.set(1, true);
    let c1 = counts();
    assert_eq!(c1[0] - c0[0], 3, "one allocation per nonzero-capacity new");
    assert!(c1[1] - c0[1] >= 5 + 64 + 3, "each allocation at least its requested capacity");
    assert_eq!(c1[2] - c0[2], 0, "no realloc");
    assert_eq!(c1[3] - c0[3], 0, "no free while filling");
    assert!(a.capacity() >= 5 && b.capacity() >= 64 && f.capacity() >= 3);
    assert_eq!(e.len(), 0);
    assert_eq!(a.as_slice(), &[10, 11, 99, 13, 14]);
    assert_eq!(b.as_slice(), &src[..]);
    assert_eq!(f.as_slice(), &[true, true, true]);
    assert_eq!((*a.index(4), *f.index(0)), (14, true));
    let v = b.into_vec();
    assert_eq!(v.as_slice(), &src[..]);
    drop((e, a, f, v));
    let c2 = counts();
    assert_eq!(c2[0] - c0[0], 3, "into_vec and drop allocate nothing");
    assert_eq!(c2[3] - c0[3], 3, "each allocation freed once");
    assert_eq!(std::mem::size_of::<CapVec<u8>>(), std::mem::size_of::<Vec<u8>>(), "the ghost capacity takes no space");
}
