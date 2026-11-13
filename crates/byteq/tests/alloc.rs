//! 9b2 D3: a `CapVec` allocates once, at `new`, with the capacity it was asked for, and never reallocates; a
//! `ByteQueue` allocates only where D4's branches say.
use byteq::capvec::CapVec;
use byteq::queue::ByteQueue;
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

#[test]
fn queue_new_allocates_nothing() {
    let c0 = counts();
    let q = ByteQueue::new();
    let c1 = counts();
    assert_eq!(c1[0] - c0[0], 0, "new allocates nothing");
    assert_eq!((q.len(), q.as_slice(), q.caps()), (0, &[][..], (0, 0)));
}

#[test]
fn take_and_drop_zero() {
    let mut q = ByteQueue::new();
    let c0 = counts();
    let (t, _) = q.take_front(0);
    let _ = q.drop_front(0);
    let c1 = counts();
    assert_eq!(c1[0] - c0[0], 0, "take_front(0) and drop_front(0) allocate nothing");
    assert_eq!(c1[2] - c0[2], 0, "no realloc");
    assert_eq!((t.len(), q.len(), q.caps()), (0, 0, (0, 0)));
}

/// The cap of the buffer a push would have made last: `b` while migrating, else `a`.
fn newest_cap(q: &ByteQueue) -> usize {
    let (a, b) = q.caps();
    if b != 0 {
        b
    } else {
        a
    }
}

#[derive(Clone, Copy, Debug)]
enum Op {
    Push(usize),
    Take(usize),
    Drop(usize),
}

/// The queue under test beside its `VecDeque` model and `P`, the largest length plus push since the model was last empty.
struct Run {
    q: ByteQueue,
    m: std::collections::VecDeque<u8>,
    p: usize,
}

impl Run {
    fn new() -> Run {
        Run { q: ByteQueue::new(), m: std::collections::VecDeque::with_capacity(1 << 16), p: 0 }
    }

    /// Runs `op` (a push takes `src[..d]`) and checks it: the view equals the model, no realloc, and the allocations
    /// are exactly those of D4's branch: one queue buffer of `max(64, 3·S)` bytes (`S` the length after the push)
    /// when a new buffer became the newest one (a swap only moves `b` into `a`), plus `take_front`'s exact `n` bytes.
    fn op(&mut self, op: Op, src: &[u8]) {
        let (caps0, new0, len0) = (self.q.caps(), self.q.newest(), self.q.len());
        let c0 = counts();
        let got = match op {
            Op::Push(d) => {
                let _ = self.q.push_slice(&src[..d]);
                None
            }
            Op::Take(n) => Some(self.q.take_front(n).0),
            Op::Drop(n) => {
                let _ = self.q.drop_front(n);
                None
            }
        };
        let c1 = counts();
        let fresh = self.q.newest() != new0 && newest_cap(&self.q) != 0;
        let out = if let Op::Take(n) = op { n } else { 0 };
        assert_eq!(c1[2] - c0[2], 0, "{op:?}: no realloc");
        assert_eq!(c1[0] - c0[0], fresh as usize + (out > 0) as usize, "{op:?}: the branch's allocations, caps {caps0:?} -> {:?}", self.q.caps());
        assert_eq!(c1[1] - c0[1], if fresh { newest_cap(&self.q) } else { 0 } + out, "{op:?}: allocated bytes");
        if fresh {
            assert!(matches!(op, Op::Push(_)), "{op:?}: only a push allocates a queue buffer");
            assert_eq!(newest_cap(&self.q), 64.max(3 * self.q.len()), "{op:?}: a new buffer is max(MIN_CAP, 3·S)");
        }
        match op {
            Op::Push(d) => {
                self.m.extend(&src[..d]);
                self.p = self.p.max(len0 + d);
            }
            Op::Take(n) => {
                let t: Vec<u8> = self.m.drain(..n).collect();
                assert_eq!(got.unwrap().as_slice(), &t[..], "{op:?}: take_front hands over the front");
            }
            Op::Drop(n) => {
                self.m.drain(..n);
            }
        }
        if self.m.is_empty() {
            self.p = 0;
            assert_eq!(self.q.caps(), (0, 0), "{op:?}: a drained queue holds no buffer");
        }
        assert!(self.q.as_slice().iter().eq(self.m.iter()), "{op:?}: view equals the model");
        assert_eq!(self.q.len(), self.m.len());
        let (a, b) = self.q.caps();
        assert!(a + b <= 2 * 64.max(3 * self.p), "{op:?}: requested {a} + {b} within 2·max(64, 3·{})", self.p);
    }
}

fn xorshift(x: &mut u64) -> u64 {
    *x ^= *x << 13;
    *x ^= *x >> 7;
    *x ^= *x << 17;
    *x
}

#[test]
fn queue_model_random() {
    let (mut migs, mut swaps) = (0, 0);
    for seed in 1..=8u64 {
        let mut x = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15);
        let mut r = Run::new();
        let mut src = [0u8; 300];
        for _ in 0..20_000 {
            let v = xorshift(&mut x);
            let op = match v % 5 {
                0..=2 => {
                    for b in src.iter_mut() {
                        *b = xorshift(&mut x) as u8;
                    }
                    Op::Push((v >> 8) as usize % 301)
                }
                3 => Op::Take((v >> 8) as usize % (r.m.len() + 1)),
                _ => Op::Drop((v >> 8) as usize % (r.m.len() + 1)),
            };
            let b0 = r.q.caps().1;
            r.op(op, &src);
            let b1 = r.q.caps().1;
            migs += (b1 != 0 && b1 != b0) as usize;
            swaps += (b0 != 0 && b1 == 0 && r.q.len() > 0) as usize;
        }
    }
    assert!(migs > 100 && swaps > 100, "the runs migrate and swap ({migs}, {swaps})");
}

#[test]
fn consume_during_migration_then_swap() {
    let src: [u8; 100] = core::array::from_fn(|i| i as u8 ^ 0x5a);
    let mut r = Run::new();
    r.op(Op::Push(100), &src);
    assert_eq!(r.q.caps(), (300, 0), "case 4 from empty");
    r.op(Op::Push(40), &src);
    assert_eq!(r.q.caps(), (300, 0), "case 2: 140 <= 150");
    r.op(Op::Push(20), &src);
    assert_eq!(r.q.caps(), (300, 480), "case 3: a migration into 3·160");
    r.op(Op::Drop(70), &src);
    r.op(Op::Take(10), &src);
    assert_eq!(r.q.caps(), (300, 480), "consuming keeps the migration");
    // 60 of 160 copied: R = 100 falls by 2 per 1-byte push (3 copied, 1 appended), so the 50th push swaps.
    for k in 1..=50 {
        r.op(Op::Push(1), &src[k..]);
        assert_eq!(r.q.caps(), if k < 50 { (300, 480) } else { (480, 0) }, "push {k}");
    }
    r.op(Op::Push(1), &src);
    assert_eq!(r.q.caps(), (480, 0));
}

#[test]
fn push_empty_is_noop() {
    let src = [7u8; 160];
    let mut r = Run::new();
    r.op(Op::Push(0), &src);
    assert_eq!(r.q.caps(), (0, 0));
    r.op(Op::Push(100), &src);
    r.op(Op::Push(40), &src);
    r.op(Op::Push(20), &src);
    assert_eq!(r.q.caps(), (300, 480), "migrating");
    let c0 = counts();
    r.op(Op::Push(0), &src);
    assert_eq!(counts()[0] - c0[0], 0, "push_slice(&[]) allocates nothing");
    assert_eq!(r.q.caps(), (300, 480));
}

#[test]
fn boundary_sizes() {
    let src: [u8; 64] = core::array::from_fn(|i| 200 - i as u8);
    // (d, caps after): from ca = 64 holding 10 bytes, C/2 = 32.
    for (d, caps) in [(22, (64, 0)), (23, (99, 0)), (32, (126, 0)), (33, (129, 0))] {
        let mut r = Run::new();
        r.op(Op::Push(10), &src);
        assert_eq!(r.q.caps(), (64, 0));
        r.op(Op::Push(d), &src[10..]);
        assert_eq!(r.q.caps(), caps, "d = {d}: L_a + d == C/2 is case 2, d <= C/2 case 3 (all copied: swap), d > C/2 case 4");
    }
}

#[test]
fn drained_queue_holds_nothing() {
    let src = [3u8; 160];
    let mut r = Run::new();
    r.op(Op::Push(100), &src);
    r.op(Op::Push(40), &src);
    r.op(Op::Push(20), &src);
    assert_eq!(r.q.caps(), (300, 480), "migrating: two buffers");
    let c0 = counts();
    r.op(Op::Drop(160), &src);
    assert_eq!(counts()[3] - c0[3], 2, "draining frees both buffers");
    assert_eq!(r.q.caps(), (0, 0));
    // The peak restarts: a 10-byte push gets max(MIN_CAP, 3·10), not 3·160.
    r.op(Op::Push(10), &src);
    assert_eq!(r.q.caps(), (64, 0));
    r.op(Op::Take(10), &src);
    assert_eq!(r.q.caps(), (0, 0));
}
