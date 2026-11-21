//! `quic::ring` (9b2 D11): the paged receive buffer under a stream's window.
use quic::ring::{Ring, PAGE};
use std::collections::{BTreeMap, BTreeSet};

/// Delivers everything ready, at most `max` bytes.
fn take(r: &mut Ring, max: u64) -> Vec<u8> {
    let (out, _) = r.deliver(max);
    assert_eq!(out.capacity() >= out.len(), true);
    out.as_slice().to_vec()
}

#[test]
fn ring_no_slots_before_first_byte() {
    let mut r = Ring::new(16384);
    assert!(!r.has_slots());
    r.insert_bytes(0, &[]);
    r.insert_bytes(100, &[]);
    assert!(!r.has_slots());
    assert!(!r.ready());
    assert_eq!(take(&mut r, 100), Vec::<u8>::new());
    assert!(!r.has_slots());
    r.insert_bytes(5, &[7]);
    assert!(r.has_slots());
    assert_eq!(r.page_count(), 1);
}

#[test]
fn ring_first_writer_wins() {
    let mut r = Ring::new(16384);
    r.insert_bytes(10, &[1; 10]);
    r.insert_bytes(5, &[2; 20]);
    r.insert_bytes(0, &[3; 5]);
    let mut want = vec![3u8; 5];
    want.extend([2u8; 5]);
    want.extend([1u8; 10]);
    want.extend([2u8; 5]);
    assert_eq!(take(&mut r, 1000), want);
}

#[test]
fn ring_deliver_stops_at_gap() {
    let mut r = Ring::new(16384);
    r.insert_bytes(0, &[9; 300]);
    r.insert_bytes(400, &[8; 100]);
    let (out, _) = r.deliver(1000);
    assert_eq!(out.as_slice(), &[9u8; 300][..]);
    assert_eq!(out.capacity(), 300);
    assert!(!r.ready());
    r.insert_bytes(300, &[7; 100]);
    assert!(r.ready());
    let (out, _) = r.deliver(150);
    assert_eq!(out.as_slice(), &[7u8; 100].iter().chain(&[8u8; 50]).copied().collect::<Vec<_>>()[..]);
    assert_eq!(out.capacity(), 150);
    assert_eq!(take(&mut r, 1000), vec![8u8; 50]);
    assert_eq!(r.page_count(), 0);
}

/// A seeded xorshift: the same ops every run.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// The model: held offsets at or past `base`, first writer wins.
struct Model {
    base: u64,
    m: BTreeMap<u64, u8>,
}

impl Model {
    fn insert(&mut self, off: u64, d: &[u8]) {
        for (i, b) in d.iter().enumerate() {
            let p = off + i as u64;
            if p >= self.base {
                self.m.entry(p).or_insert(*b);
            }
        }
    }

    fn deliver(&mut self, max: u64) -> Vec<u8> {
        let mut out = Vec::new();
        while (out.len() as u64) < max {
            match self.m.remove(&self.base) {
                Some(b) => out.push(b),
                None => break,
            }
            self.base += 1;
        }
        out
    }

    fn pages(&self) -> usize {
        self.m.keys().map(|p| p / PAGE).collect::<BTreeSet<_>>().len()
    }
}

/// Inserts and deliveries over 20 windows' worth of offsets in a 1024-byte window: every delivery, `ready` and page
/// count equals the model's (a page is allocated exactly while it holds a byte at or past `base`).
#[test]
fn ring_wraps() {
    let w = 1024;
    let mut r = Ring::new(w);
    let mut m = Model { base: 0, m: BTreeMap::new() };
    let mut g = Rng(0x9e37_79b9_7f4a_7c15);
    let mut step = 0u64;
    while m.base < 20 * w {
        let base = m.base;
        let lo = base.saturating_sub(300) + g.below(w + 300);
        let len = g.below(base + w - lo.min(base + w) + 1).min(700);
        let d: Vec<u8> = (0..len).map(|_| g.next() as u8).collect();
        let off = lo.min(base + w - len);
        r.insert_bytes(off, &d);
        m.insert(off, &d);
        assert_eq!(r.ready(), m.m.contains_key(&m.base), "step {step}");
        assert_eq!(r.page_count(), m.pages(), "step {step}");
        if g.below(3) == 0 {
            let max = g.below(900);
            let (out, _) = r.deliver(max);
            let want = m.deliver(max);
            assert_eq!(out.as_slice(), &want[..], "step {step}");
            assert_eq!(out.capacity(), want.len(), "step {step}");
            assert_eq!(r.page_count(), m.pages(), "step {step}");
        }
        step += 1;
    }
    assert!(step > 100);
}

#[test]
fn ring_frees_pages_past_delivery() {
    let mut r = Ring::new(4096);
    r.insert_bytes(0, &[1; 1024]);
    assert_eq!(r.page_count(), 4);
    assert_eq!(take(&mut r, 255).len(), 255);
    assert_eq!(r.page_count(), 4);
    assert_eq!(take(&mut r, 1).len(), 1);
    assert_eq!(r.page_count(), 3);
    assert_eq!(take(&mut r, 600).len(), 600);
    assert_eq!(r.page_count(), 1);
    assert_eq!(take(&mut r, 1000).len(), 168);
    assert_eq!(r.page_count(), 0);
    // A page holding only delivered bytes is freed even though delivery stopped inside it.
    r.insert_bytes(1024, &[2; 44]);
    assert_eq!(take(&mut r, 1000).len(), 44);
    assert_eq!(r.page_count(), 0);
}

/// Review Focus 2: bytes below `base` never land again, and pages below it are never allocated again.
#[test]
fn ring_below_base_ignored() {
    let mut r = Ring::new(16384);
    let d: Vec<u8> = (0..700u32).map(|i| i as u8).collect();
    r.insert_bytes(0, &d[..600]);
    assert_eq!(take(&mut r, 600), d[..600].to_vec());
    assert_eq!(r.page_count(), 0);
    r.insert_bytes(0, &[0xee; 700]);
    assert_eq!(r.page_count(), 1);
    r.insert_bytes(0, &[0xdd; 600]);
    assert_eq!(r.page_count(), 1);
    assert_eq!(take(&mut r, 1000), vec![0xee; 100]);
    assert_eq!(r.page_count(), 0);
}
