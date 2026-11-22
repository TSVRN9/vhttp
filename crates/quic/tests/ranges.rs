//! `quic::ranges` (9b2 D10): merged range sets and exact piece sets on `byteq::avl` (re-exported as `quic::avl`).
use quic::ranges::{PieceSet, RangeSet};
use std::collections::BTreeSet;

#[test]
fn ranges_add_merges() {
    let mut r = RangeSet::new();
    r.add(0, 300);
    r.add(600, 900);
    let (m, _) = r.add(300, 600);
    assert_eq!(m, (0, 900));
    assert_eq!(r.to_vec(), vec![(0, 900)]);
    assert_eq!(r.len(), 1);
    r.add(1000, 1001);
    let (m, _) = r.add(1001, 1300);
    assert_eq!(m, (1000, 1300));
    assert_eq!(r.to_vec(), vec![(0, 900), (1000, 1300)]);
}

#[test]
fn ranges_take_first() {
    let mut r = RangeSet::new();
    r.add(0, 600);
    r.take_first(300);
    assert_eq!(r.to_vec(), vec![(300, 600)]);
    r.take_first(300);
    assert_eq!(r.to_vec(), vec![]);
    assert_eq!(r.len(), 0);
}

#[test]
fn pieces_exact() {
    let mut p = PieceSet::new();
    p.insert_piece(0, 300);
    p.insert_piece(300, 600);
    assert_eq!(p.to_vec(), vec![(0, 300), (300, 600)]);
    assert!(!p.take_piece(0, 600).0);
    assert!(!p.take_piece(100, 300).0);
    assert_eq!(p.to_vec(), vec![(0, 300), (300, 600)]);
    assert!(p.take_piece(0, 300).0);
    assert_eq!(p.to_vec(), vec![(300, 600)]);
    assert_eq!(p.len(), 1);
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

fn bytes(v: &[(u64, u64)]) -> BTreeSet<u64> {
    v.iter().flat_map(|&(s, e)| s..e).collect()
}

#[test]
fn ranges_model() {
    let mut rng = Rng(0x9b2_8a);
    let mut r = RangeSet::new();
    let mut p = PieceSet::new();
    let mut model: BTreeSet<u64> = BTreeSet::new();
    let mut pieces: BTreeSet<(u64, u64)> = BTreeSet::new();
    for _ in 0..20_000 {
        let s = rng.below(2000);
        let e = s + 1 + rng.below(40);
        let free = (s..e).all(|x| !model.contains(&x));
        match rng.below(4) {
            0 | 1 if free => {
                let (m, _) = r.add(s, e);
                model.extend(s..e);
                assert!(m.0 <= s && e <= m.1 && r.to_vec().contains(&m));
            },
            2 => {
                let v = r.to_vec();
                if let Some(&(a, b)) = v.get(rng.below(v.len() as u64 + 1) as usize) {
                    r.remove_range(a, b);
                    for x in a..b {
                        model.remove(&x);
                    }
                }
            },
            _ => {
                if let Some(&(a, b)) = r.to_vec().first() {
                    let k = 1 + rng.below(b - a);
                    r.take_first(k);
                    for x in a..a + k {
                        model.remove(&x);
                    }
                }
            },
        }
        let v = r.to_vec();
        assert!(v.windows(2).all(|w| w[0].0 < w[0].1 && w[0].1 < w[1].0), "sorted, disjoint, merged: {v:?}");
        assert_eq!(bytes(&v), model);
        assert_eq!(r.len() as usize, v.len());
        // Pieces: inserted where no piece meets them, taken only whole.
        let pfree = pieces.iter().all(|&(a, b)| b <= s || e <= a);
        if rng.below(2) == 0 && pfree {
            p.insert_piece(s, e);
            pieces.insert((s, e));
        } else {
            let pv = p.to_vec();
            let pick = pv.get(rng.below(pv.len() as u64 + 1) as usize).copied().unwrap_or((s, e));
            let (hit, _) = p.take_piece(pick.0, pick.1);
            assert_eq!(hit, pieces.remove(&pick));
        }
        assert_eq!(p.to_vec(), pieces.iter().copied().collect::<Vec<_>>());
        assert_eq!(p.len() as usize, pieces.len());
    }
}

/// The spec's memory unit (D10 (f)): one node of a range tree is 40 bytes.
#[test]
fn node_size() {
    assert_eq!(std::mem::size_of::<quic::avl::Node<u64>>(), 40);
}
