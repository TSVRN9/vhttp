use quic::frags::Frags;

fn front(f: &mut Frags, end: u64) -> (u64, Vec<u8>) {
    let mut out = Vec::new();
    let r = f.take_front(end, &mut out);
    (r, out)
}

/// Checks `after_insert` against the `insert` it predicts.
fn put(f: &mut Frags, lo: u64, off: u64, data: &[u8]) {
    let want = f.after_insert(lo, off, data);
    f.insert(lo, off, data);
    assert_eq!((f.held(), f.count()), want);
}

#[test]
fn frags_disjoint_and_adjacent_merge() {
    let mut f = Frags::new();
    put(&mut f, 0, 10, &[1; 5]);
    assert_eq!((f.held(), f.count()), (5, 1));
    put(&mut f, 0, 30, &[3; 2]);
    assert_eq!((f.held(), f.count()), (7, 2));
    // [15, 20) touches [10, 15): one run.
    put(&mut f, 0, 15, &[2; 5]);
    assert_eq!((f.held(), f.count()), (12, 2));
    // [20, 30) touches both sides: the two runs become one.
    put(&mut f, 0, 20, &[4; 10]);
    assert_eq!((f.held(), f.count()), (22, 1));
    let mut want = vec![1; 5];
    want.extend([2; 5]);
    want.extend([4; 10]);
    want.extend([3; 2]);
    assert_eq!(front(&mut f, 10), (32, want));
    assert_eq!((f.held(), f.count()), (0, 0));
}

#[test]
fn frags_overlap_left() {
    let mut f = Frags::new();
    put(&mut f, 0, 10, &[1; 5]);
    put(&mut f, 0, 8, &[9; 4]);
    assert_eq!((f.held(), f.count()), (7, 1));
    assert_eq!(front(&mut f, 8), (15, vec![9, 9, 1, 1, 1, 1, 1]));
}

#[test]
fn frags_overlap_right() {
    let mut f = Frags::new();
    put(&mut f, 0, 10, &[1; 5]);
    put(&mut f, 0, 13, &[9; 4]);
    assert_eq!((f.held(), f.count()), (7, 1));
    assert_eq!(front(&mut f, 10), (17, vec![1, 1, 1, 1, 1, 9, 9]));
}

#[test]
fn frags_inside_and_duplicate() {
    let mut f = Frags::new();
    put(&mut f, 0, 10, &[1; 10]);
    put(&mut f, 0, 12, &[9; 3]);
    put(&mut f, 0, 10, &[8; 10]);
    assert_eq!((f.held(), f.count()), (10, 1));
    assert_eq!(front(&mut f, 10), (20, vec![1; 10]));
}

#[test]
fn frags_spanning_several() {
    let mut f = Frags::new();
    put(&mut f, 0, 10, &[1; 2]);
    put(&mut f, 0, 14, &[2; 2]);
    put(&mut f, 0, 20, &[3; 2]);
    put(&mut f, 0, 40, &[5; 1]);
    assert_eq!((f.held(), f.count()), (7, 4));
    // [11, 21) covers the gaps 12..14 and 16..20 and joins the first three fragments.
    put(&mut f, 0, 11, &[9; 10]);
    assert_eq!((f.held(), f.count()), (13, 2));
    let want = vec![1, 1, 9, 9, 2, 2, 9, 9, 9, 9, 3, 3];
    assert_eq!(front(&mut f, 10), (22, want));
    assert_eq!((f.held(), f.count()), (1, 1));
}

#[test]
fn frags_lo_cuts_below() {
    let mut f = Frags::new();
    put(&mut f, 12, 10, &[5; 5]);
    assert_eq!((f.held(), f.count()), (3, 1));
    put(&mut f, 20, 10, &[5; 5]);
    put(&mut f, 0, 30, &[]);
    assert_eq!((f.held(), f.count()), (3, 1));
    assert_eq!(front(&mut f, 12), (15, vec![5; 3]));
}

#[test]
fn frags_take_front_no_match() {
    let mut f = Frags::new();
    put(&mut f, 0, 10, &[1; 3]);
    assert_eq!(front(&mut f, 5), (5, vec![]));
    assert_eq!(front(&mut f, 9), (9, vec![]));
    assert_eq!((f.held(), f.count()), (3, 1));
}
