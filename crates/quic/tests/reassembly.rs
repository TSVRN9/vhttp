use quic::reassembly::*;

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
    // The CRYPTO pattern at 1 MiB. Copying the tail on every pop moves ~512 GiB here (about
    // 20 s in a debug build); amortized compaction moves under 2 MiB.
    const N: u64 = 1 << 20;
    let t = std::time::Instant::now();
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
    assert!(t.elapsed().as_secs() < 5, "took {:?}", t.elapsed());
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
