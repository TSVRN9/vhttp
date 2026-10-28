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
