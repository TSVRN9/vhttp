use quic::ack::*;
use quic::codes::FRAME_ENCODING_ERROR;

fn ack(largest: u64, delay: u64, first_range: u64, ranges: Vec<(u64, u64)>) -> AckFrame {
    AckFrame { largest, delay, first_range, ranges, ecn: None }
}

/// Test-local mirror of `ack_contains`: walk the ranges from the largest down.
fn contains(a: &AckFrame, pn: u64) -> bool {
    let mut smallest = a.largest - a.first_range;
    if (smallest..=a.largest).contains(&pn) {
        return true;
    }
    for &(gap, len) in &a.ranges {
        let largest = smallest - gap - 2;
        smallest = largest - len;
        if (smallest..=largest).contains(&pn) {
            return true;
        }
    }
    false
}

#[test]
fn ack_basic() {
    let (a, n) = parse_ack(2, &[0x05, 0x00, 0x00, 0x02]).unwrap();
    assert_eq!((a, n), (ack(5, 0, 2, vec![]), 4));
}

#[test]
fn ack_ranges() {
    let (a, n) = parse_ack(2, &[0x0a, 0x00, 0x01, 0x01, 0x01, 0x02]).unwrap();
    assert_eq!((&a, n), (&ack(10, 0, 1, vec![(1, 2)]), 6));
    for pn in [4, 5, 6, 9, 10] {
        assert!(contains(&a, pn), "{pn}");
    }
    for pn in [3, 7, 8, 11] {
        assert!(!contains(&a, pn), "{pn}");
    }
}

#[test]
fn ack_ecn() {
    let want = AckFrame { largest: 0, delay: 0, first_range: 0, ranges: vec![], ecn: Some((1, 2, 3)) };
    assert_eq!(parse_ack(3, &[0, 0, 0, 0, 1, 2, 3]), Ok((want, 7)));
    // Type 0x02 stops before the ECN counts.
    assert_eq!(parse_ack(2, &[0, 0, 0, 0, 1, 2, 3]).unwrap().1, 4);
    // Type 0x03 with a missing ECN count.
    assert_eq!(parse_ack(3, &[0, 0, 0, 0, 1, 2]), Err(FRAME_ENCODING_ERROR));
}

#[test]
fn ack_negative() {
    let fee = Err(FRAME_ENCODING_ERROR);
    assert_eq!(parse_ack(2, &[0x02, 0x00, 0x00, 0x03]), fee);
    assert_eq!(parse_ack(2, &[0x05, 0x00, 0x01, 0x00, 0x04, 0x00]), fee);
    let (a, n) = parse_ack(2, &[0x05, 0x00, 0x01, 0x00, 0x03, 0x00]).unwrap();
    assert_eq!((&a, n), (&ack(5, 0, 0, vec![(3, 0)]), 6));
    assert!(contains(&a, 0) && !contains(&a, 1));
    assert_eq!(parse_ack(2, &[0x05, 0x00, 0x01, 0x00, 0x03, 0x01]), fee);
    // Truncated before each field.
    let whole = [0x05, 0x00, 0x01, 0x00, 0x03, 0x00];
    for k in 0..whole.len() {
        assert_eq!(parse_ack(2, &whole[..k]), fee, "{k}");
    }
}

#[test]
fn ack_count_exceeds_bytes() {
    let b = [0x05, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00];
    assert_eq!(parse_ack(2, &b), Err(FRAME_ENCODING_ERROR));
}

#[test]
fn ack_roundtrip() {
    let a = AckFrame {
        largest: 1000,
        delay: 25,
        first_range: 3,
        ranges: vec![(0, 0), (10, 5)],
        ecn: Some((7, 0, 1)),
    };
    let mut bytes = vec![0xee];
    serialize_ack(&a, &mut bytes);
    assert_eq!(bytes[0], 0xee);
    let bytes = &bytes[1..];
    assert_eq!(bytes[0], 0x03);
    let mut tail = bytes[1..].to_vec();
    tail.push(0x99);
    assert_eq!(parse_ack(bytes[0] as u64, &tail), Ok((a, bytes.len() - 1)));

    let b = ack(1000, 25, 3, vec![(0, 0), (10, 5)]);
    let mut bytes = vec![];
    serialize_ack(&b, &mut bytes);
    assert_eq!(bytes[0], 0x02);
    assert_eq!(parse_ack(2, &bytes[1..]), Ok((b, bytes.len() - 1)));
}

const VMAX: u64 = (1 << 62) - 1;
const M: [u8; 8] = [0xff; 8];

#[test]
fn ack_edges() {
    let fee = Err(FRAME_ENCODING_ERROR);
    // Largest, delay and first range all 2^62-1 in 8-byte varints: smallest is 0.
    let b = [&M[..], &M, &[0], &M].concat();
    assert_eq!(parse_ack(2, &b), Ok((ack(VMAX, VMAX, VMAX, vec![]), 25)));
    // Gap 2^62-1 at smallest 2^62-1: the u64 `gap + 2` guard must reject, not wrap.
    let b = [&M[..], &[0, 1, 0], &M, &[0]].concat();
    assert_eq!(parse_ack(2, &b), fee);
    // Gap 2^62-3 at smallest 2^62-1: next largest is 0, so length 0 is fine and 1 is not.
    let g = [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfd];
    let b = [&M[..], &[0, 1, 0], &g, &[0]].concat();
    assert_eq!(parse_ack(2, &b), Ok((ack(VMAX, 0, 0, vec![(VMAX - 2, 0)]), 20)));
    let b = [&M[..], &[0, 1, 0], &g, &[1]].concat();
    assert_eq!(parse_ack(2, &b), fee);
    // gap + 2 == smallest is accepted (next largest 0); one more is negative.
    assert_eq!(parse_ack(2, &[10, 0, 1, 0, 8, 0]), Ok((ack(10, 0, 0, vec![(8, 0)]), 6)));
    assert_eq!(parse_ack(2, &[10, 0, 1, 0, 9, 0]), fee);
    // Non-minimal varints are accepted (§16); consumed counts the encoded bytes.
    let b = [0x40, 5, 0x80, 0, 0, 0, 0, 0x40, 2];
    assert_eq!(parse_ack(2, &b), Ok((ack(5, 0, 2, vec![]), 9)));
}
