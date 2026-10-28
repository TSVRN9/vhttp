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
    let (a, n) = parse_ack(3, &[0, 0, 0, 0, 1, 2, 3]).unwrap();
    assert_eq!(a.ecn, Some((1, 2, 3)));
    assert_eq!(n, 7);
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
