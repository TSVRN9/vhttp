use h3::codes::*;
use h3::uni::*;

fn fresh() -> SeenUni {
    SeenUni { control: false, encoder: false, decoder: false }
}

fn run_with(bytes: &[u8], fin: bool, seen: &mut SeenUni) -> (Result<(), u64>, Vec<UniEvent>) {
    let mut s = UniStream::new();
    let mut ev = Vec::new();
    let r = s.on_data(bytes, fin, seen, &mut ev);
    (r, ev)
}

fn run(bytes: &[u8], fin: bool) -> (Result<(), u64>, Vec<UniEvent>) {
    run_with(bytes, fin, &mut fresh())
}

#[test]
fn control_rules() {
    let mut seen = fresh();
    assert_eq!(
        run_with(&[0x00, 0x04, 0x00], false, &mut seen),
        (Ok(()), vec![UniEvent::PeerSettings(vec![])])
    );
    assert!(seen.control && !seen.encoder && !seen.decoder);
    assert_eq!(run(&[0x00, 0x07, 0x01, 0x00], false).0, Err(H3_MISSING_SETTINGS));
    assert_eq!(run(&[0x00, 0x04, 0x00, 0x04, 0x00], false).0, Err(H3_FRAME_UNEXPECTED));
    assert_eq!(run(&[0x00, 0x04, 0x00, 0x00, 0x00], false).0, Err(H3_FRAME_UNEXPECTED));
    assert_eq!(run(&[0x00, 0x04, 0x00, 0x03, 0x01, 0x00], false).0, Err(H3_ID_ERROR));
    assert_eq!(
        run(&[0x00, 0x04, 0x00, 0x0d, 0x01, 0x05, 0x0d, 0x01, 0x03], false),
        (
            Err(H3_ID_ERROR),
            vec![UniEvent::PeerSettings(vec![]), UniEvent::PeerMaxPushId(5)]
        )
    );
    assert_eq!(run(&[0x00, 0x04, 0x00], true).0, Err(H3_CLOSED_CRITICAL_STREAM));
    let mut seen = fresh();
    seen.control = true;
    assert_eq!(run_with(&[0x00, 0x04, 0x00], false, &mut seen).0, Err(H3_STREAM_CREATION_ERROR));
}

#[test]
fn control_rejects_from_header_alone() {
    // HEADERS, PUSH_PROMISE, HTTP/2-reserved 0x02: rejected before any payload arrives.
    for ty in [0x01u8, 0x05, 0x02] {
        assert_eq!(run(&[0x00, 0x04, 0x00, ty, 0x05], false).0, Err(H3_FRAME_UNEXPECTED));
    }
    // GOAWAY 8 then 9.
    assert_eq!(
        run(&[0x00, 0x04, 0x00, 0x07, 0x01, 0x08, 0x07, 0x01, 0x09], false),
        (Err(H3_ID_ERROR), vec![UniEvent::PeerSettings(vec![]), UniEvent::PeerGoaway(8)])
    );
    // Unknown frame announcing 16385 bytes; SETTINGS announcing 1025 bytes.
    assert_eq!(
        run(&[0x00, 0x04, 0x00, 0x21, 0x80, 0x00, 0x40, 0x01], false).0,
        Err(H3_EXCESSIVE_LOAD)
    );
    assert_eq!(run(&[0x00, 0x04, 0x44, 0x01], false).0, Err(H3_EXCESSIVE_LOAD));
    // Malformed SETTINGS payload passes the frame codec's error through.
    assert_eq!(run(&[0x00, 0x04, 0x01, 0x06], false).0, Err(H3_FRAME_ERROR));
}

#[test]
fn stream_types() {
    assert_eq!(run(&[0x01], false).0, Err(H3_STREAM_CREATION_ERROR));
    let mut s = UniStream::new();
    let mut ev = Vec::new();
    let mut seen = fresh();
    assert_eq!(s.on_data(&[0x21, 0xff, 0xff], false, &mut seen, &mut ev), Ok(()));
    assert_eq!(s.on_data(&[0x00, 0x07, 0x09], true, &mut seen, &mut ev), Ok(()));
    assert!(ev.is_empty() && !seen.control);
    let mut seen = fresh();
    assert_eq!(run_with(&[0x02, 0x20], false, &mut seen).0, Ok(()));
    assert!(seen.encoder);
    assert_eq!(run_with(&[0x02], false, &mut seen).0, Err(H3_STREAM_CREATION_ERROR));
    assert_eq!(run(&[0x02, 0x3f, 0xbd, 0x01], false).0, Err(QPACK_ENCODER_STREAM_ERROR));
    let mut s = UniStream::new();
    let mut seen = fresh();
    assert_eq!(s.on_data(&[0x03], false, &mut seen, &mut ev), Ok(()));
    assert!(seen.decoder);
    assert_eq!(s.on_data(&[], true, &mut seen, &mut ev), Err(H3_CLOSED_CRITICAL_STREAM));
    // A stream closed before its type arrives is not an error.
    assert_eq!(run(&[], true).0, Ok(()));
    assert_eq!(run(&[0x40], true).0, Ok(()));
}

#[test]
fn chunking() {
    let stream = [
        0x00, // control
        0x04, 0x04, 0x06, 0x01, 0x21, 0x00, // SETTINGS [(6, 1), (0x21, 0)]
        0x21, 0x03, 0xaa, 0xbb, 0xcc, // unknown frame 0x21, 3 bytes
        0x07, 0x01, 0x08, // GOAWAY 8
    ];
    let want = vec![UniEvent::PeerSettings(vec![(6, 1), (0x21, 0)]), UniEvent::PeerGoaway(8)];
    assert_eq!(run(&stream, false), (Ok(()), want));
    let mut s = UniStream::new();
    let mut ev = Vec::new();
    let mut seen = fresh();
    for b in stream.iter() {
        assert_eq!(s.on_data(&[*b], false, &mut seen, &mut ev), Ok(()));
    }
    assert_eq!(ev, run(&stream, false).1);
    // Encoder stream split mid-instruction (0x3f 0xe1 0x1f is capacity 4000 > 0).
    let mut s = UniStream::new();
    let mut seen = fresh();
    assert_eq!(s.on_data(&[0x02, 0x20, 0x3f], false, &mut seen, &mut ev), Ok(()));
    assert_eq!(s.on_data(&[0xe1], false, &mut seen, &mut ev), Ok(()));
    assert_eq!(s.on_data(&[0x1f], false, &mut seen, &mut ev), Err(QPACK_ENCODER_STREAM_ERROR));
}
