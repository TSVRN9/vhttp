use byteq::capvec::CapVec;
use h3::codes::*;
use h3::uni::*;

fn fresh() -> SeenUni {
    SeenUni { control: false, encoder: false, decoder: false }
}

fn run_with(bytes: &[u8], fin: bool, seen: &mut SeenUni) -> (Result<(), u64>, Vec<UniEvent>) {
    let mut s = UniStream::new();
    let mut ev = CapVec::new(bytes.len() / 3 + 1);
    let r = s.on_data(bytes, fin, seen, &mut ev).0;
    (r, ev.into_vec())
}

/// Room for every event of a multi-call test (each call needs `d / 3 + 1` free).
fn evs() -> CapVec<UniEvent> {
    CapVec::new(4096)
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
    // SETTINGS announcing 1025 bytes; GOAWAY announcing 9 (a varint is at most 8).
    assert_eq!(run(&[0x00, 0x04, 0x44, 0x01], false).0, Err(H3_EXCESSIVE_LOAD));
    assert_eq!(run(&[0x00, 0x04, 0x00, 0x07, 0x09], false).0, Err(H3_FRAME_ERROR));
    // Malformed SETTINGS payload passes the frame codec's error through.
    assert_eq!(run(&[0x00, 0x04, 0x01, 0x06], false).0, Err(H3_FRAME_ERROR));
}

#[test]
fn stream_types() {
    assert_eq!(run(&[0x01], false).0, Err(H3_STREAM_CREATION_ERROR));
    let mut s = UniStream::new();
    let mut ev = evs();
    let mut seen = fresh();
    assert_eq!(s.on_data(&[0x21, 0xff, 0xff], false, &mut seen, &mut ev).0, Ok(()));
    assert_eq!(s.on_data(&[0x00, 0x07, 0x09], true, &mut seen, &mut ev).0, Ok(()));
    assert!(ev.len() == 0 && !seen.control);
    let mut seen = fresh();
    assert_eq!(run_with(&[0x02, 0x20], false, &mut seen).0, Ok(()));
    assert!(seen.encoder);
    assert_eq!(run_with(&[0x02], false, &mut seen).0, Err(H3_STREAM_CREATION_ERROR));
    assert_eq!(run(&[0x02, 0x3f, 0xbd, 0x01], false).0, Err(QPACK_ENCODER_STREAM_ERROR));
    let mut s = UniStream::new();
    let mut seen = fresh();
    assert_eq!(s.on_data(&[0x03], false, &mut seen, &mut ev).0, Ok(()));
    assert!(seen.decoder);
    assert_eq!(s.on_data(&[], true, &mut seen, &mut ev).0, Err(H3_CLOSED_CRITICAL_STREAM));
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
    let mut ev = evs();
    let mut seen = fresh();
    for b in stream.iter() {
        assert_eq!(s.on_data(&[*b], false, &mut seen, &mut ev).0, Ok(()));
    }
    assert_eq!(ev.as_slice(), &run(&stream, false).1[..]);
    // Encoder stream split mid-instruction (0x3f 0xe1 0x1f is capacity 4000 > 0).
    let mut s = UniStream::new();
    let mut seen = fresh();
    assert_eq!(s.on_data(&[0x02, 0x20, 0x3f], false, &mut seen, &mut ev).0, Ok(()));
    assert_eq!(s.on_data(&[0xe1], false, &mut seen, &mut ev).0, Ok(()));
    assert_eq!(s.on_data(&[0x1f], false, &mut seen, &mut ev).0, Err(QPACK_ENCODER_STREAM_ERROR));
}

#[test]
fn large_unknown_frame_skipped() {
    // SETTINGS, unknown frame 0x21 of 16385 bytes, GOAWAY 8.
    let mut stream = vec![0x00, 0x04, 0x00, 0x21, 0x80, 0x00, 0x40, 0x01];
    stream.extend(std::iter::repeat(0xab).take(16385));
    stream.extend([0x07, 0x01, 0x08]);
    let want = || vec![UniEvent::PeerSettings(vec![]), UniEvent::PeerGoaway(8)];
    assert_eq!(run(&stream, false), (Ok(()), want()));
    for size in [1000, 1, 7] {
        let mut s = UniStream::new();
        let mut ev = evs();
        let mut seen = fresh();
        for c in stream.chunks(size) {
            assert_eq!(s.on_data(c, false, &mut seen, &mut ev).0, Ok(()));
        }
        assert_eq!(ev.as_slice(), &want()[..]);
    }
    // A FIN while skipping is still a closed critical stream.
    assert_eq!(run(&stream[..100], true).0, Err(H3_CLOSED_CRITICAL_STREAM));
}

#[test]
fn qpack_instruction_split_frees() {
    // A decoder-stream Stream Cancellation (0x7F, then continuation bytes) cut across calls: the queue holds the
    // incomplete instruction only, and frees both buffers once it completes.
    let mut s = UniStream::new();
    let mut seen = fresh();
    let mut ev = evs();
    assert_eq!(s.on_data(&[0x03, 0x7F], false, &mut seen, &mut ev).0, Ok(()));
    assert_eq!(s.buffered_len(), 1);
    assert_eq!(s.on_data(&[0x80], false, &mut seen, &mut ev).0, Ok(()));
    assert_eq!(s.buffered_len(), 2);
    assert_eq!(s.on_data(&[0x01, 0x7F], false, &mut seen, &mut ev).0, Ok(()));
    assert_eq!(s.buffered_len(), 1);
    assert_eq!(s.on_data(&[0x05], false, &mut seen, &mut ev).0, Ok(()));
    // Both buffers are freed: UniStream's wf holds its queue's, which proves an empty queue holds none (ByteQueue::lemma_wf).
    assert_eq!(s.buffered_len(), 0);
    // The longest incomplete instruction: 0x7F and 10 continuation bytes, one per call, 11 held; an 11th is too large.
    let mut s = UniStream::new();
    let mut seen = fresh();
    assert_eq!(s.on_data(&[0x03, 0x7F], false, &mut seen, &mut ev).0, Ok(()));
    for i in 0..10 {
        assert_eq!(s.on_data(&[0x80], false, &mut seen, &mut ev).0, Ok(()));
        assert_eq!(s.buffered_len(), i + 2);
    }
    assert_eq!(s.on_data(&[0x00], false, &mut seen, &mut ev).0, Err(QPACK_DECODER_STREAM_ERROR));
    assert!(ev.len() == 0);
}
