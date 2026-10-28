use quic::ack::AckFrame;
use quic::codes::{FRAME_ENCODING_ERROR, PROTOCOL_VIOLATION};
use quic::frame::*;

const FEE: u64 = FRAME_ENCODING_ERROR;
const PV: u64 = PROTOCOL_VIOLATION;
const VMAX: u64 = (1 << 62) - 1;

fn stream(stream_id: u64, offset: u64, data: &[u8], fin: bool) -> Frame {
    Frame::Stream { stream_id, offset, data: data.to_vec(), fin }
}

#[test]
fn frame_type_encoding() {
    assert_eq!(parse_frame_type(&[0x01]), Ok((1, 1)));
    assert_eq!(parse_frame_type(&[0x40, 0x01]), Err(PV));
    assert_eq!(parse_frame_type(&[]), Err(FEE));
    assert_eq!(parse_frame_type(&[0x40]), Err(FEE));
    assert_eq!(parse_frame(&[0x1f]), Err(FEE));
    assert_eq!(parse_frame(&[0x7f, 0xff]), Err(FEE));
    // A non-minimal type is PROTOCOL_VIOLATION before the body is looked at.
    assert_eq!(parse_frame(&[0x40, 0x01]), Err(PV));
}

#[test]
fn stream_variants() {
    assert_eq!(parse_frame(&[0x08, 0x04, 0x61, 0x62]), Ok((stream(4, 0, b"ab", false), 4)));
    assert_eq!(
        parse_frame(&[0x0f, 0x04, 0x05, 0x01, 0x61, 0x99]),
        Ok((stream(4, 5, b"a", true), 5))
    );
    assert_eq!(parse_frame(&[0x0a, 0x04, 0x05, 0x61]), Err(FEE));
}

#[test]
fn offset_limit() {
    let m = [0xff; 8];
    let ok = [&[0x0e, 0x00][..], &m, &[0x00]].concat();
    assert_eq!(parse_frame(&ok), Ok((stream(0, VMAX, b"", false), 11)));
    let over = [&[0x0e, 0x00][..], &m, &[0x01, 0x61]].concat();
    assert_eq!(parse_frame(&over), Err(FEE));
    let crypto = [&[0x06][..], &m, &[0x01, 0x61]].concat();
    assert_eq!(parse_frame(&crypto), Err(FEE));
    // Without LEN the data runs to the end, and the same limit applies.
    let nolen = [&[0x0c, 0x00][..], &m, &[0x61]].concat();
    assert_eq!(parse_frame(&nolen), Err(FEE));
    let crypto_ok = [&[0x06][..], &m, &[0x00]].concat();
    assert_eq!(parse_frame(&crypto_ok), Ok((Frame::Crypto { offset: VMAX, data: vec![] }, 10)));
}

#[test]
fn ncid_rules() {
    let b = [&[0x18, 0x01, 0x00, 0x08][..], &[0x11; 8], &[0x22; 16]].concat();
    let want = Frame::NewConnectionId {
        seq: 1,
        retire_prior_to: 0,
        cid: vec![0x11; 8],
        reset_token: [0x22; 16],
    };
    assert_eq!(parse_frame(&b), Ok((want, b.len())));
    let zero = [&[0x18, 0x01, 0x00, 0x00][..], &[0x22; 16]].concat();
    assert_eq!(parse_frame(&zero), Err(FEE));
    let long = [&[0x18, 0x01, 0x00, 21][..], &[0x11; 21], &[0x22; 16]].concat();
    assert_eq!(parse_frame(&long), Err(FEE));
    let rpt = [&[0x18, 0x01, 0x02, 0x08][..], &[0x11; 8], &[0x22; 16]].concat();
    assert_eq!(parse_frame(&rpt), Err(FEE));
    // One token byte short.
    assert_eq!(parse_frame(&b[..b.len() - 1]), Err(FEE));
}

#[test]
fn stream_count_limit() {
    let at = [0x12, 0xd0, 0, 0, 0, 0, 0, 0, 0];
    let over = [0x12, 0xd0, 0, 0, 0, 0, 0, 0, 0x01];
    assert_eq!(parse_frame(&at), Ok((Frame::MaxStreams { bidi: true, max: 1 << 60 }, 9)));
    assert_eq!(parse_frame(&over), Err(FEE));
    let (mut at, mut over) = (at, over);
    at[0] = 0x17;
    over[0] = 0x17;
    assert_eq!(parse_frame(&at), Ok((Frame::StreamsBlocked { bidi: false, max: 1 << 60 }, 9)));
    assert_eq!(parse_frame(&over), Err(FEE));
}

#[test]
fn server_receive_rules() {
    assert_eq!(parse_frame(&[0x07, 0x01, 0xaa]), Err(PV));
    assert_eq!(parse_frame(&[0x1e]), Err(PV));
}

#[test]
fn close_frames() {
    let transport = Frame::ConnectionClose { app: false, error_code: 0x0a, frame_type: 6, reason: b"hi".to_vec() };
    assert_eq!(parse_frame(&[0x1c, 0x0a, 0x06, 0x02, 0x68, 0x69]), Ok((transport, 6)));
    let app = Frame::ConnectionClose { app: true, error_code: 1, frame_type: 0, reason: vec![] };
    assert_eq!(parse_frame(&[0x1d, 0x01, 0x00]), Ok((app, 3)));
    assert_eq!(parse_frame(&[0x1c, 0x00, 0x00, 0x05, 0x68]), Err(FEE));
}

#[test]
fn path_frames() {
    let b = [0x1a, 1, 2, 3, 4, 5, 6, 7, 8];
    assert_eq!(parse_frame(&b), Ok((Frame::PathChallenge([1, 2, 3, 4, 5, 6, 7, 8]), 9)));
    assert_eq!(parse_frame(&b[..8]), Err(FEE));
    let mut r = b;
    r[0] = 0x1b;
    assert_eq!(parse_frame(&r), Ok((Frame::PathResponse([1, 2, 3, 4, 5, 6, 7, 8]), 9)));
}

#[test]
fn small_frames() {
    assert_eq!(parse_frame(&[0x00, 0x01]), Ok((Frame::Padding, 1)));
    assert_eq!(parse_frame(&[0x01]), Ok((Frame::Ping, 1)));
    let rs = Frame::ResetStream { stream_id: 4, error_code: 7, final_size: 0x1234 };
    assert_eq!(parse_frame(&[0x04, 0x04, 0x07, 0x52, 0x34]), Ok((rs, 5)));
    assert_eq!(parse_frame(&[0x04, 0x04, 0x07]), Err(FEE));
    assert_eq!(parse_frame(&[0x05, 0x04, 0x07]), Ok((Frame::StopSending { stream_id: 4, error_code: 7 }, 3)));
    assert_eq!(parse_frame(&[0x10, 0x05]), Ok((Frame::MaxData(5), 2)));
    assert_eq!(parse_frame(&[0x11, 0x04, 0x05]), Ok((Frame::MaxStreamData { stream_id: 4, max: 5 }, 3)));
    assert_eq!(parse_frame(&[0x14, 0x05]), Ok((Frame::DataBlocked(5), 2)));
    assert_eq!(parse_frame(&[0x15, 0x04, 0x05]), Ok((Frame::StreamDataBlocked { stream_id: 4, max: 5 }, 3)));
    assert_eq!(parse_frame(&[0x19, 0x03]), Ok((Frame::RetireConnectionId(3), 2)));
    assert_eq!(parse_frame(&[0x19]), Err(FEE));
    let ack = AckFrame { largest: 5, delay: 0, first_range: 2, ranges: vec![], ecn: None };
    assert_eq!(parse_frame(&[0x02, 0x05, 0x00, 0x00, 0x02]), Ok((Frame::Ack(ack), 5)));
    assert_eq!(parse_frame(&[0x02, 0x02, 0x00, 0x00, 0x03]), Err(FEE));
}

#[test]
fn frame_roundtrip() {
    let all = vec![
        Frame::Padding,
        Frame::Ping,
        Frame::Ack(AckFrame { largest: 1000, delay: 25, first_range: 3, ranges: vec![(0, 0), (10, 5)], ecn: Some((7, 0, 1)) }),
        Frame::Ack(AckFrame { largest: 9, delay: 0, first_range: 9, ranges: vec![], ecn: None }),
        Frame::ResetStream { stream_id: 4, error_code: 7, final_size: VMAX },
        Frame::StopSending { stream_id: 8, error_code: 0x4000 },
        Frame::Crypto { offset: 1 << 30, data: b"hello".to_vec() },
        stream(4, 0, b"ab", false),
        stream(4, 0, b"", true),
        stream(VMAX, 7, b"xyz", false),
        stream(1, VMAX - 1, b"z", true),
        Frame::MaxData(VMAX),
        Frame::MaxStreamData { stream_id: 3, max: 64 },
        Frame::MaxStreams { bidi: true, max: 1 << 60 },
        Frame::MaxStreams { bidi: false, max: 0 },
        Frame::DataBlocked(16384),
        Frame::StreamDataBlocked { stream_id: 2, max: 63 },
        Frame::StreamsBlocked { bidi: true, max: 100 },
        Frame::StreamsBlocked { bidi: false, max: 1 << 60 },
        Frame::NewConnectionId { seq: 5, retire_prior_to: 5, cid: vec![0xab; 20], reset_token: [0x5a; 16] },
        Frame::NewConnectionId { seq: 1, retire_prior_to: 0, cid: vec![0x01], reset_token: [0; 16] },
        Frame::RetireConnectionId(2),
        Frame::PathChallenge([9; 8]),
        Frame::PathResponse([1, 2, 3, 4, 5, 6, 7, 8]),
        Frame::ConnectionClose { app: false, error_code: 0x0a, frame_type: 0x08, reason: b"bad".to_vec() },
        Frame::ConnectionClose { app: true, error_code: 0x101, frame_type: 0, reason: vec![] },
    ];
    for f in all {
        let mut bytes = vec![0xee];
        serialize_frame(&f, &mut bytes);
        assert_eq!(bytes[0], 0xee);
        let mut bytes = bytes[1..].to_vec();
        assert_eq!(bytes[0] as u64, frame_type_of(&f), "{f:?}");
        let n = bytes.len();
        bytes.push(0x01);
        assert_eq!(parse_frame(&bytes), Ok((f, n)));
    }
    let mut out = vec![];
    serialize_frame(&Frame::HandshakeDone, &mut out);
    assert_eq!(out, [0x1e]);
    assert_eq!(frame_type_of(&Frame::HandshakeDone), 0x1e);
    let mut out = vec![];
    serialize_frame(&stream(4, 0, b"ab", false), &mut out);
    assert_eq!(out, [0x0a, 0x04, 0x02, 0x61, 0x62]);
}
