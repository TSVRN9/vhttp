use h3::codes::*;
use h3::frame::*;

fn hdr(ty: u64, len: u64, hdr_len: usize) -> FrameHeader {
    FrameHeader::Complete { ty, len, hdr_len }
}

#[test]
fn header_incomplete_vs_complete() {
    assert_eq!(parse_frame_header(&[]), FrameHeader::Incomplete);
    assert_eq!(parse_frame_header(&[0x40]), FrameHeader::Incomplete);
    assert_eq!(parse_frame_header(&[0x04, 0x00]), hdr(4, 0, 2));
    assert_eq!(parse_frame_header(&[0x40, 0x04, 0x00]), hdr(4, 0, 3));
}

#[test]
fn frame_layout_errors() {
    assert_eq!(parse_frame_payload(FRAME_GOAWAY, &[0x04, 0x00]), Err(H3_FRAME_ERROR));
    assert_eq!(parse_frame_payload(FRAME_GOAWAY, &[0x40]), Err(H3_FRAME_ERROR));
    assert_eq!(parse_frame_payload(FRAME_SETTINGS, &[0x06]), Err(H3_FRAME_ERROR));
}

#[test]
fn settings_rules() {
    assert_eq!(
        parse_frame_payload(FRAME_SETTINGS, &[0x06, 0x44, 0x00]),
        Ok(Frame::Settings(vec![(6, 0x400)]))
    );
    assert_eq!(
        parse_frame_payload(FRAME_SETTINGS, &[0x06, 0x01, 0x06, 0x02]),
        Err(H3_SETTINGS_ERROR)
    );
    assert_eq!(parse_frame_payload(FRAME_SETTINGS, &[0x02, 0x00]), Err(H3_SETTINGS_ERROR));
    assert_eq!(
        parse_frame_payload(FRAME_SETTINGS, &[0x00, 0x05]),
        Ok(Frame::Settings(vec![(0, 5)]))
    );
    assert!(parse_frame_payload(FRAME_SETTINGS, &[0x21, 0x07]).is_ok());
}

#[test]
fn frame_types() {
    assert_eq!(parse_frame_payload(0x02, &[]), Ok(Frame::H2Reserved(2)));
    assert_eq!(parse_frame_payload(0x21, &[1, 2]), Ok(Frame::Unknown(0x21)));
    assert_eq!(
        parse_frame_payload(FRAME_PUSH_PROMISE, &[0x00, 0xAB]),
        Ok(Frame::PushPromise { push_id: 0, field_section: vec![0xAB] })
    );
}

fn split(buf: &[u8]) -> (u64, Vec<u8>) {
    match parse_frame_header(buf) {
        FrameHeader::Complete { ty, len, hdr_len } => {
            assert_eq!(buf.len(), hdr_len + len as usize);
            (ty, buf[hdr_len..].to_vec())
        }
        FrameHeader::Incomplete => panic!("incomplete"),
    }
}

#[test]
fn roundtrip_send_frames() {
    let s = [(1u64, 0u64), (7, 0)];
    let mut out = Vec::new();
    serialize_settings(&s, &mut out);
    let (ty, p) = split(&out);
    assert_eq!(parse_frame_payload(ty, &p), Ok(Frame::Settings(s.to_vec())));

    let mut out = Vec::new();
    serialize_goaway(4, &mut out);
    let (ty, p) = split(&out);
    assert_eq!(parse_frame_payload(ty, &p), Ok(Frame::Goaway(4)));

    let mut out = Vec::new();
    serialize_frame_header(0x1234, 70000, &mut out);
    assert_eq!(parse_frame_header(&out), hdr(0x1234, 70000, out.len()));
}
