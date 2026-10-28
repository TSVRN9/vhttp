use h3::codes::*;
use h3::qpack::instructions::*;

#[test]
fn b2_rejected() {
    assert_eq!(process_encoder_stream(&[0x3f, 0xbd, 0x01]), Err(QPACK_ENCODER_STREAM_ERROR));
    assert_eq!(process_decoder_stream(&[0x84]), Err(QPACK_DECODER_STREAM_ERROR));
}

#[test]
fn capacity_zero_ok() {
    assert_eq!(process_encoder_stream(&[0x20]), Ok(1));
    assert_eq!(process_encoder_stream(&[]), Ok(0));
    assert_eq!(process_encoder_stream(&[0x20, 0x20]), Ok(2));
}

#[test]
fn partial_kept() {
    assert_eq!(process_encoder_stream(&[0x20, 0x3f]), Ok(1));
    assert_eq!(process_decoder_stream(&[0x44, 0x7f, 0x80]), Ok(1));
}

#[test]
fn stream_cancel_ok() {
    assert_eq!(process_decoder_stream(&[0x44]), Ok(1));
    assert_eq!(process_decoder_stream(&[0x44, 0x7f, 0x01, 0x40]), Ok(4));
}

#[test]
fn insert_count_increment_rejected() {
    assert_eq!(process_decoder_stream(&[0x01]), Err(QPACK_DECODER_STREAM_ERROR));
    assert_eq!(process_decoder_stream(&[0x44, 0x00]), Err(QPACK_DECODER_STREAM_ERROR));
}

#[test]
fn insert_rejected() {
    assert_eq!(process_encoder_stream(&[0xc0, 0x00]), Err(QPACK_ENCODER_STREAM_ERROR));
    assert_eq!(process_encoder_stream(&[0x40]), Err(QPACK_ENCODER_STREAM_ERROR));
    assert_eq!(process_encoder_stream(&[0x20, 0x80]), Err(QPACK_ENCODER_STREAM_ERROR));
}

#[test]
fn duplicate_rejected() {
    assert_eq!(process_encoder_stream(&[0x00]), Err(QPACK_ENCODER_STREAM_ERROR));
}

#[test]
fn too_large_rejected() {
    let mut b = vec![0x3f];
    b.extend([0xff; 10]);
    b.push(0x7f);
    assert_eq!(process_encoder_stream(&b), Err(QPACK_ENCODER_STREAM_ERROR));
    let mut d = vec![0x7f];
    d.extend([0xff; 10]);
    d.push(0x7f);
    assert_eq!(process_decoder_stream(&d), Err(QPACK_DECODER_STREAM_ERROR));
}
