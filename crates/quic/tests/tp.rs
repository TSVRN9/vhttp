use quic::codes::TRANSPORT_PARAMETER_ERROR;
use quic::tp::*;

const TPE: u64 = TRANSPORT_PARAMETER_ERROR;

fn hex(s: &str) -> Vec<u8> {
    let s: String = s.split_whitespace().collect();
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

fn client(b: &[u8]) -> Result<TransportParams, u64> {
    parse_transport_params(b, true)
}

#[test]
fn defaults() {
    let d = default_transport_params();
    assert_eq!(d.original_destination_connection_id, None);
    assert_eq!(d.max_idle_timeout, 0);
    assert_eq!(d.stateless_reset_token, None);
    assert_eq!(d.max_udp_payload_size, 65527);
    assert_eq!(d.initial_max_data, 0);
    assert_eq!(d.initial_max_stream_data_bidi_local, 0);
    assert_eq!(d.initial_max_stream_data_bidi_remote, 0);
    assert_eq!(d.initial_max_stream_data_uni, 0);
    assert_eq!(d.initial_max_streams_bidi, 0);
    assert_eq!(d.initial_max_streams_uni, 0);
    assert_eq!(d.ack_delay_exponent, 3);
    assert_eq!(d.max_ack_delay, 25);
    assert!(!d.disable_active_migration);
    assert_eq!(d.active_connection_id_limit, 2);
    assert_eq!(d.initial_source_connection_id, None);
}

/// RFC 9001 §A.2: the client's quic_transport_parameters extension value.
#[test]
fn rfc9001_a2_client_params() {
    let b = hex("0408ffffffffffffffff 05048000ffff 07048000ffff 080110 010480007530 090110
                 0f088394c8f03e515708 06048000ffff");
    assert_eq!(b.len(), 50);
    let want = TransportParams {
        initial_max_data: 0x3fff_ffff_ffff_ffff,
        initial_max_stream_data_bidi_local: 0xffff,
        initial_max_stream_data_bidi_remote: 0xffff,
        initial_max_stream_data_uni: 0xffff,
        initial_max_streams_bidi: 16,
        initial_max_streams_uni: 16,
        max_idle_timeout: 30000,
        initial_source_connection_id: Some(hex("8394c8f03e515708")),
        ..default_transport_params()
    };
    assert_eq!(client(&b), Ok(want));
}

#[test]
fn tp_errors() {
    let cases: Vec<Vec<u8>> = vec![
        hex("0000"),
        [&hex("0210")[..], &[0u8; 16][..]].concat(),
        hex("0e0101"),
        hex("030244af"),
        hex("0a0115"),
        hex("0b0480004000"),
        hex("0c0100"),
        hex("010100010100"),
        hex("010500"),
        hex("01020000"),
        hex("0808d000000000000001"),
        [&hex("0f15")[..], &[0u8; 21][..]].concat(),
    ];
    for b in &cases {
        assert_eq!(client(b), Err(TPE), "{b:02x?}");
    }
    // A truncated ID or Length.
    assert_eq!(client(&hex("40")), Err(TPE));
    assert_eq!(client(&hex("01")), Err(TPE));
    assert_eq!(client(&hex("0140")), Err(TPE));
    // preferred_address and retry_source_connection_id are errors from either side.
    assert_eq!(client(&hex("0d00")), Err(TPE));
    assert_eq!(client(&hex("1000")), Err(TPE));
    assert_eq!(parse_transport_params(&hex("0d00"), false), Err(TPE));
    assert_eq!(parse_transport_params(&hex("1000"), false), Err(TPE));
    // A duplicate known ID with differing values; uni streams 2^60+1; an empty integer value.
    assert_eq!(client(&hex("0901 00 09088000000000000001")), Err(TPE));
    assert_eq!(client(&hex("0908d000000000000001")), Err(TPE));
    assert_eq!(client(&hex("0e00")), Err(TPE));
}

#[test]
fn tp_accepts() {
    let d = default_transport_params();
    assert_eq!(client(&hex("030244b0")), Ok(TransportParams { max_udp_payload_size: 1200, ..d }));
    let d = default_transport_params();
    assert_eq!(client(&hex("01024000")), Ok(d));
    assert_eq!(client(&hex("1b02aabb")), Ok(default_transport_params()));
    assert_eq!(client(&hex("40ff00")), Ok(default_transport_params()));
    let d = default_transport_params();
    assert_eq!(client(&hex("0c00")), Ok(TransportParams { disable_active_migration: true, ..d }));
    assert_eq!(client(&[]), Ok(default_transport_params()));
    // Unknown IDs may repeat; the value bounds' edges are accepted.
    assert_eq!(client(&hex("1100 1100")), Ok(default_transport_params()));
    let d = default_transport_params();
    let want = TransportParams {
        initial_max_streams_bidi: 1 << 60,
        ack_delay_exponent: 20,
        max_ack_delay: 0x3fff,
        active_connection_id_limit: 2,
        ..d
    };
    assert_eq!(client(&hex("0808d000000000000000 0a0114 0b027fff 0e0102")), Ok(want));
}

fn server_params() -> TransportParams {
    TransportParams {
        original_destination_connection_id: Some(hex("8394c8f03e515708")),
        initial_source_connection_id: Some(hex("f067a5502a4262b5")),
        stateless_reset_token: Some([0x11; 16]),
        max_idle_timeout: 30000,
        initial_max_data: 1048576,
        initial_max_stream_data_bidi_local: 65536,
        initial_max_stream_data_bidi_remote: 65536,
        initial_max_stream_data_uni: 65536,
        initial_max_streams_bidi: 100,
        initial_max_streams_uni: 3,
        disable_active_migration: true,
        active_connection_id_limit: 4,
        ..default_transport_params()
    }
}

#[test]
fn server_params_roundtrip() {
    let p = server_params();
    let mut out = Vec::new();
    serialize_server_params(&p, &mut out);
    let head = [&hex("00088394c8f03e515708 0f08f067a5502a4262b5 0210")[..], &[0x11; 16][..]].concat();
    assert_eq!(out[..head.len()], head[..]);
    // Then 0x01, 0x03-0x0b, 0x0c and 0x0e, every integer written even at its default.
    let rest = hex("010480007530 03048000fff7 040480100000 050480010000 060480010000
                    070480010000 08024064 090103 0a0103 0b0119 0c00 0e0104");
    assert_eq!(out[head.len()..], rest[..]);
    assert_eq!(parse_transport_params(&out, false), Ok(server_params()));
    assert_eq!(parse_transport_params(&out, true), Err(TPE));
    // Within 4a's EncryptedExtensions budget, and allows HTTP/3's three peer uni streams.
    assert!(out.len() <= 1024);
    assert!(p.initial_max_streams_uni >= 3);
}
