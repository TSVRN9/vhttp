//! Phase 3d handshake connection IDs (RFC 9000 §7.2-7.3), our transport parameters, tokens
//! (§8.1.3) and ALPN (§7).
use quic::codes::TRANSPORT_PARAMETER_ERROR;
use quic::handshake::*;
use quic::payload::PacketKind;
use quic::tp::*;

const TPE: u64 = TRANSPORT_PARAMETER_ERROR;
const S1: [u8; 8] = [0x83, 0x94, 0xc8, 0xf0, 0x3e, 0x51, 0x57, 0x08];
const C1: [u8; 8] = [0xc1; 8];
const L: [u8; 8] = [0x5a; 8];

fn hex(s: &str) -> Vec<u8> {
    let s: String = s.split_whitespace().collect();
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

fn ltp() -> TransportParams {
    TransportParams {
        initial_max_streams_bidi: 10,
        initial_max_streams_uni: 3,
        active_connection_id_limit: 2,
        disable_active_migration: true,
        ..default_transport_params()
    }
}

fn ids() -> HandshakeIds {
    from_first(PacketKind::Initial, &S1, &C1, L).unwrap()
}

#[test]
fn from_first_ids() {
    let h = ids();
    assert_eq!(h.odcid(), &S1[..]);
    assert_eq!(h.client_scid(), &C1[..]);
    assert_eq!(h.local_scid(), L);
    assert_eq!(from_first(PacketKind::Initial, &S1[..7], &C1, L), None);
    assert_eq!(from_first(PacketKind::Handshake, &S1, &C1, L), None);
    assert_eq!(from_first(PacketKind::OneRtt, &S1, &C1, L), None);
    assert_eq!(from_first(PacketKind::Initial, &[7; 21], &C1, L), None);
    assert_eq!(from_first(PacketKind::Initial, &S1, &[7; 21], L), None);
    assert!(from_first(PacketKind::Initial, &[7; 20], &[7; 20], L).is_some());
    let h = from_first(PacketKind::Initial, &S1, &[], L).unwrap();
    assert_eq!(h.client_scid(), &[] as &[u8]);
}

#[test]
fn later_initial_scid() {
    let h = ids();
    assert!(h.initial_scid_ok(&C1));
    assert!(!h.initial_scid_ok(&[0xc2; 8]));
    assert!(!h.initial_scid_ok(&[]));
}

#[test]
fn fill_local_tp_sets_ids() {
    let r = ids().fill_local_tp(&ltp(), [0x11; 16]);
    assert_eq!(r.original_destination_connection_id, Some(S1.to_vec()));
    assert_eq!(r.initial_source_connection_id, Some(L.to_vec()));
    assert_eq!(r.stateless_reset_token, Some([0x11; 16]));
    let want = TransportParams {
        original_destination_connection_id: Some(S1.to_vec()),
        initial_source_connection_id: Some(L.to_vec()),
        stateless_reset_token: Some([0x11; 16]),
        ..ltp()
    };
    assert_eq!(r, want);
    let mut out = Vec::new();
    serialize_server_params(&r, &mut out);
    let head = [&hex("0008 8394c8f03e515708 0f08 5a5a5a5a5a5a5a5a 0210")[..], &[0x11; 16][..]].concat();
    assert!(out.starts_with(&head), "{out:02x?}");
    assert!(is_local_tp_ok(&r));
}

#[test]
fn local_tp_rules() {
    assert!(is_local_tp_ok(&ltp()));
    assert!(!is_local_tp_ok(&TransportParams { initial_max_streams_uni: 2, ..ltp() }));
    assert!(!is_local_tp_ok(&TransportParams { initial_max_streams_uni: 101, ..ltp() }));
    assert!(!is_local_tp_ok(&TransportParams { initial_max_streams_bidi: 101, ..ltp() }));
    assert!(!is_local_tp_ok(&TransportParams { active_connection_id_limit: 9, ..ltp() }));
    assert!(!is_local_tp_ok(&TransportParams { disable_active_migration: false, ..ltp() }));
    // The edges are accepted.
    assert!(is_local_tp_ok(&TransportParams {
        initial_max_streams_uni: 100,
        initial_max_streams_bidi: 100,
        active_connection_id_limit: 8,
        ..ltp()
    }));
    // server_tp_wf's own bounds.
    assert!(!is_local_tp_ok(&TransportParams { max_udp_payload_size: 1199, ..ltp() }));
    assert!(!is_local_tp_ok(&TransportParams { ack_delay_exponent: 21, ..ltp() }));
    assert!(!is_local_tp_ok(&TransportParams { max_ack_delay: 1 << 14, ..ltp() }));
    assert!(!is_local_tp_ok(&TransportParams { initial_max_data: 1 << 62, ..ltp() }));
}

#[test]
fn peer_tp_check() {
    let h = ids();
    let with = |c: Option<Vec<u8>>| TransportParams { initial_source_connection_id: c, ..default_transport_params() };
    assert_eq!(h.check_peer_tp(&with(Some(C1.to_vec()))), Ok(()));
    assert_eq!(h.check_peer_tp(&with(None)), Err(TPE));
    assert_eq!(h.check_peer_tp(&with(Some(vec![0xc2; 8]))), Err(TPE));
    assert_eq!(h.check_peer_tp(&with(Some(vec![]))), Err(TPE));
    // An empty client SCID needs an empty initial_source_connection_id (§7.3).
    let e = from_first(PacketKind::Initial, &S1, &[], L).unwrap();
    assert_eq!(e.check_peer_tp(&with(Some(vec![]))), Ok(()));
    assert_eq!(e.check_peer_tp(&with(None)), Err(TPE));
}

/// RFC 9001 §A.2: the client's Initial has DCID 8394c8f03e515708 and an empty SCID, yet its
/// transport parameters carry initial_source_connection_id = 8394c8f03e515708.
#[test]
fn rfc9001_a2_iscid_mismatch() {
    let h = from_first(PacketKind::Initial, &S1, &[], L).unwrap();
    let b = hex("0408ffffffffffffffff 05048000ffff 07048000ffff 080110 010480007530 090110
                 0f088394c8f03e515708 06048000ffff");
    assert_eq!(b.len(), 50);
    let tp = parse_transport_params(&b, true).unwrap();
    assert_eq!(tp.initial_source_connection_id, Some(S1.to_vec()));
    assert_eq!(h.check_peer_tp(&tp), Err(TPE));
}

#[test]
fn token_never_validates() {
    assert!(!token_validates(&[1, 2, 3]));
    assert!(!token_validates(&[]));
}

#[test]
fn alpn() {
    assert_eq!(check_alpn(b"h3"), Ok(()));
    assert_eq!(check_alpn(b"h3-29"), Err(0x178));
    assert_eq!(check_alpn(b""), Err(0x178));
    assert_eq!(check_alpn(b"h"), Err(0x178));
    assert_eq!(check_alpn(b"h2"), Err(0x178));
}
