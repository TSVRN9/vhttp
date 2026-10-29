use quic::codes::STREAM_LIMIT_ERROR;
use quic::stream_id::*;

const SLE: u64 = STREAM_LIMIT_ERROR;

#[test]
fn kinds() {
    use StreamKind::*;
    let ids = [0u64, 1, 2, 3, 7, (1 << 62) - 1];
    let want = [ClientBidi, ServerBidi, ClientUni, ServerUni, ServerUni, ServerUni];
    for (id, k) in ids.iter().zip(want) {
        assert_eq!(stream_kind(*id), k, "id {id}");
    }
}

#[test]
fn peer_open_implicit() {
    let mut s = StreamIds::new(10, 3, 1);
    assert_eq!(s.on_peer_stream(8), Ok(Opened::New { first: 0, count: 3 }));
    assert_eq!(s.on_peer_stream(4), Ok(Opened::Existing));
    assert_eq!(s.on_peer_stream(12), Ok(Opened::New { first: 12, count: 1 }));
}

#[test]
fn peer_limit() {
    let mut s = StreamIds::new(10, 3, 1);
    assert_eq!(s.on_peer_stream(10), Ok(Opened::New { first: 2, count: 3 }));
    assert_eq!(s.on_peer_stream(14), Err(SLE));
    assert_eq!(s.on_peer_stream((1 << 62) - 2), Err(SLE));
}

#[test]
fn max_streams_on_close() {
    let mut s = StreamIds::new(4, 3, 1);
    assert_eq!(s.on_peer_stream(12), Ok(Opened::New { first: 0, count: 4 }));
    s.on_peer_closed(true);
    s.on_peer_closed(true);
    assert_eq!(s.pending_max_streams(true), None);
    s.on_peer_closed(true);
    assert_eq!(s.pending_max_streams(true), Some(7));
    // Not committed yet, so the limit as sent is still 4.
    assert_eq!(s.on_peer_stream(16), Err(SLE));
    s.commit_max_streams(true);
    assert_eq!(s.on_peer_stream(24), Ok(Opened::New { first: 16, count: 3 }));
    assert_eq!(s.on_peer_stream(28), Err(SLE));
}

#[test]
fn local_uni() {
    let mut s = StreamIds::new(10, 3, 1);
    assert!(!s.open_local_uni(7));
    assert!(s.open_local_uni(3));
    assert!(!s.open_local_uni(3));
    assert!(!s.open_local_uni(7));
    s.on_max_streams(false, 2);
    assert!(s.open_local_uni(7));
    s.on_max_streams(false, 1);
    assert_eq!(s.local_uni_limit(), 2);
    assert!(s.local_uni_created(3));
    assert!(s.local_uni_created(7));
    assert!(!s.local_uni_created(11));
}

#[test]
fn stream_limit_edges() {
    let mut s = StreamIds::new(1 << 60, 1 << 60, 0);
    assert_eq!(s.on_peer_stream((1 << 62) - 4), Ok(Opened::New { first: 0, count: 1 << 60 }));
    s.on_max_streams(false, 1 << 60);
    assert_eq!(s.local_uni_limit(), 1 << 60);
    assert!(s.open_local_uni(3));
}
