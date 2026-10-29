//! Phase 3d connection IDs: our issued CIDs (limits, uniqueness, RETIRE_CONNECTION_ID rules)
//! and the peer's CIDs (NEW_CONNECTION_ID semantics, Retire Prior To, limits, reset tokens).
use quic::cid::*;
use quic::codes::{CONNECTION_ID_LIMIT_ERROR, PROTOCOL_VIOLATION};
use quic::frame::Frame;

#[allow(non_snake_case)]
fn T(x: u8) -> [u8; 16] {
    [x; 16]
}

#[allow(non_snake_case)]
fn R(x: u8) -> [u8; 24] {
    [x; 24]
}

const A: [u8; 8] = [0xa1; 8];
const B: [u8; 8] = [0xb1; 8];

fn local() -> LocalCids {
    LocalCids::new([0xa0; 8], T(0xb0))
}

fn peer() -> PeerCids {
    PeerCids::new(&[0xc0; 8])
}

#[allow(non_snake_case)]
fn N(p: &mut PeerCids, seq: u64, rpt: u64, cid: &[u8], tok: [u8; 16]) -> Result<(), u64> {
    p.on_new_cid(seq, rpt, cid, tok, 2)
}

fn ncid(seq: u64, x: u8) -> Frame {
    Frame::NewConnectionId { seq, retire_prior_to: 0, cid: vec![x; 8], reset_token: T(x) }
}

/// Sends every pending NEW_CONNECTION_ID frame.
fn send_all(l: &mut LocalCids) -> Vec<Frame> {
    let mut v = Vec::new();
    while let Some(f) = l.pending_frame() {
        v.push(f);
        l.commit_pending();
    }
    v
}

/// Commits every pending RETIRE_CONNECTION_ID frame and returns their sequence numbers.
fn retires(p: &mut PeerCids) -> Vec<u64> {
    let mut v = Vec::new();
    while let Some(f) = p.pending_retire() {
        match f {
            Frame::RetireConnectionId(s) => v.push(s),
            _ => panic!("not a RETIRE_CONNECTION_ID"),
        }
        p.commit_retire();
    }
    v
}

fn seqs_active(p: &PeerCids, cids: &[[u8; 8]]) -> Vec<bool> {
    cids.iter().map(|c| p.is_active(c)).collect()
}

#[test]
fn issue_sequence() {
    let mut l = local();
    assert_eq!(l.active_len(), 1);
    assert!(l.issue(&R(1), 4));
    assert_eq!(l.pending_frame(), Some(ncid(1, 1)));
    assert!(l.issue(&R(2), 4));
    assert!(l.issue(&R(3), 4));
    assert!(!l.issue(&R(4), 4));
    assert_eq!(l.active_len(), 4);
    assert_eq!(send_all(&mut l), vec![ncid(1, 1), ncid(2, 2), ncid(3, 3)]);
    let mut l = local();
    assert!(l.issue(&R(1), 2));
    assert!(!l.issue(&R(2), 2));
    // ISSUE_CAP_ACTIVE binds even when the peer allows more.
    let mut l = local();
    for x in 1..=3 {
        assert!(l.issue(&R(x), 8));
    }
    assert!(!l.issue(&R(4), 8));
}

#[test]
fn no_reissue() {
    let mut l = local();
    let mut r = [9u8; 24];
    r[..8].copy_from_slice(&[0xa0; 8]);
    assert!(!l.issue(&r, 4));
    let mut r = [0xb0u8; 24];
    r[..8].copy_from_slice(&[9; 8]);
    assert!(!l.issue(&r, 4));
    assert!(l.issue(&R(1), 4));
    assert_eq!(l.seq_of(&[1; 8]), Some(1));
    assert_eq!(l.seq_of(&[0xa0; 8]), Some(0));
    assert_eq!(l.seq_of(&[9; 8]), None);
}

#[test]
fn retire_rules() {
    let mut l = local();
    assert!(l.issue(&R(1), 4));
    assert!(l.issue(&R(2), 4));
    // Issued but never sent (preflight I3).
    assert_eq!(l.on_retire(2, &[0xff; 8]), Err(PROTOCOL_VIOLATION));
    assert_eq!(l.on_retire(1, &[0xff; 8]), Err(PROTOCOL_VIOLATION));
    assert_eq!(send_all(&mut l).len(), 2);
    assert_eq!(l.on_retire(5, &[0xff; 8]), Err(PROTOCOL_VIOLATION));
    assert_eq!(l.on_retire(1, &[1; 8]), Err(PROTOCOL_VIOLATION));
    assert!(l.is_active(&[1; 8]));
    assert_eq!(l.on_retire(1, &[0xa0; 8]), Ok(Some([1; 8])));
    assert_eq!(l.on_retire(1, &[0xa0; 8]), Ok(None));
    assert!(!l.is_active(&[1; 8]));
    assert!(l.is_active(&[2; 8]));
    assert!(l.is_active(&[0xa0; 8]));
    assert_eq!(l.active_len(), 2);
}

#[test]
fn lifetime_cap() {
    let mut l = local();
    for s in 1..=15u8 {
        assert!(l.issue(&R(s), 4), "issue {s}");
        assert_eq!(send_all(&mut l), vec![ncid(s as u64, s)]);
        assert_eq!(l.on_retire(s as u64, &[0xa0; 8]), Ok(Some([s; 8])));
    }
    assert!(!l.issue(&R(16), 4));
    assert_eq!(l.active_len(), 1);
}

#[test]
fn lost_frame_repends_once() {
    let mut l = local();
    assert!(l.issue(&R(1), 4));
    assert_eq!(send_all(&mut l).len(), 1);
    l.on_frame_lost(1);
    l.on_frame_lost(1);
    l.on_frame_lost(0);
    assert_eq!(send_all(&mut l), vec![ncid(1, 1)]);
    assert_eq!(l.on_retire(1, &[0xa0; 8]), Ok(Some([1; 8])));
    l.on_frame_lost(1);
    assert_eq!(l.pending_frame(), None);
    // A pending frame whose CID the peer retires is never sent.
    assert!(l.issue(&R(2), 4));
    assert_eq!(send_all(&mut l).len(), 1);
    l.on_frame_lost(2);
    assert_eq!(l.on_retire(2, &[0xa0; 8]), Ok(Some([2; 8])));
    assert_eq!(l.pending_frame(), None);
}

#[test]
fn zero_length_peer() {
    let mut p = PeerCids::new(&[]);
    assert_eq!(p.on_new_cid(1, 0, &[1; 8], T(1), 2), Err(PROTOCOL_VIOLATION));
    assert_eq!(p.current(), &[] as &[u8]);
}

#[test]
fn limit() {
    let mut p = peer();
    assert_eq!(N(&mut p, 1, 0, &[1; 8], T(1)), Ok(()));
    assert_eq!(N(&mut p, 2, 0, &[2; 8], T(2)), Err(CONNECTION_ID_LIMIT_ERROR));
    // Nothing changed on the error (preflight I4).
    assert!(!p.is_active(&[2; 8]));
    assert_eq!(p.pending_retire(), None);
    assert_eq!(N(&mut p, 2, 1, &[2; 8], T(2)), Ok(()));
}

#[test]
fn limit_after_retire() {
    let mut p = peer();
    assert_eq!(N(&mut p, 1, 0, &A, T(1)), Ok(()));
    assert_eq!(N(&mut p, 2, 1, &B, T(2)), Ok(()));
    assert_eq!(seqs_active(&p, &[[0xc0; 8], A, B]), vec![false, true, true]);
    assert_eq!(p.pending_retire(), Some(Frame::RetireConnectionId(0)));
}

#[test]
fn rpt_switches_current() {
    let mut p = peer();
    assert_eq!(p.current(), &[0xc0; 8]);
    assert_eq!(N(&mut p, 1, 1, &A, T(1)), Ok(()));
    assert_eq!(p.current(), &A);
    assert_eq!(N(&mut p, 2, 2, &B, T(2)), Ok(()));
    assert_eq!(p.current(), &B);
    assert_eq!(retires(&mut p), vec![0, 1]);
    assert_eq!(p.largest_rpt(), 2);
}

#[test]
fn retire_of_used_non_current() {
    // current stays put while a CID another destination uses is retired (the 3d2 I2 hook).
    let mut p = peer();
    assert_eq!(N(&mut p, 2, 1, &B, T(2)), Ok(()));
    assert_eq!(p.current(), &B);
    assert_eq!(N(&mut p, 1, 0, &A, T(1)), Ok(()));
    assert_eq!(p.use_next(), Some(A.to_vec()));
    assert_eq!(p.use_next(), None);
    assert_eq!(p.on_new_cid(4, 2, &[4; 8], T(4), 3), Ok(()));
    assert_eq!(p.current(), &B);
    assert!(!p.is_active(&A));
    assert_eq!(retires(&mut p), vec![0, 1]);
}

#[test]
fn duplicate_ok() {
    let mut p = peer();
    assert_eq!(N(&mut p, 1, 0, &A, T(1)), Ok(()));
    assert_eq!(N(&mut p, 1, 0, &A, T(1)), Ok(()));
    assert_eq!(N(&mut p, 1, 0, &B, T(1)), Err(PROTOCOL_VIOLATION));
    assert_eq!(N(&mut p, 1, 0, &A, T(9)), Err(PROTOCOL_VIOLATION));
    let mut p = peer();
    assert_eq!(N(&mut p, 1, 0, &A, T(1)), Ok(()));
    assert_eq!(N(&mut p, 3, 0, &A, T(3)), Err(PROTOCOL_VIOLATION));
    let mut p = peer();
    assert_eq!(N(&mut p, 1, 0, &A, T(1)), Ok(()));
    assert_eq!(N(&mut p, 2, 1, &B, T(1)), Err(PROTOCOL_VIOLATION));
    // The handshake CID under a new sequence number.
    let mut p = peer();
    assert_eq!(N(&mut p, 1, 0, &[0xc0; 8], T(1)), Err(PROTOCOL_VIOLATION));
}

#[test]
fn repeat_with_higher_rpt_retires() {
    let mut p = peer();
    assert_eq!(N(&mut p, 1, 0, &A, T(1)), Ok(()));
    assert_eq!(N(&mut p, 2, 0, &B, T(2)), Err(CONNECTION_ID_LIMIT_ERROR));
    // The same frame again, now with Retire Prior To 1: seq 0 is retired (§5.1.2).
    assert_eq!(N(&mut p, 1, 1, &A, T(1)), Ok(()));
    assert_eq!(p.largest_rpt(), 1);
    assert_eq!(p.current(), &A);
    assert!(p.is_active(&A));
    assert!(!p.is_active(&[0xc0; 8]));
    assert_eq!(p.pending_retire(), Some(Frame::RetireConnectionId(0)));
    // Repeating it again changes nothing more.
    assert_eq!(N(&mut p, 1, 1, &A, T(1)), Ok(()));
    assert_eq!(N(&mut p, 1, 0, &A, T(1)), Ok(()));
    assert_eq!(retires(&mut p), vec![0]);
    assert_eq!(p.largest_rpt(), 1);
    // Room was made: a new CID fits now.
    assert_eq!(N(&mut p, 2, 0, &B, T(2)), Ok(()));
}

#[test]
fn non_increasing_rpt() {
    let mut p = peer();
    assert_eq!(N(&mut p, 1, 1, &A, T(1)), Ok(()));
    assert_eq!(retires(&mut p), vec![0]);
    assert_eq!(N(&mut p, 2, 0, &B, T(2)), Ok(()));
    assert_eq!(p.pending_retire(), None);
    assert_eq!(seqs_active(&p, &[A, B]), vec![true, true]);
    assert_eq!(p.largest_rpt(), 1);
}

#[test]
fn seq_below_rpt() {
    // Retire Prior To 2 retires seqs 0 and 1 at once, seq 1 before it ever arrives; a late or
    // replayed seq 1 is then already retired (§19.15 "unless it has already done so").
    let mut p = peer();
    assert_eq!(N(&mut p, 2, 2, &B, T(2)), Ok(()));
    assert_eq!(p.pending_retire(), Some(Frame::RetireConnectionId(0)));
    assert_eq!(N(&mut p, 1, 0, &A, T(1)), Ok(()));
    assert!(!p.is_active(&A));
    assert_eq!(N(&mut p, 1, 0, &A, T(1)), Ok(()));
    p.commit_retire();
    assert_eq!(p.pending_retire(), Some(Frame::RetireConnectionId(1)));
    p.commit_retire();
    assert_eq!(p.pending_retire(), None);
    assert_eq!(N(&mut p, 1, 0, &A, T(1)), Ok(()));
    assert_eq!(p.pending_retire(), None);
    p.retire_acked(1);
    assert_eq!(N(&mut p, 1, 0, &A, T(1)), Ok(()));
    assert_eq!(p.pending_retire(), None);
}

#[test]
fn replay_of_retired_seq_with_full_backlog() {
    // Review Important 1: a byte-identical replay is never a connection error (§19.15).
    let mut p = peer();
    assert_eq!(N(&mut p, 1, 0, &A, T(1)), Ok(()));
    assert_eq!(N(&mut p, 2, 2, &B, T(2)), Ok(()));
    p.commit_retire();
    p.commit_retire();
    p.retire_acked(1);
    for k in 3..=5u8 {
        assert_eq!(N(&mut p, k as u64, k as u64, &[k; 8], T(k)), Ok(()), "k = {k}");
    }
    assert_eq!(N(&mut p, 1, 0, &A, T(1)), Ok(()));
    assert_eq!(N(&mut p, 2, 2, &B, T(2)), Ok(()));
    assert_eq!(retires(&mut p), vec![2, 3, 4]);
    assert_eq!(p.current(), &[5; 8]);
}

#[test]
fn rpt_jump_retires_unseen() {
    let mut p = peer();
    assert_eq!(N(&mut p, 3, 3, &[3; 8], T(3)), Ok(()));
    assert_eq!(N(&mut p, 1, 0, &A, T(1)), Ok(()));
    assert_eq!(N(&mut p, 2, 1, &B, T(2)), Ok(()));
    assert_eq!(retires(&mut p), vec![0, 1, 2]);
    assert!(!p.is_active(&A) && !p.is_active(&B));
    for s in 0..3 {
        p.retire_acked(s);
    }
    // A jump past `2 * local_limit` retirements is CONNECTION_ID_LIMIT_ERROR (§5.1.2 MAY),
    // with nothing changed.
    assert_eq!(N(&mut p, 8, 8, &[8; 8], T(8)), Err(CONNECTION_ID_LIMIT_ERROR));
    assert_eq!(p.largest_rpt(), 3);
    assert_eq!(p.pending_retire(), None);
    assert_eq!(N(&mut p, 7, 7, &[7; 8], T(7)), Ok(()));
    assert_eq!(retires(&mut p), vec![3, 4, 5, 6]);
}

#[test]
fn retire_lost_requeues() {
    let mut p = peer();
    assert_eq!(N(&mut p, 1, 1, &A, T(1)), Ok(()));
    assert_eq!(retires(&mut p), vec![0]);
    p.retire_lost(0);
    p.retire_lost(0);
    assert_eq!(retires(&mut p), vec![0]);
    p.retire_acked(0);
    p.retire_lost(0);
    assert_eq!(p.pending_retire(), None);
}

#[test]
fn retire_backlog() {
    let mut p = peer();
    for k in 1..=4u8 {
        assert_eq!(p.on_new_cid(k as u64, k as u64, &[k; 8], T(k), 2), Ok(()), "k = {k}");
    }
    assert_eq!(p.on_new_cid(5, 5, &[5; 8], T(5), 2), Err(CONNECTION_ID_LIMIT_ERROR));
    assert_eq!(p.current(), &[4; 8]);
    // A late or replayed sequence number below Retire Prior To is already retired: Ok, and
    // it adds nothing to the backlog.
    assert_eq!(p.on_new_cid(0, 0, &[9; 8], T(9), 2), Ok(()));
    assert_eq!(p.on_new_cid(3, 0, &[3; 8], T(3), 2), Ok(()));
    assert_eq!(retires(&mut p), vec![0, 1, 2, 3]);
    p.retire_acked(3);
    assert_eq!(p.on_new_cid(3, 0, &[3; 8], T(3), 2), Ok(()));
    p.retire_acked(0);
    assert!(p.retire_capacity() <= 16);
}

#[test]
fn reset_token_used_only() {
    let mut p = peer();
    assert_eq!(N(&mut p, 1, 0, &A, T(1)), Ok(()));
    assert!(!p.matches_reset(&T(1)));
    assert_eq!(p.used_tokens(), Vec::<[u8; 16]>::new());
    assert!(p.has_unused());
    assert_eq!(N(&mut p, 2, 1, &B, T(2)), Ok(()));
    assert_eq!(p.current(), &A);
    assert!(p.matches_reset(&T(1)));
    assert!(!p.matches_reset(&T(2)));
    assert!(!p.matches_reset(&[0; 16]));
    assert_eq!(p.used_tokens(), vec![T(1)]);
    assert_eq!(p.use_next(), Some(B.to_vec()));
    assert!(p.matches_reset(&T(2)));
    assert!(!p.has_unused());
    let mut u = p.used_tokens();
    u.sort();
    assert_eq!(u, vec![T(1), T(2)]);
}
