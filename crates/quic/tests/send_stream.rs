use quic::send_stream::*;

#[allow(non_snake_case)]
fn C(off: u64, data: &[u8], fin: bool, new_bytes: u64) -> Chunk {
    Chunk { off, data: data.to_vec(), fin, new_bytes }
}

#[test]
fn send_flow() {
    let mut s = SendStream::new(5);
    assert_eq!(s.write(b"abcdefgh", true), Ok(()));
    assert_eq!(s.state_exec(), SendState::Ready);
    assert_eq!(s.poll_data(100, 100), Some(C(0, b"abcde", false, 5)));
    assert_eq!(s.state_exec(), SendState::Send);
    assert_eq!(s.poll_data(100, 100), None);
    s.on_max_stream_data(4);
    assert_eq!(s.max(), 5);
    s.on_max_stream_data(8);
    assert_eq!(s.poll_data(100, 100), Some(C(5, b"fgh", true, 3)));
    assert_eq!(s.state_exec(), SendState::DataSent);
    assert_eq!(s.sent_end(), 8);
}

#[test]
fn conn_limited() {
    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"abcdef", false), Ok(()));
    assert_eq!(s.poll_data(100, 2), Some(C(0, b"ab", false, 2)));
    assert_eq!(s.poll_data(100, 0), None);
}

#[test]
fn fin_only() {
    let mut s = SendStream::new(0);
    assert_eq!(s.write(b"", true), Ok(()));
    assert_eq!(s.poll_data(100, 0), Some(C(0, b"", true, 0)));
    assert_eq!(s.state_exec(), SendState::DataSent);
}

/// A short piece goes whole or not at all: the room is short of the 6 bytes to the FIN.
#[test]
fn max_len_split() {
    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"abcdef", true), Ok(()));
    assert_eq!(s.poll_data(4, 100), None);
    assert_eq!(s.poll_data(6, 100), Some(C(0, b"abcdef", true, 6)));
}

/// A lost short piece is resent whole: no split below `FLOOR` (D10 (c)).
#[test]
fn retransmit_same_bytes() {
    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"abcdef", true), Ok(()));
    assert_eq!(s.poll_data(100, 100), Some(C(0, b"abcdef", true, 6)));
    s.on_data_lost(0, 6, true);
    assert_eq!(s.poll_data(4, 0), None);
    assert_eq!(s.poll_data(6, 0), Some(C(0, b"abcdef", true, 0)));
    s.on_data_acked(0, 6, true);
    assert_eq!(s.state_exec(), SendState::DataRecvd);
    assert_eq!(s.poll_data(100, 100), None);
}

#[test]
fn all_acks_required() {
    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"ab", false), Ok(()));
    s.flush();
    assert_eq!(s.poll_data(100, 100), Some(C(0, b"ab", false, 2)));
    assert_eq!(s.write(b"cd", true), Ok(()));
    assert_eq!(s.poll_data(100, 100), Some(C(2, b"cd", true, 2)));
    s.on_data_acked(2, 2, true);
    assert_eq!(s.state_exec(), SendState::DataSent);
    s.on_data_acked(0, 2, false);
    assert_eq!(s.state_exec(), SendState::DataRecvd);
}

#[test]
fn reset_stops_stream() {
    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"abcdef", false), Ok(()));
    // Three bytes of connection credit: a credit cut ends a short piece.
    assert_eq!(s.poll_data(100, 3), Some(C(0, b"abc", false, 3)));
    assert!(s.reset(9));
    assert_eq!(s.state_exec(), SendState::ResetSent);
    assert_eq!(s.poll_data(100, 100), None);
    assert_eq!(s.pending_reset(), Some((9, 3)));
    s.commit_reset();
    assert_eq!(s.pending_reset(), None);
    s.on_data_lost(0, 3, false);
    assert_eq!(s.poll_data(100, 100), None);
    assert_eq!(s.write(b"x", false), Err(()));
    s.on_reset_lost();
    assert_eq!(s.pending_reset(), Some((9, 3)));
    s.commit_reset();
    s.on_reset_acked();
    assert_eq!(s.state_exec(), SendState::ResetRecvd);
    assert!(!s.reset(1));
}

#[test]
fn stop_sending_forces_reset() {
    let mut s = SendStream::new(100);
    assert!(s.on_stop_sending(5));
    assert_eq!(s.pending_reset(), Some((5, 0)));

    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"ab", true), Ok(()));
    assert!(s.poll_data(100, 100).is_some());
    assert_eq!(s.state_exec(), SendState::DataSent);
    assert!(s.on_stop_sending(6));
    assert_eq!(s.pending_reset(), Some((6, 2)));

    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"ab", true), Ok(()));
    assert!(s.poll_data(100, 100).is_some());
    s.on_data_acked(0, 2, true);
    assert_eq!(s.state_exec(), SendState::DataRecvd);
    assert!(!s.on_stop_sending(7));
    assert_eq!(s.pending_reset(), None);

    let mut s = SendStream::new(100);
    assert!(s.reset(1));
    assert!(!s.on_stop_sending(8));
}

#[test]
fn write_rules() {
    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"a", true), Ok(()));
    assert_eq!(s.write(b"b", false), Err(()));
    assert_eq!(s.write(b"", true), Err(()));
}

#[test]
fn next_off_tracks_poll() {
    let mut s = SendStream::new(100);
    assert_eq!(s.write(b"abcd", false), Ok(()));
    s.flush();
    assert_eq!(s.next_off(), Some(0));
    assert_eq!(s.poll_data(100, 100), Some(C(0, b"abcd", false, 4)));
    assert_eq!(s.next_off(), None);
    s.on_data_lost(0, 4, false);
    assert_eq!(s.next_off(), Some(0));
    assert_eq!(s.poll_data(100, 100), Some(C(0, b"abcd", false, 0)));
    assert_eq!(s.write(b"ef", true), Ok(()));
    assert_eq!(s.next_off(), Some(4));
    assert_eq!(s.poll_data(100, 100), Some(C(4, b"ef", true, 2)));
    assert_eq!(s.next_off(), None);
    assert!(s.reset(0));
    assert_eq!(s.next_off(), None);
}

/// Sends everything at room `m`, returning the pieces in order.
fn send_all(s: &mut SendStream, m: u64) -> Vec<(u64, u64)> {
    let mut v = Vec::new();
    while let Some(c) = s.poll_data(m, u64::MAX) {
        v.push((c.off, c.data.len() as u64));
    }
    v
}

#[test]
fn ack_releases_capacity() {
    // Everything written is acked: the send buffer keeps no allocation.
    const W: usize = 1 << 16;
    let mut s = SendStream::new(W as u64);
    assert_eq!(s.write(&vec![7u8; W], true), Ok(()));
    assert!(s.buf_capacity() >= W);
    let p = send_all(&mut s, 1200);
    let (lo, hi) = p.split_at(p.len() / 2);
    for (i, &(o, n)) in hi.iter().enumerate() {
        s.on_data_acked(o, n, i == hi.len() - 1);
    }
    assert!(s.buf_capacity() >= W / 2);
    for &(o, n) in lo {
        s.on_data_acked(o, n, false);
    }
    assert_eq!(s.state_exec(), SendState::DataRecvd);
    assert_eq!(s.buf_capacity(), 0);
}

/// A lost range of 600 is cut only leaving both parts at least `FLOOR`; one of 400 goes whole or not at all; a `None`
/// sends no new byte either (D10 (c)).
#[test]
fn floor_skips_small_room() {
    let mut s = SendStream::new(1 << 20);
    assert_eq!(s.write(&[1; 600], false), Ok(()));
    assert_eq!(send_all(&mut s, 600), vec![(0, 600)]);
    s.on_data_lost(0, 600, false);
    assert_eq!(s.poll_data(255, u64::MAX), None);
    let c = s.poll_data(300, u64::MAX).unwrap();
    assert_eq!((c.off, c.data.len()), (0, 300));
    assert_eq!(s.range_sets().1, vec![(300, 600)]);

    let mut s = SendStream::new(1 << 20);
    assert_eq!(s.write(&[1; 1000], false), Ok(()));
    let c = s.poll_data(400, u64::MAX).unwrap();
    assert_eq!((c.off, c.data.len()), (0, 400));
    s.on_data_lost(0, 400, false);
    assert_eq!(s.poll_data(300, u64::MAX), None);
    assert_eq!(s.sent_end(), 400);
    let c = s.poll_data(400, u64::MAX).unwrap();
    assert_eq!((c.off, c.data.len()), (0, 400));
}

/// Tiny writes wait for a flush point or `FLOOR` bytes: nine 10-byte writes send nothing until `flush`, then go as one
/// piece; 300 unflushed bytes go at once.
#[test]
fn small_writes_coalesce() {
    let mut s = SendStream::new(1 << 20);
    for _ in 0..9 {
        assert_eq!(s.write(&[2; 10], false), Ok(()));
        assert_eq!(s.poll_data(1200, u64::MAX), None);
    }
    s.flush();
    assert_eq!(send_all(&mut s, 1200), vec![(0, 90)]);
    let mut s = SendStream::new(1 << 20);
    assert_eq!(s.write(&[2; 300], false), Ok(()));
    assert_eq!(send_all(&mut s, 1200), vec![(0, 300)]);
}

/// Flushed bytes never wait behind an unflushed tail (review M1).
#[test]
fn flush_point_before_tail() {
    let mut s = SendStream::new(1 << 20);
    assert_eq!(s.write(&[3; 100], false), Ok(()));
    s.flush();
    assert_eq!(s.write(&[3; 50], false), Ok(()));
    assert_eq!(send_all(&mut s, 1200), vec![(0, 100)]);
}

/// At most `MAX_FLUSH` short pieces open: the fifth waits until the first one's ACK closes its slot; a lone FIN needs
/// no slot.
#[test]
fn flush_slots_cap() {
    let mut s = SendStream::new(1 << 20);
    let mut sent = Vec::new();
    for _ in 0..5 {
        assert_eq!(s.write(&[4; 10], false), Ok(()));
        s.flush();
        sent.extend(send_all(&mut s, 1200));
    }
    assert_eq!(sent, vec![(0, 10), (10, 10), (20, 10), (30, 10)]);
    s.on_data_acked(0, 10, false);
    assert_eq!(send_all(&mut s, 1200), vec![(40, 10)]);
    assert_eq!(s.write(&[], true), Ok(()));
    assert_eq!(s.poll_data(1200, u64::MAX), Some(C(50, b"", true, 0)));
}

/// A credit cut ends a short piece, which takes a slot: four such pieces and the fifth waits.
#[test]
fn credit_cut_short_piece() {
    let mut s = SendStream::new(100);
    assert_eq!(s.write(&[5; 1000], false), Ok(()));
    assert_eq!(send_all(&mut s, 1200), vec![(0, 100)]);
    for (k, m) in [110u64, 120, 130].into_iter().enumerate() {
        s.on_max_stream_data(m);
        assert_eq!(send_all(&mut s, 1200), vec![(100 + 10 * k as u64, 10)]);
    }
    s.on_max_stream_data(140);
    assert_eq!(s.poll_data(1200, u64::MAX), None);
}

/// A seeded xorshift: the same run every time.
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: u64) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0 % n
    }
}

/// Each byte of `[acked_base, sent_end)` lies in exactly one of acked, lost and in flight, and none outside it.
fn partition_ok(s: &SendStream, written: u64) {
    let (a, l, f) = s.range_sets();
    let base = written - s.buffered() as u64;
    let mut seen = std::collections::BTreeMap::new();
    for (k, v) in [a, l, f].iter().enumerate() {
        for &(x, y) in v {
            for b in x..y {
                assert!(seen.insert(b, k).is_none(), "byte {b} in two sets");
            }
        }
    }
    assert_eq!(seen.len() as u64, s.sent_end() - base, "bytes outside the sets");
    assert!(seen.keys().all(|&b| base <= b && b < s.sent_end()));
}

/// Seeded writes, polls at random rooms, ACKs and losses of random pieces in flight: after every call the partition
/// holds, an acknowledged byte never shows up lost again, and the stream reaches Data Recvd.
#[test]
fn partition_never_forgets() {
    let mut rng = Rng(0x8a_9b2);
    let mut s = SendStream::new(1 << 20);
    let mut written = 0u64;
    let mut acked = std::collections::BTreeSet::new();
    for step in 0..4000 {
        match rng.below(6) {
            0 if written < 60_000 => {
                let n = 1 + rng.below(700);
                assert_eq!(s.write(&vec![6; n as usize], false), Ok(()));
                written += n;
                if rng.below(2) == 0 {
                    s.flush();
                }
            },
            1 | 2 => {
                let _ = s.poll_data(1 + rng.below(1400), u64::MAX);
            },
            3 | 4 | 5 => {
                let f = s.range_sets().2;
                if !f.is_empty() {
                    let (x, y) = f[rng.below(f.len() as u64) as usize];
                    if rng.below(3) == 0 {
                        s.on_data_lost(x, y - x, false);
                    } else {
                        s.on_data_acked(x, y - x, false);
                        acked.extend(x..y);
                    }
                }
            },
            _ => {},
        }
        partition_ok(&s, written);
        for &(x, y) in &s.range_sets().1 {
            assert!((x..y).all(|b| !acked.contains(&b)), "step {step}: acked byte lost again");
        }
    }
    assert_eq!(s.write(&[], true), Ok(()));
    while s.state_exec() != SendState::DataRecvd {
        let _ = send_all(&mut s, 1200);
        for (x, y) in s.range_sets().2 {
            s.on_data_acked(x, y - x, y == written);
        }
        if s.range_sets().2.is_empty() && s.sent_end() == written {
            s.on_data_acked(written, 0, true);
        }
        partition_ok(&s, written);
    }
}

/// The selective-ACK adversary (9b2 ruling 11's experiment): 64 KiB sent in 1200-byte pieces, all lost; each round
/// polls with rooms 1..8 (each `None`: the floor) then 1200, acknowledges every other piece in flight and loses the
/// rest (parity over all pieces); after 8 rounds everything is acknowledged. After every call the three sets hold at
/// most `buffered()/256 + 4` entries (D10 (d)).
#[test]
fn send_ranges_bounded_under_selective_acks() {
    const W: usize = 64 << 10;
    let mut s = SendStream::new(W as u64);
    assert_eq!(s.write(&vec![8u8; W], true), Ok(()));
    let bound = |s: &SendStream| {
        let (a, l, f) = s.range_counts();
        assert!(a + l + f <= s.buffered() / 256 + 4, "{a} + {l} + {f} > {} / 256 + 4", s.buffered());
    };
    for (o, n) in send_all(&mut s, 1200) {
        s.on_data_lost(o, n, o + n == W as u64);
        bound(&s);
    }
    let mut parity = 0u64;
    for round in 0..8u64 {
        assert_eq!(s.poll_data(1 + round, u64::MAX), None);
        bound(&s);
        while s.poll_data(1200, u64::MAX).is_some() {
            bound(&s);
        }
        for (x, y) in s.range_sets().2 {
            parity += 1;
            if parity % 2 == 0 {
                s.on_data_acked(x, y - x, y == W as u64);
            } else {
                s.on_data_lost(x, y - x, y == W as u64);
            }
            bound(&s);
        }
    }
    while s.state_exec() != SendState::DataRecvd {
        for (o, n) in send_all(&mut s, 1200) {
            s.on_data_acked(o, n, o + n == W as u64);
            bound(&s);
        }
    }
}
