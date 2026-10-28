//! Packet number encoding and decoding (RFC 9000 §17.1, Appendix A.2 and A.3).
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::codes::*;

verus! {

// =============================================================================
// RFC 9000 transcription
// =============================================================================

//= https://www.rfc-editor.org/rfc/rfc9000#section-17.1
//# Prior to receiving an acknowledgment for a packet number space, the
//# full packet number MUST be included; it is not to be truncated, as
//# described below.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.1
//# After an acknowledgment is received for a packet number space, the
//# sender MUST use a packet number size able to represent more than
//# twice as large a range as the difference between the largest
//# acknowledged packet number and the packet number being sent.
//
//= https://www.rfc-editor.org/rfc/rfc9000#appendix-A.2
//# if largest_acked is None:
//# num_unacked = full_pn + 1
//# else:
//# num_unacked = full_pn - largest_acked
/// An `n`-byte packet number field (1..=4) is acceptable for `full`. The prose overrides
/// Appendix A.2's `log` pseudocode at exact powers of two.
pub open spec fn pn_len_ok(full: u64, largest_acked: Option<u64>, n: nat) -> bool {
    1 <= n <= 4 && match largest_acked {
        None => pow2(8 * n) > full,
        Some(a) => pow2(8 * n) > 2 * ((full as int) - (a as int)),
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#appendix-A.3
//# expected_pn  = largest_pn + 1
/// `largest_pn + 1`, or 0 before any packet has been processed.
pub open spec fn expected_pn(largest: Option<u64>) -> int {
    match largest {
        None => 0,
        Some(l) => l as int + 1,
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#appendix-A.3
//# pn_win       = 1 << pn_nbits
//# pn_hwin      = pn_win / 2
//# pn_mask      = pn_win - 1
//
//= https://www.rfc-editor.org/rfc/rfc9000#appendix-A.3
//# candidate_pn = (expected_pn & ~pn_mask) | truncated_pn
//# if candidate_pn <= expected_pn - pn_hwin and
//# candidate_pn < (1 << 62) - pn_win:
//# return candidate_pn + pn_win
//# if candidate_pn > expected_pn + pn_hwin and
//# candidate_pn >= pn_win:
//# return candidate_pn - pn_win
//# return candidate_pn
/// Figure 47 over unbounded integers. `(x & ~mask) | t` is written `x - x % win + t`, which
/// is the same whenever `t < win`.
pub open spec fn rfc_decode_pn(largest: Option<u64>, truncated: u64, nbits: nat) -> int
    recommends
        truncated < pow2(nbits),
{
    let expected = expected_pn(largest);
    let win = pow2(nbits) as int;
    let hwin = win / 2;
    let candidate = expected - expected % win + truncated as int;
    if candidate <= expected - hwin && candidate < pow2(62) as int - win {
        candidate + win
    } else if candidate > expected + hwin && candidate >= win {
        candidate - win
    } else {
        candidate
    }
}

// =============================================================================
// Proofs
// =============================================================================

/// The decoded packet number lies in `0..=PN_MAX` whenever the largest one processed is below
/// `PN_MAX`: `expected - expected % win` is a multiple of `win` below `2^62`, so it is at most
/// `2^62 - win`, and the `+ win` step is guarded.
pub proof fn lemma_decode_pn_bound(largest: Option<u64>, truncated: u64, pn_len: u8)
    requires
        1 <= pn_len <= 4,
        truncated < pow2(8 * pn_len as nat),
        largest matches Some(l) ==> l < PN_MAX,
    ensures
        0 <= rfc_decode_pn(largest, truncated, 8 * pn_len as nat) <= PN_MAX,
{
    lemma2_to64();
    lemma2_to64_rest();
    let nb = 8 * pn_len as nat;
    lemma_pow2_adds(nb, (62 - nb) as nat);
    lemma_pow2_pos((62 - nb) as nat);
    let win = pow2(nb) as int;
    let m = pow2((62 - nb) as nat) as int;
    assert(win >= 256);
    assert(m * win == pow2(62)) by (nonlinear_arith)
        requires
            pow2(62) == pow2(nb) * pow2((62 - nb) as nat),
            win == pow2(nb),
            m == pow2((62 - nb) as nat),
    ;
    let e = expected_pn(largest);
    assert(0 <= e < pow2(62));
    let q = e / win;
    assert(e - e % win == q * win && q >= 0) by (nonlinear_arith)
        requires
            q == e / win,
            win > 0,
            e >= 0,
    ;
    assert(q * win <= pow2(62) - win) by (nonlinear_arith)
        requires
            q * win <= e,
            e < m * win,
            m * win == pow2(62),
            q >= 0,
            win > 0,
    ;
}

/// A packet number sent with a length `pn_len_ok` accepts decodes back to itself at a receiver
/// that has processed every acknowledged packet but not this one: its largest `l` is at least
/// the sender's largest acknowledged `a` and below `full`. Before any ACK (`None`), the
/// receiver's expected number is at most `full`.
pub proof fn theorem_pn_len_decodes(
    full: u64,
    largest_acked: Option<u64>,
    pn_len: u8,
    largest: Option<u64>,
)
    requires
        1 <= pn_len <= 4,
        full <= PN_MAX,
        pn_len_ok(full, largest_acked, pn_len as nat),
        largest_acked matches Some(a) ==> largest matches Some(l) && a <= l < full,
        largest_acked is None ==> expected_pn(largest) <= full,
    ensures
        rfc_decode_pn(largest, ((full as nat) % pow2(8 * pn_len as nat)) as u64, 8 * pn_len as nat)
            == full as int,
{
    lemma2_to64();
    lemma2_to64_rest();
    let nb = 8 * pn_len as nat;
    lemma_pow2_adds((nb - 1) as nat, 1);
    assert(pow2(nb) == 2 * pow2((nb - 1) as nat));
    match largest_acked {
        Some(a) => {
            theorem_decode_pn_recovers(full, largest, pn_len);
        },
        None => {
            let win = pow2(nb) as int;
            let e = expected_pn(largest);
            assert((full as int) % win == full as int) by {
                lemma_small_mod(full as nat, win as nat);
            }
            assert(e % win == e) by {
                lemma_small_mod(e as nat, win as nat);
            }
        },
    }
}

// =============================================================================
// Executable code
// =============================================================================

fn pow2_bytes(n: u8) -> (r: u64)
    requires
        1 <= n <= 4,
    ensures
        r == pow2(8 * n as nat),
        r % 2 == 0,
        256 <= r <= 0x1_0000_0000,
{
    proof {
        lemma2_to64();
    }
    if n == 1 {
        0x100
    } else if n == 2 {
        0x1_0000
    } else if n == 3 {
        0x100_0000
    } else {
        0x1_0000_0000
    }
}

/// Smallest acceptable length in bytes; `None` when even 4 bytes cannot cover the range
/// (more than 2^31 packets unacknowledged, an internal limit for the caller).
pub fn pn_encode_len(full: u64, largest_acked: Option<u64>) -> (r: Option<u8>)
    requires
        full <= PN_MAX,
        largest_acked is Some ==> largest_acked->0 < full,
    ensures
        r matches Some(n) ==> pn_len_ok(full, largest_acked, n as nat) && forall|m: nat|
            1 <= m < n ==> !pn_len_ok(full, largest_acked, m),
        r is None ==> !pn_len_ok(full, largest_acked, 4),
{
    let mut n: u8 = 1;
    while n <= 4
        invariant
            1 <= n <= 5,
            full <= PN_MAX,
            largest_acked is Some ==> largest_acked->0 < full,
            forall|m: nat| 1 <= m < n ==> !pn_len_ok(full, largest_acked, m),
        decreases 5 - n,
    {
        let limit = pow2_bytes(n);
        let ok = match largest_acked {
            None => limit > full,
            Some(a) => {
                assert(a < full);
                limit / 2 > full - a
            },
        };
        proof {
            assert(ok == pn_len_ok(full, largest_acked, n as nat));
        }
        if ok {
            return Some(n);
        }
        proof {
            assert forall|m: nat| 1 <= m < n + 1 implies !pn_len_ok(full, largest_acked, m) by {
            }
        }
        n += 1;
    }
    None
}

//= https://www.rfc-editor.org/rfc/rfc9000#appendix-A.3
//# DecodePacketNumber(largest_pn, truncated_pn, pn_nbits):
/// The `u64` arithmetic never overflows: `expected <= 2^62 - 1` and `candidate <= 2^62 - 1`
/// (`lemma_decode_pn_bound`).
pub fn decode_pn(largest: Option<u64>, truncated: u64, pn_len: u8) -> (r: u64)
    requires
        1 <= pn_len <= 4,
        truncated < pow2(8 * pn_len as nat),
        largest matches Some(l) ==> l < PN_MAX,
    ensures
        r == rfc_decode_pn(largest, truncated, 8 * pn_len as nat),
        r <= PN_MAX,
{
    let win = pow2_bytes(pn_len);
    proof {
        lemma2_to64();
        lemma2_to64_rest();
        lemma_decode_pn_bound(largest, truncated, pn_len);
    }
    let hwin = win / 2;
    let expected: u64 = match largest {
        None => 0,
        Some(l) => l + 1,
    };
    assert(expected % win <= expected) by (nonlinear_arith)
        requires
            win >= 256,
    ;
    let candidate = expected - expected % win + truncated;
    if candidate + hwin <= expected && candidate < 0x4000_0000_0000_0000u64 - win {
        candidate + win
    } else if candidate > expected + hwin && candidate >= win {
        candidate - win
    } else {
        candidate
    }
}

/// A decoder whose largest-processed packet number is within half a window of `full` recovers
/// `full` from its low `8 * pn_len` bits (the property Appendix A.3 is designed for).
pub proof fn theorem_decode_pn_recovers(full: u64, largest: Option<u64>, pn_len: u8)
    requires
        1 <= pn_len <= 4,
        full <= PN_MAX,
        expected_pn(largest) - pow2((8 * pn_len - 1) as nat) < full <= expected_pn(largest) + pow2(
            (8 * pn_len - 1) as nat,
        ),
    ensures
        rfc_decode_pn(largest, ((full as nat) % pow2(8 * pn_len as nat)) as u64, 8 * pn_len as nat)
            == full as int,
{
    lemma2_to64();
    lemma2_to64_rest();
    lemma_pow2_adds((8 * pn_len - 1) as nat, 1);
    let nb = 8 * pn_len as nat;
    let win = pow2(nb) as int;
    let hwin = win / 2;
    assert(win == 2 * pow2((8 * pn_len - 1) as nat));
    assert(hwin == pow2((8 * pn_len - 1) as nat));
    assert(win >= 256 && win <= 0x1_0000_0000);
    let e = expected_pn(largest);
    let t = full as int % win;
    let q = e / win;
    let r = e % win;
    let k = full as int / win;
    let cand = e - r + t;
    assert(e - r == q * win) by (nonlinear_arith)
        requires
            q == e / win,
            r == e % win,
            win > 0,
    ;
    assert(full as int == k * win + t) by (nonlinear_arith)
        requires
            k == full as int / win,
            t == full as int % win,
            win > 0,
    ;
    assert(0 <= t < win && 0 <= r < win);
    // (k - q) * win = (full - e) + (r - t), strictly between -1.5 win and 1.5 win
    let d = k - q;
    assert(d * win == (full as int - e) + (r - t)) by (nonlinear_arith)
        requires
            full as int == k * win + t,
            e == q * win + r,
            d == k - q,
    ;
    assert(-1 <= d <= 1) by (nonlinear_arith)
        requires
            d * win == (full as int - e) + (r - t),
            e - hwin < full as int <= e + hwin,
            win == 2 * hwin,
            hwin >= 128,
            0 <= t < win,
            0 <= r < win,
    ;
    assert(cand == q * win + t);
    assert(full as int == cand + d * win) by (nonlinear_arith)
        requires
            full as int == k * win + t,
            cand == q * win + t,
            d == k - q,
    ;
    if d == 0 {
    } else if d == 1 {
        assert(d == 1);
        assert(d * win == win) by (nonlinear_arith)
            requires
                d == 1,
        ;
        assert(full as int == cand + win);
    } else {
        assert(d == -1);
        assert(d * win == -win) by (nonlinear_arith)
            requires
                d == -1,
        ;
        assert(full as int == cand - win);
        assert(q >= 1) by (nonlinear_arith)
            requires
                d == k - q,
                d == -1,
                k >= 0,
        ;
        assert(cand >= win) by (nonlinear_arith)
            requires
                cand == q * win + t,
                q >= 1,
                t >= 0,
                win > 0,
        ;
    }
}

// =============================================================================
// Wire bytes (big-endian, low `n` bytes)
// =============================================================================

/// The low `n` bytes of `v`, big-endian.
pub open spec fn pn_be(v: u64, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        pn_be(v / 256, (n - 1) as nat).push((v % 256) as u8)
    }
}

/// The big-endian value of `s`.
pub open spec fn be_val(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        be_val(s.drop_last()) * 256 + s.last() as nat
    }
}

pub proof fn lemma_be_val_bound(s: Seq<u8>)
    ensures
        be_val(s) < pow2(8 * s.len()),
    decreases s.len(),
{
    if s.len() == 0 {
        lemma2_to64();
    } else {
        lemma_be_val_bound(s.drop_last());
        lemma_pow2_adds(8 * (s.len() - 1) as nat, 8);
        lemma2_to64();
        assert(pow2(8 * s.len()) == pow2(8 * (s.len() - 1) as nat) * 256);
        assert(be_val(s) < pow2(8 * s.len())) by (nonlinear_arith)
            requires
                be_val(s) == be_val(s.drop_last()) * 256 + s.last() as nat,
                be_val(s.drop_last()) < pow2(8 * (s.len() - 1) as nat),
                s.last() < 256,
                pow2(8 * s.len()) == pow2(8 * (s.len() - 1) as nat) * 256,
        ;
    }
}

/// Writing the low `n` bytes of `full` and reading them back gives `full % 2^(8n)`.
pub proof fn lemma_pn_roundtrip(full: u64, n: nat)
    ensures
        pn_be(full, n).len() == n,
        be_val(pn_be(full, n)) == (full as nat) % pow2(8 * n),
    decreases n,
{
    if n == 0 {
        lemma2_to64();
    } else {
        lemma_pn_roundtrip(full / 256, (n - 1) as nat);
        let s = pn_be(full, n);
        assert(s.drop_last() =~= pn_be(full / 256, (n - 1) as nat));
        lemma_pow2_adds(8 * (n - 1) as nat, 8);
        lemma2_to64();
        let p = pow2(8 * (n - 1) as nat);
        assert(pow2(8 * n) == p * 256);
        assert(p > 0) by {
            lemma_pow2_pos(8 * (n - 1) as nat);
        }
        lemma_mod_breakdown(full as int, 256, p as int);
        assert(256 * p == p * 256) by (nonlinear_arith);
    }
}

/// Appends the low `pn_len` bytes of `full`, big-endian.
pub fn put_pn(full: u64, pn_len: u8, out: &mut Vec<u8>)
    requires
        1 <= pn_len <= 4,
    ensures
        final(out)@ == old(out)@ + pn_be(full, pn_len as nat),
{
    let ghost start = out@;
    if pn_len >= 4 {
        out.push((full / 0x100_0000 % 256) as u8);
    }
    if pn_len >= 3 {
        out.push((full / 0x1_0000 % 256) as u8);
    }
    if pn_len >= 2 {
        out.push((full / 0x100 % 256) as u8);
    }
    out.push((full % 256) as u8);
    proof {
        let n = pn_len as nat;
        reveal_with_fuel(pn_be, 5);
        assert(full / 256 / 256 == full / 0x1_0000) by (nonlinear_arith);
        assert(full / 256 / 256 / 256 == full / 0x100_0000) by (nonlinear_arith);
        assert(out@ =~= start + pn_be(full, n));
    }
}

/// Big-endian value of 1 to 4 bytes.
pub fn read_pn(b: &[u8]) -> (r: u64)
    requires
        1 <= b.len() <= 4,
    ensures
        r as nat == be_val(b@),
{
    let mut r: u64 = 0;
    let mut i: usize = 0;
    while i < b.len()
        invariant
            i <= b.len() <= 4,
            r as nat == be_val(b@.take(i as int)),
        decreases b.len() - i,
    {
        proof {
            lemma_be_val_bound(b@.take(i as int));
            lemma2_to64();
            assert(b@.take(i as int + 1).drop_last() =~= b@.take(i as int));
            assert(pow2(8 * i as nat) <= pow2(32)) by {
                lemma_pow2_adds(8 * i as nat, 8 * (4 - i) as nat);
                lemma_pow2_pos(8 * (4 - i) as nat);
            }
        }
        r = r * 256 + b[i] as u64;
        i += 1;
    }
    proof {
        assert(b@.take(b.len() as int) =~= b@);
    }
    r
}

} // verus!
