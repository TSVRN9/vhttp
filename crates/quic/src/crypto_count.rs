//! The CRYPTO data bytes a datagram carries (D6's induction): each packet's frames carry at most its bytes, so a
//! datagram's packets carry at most its length, and nothing past a UDP payload. Likewise its load (9b2 Task 10d): one
//! per packet and per frame plus each frame's CRYPTO or STREAM data bytes, at most its length, which bounds the
//! receive pipeline's cost (`Connection::on_datagram`). Kept apart from the codecs it reads, so their modules' proofs
//! do not carry these definitions.
#[allow(unused_imports)]
use vstd::prelude::*;
#[allow(unused_imports)]
use crypto::aes::*;
#[allow(unused_imports)]
use crypto::gcm::*;
#[allow(unused_imports)]
use wire::varint::*;
#[allow(unused_imports)]
use crate::aead::*;
#[allow(unused_imports)]
use crate::cid::LOCAL_CID_LEN;
#[allow(unused_imports)]
use crate::codes::*;
#[allow(unused_imports)]
use crate::datagram::*;
#[allow(unused_imports)]
use crate::frame::*;
#[allow(unused_imports)]
use crate::header::*;
#[allow(unused_imports)]
use crate::hp::*;
#[allow(unused_imports)]
use crate::payload::*;
#[allow(unused_imports)]
use crate::pn::*;
#[allow(unused_imports)]
use crate::protect::*;

verus! {

/// The CRYPTO data bytes frame `f` carries.
pub open spec fn frame_crypto(f: SpecFrame) -> nat {
    match f {
        SpecFrame::Crypto { data, .. } => data.len(),
        _ => 0,
    }
}

/// The CRYPTO data bytes the frames carry.
pub open spec fn frames_crypto(fs: Seq<SpecFrame>) -> nat
    decreases fs.len(),
{
    if fs.len() == 0 {
        0
    } else {
        frames_crypto(fs.drop_last()) + frame_crypto(fs.last())
    }
}

/// `frames_crypto` of one frame then `fs`.
pub proof fn lemma_frames_crypto_prepend(f: SpecFrame, fs: Seq<SpecFrame>)
    ensures
        frames_crypto(seq![f] + fs) == frame_crypto(f) + frames_crypto(fs),
    decreases fs.len(),
{
    if fs.len() == 0 {
        assert((seq![f] + fs).drop_last() =~= Seq::<SpecFrame>::empty());
        assert((seq![f] + fs).last() == f);
        assert(frames_crypto(Seq::<SpecFrame>::empty()) == 0);
    } else {
        assert((seq![f] + fs).drop_last() =~= seq![f] + fs.drop_last());
        assert((seq![f] + fs).last() == fs.last());
        lemma_frames_crypto_prepend(f, fs.drop_last());
    }
}

/// A prefix carries no more, and one more frame adds its own.
pub proof fn lemma_frames_crypto_take(fs: Seq<SpecFrame>, i: int)
    requires
        0 <= i <= fs.len(),
    ensures
        frames_crypto(fs.take(i)) <= frames_crypto(fs),
        i < fs.len() ==> frames_crypto(fs.take(i + 1)) == frames_crypto(fs.take(i)) + frame_crypto(fs[i]),
    decreases fs.len() - i,
{
    if i < fs.len() {
        assert(fs.take(i + 1).drop_last() =~= fs.take(i));
        lemma_frames_crypto_take(fs, i + 1);
    } else {
        assert(fs.take(i) =~= fs);
    }
}

/// A CRYPTO frame body holds its data: no more bytes than it consumes, within `b`.
pub proof fn lemma_body_crypto(ty: u64, b: Seq<u8>)
    requires
        ty <= FRAME_HANDSHAKE_DONE,
    ensures
        rfc_frame_body(ty, b) matches Ok((f, m)) ==> frame_crypto(f) <= m && (f is Crypto ==> m <= b.len()),
{
    lemma_frame_body_received(ty, b);
    if let Ok((f, m)) = rfc_frame_body(ty, b) {
        if f is Crypto {
            assert(ty == FRAME_CRYPTO);
            lemma_vints_ok(b);
        }
    }
}


/// The frames from `p` on carry at most the bytes from `p` on as CRYPTO data.
pub proof fn lemma_frames_crypto_len(b: Seq<u8>, p: int, k: PacketKind)
    requires
        0 <= p,
    ensures
        rfc_frames(b, p, k) matches Ok(fs) ==> frames_crypto(fs) <= (if p < b.len() { b.len() - p } else { 0 }),
    decreases (if p < b.len() {
        b.len() - p
    } else {
        0
    }),
{
    hide(rfc_frame_body);
    if p < b.len() {
        let c = b.skip(p);
        lemma_decode_len_bounds(c);
        if let Ok((ty, n)) = rfc_frame_type(c) {
            if ty <= FRAME_HANDSHAKE_DONE && frame_permitted(ty, k) {
                lemma_body_crypto(ty, c.skip(n as int));
                if let Ok((f, m)) = rfc_frame_body(ty, c.skip(n as int)) {
                    lemma_frames_crypto_len(b, p + n + m, k);
                    if let Ok(fs) = rfc_frames(b, p + n + m, k) {
                        if !(f is Padding) {
                            lemma_frames_crypto_prepend(f, fs);
                        }
                    }
                }
            }
        }
    }
}

/// A payload's frames carry at most its bytes as CRYPTO data.
pub proof fn lemma_payload_crypto(b: Seq<u8>, k: PacketKind)
    ensures
        rfc_payload(b, k) matches Ok(fs) ==> frames_crypto(fs) <= b.len(),
{
    lemma_frames_crypto_len(b, 0, k);
}


/// The CRYPTO data bytes the packets' frames carry.
pub open spec fn plains_crypto(ps: Seq<SpecPlain>) -> nat
    decreases ps.len(),
{
    if ps.len() == 0 {
        0
    } else {
        plains_crypto(ps.drop_last()) + frames_crypto(ps.last().frames)
    }
}

/// `plains_crypto` of one packet then `ps`.
pub proof fn lemma_plains_crypto_prepend(p: SpecPlain, ps: Seq<SpecPlain>)
    ensures
        plains_crypto(seq![p] + ps) == frames_crypto(p.frames) + plains_crypto(ps),
    decreases ps.len(),
{
    if ps.len() == 0 {
        assert((seq![p] + ps).drop_last() =~= Seq::<SpecPlain>::empty());
        assert((seq![p] + ps).last() == p);
        assert(plains_crypto(Seq::<SpecPlain>::empty()) == 0);
    } else {
        assert((seq![p] + ps).drop_last() =~= seq![p] + ps.drop_last());
        assert((seq![p] + ps).last() == ps.last());
        lemma_plains_crypto_prepend(p, ps.drop_last());
    }
}

/// A prefix carries no more, and one more packet adds its own.
pub proof fn lemma_plains_crypto_take(ps: Seq<SpecPlain>, i: int)
    requires
        0 <= i <= ps.len(),
    ensures
        plains_crypto(ps.take(i)) <= plains_crypto(ps),
        i < ps.len() ==> plains_crypto(ps.take(i + 1)) == plains_crypto(ps.take(i)) + frames_crypto(ps[i].frames),
    decreases ps.len() - i,
{
    if i < ps.len() {
        assert(ps.take(i + 1).drop_last() =~= ps.take(i));
        lemma_plains_crypto_take(ps, i + 1);
    } else {
        assert(ps.take(i) =~= ps);
    }
}


/// A packet `rfc_open` opens carries at most its bytes as CRYPTO data.
proof fn lemma_open_crypto(pkt: Seq<u8>, kind: PacketKind, o: nat, k: SpecKeys, largest: Option<u64>)
    requires
        o + 20 <= pkt.len(),
    ensures
        rfc_open(pkt, kind, o, k, largest) matches Some((_, Ok(fs))) ==> frames_crypto(fs) <= pkt.len(),
{
    hide(spec_aes128_encrypt);
    hide(rfc_payload);
    hide(rfc_decode_pn);
    hide(gctr);
    let u = rfc_hp_remove(pkt, o, rfc_hp_mask(k.hp, rfc_sample(pkt, o)));
    assert(u.len() == pkt.len());
    let b0 = u[0];
    let n = spec_pn_len(b0);
    assert(1 <= n <= 4) by (bit_vector)
        requires
            n == ((b0 & 3u8) + 1) as u8,
    ;
    let e = (o + n) as int;
    if let Some((pn, Ok(fs))) = rfc_open(pkt, kind, o, k, largest) {
        let ct = u.subrange(e, pkt.len() as int);
        if let Some(pt) = spec_gcm_open(k.key, rfc_nonce(k.iv, pn), u.take(e), ct) {
            let c = ct.subrange(0, ct.len() - 16);
            lemma_gctr_len(k.key, inc32(gcm_j0(rfc_nonce(k.iv, pn))), c);
            lemma_payload_crypto(pt, kind);
        }
    }
}

/// A packet `rfc_unprotect` opens carries at most the bytes it consumes as CRYPTO data.
proof fn lemma_unprotect_crypto(b: Seq<u8>, keys: Seq<Option<SpecKeyPair>>, largest: Seq<Option<u64>>)
    ensures
        rfc_unprotect(b, keys, largest) matches Ok((Some(p), n)) ==> frames_crypto(p.frames) <= n,
{
    hide(rfc_open);
    hide(rfc_header);
    lemma_header_bounds(b);
    if b.len() <= MAX_UDP_PAYLOAD {
        match rfc_header(b, LOCAL_CID_LEN as nat) {
            Some(SpecHeader::Long { ty, dcid, scid, token, pn_offset, packet_end }) => {
                if !(ty is ZeroRtt) {
                    let kind = if ty is Initial {
                        PacketKind::Initial
                    } else {
                        PacketKind::Handshake
                    };
                    let pkt = b.take(packet_end as int);
                    if let Some(kp) = keys[crate::conn::space_idx(kind)] {
                        if !(pkt.len() < pn_offset + 20 || pn_exhausted(largest[crate::conn::space_idx(kind)])) {
                            lemma_open_crypto(pkt, kind, pn_offset, kp.rx, largest[crate::conn::space_idx(kind)]);
                        }
                    }
                }
            },
            Some(SpecHeader::Short { dcid, pn_offset }) => {
                if let Some(kp) = keys[2] {
                    if !(b.len() < pn_offset + 20 || pn_exhausted(largest[2])) {
                        lemma_open_crypto(b, PacketKind::OneRtt, pn_offset, kp.rx, largest[2]);
                    }
                }
            },
            _ => {},
        }
    }
}

/// The packets `open_from` opens from `off` on carry at most the bytes from `off` on as CRYPTO data.
proof fn lemma_open_from_crypto(d: Seq<u8>, off: nat, keys: Seq<Option<SpecKeyPair>>, largest: Seq<Option<u64>>)
    ensures
        plains_crypto(open_from(d, off, keys, largest).0) <= (if off < d.len() { d.len() - off } else { 0 }),
    decreases d.len() - off,
{
    if off < d.len() {
        let b = d.skip(off as int);
        if let Ok((p, n)) = rfc_unprotect(b, keys, largest) {
            if !(n == 0 || off + n > d.len()) {
                lemma_open_from_crypto(d, off + n, keys, largest);
                let r = open_from(d, off + n, keys, largest);
                if let Some(q) = p {
                    lemma_unprotect_crypto(b, keys, largest);
                    lemma_plains_crypto_prepend(q, r.0);
                }
            }
        }
    }
}

/// The packets of a datagram carry at most its bytes as CRYPTO data, and none at all past `MAX_UDP_PAYLOAD`.
pub proof fn lemma_open_datagram_crypto(d: Seq<u8>, keys: Seq<Option<SpecKeyPair>>, largest: Seq<Option<u64>>)
    ensures
        plains_crypto(rfc_open_datagram(d, keys, largest).packets) <= d.len(),
        d.len() > MAX_UDP_PAYLOAD ==> plains_crypto(rfc_open_datagram(d, keys, largest).packets) == 0,
        d.len() > MAX_UDP_PAYLOAD ==> rfc_open_datagram(d, keys, largest).packets.len() == 0 && rfc_open_datagram(
            d,
            keys,
            largest,
        ).error is None,
{
    if d.len() <= MAX_UDP_PAYLOAD {
        lemma_open_from_crypto(d, 0, keys, largest);
    }
}


// ---- The load (9b2 Task 10d): what the receive pipeline's per-call cost is linear in.

/// The data bytes frame `f` carries: CRYPTO's and STREAM's.
pub open spec fn frame_bytes(f: SpecFrame) -> nat {
    match f {
        SpecFrame::Crypto { data, .. } => data.len(),
        SpecFrame::Stream { data, .. } => data.len(),
        _ => 0,
    }
}

/// One frame's load: its type byte and its data.
pub open spec fn frame_load(f: SpecFrame) -> nat {
    1 + frame_bytes(f)
}

/// The frames' load.
pub open spec fn frames_load(fs: Seq<SpecFrame>) -> nat
    decreases fs.len(),
{
    if fs.len() == 0 {
        0
    } else {
        frames_load(fs.drop_last()) + frame_load(fs.last())
    }
}

/// `frames_load` of one frame then `fs`.
pub proof fn lemma_frames_load_prepend(f: SpecFrame, fs: Seq<SpecFrame>)
    ensures
        frames_load(seq![f] + fs) == frame_load(f) + frames_load(fs),
    decreases fs.len(),
{
    if fs.len() == 0 {
        assert((seq![f] + fs).drop_last() =~= Seq::<SpecFrame>::empty());
        assert((seq![f] + fs).last() == f);
        assert(frames_load(Seq::<SpecFrame>::empty()) == 0);
    } else {
        assert((seq![f] + fs).drop_last() =~= seq![f] + fs.drop_last());
        assert((seq![f] + fs).last() == fs.last());
        lemma_frames_load_prepend(f, fs.drop_last());
    }
}

/// A prefix loads no more, and one more frame adds its own.
pub proof fn lemma_frames_load_take(fs: Seq<SpecFrame>, i: int)
    requires
        0 <= i <= fs.len(),
    ensures
        frames_load(fs.take(i)) <= frames_load(fs),
        i < fs.len() ==> frames_load(fs.take(i + 1)) == frames_load(fs.take(i)) + frame_load(fs[i]),
    decreases fs.len() - i,
{
    if i < fs.len() {
        assert(fs.take(i + 1).drop_last() =~= fs.take(i));
        lemma_frames_load_take(fs, i + 1);
    } else {
        assert(fs.take(i) =~= fs);
    }
}

/// A frame body holds its CRYPTO or STREAM data: no more bytes than it consumes, within `b`.
pub proof fn lemma_body_bytes(ty: u64, b: Seq<u8>)
    requires
        ty <= FRAME_HANDSHAKE_DONE,
    ensures
        rfc_frame_body(ty, b) matches Ok((f, m)) ==> frame_bytes(f) <= m && frame_bytes(f) <= b.len(),
{
    lemma_frame_body_received(ty, b);
    if let Ok((f, m)) = rfc_frame_body(ty, b) {
        if f is Crypto {
            assert(ty == FRAME_CRYPTO);
            lemma_vints_ok(b);
        } else if f is Stream {
            assert(FRAME_STREAM_MIN <= ty <= FRAME_STREAM_MAX);
            lemma_vints_ok(b);
        }
    }
}

/// The frames from `p` on load at most the bytes from `p` on: each takes at least its type byte and its data.
pub proof fn lemma_frames_load_len(b: Seq<u8>, p: int, k: PacketKind)
    requires
        0 <= p,
    ensures
        rfc_frames(b, p, k) matches Ok(fs) ==> frames_load(fs) <= (if p < b.len() { b.len() - p } else { 0 }),
    decreases (if p < b.len() {
        b.len() - p
    } else {
        0
    }),
{
    hide(rfc_frame_body);
    if p < b.len() {
        let c = b.skip(p);
        lemma_decode_len_bounds(c);
        if let Ok((ty, n)) = rfc_frame_type(c) {
            if ty <= FRAME_HANDSHAKE_DONE && frame_permitted(ty, k) {
                lemma_body_bytes(ty, c.skip(n as int));
                if let Ok((f, m)) = rfc_frame_body(ty, c.skip(n as int)) {
                    // A frame takes its type byte and holds its data: `1 + bytes <= n + m`, and its data lies
                    // past the type, within what is left.
                    assert(1 <= n);
                    assert(frame_bytes(f) <= c.len() - n);
                    lemma_frames_load_len(b, p + n + m, k);
                    if let Ok(fs) = rfc_frames(b, p + n + m, k) {
                        if !(f is Padding) {
                            lemma_frames_load_prepend(f, fs);
                        }
                    }
                }
            }
        }
    }
}

/// A payload's frames load at most its bytes.
pub proof fn lemma_payload_load(b: Seq<u8>, k: PacketKind)
    ensures
        rfc_payload(b, k) matches Ok(fs) ==> frames_load(fs) <= b.len(),
{
    lemma_frames_load_len(b, 0, k);
}

/// One packet's load: one, and its frames'.
pub open spec fn plain_load(p: SpecPlain) -> nat {
    1 + frames_load(p.frames)
}

/// The packets' load.
pub open spec fn plains_load(ps: Seq<SpecPlain>) -> nat
    decreases ps.len(),
{
    if ps.len() == 0 {
        0
    } else {
        plains_load(ps.drop_last()) + plain_load(ps.last())
    }
}

/// `plains_load` of one packet then `ps`.
pub proof fn lemma_plains_load_prepend(p: SpecPlain, ps: Seq<SpecPlain>)
    ensures
        plains_load(seq![p] + ps) == plain_load(p) + plains_load(ps),
    decreases ps.len(),
{
    if ps.len() == 0 {
        assert((seq![p] + ps).drop_last() =~= Seq::<SpecPlain>::empty());
        assert((seq![p] + ps).last() == p);
        assert(plains_load(Seq::<SpecPlain>::empty()) == 0);
    } else {
        assert((seq![p] + ps).drop_last() =~= seq![p] + ps.drop_last());
        assert((seq![p] + ps).last() == ps.last());
        lemma_plains_load_prepend(p, ps.drop_last());
    }
}

/// A prefix loads no more, and one more packet adds its own.
pub proof fn lemma_plains_load_take(ps: Seq<SpecPlain>, i: int)
    requires
        0 <= i <= ps.len(),
    ensures
        plains_load(ps.take(i)) <= plains_load(ps),
        i < ps.len() ==> plains_load(ps.take(i + 1)) == plains_load(ps.take(i)) + plain_load(ps[i]),
    decreases ps.len() - i,
{
    if i < ps.len() {
        assert(ps.take(i + 1).drop_last() =~= ps.take(i));
        lemma_plains_load_take(ps, i + 1);
    } else {
        assert(ps.take(i) =~= ps);
    }
}

/// A packet `rfc_open` opens loads less than its bytes: its plaintext is 16 bytes shorter than its ciphertext.
proof fn lemma_open_load(pkt: Seq<u8>, kind: PacketKind, o: nat, k: SpecKeys, largest: Option<u64>)
    requires
        o + 20 <= pkt.len(),
    ensures
        rfc_open(pkt, kind, o, k, largest) matches Some((_, Ok(fs))) ==> 1 + frames_load(fs) <= pkt.len(),
{
    hide(spec_aes128_encrypt);
    hide(rfc_payload);
    hide(rfc_decode_pn);
    hide(gctr);
    let u = rfc_hp_remove(pkt, o, rfc_hp_mask(k.hp, rfc_sample(pkt, o)));
    assert(u.len() == pkt.len());
    let b0 = u[0];
    let n = spec_pn_len(b0);
    assert(1 <= n <= 4) by (bit_vector)
        requires
            n == ((b0 & 3u8) + 1) as u8,
    ;
    let e = (o + n) as int;
    if let Some((pn, Ok(fs))) = rfc_open(pkt, kind, o, k, largest) {
        let ct = u.subrange(e, pkt.len() as int);
        if let Some(pt) = spec_gcm_open(k.key, rfc_nonce(k.iv, pn), u.take(e), ct) {
            let c = ct.subrange(0, ct.len() - 16);
            lemma_gctr_len(k.key, inc32(gcm_j0(rfc_nonce(k.iv, pn))), c);
            lemma_payload_load(pt, kind);
        }
    }
}

/// A packet `rfc_unprotect` opens loads at most the bytes it consumes.
proof fn lemma_unprotect_load(b: Seq<u8>, keys: Seq<Option<SpecKeyPair>>, largest: Seq<Option<u64>>)
    ensures
        rfc_unprotect(b, keys, largest) matches Ok((Some(p), n)) ==> plain_load(p) <= n,
{
    hide(rfc_open);
    hide(rfc_header);
    lemma_header_bounds(b);
    if b.len() <= MAX_UDP_PAYLOAD {
        match rfc_header(b, LOCAL_CID_LEN as nat) {
            Some(SpecHeader::Long { ty, dcid, scid, token, pn_offset, packet_end }) => {
                if !(ty is ZeroRtt) {
                    let kind = if ty is Initial {
                        PacketKind::Initial
                    } else {
                        PacketKind::Handshake
                    };
                    let pkt = b.take(packet_end as int);
                    if let Some(kp) = keys[crate::conn::space_idx(kind)] {
                        if !(pkt.len() < pn_offset + 20 || pn_exhausted(largest[crate::conn::space_idx(kind)])) {
                            lemma_open_load(pkt, kind, pn_offset, kp.rx, largest[crate::conn::space_idx(kind)]);
                        }
                    }
                }
            },
            Some(SpecHeader::Short { dcid, pn_offset }) => {
                if let Some(kp) = keys[2] {
                    if !(b.len() < pn_offset + 20 || pn_exhausted(largest[2])) {
                        lemma_open_load(b, PacketKind::OneRtt, pn_offset, kp.rx, largest[2]);
                    }
                }
            },
            _ => {},
        }
    }
}

/// The packets `open_from` opens from `off` on load at most the bytes from `off` on.
proof fn lemma_open_from_load(d: Seq<u8>, off: nat, keys: Seq<Option<SpecKeyPair>>, largest: Seq<Option<u64>>)
    ensures
        plains_load(open_from(d, off, keys, largest).0) <= (if off < d.len() { d.len() - off } else { 0 }),
    decreases d.len() - off,
{
    if off < d.len() {
        let b = d.skip(off as int);
        if let Ok((p, n)) = rfc_unprotect(b, keys, largest) {
            if !(n == 0 || off + n > d.len()) {
                lemma_open_from_load(d, off + n, keys, largest);
                let r = open_from(d, off + n, keys, largest);
                if let Some(q) = p {
                    lemma_unprotect_load(b, keys, largest);
                    lemma_plains_load_prepend(q, r.0);
                }
            }
        }
    }
}

/// A datagram's packets load at most its bytes.
pub proof fn lemma_open_datagram_load(d: Seq<u8>, keys: Seq<Option<SpecKeyPair>>, largest: Seq<Option<u64>>)
    ensures
        plains_load(rfc_open_datagram(d, keys, largest).packets) <= d.len(),
{
    if d.len() <= MAX_UDP_PAYLOAD {
        lemma_open_from_load(d, 0, keys, largest);
    } else {
        lemma_open_datagram_crypto(d, keys, largest);
    }
}


} // verus!
