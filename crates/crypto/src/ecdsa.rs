//! ECDSA P-256/SHA-256 (FIPS 186-5 §6.4.1) with RFC 6979 deterministic nonces: spec and an exec
//! signature backed by the trusted shim. Also the ECDSA-Sig-Value DER encoding (RFC 3279 §2.2.3,
//! X.690 §8.3), as verified exec code.
#[allow(unused_imports)]
use crate::bytes::*;
#[allow(unused_imports)]
use crate::hmac::*;
#[allow(unused_imports)]
use crate::p256::*;
#[allow(unused_imports)]
use crate::sha256::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::power::*;

verus! {

// Every spec below is specialized to qlen = hlen = rlen = 256 (P-256 with SHA-256), so
// bits2int (RFC 6979 §2.3.2) is os2ip, int2octets (§2.3.3) is i2osp(_, 32), and step h.2 of
// §3.2 takes exactly one HMAC.

/// RFC 6979 §2.3.4 bits2octets: int2octets(bits2int(h1) mod q), with q = n.
pub open spec fn bits2octets(h1: Seq<u8>) -> Seq<u8> {
    i2osp((os2ip(h1) as int % p256_n()) as nat, 32)
}

/// RFC 6979 §3.2 steps b-g: returns (K, V) after step g.
/// - Step b: V = 0x01 0x01 ... 0x01 (32 octets). Step c: K = 0x00 0x00 ... 0x00 (32 octets).
/// - Step d: K = HMAC_K(V || 0x00 || int2octets(x) || bits2octets(h1)). Step e: V = HMAC_K(V).
/// - Step f: K = HMAC_K(V || 0x01 || int2octets(x) || bits2octets(h1)). Step g: V = HMAC_K(V).
/// `x` is the 32-octet private key, which is already int2octets(x).
pub open spec fn rfc6979_init(x: Seq<u8>, h1: Seq<u8>) -> (Seq<u8>, Seq<u8>) {
    let v0 = Seq::new(32, |i: int| 0x01u8);
    let k0 = Seq::new(32, |i: int| 0x00u8);
    let b = bits2octets(h1);
    let k1 = spec_hmac_sha256(k0, v0 + seq![0x00u8] + x + b);
    let v1 = spec_hmac_sha256(k1, v0);
    let k2 = spec_hmac_sha256(k1, v1 + seq![0x01u8] + x + b);
    let v2 = spec_hmac_sha256(k2, v1);
    (k2, v2)
}

/// RFC 6979 §3.2 step h: the (K, V) before attempt i.
/// - Attempt 0 starts from steps b-g.
/// - Attempt i + 1 starts after attempt i's step h.2 (T = V = HMAC_K(V)) and step h.3
///   (K = HMAC_K(V || 0x00), then V = HMAC_K(V)).
/// Every rejection takes this one transition: k outside [1, q - 1] (step h.3), and r = 0
/// (§3.4) or s = 0 for an otherwise valid k. This matches RustCrypto's HMAC_DRBG, whose every
/// `fill_bytes` is one h.2 plus one h.3 update.
pub open spec fn rfc6979_state(x: Seq<u8>, h1: Seq<u8>, i: nat) -> (Seq<u8>, Seq<u8>)
    decreases i,
{
    if i == 0 {
        rfc6979_init(x, h1)
    } else {
        let (k, v) = rfc6979_state(x, h1, (i - 1) as nat);
        let t = spec_hmac_sha256(k, v);
        let k2 = spec_hmac_sha256(k, t + seq![0x00u8]);
        let v2 = spec_hmac_sha256(k2, t);
        (k2, v2)
    }
}

/// RFC 6979 §3.2 step h.2 (V = HMAC_K(V), T = V; one block since tlen = qlen = 256) and h.3
/// (k = bits2int(T)): the candidate k of attempt i, compared with n by `suitable`, not reduced.
pub open spec fn rfc6979_k(x: Seq<u8>, h1: Seq<u8>, i: nat) -> nat {
    let (k, v) = rfc6979_state(x, h1, i);
    os2ip(spec_hmac_sha256(k, v))
}

/// RFC 6979 §2.4 step 3 (FIPS 186-5 §6.4.1 steps 5-8): r = x-coordinate of kG mod n.
/// kG = O cannot occur for k in [1, n - 1]; it maps to 0, which `suitable` rejects.
pub open spec fn ecdsa_r(k: nat) -> nat {
    match scalar_mult(k, p256_g()) {
        SpecPoint::Infinity => 0,
        SpecPoint::Affine(x, _) => (x % p256_n()) as nat,
    }
}

/// RFC 6979 §2.4 step 4 (FIPS 186-5 §6.4.1 steps 4 and 9): s = k^-1 (h + r d) mod n, with
/// the inverse by Fermat (n is prime).
pub open spec fn ecdsa_s(d: nat, h: nat, k: nat) -> nat {
    ((pow(k as int, (p256_n() - 2) as nat) * (h + ecdsa_r(k) * d)) % p256_n()) as nat
}

/// RFC 6979 §2.4 step 1: h = bits2int(H(m)) mod n. FIPS 186-5 §6.4.1 step 2 leaves e
/// unreduced; s mod n is the same either way.
pub open spec fn ecdsa_h(h1: Seq<u8>) -> nat {
    (os2ip(h1) as int % p256_n()) as nat
}

/// Attempt i yields a signature: k in [1, n - 1] (RFC 6979 §3.2 step h.3), r != 0 (§3.4) and
/// s != 0 (SEC 1 v2 §4.1.3 steps 3 and 6: return to step 1). FIPS 186-5 §6.4.1 step 11 outputs
/// failure for a deterministic k with r = 0 or s = 0; RFC 6979 §3.4, SEC 1 and RustCrypto retry, as here.
pub open spec fn suitable(x: Seq<u8>, h1: Seq<u8>, i: nat) -> bool {
    let k = rfc6979_k(x, h1, i);
    1 <= k < p256_n() && ecdsa_r(k) != 0 && ecdsa_s(os2ip(x), ecdsa_h(h1), k) != 0
}

/// RFC 6979 §3.2 step h (loop until a proper k is found): attempt i is the first suitable one.
pub open spec fn least_suitable(x: Seq<u8>, h1: Seq<u8>, i: nat) -> bool {
    suitable(x, h1, i) && forall|j: nat| j < i ==> !#[trigger] suitable(x, h1, j)
}

/// ECDSA P-256/SHA-256 signing (FIPS 186-5 §6.4.1) with the nonce of RFC 6979 §3.2, as
/// r || s, each I2OSP'd to 32 octets. None for d outside [1, n - 1] (SEC 1 v2 §3.2.1 step 1),
/// and None if no attempt is suitable. No low-S normalization: s is returned as computed.
pub open spec fn spec_ecdsa_p256_sha256_sign(d: Seq<u8>, msg: Seq<u8>) -> Option<Seq<u8>> {
    if !scalar_valid(d) {
        None
    } else {
        let h1 = spec_sha256(msg);
        if exists|i: nat| #[trigger] least_suitable(d, h1, i) {
            let i = choose|i: nat| #[trigger] least_suitable(d, h1, i);
            let k = rfc6979_k(d, h1, i);
            Some(i2osp(ecdsa_r(k), 32) + i2osp(ecdsa_s(os2ip(d), ecdsa_h(h1), k), 32))
        } else {
            None
        }
    }
}

/// Trusted shim: the body is RustCrypto p256; the ensures is the trusted statement.
/// Partial correctness: where the spec is None (no suitable attempt, probability ~2^-256) the
/// shim loops forever instead of returning.
#[verifier::external_body]
pub fn p256_ecdsa_sign(d: &[u8], msg: &[u8]) -> (r: Option<[u8; 64]>)
    requires
        d@.len() == 32,
        msg@.len() <= MAX_INPUT_LEN,
    ensures
        r.deep_view() == spec_ecdsa_p256_sha256_sign(d@, msg@),
{
    crate::shim::p256_ecdsa_sign(d, msg)
}

/// X.690 §8.3.2: the minimal big-endian octets of x (one octet 0x00 for 0).
pub open spec fn min_octets(x: nat) -> Seq<u8>
    decreases x,
{
    if x < 256 {
        seq![x as u8]
    } else {
        min_octets(x / 256).push((x % 256) as u8)
    }
}

/// X.690 §8.3.2-8.3.3: the contents octets of a nonnegative INTEGER: the minimal two's-complement
/// form, i.e. the minimal octets with 0x00 prepended when the first octet's top bit is set.
pub open spec fn der_uint_content(x: nat) -> Seq<u8> {
    let m = min_octets(x);
    if m[0] >= 0x80u8 {
        seq![0x00u8] + m
    } else {
        m
    }
}

/// RFC 8446 §4.2.3 -> RFC 3279 §2.2.3 ECDSA-Sig-Value ::= SEQUENCE { r INTEGER, s INTEGER },
/// DER (X.690 §8.9, §8.3), with r = os2ip(sig[0..32]) and s = os2ip(sig[32..64]).
/// Each INTEGER content is at most 33 octets, so every length is at most 70 and the short form
/// (X.690 §8.1.3.4) is the minimal definite form DER requires (X.690 §10.1).
pub open spec fn spec_ecdsa_der(sig: Seq<u8>) -> Seq<u8> {
    let cr = der_uint_content(os2ip(sig.subrange(0, 32)));
    let cs = der_uint_content(os2ip(sig.subrange(32, 64)));
    seq![0x30u8, (4 + cr.len() + cs.len()) as u8] + seq![0x02u8, cr.len() as u8] + cr
        + seq![0x02u8, cs.len() as u8] + cs
}

/// Leading zero octets do not change os2ip.
proof fn lemma_os2ip_strip(t: Seq<u8>, k: int)
    requires
        0 <= k <= t.len(),
        forall|j: int| 0 <= j < k ==> t[j] == 0,
    ensures
        os2ip(t) == os2ip(t.subrange(k, t.len() as int)),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(t.subrange(k, 0) =~= t);
    } else if k == t.len() {
        lemma_os2ip_strip(t.drop_last(), k - 1);
        assert(t.drop_last().subrange(k - 1, k - 1) =~= Seq::<u8>::empty());
        assert(t.subrange(k, k) =~= Seq::<u8>::empty());
    } else {
        lemma_os2ip_strip(t.drop_last(), k);
        let s = t.subrange(k, t.len() as int);
        assert(s.drop_last() =~= t.drop_last().subrange(k, t.len() - 1));
    }
}

/// A nonempty octet string with a nonzero first octet is at least 1 as an integer.
proof fn lemma_os2ip_pos(t: Seq<u8>)
    requires
        t.len() >= 1,
        t[0] != 0,
    ensures
        os2ip(t) >= 1,
    decreases t.len(),
{
    if t.len() > 1 {
        lemma_os2ip_pos(t.drop_last());
    } else {
        assert(t.drop_last() =~= Seq::<u8>::empty());
    }
}

/// An octet string with no leading zero octet (or a single octet) is the minimal octets of its
/// os2ip.
proof fn lemma_min_octets_os2ip(t: Seq<u8>)
    requires
        t.len() >= 1,
        t[0] != 0 || t.len() == 1,
    ensures
        min_octets(os2ip(t)) == t,
    decreases t.len(),
{
    let p = t.drop_last();
    if t.len() == 1 {
        assert(p =~= Seq::<u8>::empty());
        assert(min_octets(os2ip(t)) =~= t);
    } else {
        lemma_os2ip_pos(p);
        lemma_min_octets_os2ip(p);
        let x = os2ip(t);
        lemma_fundamental_div_mod_converse(x as int, 256, os2ip(p) as int, t.last() as int);
        assert(x >= 256);
        assert(min_octets(x) =~= t);
    }
}

/// The first nonzero octet of sig[off..off + 32], or off + 31 if there is none: sig[z..off + 32]
/// is then the minimal octets of os2ip(sig[off..off + 32]).
fn der_start(sig: &[u8], off: usize) -> (z: usize)
    requires
        sig@.len() == 64,
        off <= 32,
    ensures
        off <= z < off + 32,
        min_octets(os2ip(sig@.subrange(off as int, off + 32))) == sig@.subrange(z as int, off + 32),
{
    let mut z = off;
    while z < off + 31 && sig[z] == 0
        invariant
            sig@.len() == 64,
            off <= 32,
            off <= z <= off + 31,
            forall|j: int| off <= j < z ==> sig@[j] == 0,
        decreases off + 31 - z,
    {
        z += 1;
    }
    proof {
        let t = sig@.subrange(off as int, off + 32);
        let k = z - off;
        lemma_os2ip_strip(t, k);
        let u = t.subrange(k, 32);
        assert(u =~= sig@.subrange(z as int, off + 32));
        lemma_min_octets_os2ip(u);
    }
    z
}

/// Pushes 0x02, the length and the contents octets of the INTEGER whose minimal octets are
/// sig[z..end].
fn push_der_uint(sig: &[u8], z: usize, end: usize, len: usize, out: &mut Vec<u8>)
    requires
        z < end <= sig@.len(),
        len == der_uint_content(os2ip(sig@.subrange(end - 32, end as int))).len(),
        end >= 32,
        min_octets(os2ip(sig@.subrange(end - 32, end as int))) == sig@.subrange(z as int, end as int),
    ensures
        final(out)@ == old(out)@ + seq![0x02u8, len as u8] + der_uint_content(os2ip(sig@.subrange(end - 32, end as int))),
{
    let ghost c = der_uint_content(os2ip(sig@.subrange(end - 32, end as int)));
    let ghost m = sig@.subrange(z as int, end as int);
    let ghost pre = if sig@[z as int] >= 0x80u8 { seq![0x00u8] } else { Seq::<u8>::empty() };
    out.push(0x02);
    out.push(len as u8);
    if sig[z] >= 0x80 {
        out.push(0x00);
    }
    let ghost base = out@;
    assert(base =~= old(out)@ + seq![0x02u8, len as u8] + pre);
    assert(c =~= pre + m);
    let mut i = z;
    while i < end
        invariant
            z <= i <= end <= sig@.len(),
            out@ =~= base + sig@.subrange(z as int, i as int),
        decreases end - i,
    {
        out.push(sig[i]);
        assert(sig@.subrange(z as int, i + 1) =~= sig@.subrange(z as int, i as int).push(sig@[i as int]));
        i += 1;
    }
    assert(out@ =~= old(out)@ + seq![0x02u8, len as u8] + c);
}

/// Appends the DER ECDSA-Sig-Value of r || s (`spec_ecdsa_der`) to `out`.
pub fn serialize_ecdsa_der(sig: &[u8], out: &mut Vec<u8>)
    requires
        sig@.len() == 64,
    ensures
        final(out)@ == old(out)@ + spec_ecdsa_der(sig@),
{
    let zr = der_start(sig, 0);
    let zs = der_start(sig, 32);
    let lr: usize = if sig[zr] >= 0x80 { 33 - zr } else { 32 - zr };
    let ls: usize = if sig[zs] >= 0x80 { 65 - zs } else { 64 - zs };
    out.push(0x30);
    out.push((4 + lr + ls) as u8);
    push_der_uint(sig, zr, 32, lr, out);
    push_der_uint(sig, zs, 64, ls, out);
    assert(out@ =~= old(out)@ + spec_ecdsa_der(sig@));
}

} // verus!
