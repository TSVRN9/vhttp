//! ECDSA P-256/SHA-256 (FIPS 186-5 §6.4.1) with RFC 6979 deterministic nonces: spec and the
//! verified exec signature. Also the ECDSA-Sig-Value DER encoding (RFC 3279 §2.2.3,
//! X.690 §8.3), as verified exec code.
#[allow(unused_imports)]
use crate::bytes::*;
#[allow(unused_imports)]
use crate::hmac::*;
#[allow(unused_imports)]
use crate::mont::*;
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

/// FIPS 186-5 §6.4.1 with RFC 6979 §3.2 nonces; verified against spec_ecdsa_p256_sha256_sign. Partially correct: loops while no attempt is suitable (probability ~2^-256), as RFC 6979 §3.2 step h does.
#[cfg_attr(ct_check, ct::secret(d), ct::public(msg))]
#[verifier::exec_allows_no_decreases_clause]
pub fn p256_ecdsa_sign(d: &[u8], msg: &[u8]) -> (r: Option<[u8; 64]>)
    requires
        d@.len() == 32,
        msg@.len() <= MAX_INPUT_LEN,
    ensures
        r.deep_view() == spec_ecdsa_p256_sha256_sign(d@, msg@),
{
    hide(point_add);
    hide(scalar_mult);
    hide(finv);
    hide(spec_hmac_sha256);
    hide(spec_sha256);
    hide(rfc6979_init);
    hide(rfc6979_k);
    hide(ecdsa_r);
    hide(ecdsa_s);
    // ct: declassify d in [1, n - 1] (key validity is a public error outcome)
    if !crate::ct::declassify(scalar_in_range(d)) {
        return None;
    }
    let h1 = sha256(msg);
    let (mut kk, mut vv) = rfc6979_init_exec(d, &h1);
    let ghost mut i: nat = 0;
    proof {
        assert(d@.subrange(0, 32) =~= d@);
        assert(h1@.subrange(0, 32) =~= h1@);
    }
    loop
        invariant
            d@.len() == 32,
            scalar_valid(d@),
            d@.subrange(0, 32) == d@,
            h1@.subrange(0, 32) == h1@,
            h1@ == spec_sha256(msg@),
            (kk@, vv@) == rfc6979_state(d@, h1@, i),
            forall|j: nat| j < i ==> !#[trigger] suitable(d@, h1@, j),
    {
        let (t, k2, v2) = rfc6979_next(&kk, &vv);
        proof {
            lemma_rfc6979_step(d@, h1@, i);
            assert(t@.subrange(0, 32) =~= t@);
        }
        // ct: declassify k in [1, n - 1] (the RFC 6979 §3.2 step h.3 retry, probability ~2^-32)
        if crate::ct::declassify(scalar_in_range(&t)) {
            let r = ecdsa_r_exec(&t);
            let s = ecdsa_s_exec(&limbs_from_be(d, 0), &reduce_n(&h1, 0), &limbs_from_be(&t, 0), &r);
            // ct: declassify the r = 0 / s = 0 outcomes (the RFC 6979 retry is visible through the loop count; r = 0 or s = 0 has negligible probability)
            if crate::ct::declassify(is_zero4(&r)) == 0
                && crate::ct::declassify(is_zero4(&s)) == 0
            {
                proof {
                    lemma_least_suitable_choose(d@, h1@, i);
                }
                let sig = cat64(&limbs_to_be(&r), &limbs_to_be(&s));
                assert(sig.deep_view() =~= sig@);
                return Some(sig);
            }
        }
        proof {
            i = i + 1;
        }
        kk = k2;
        vv = v2;
    }
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

// ---- Scalars mod n in Montgomery form over crate::mont (R = 2^256); values from Task 1 Step 4 ----

const N_LIMBS: [u64; 4] = [0xf3b9cac2fc632551, 0xbce6faada7179e84, 0xffffffffffffffff, 0xffffffff00000000];

// -n^-1 mod 2^64.
const N_MP: u64 = 0xccd1c8aaee00bc4f;

// R^2 mod n, the encode multiplier.
const R2_N: [u64; 4] = [0x83244c95be79eea2, 0x4699799c49bd6fa6, 0x2845b2392b6bec59, 0x66e12d94f3d95620];

// R mod n, the Montgomery form of 1.
const ONE_N: [u64; 4] = [0x0c46353d039cdaaf, 0x4319055258e8617b, 0x0000000000000000, 0x00000000ffffffff];

// R^-1 mod n (a spec fn, like p256.rs rinv_p()).
spec fn rinv_n() -> int {
    0x60d066334905c1e907f8b6041e607725badef3e243566fafce1bc8f79c197c79int
}

// n - 2, big-endian: the Fermat exponent of ecdsa_s.
const P256_N_MINUS_2: [u8; 32] = [
    0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63, 0x25, 0x4f,
];

// The Fermat exponent is n - 2.
proof fn lemma_exp_const_n()
    ensures
        os2ip(P256_N_MINUS_2@) == p256_n() - 2,
{
    assert(os2ip(P256_N_MINUS_2@) == p256_n() - 2) by (compute_only);
}

// Montgomery decode of canonical limbs into Z/nZ.
spec fn sc(l: [u64; 4]) -> int {
    mdec(v4(l), p256_n(), rinv_n())
}

// The Montgomery constants for n, checked by Z3 on literals; n > 2^255 bounds reduce_n.
proof fn lemma_mont_consts_n()
    ensures
        v4(N_LIMBS) == p256_n(),
        0x8000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int < p256_n(),
        (N_LIMBS[0] as int * N_MP as int + 1) % 0x1_0000_0000_0000_0000 == 0,
        (0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 * rinv_n()) % p256_n() == 1,
        v4(R2_N) < p256_n(),
        sc(R2_N) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int % p256_n(),
        v4(ONE_N) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int % p256_n(),
{
    lemma_p256_consts();
}

// Cancelling R: if v < n and v * R == u (mod n), then v is the decode of u.
proof fn lemma_unmont_n(v: int, u: int)
    requires
        0 <= v < p256_n(),
        (v * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000) % p256_n() == u % p256_n(),
    ensures
        v == mdec(u, p256_n(), rinv_n()),
{
    let (n, rr) = (p256_n(), 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int);
    lemma_mont_consts_n();
    // u * ri == v * R * ri == v * (R * ri) == v (mod n)
    lemma_mul_mod_noop_left(u, rinv_n(), n);
    lemma_mul_mod_noop_left(v * rr, rinv_n(), n);
    assert((v * rr) * rinv_n() == v * (rr * rinv_n())) by {
        broadcast use vstd::arithmetic::mul::group_mul_properties;
    }
    lemma_mul_mod_noop_right(v, rr * rinv_n(), n);
    lemma_small_mod(v as nat, n as nat);
}

// sc(r) == sc(a) * sc(b) mod n.
#[cfg_attr(ct_check, ct::secret(a, b))]
fn sc_mul(a: [u64; 4], b: [u64; 4]) -> (r: [u64; 4])
    requires
        v4(a) < p256_n(),
        v4(b) < p256_n(),
    ensures
        v4(r) < p256_n(),
        sc(r) == (sc(a) * sc(b)) % p256_n(),
{
    proof {
        lemma_mont_consts_n();
    }
    let r = mont_mul(&a, &b, &N_LIMBS, N_MP);
    proof {
        lemma_mdec_mul(v4(r), v4(a), v4(b), p256_n(), 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int, rinv_n());
    }
    r
}

// sc(r) == sc(a) + sc(b) mod n.
#[cfg_attr(ct_check, ct::secret(a, b))]
fn sc_add(a: [u64; 4], b: [u64; 4]) -> (r: [u64; 4])
    requires
        v4(a) < p256_n(),
        v4(b) < p256_n(),
    ensures
        v4(r) < p256_n(),
        sc(r) == (sc(a) + sc(b)) % p256_n(),
{
    proof {
        lemma_mont_consts_n();
    }
    let r = add_mod(&a, &b, &N_LIMBS);
    proof {
        lemma_mdec_add(v4(a), v4(b), p256_n(), rinv_n());
    }
    r
}

// Encoding by R^2: if r decodes to x * dec(r2) and r2 decodes to R, then r decodes to x < m.
// Stated over abstract m, ri so that Z3 does not multiply the literals.
proof fn lemma_to_mont(r: int, x: int, r2: int, m: int, rr: int, ri: int)
    requires
        m > 1,
        0 <= x < m,
        (rr * ri) % m == 1,
        mdec(r, m, ri) == (mdec(x, m, ri) * mdec(r2, m, ri)) % m,
        mdec(r2, m, ri) == rr % m,
    ensures
        mdec(r, m, ri) == x,
{
    // (x ri mod m) (R mod m) == x (R ri) == x (mod m)
    lemma_mod_mul_cong(x * ri, rr, m);
    assert((x * ri) * rr == x * (rr * ri)) by {
        broadcast use vstd::arithmetic::mul::group_mul_properties;
    }
    lemma_mul_mod_noop_right(x, rr * ri, m);
    lemma_small_mod(x as nat, m as nat);
}

// The Montgomery form of the plain value v4(a) < n: a * R^2 * R^-1.
#[cfg_attr(ct_check, ct::secret(a))]
fn sc_in(a: &[u64; 4]) -> (r: [u64; 4])
    requires
        v4(*a) < p256_n(),
    ensures
        v4(r) < p256_n(),
        sc(r) == v4(*a),
{
    proof {
        lemma_mont_consts_n();
    }
    let r = mont_mul(a, &R2_N, &N_LIMBS, N_MP);
    proof {
        let rr = 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int;
        lemma_mdec_mul(v4(r), v4(*a), v4(R2_N), p256_n(), rr, rinv_n());
        lemma_v4_bound(*a);
        lemma_to_mont(v4(r), v4(*a), v4(R2_N), p256_n(), rr, rinv_n());
    }
    r
}

// The plain value of a Montgomery-form scalar: multiply by 1.
#[cfg_attr(ct_check, ct::secret(a))]
fn sc_out(a: &[u64; 4]) -> (r: [u64; 4])
    ensures
        v4(r) == sc(*a),
{
    proof {
        lemma_mont_consts_n();
    }
    let w1: [u64; 4] = [1, 0, 0, 0];
    let d = mont_mul(a, &w1, &N_LIMBS, N_MP);
    proof {
        lemma_mul_one(v4(*a), v4(w1));
        lemma_v4_bound(d);
        lemma_unmont_n(v4(d), v4(*a));
    }
    d
}

// os2ip(b[off..off + 32]) mod n. That integer is below 2^256 < 2n, so one masked conditional
// subtract of n reduces it.
#[cfg_attr(ct_check, ct::secret(b), ct::public(off))]
fn reduce_n(b: &[u8], off: usize) -> (r: [u64; 4])
    requires
        off + 32 <= b@.len(),
    ensures
        v4(r) == os2ip(b@.subrange(off as int, off + 32)) as int % p256_n(),
{
    proof {
        lemma_mont_consts_n();
    }
    let x = limbs_from_be(b, off);
    let (d, bo) = sub4(&x, &N_LIMBS);
    // keep x iff x < n, i.e. the subtract borrowed
    let r = select4(bo, &x, &d);
    proof {
        let (xv, n) = (v4(x), p256_n());
        lemma_v4_bound(x);
        lemma_v4_bound(d);
        if bo == 1 {
            lemma_fundamental_div_mod_converse_mod(xv, n, 0, xv);
        } else {
            lemma_fundamental_div_mod_converse_mod(xv, n, 1, xv - n);
        }
    }
    r
}

// RFC 6979 §2.3.4 bits2octets(h1) = int2octets(bits2int(h1) mod n).
#[cfg_attr(ct_check, ct::secret(h1))]
fn bits2octets_exec(h1: &[u8; 32]) -> (r: [u8; 32])
    ensures
        r@ == bits2octets(h1@),
{
    let l = reduce_n(h1, 0);
    proof {
        assert(h1@.subrange(0, 32) =~= h1@);
    }
    limbs_to_be(&l)
}

// ecdsa_r is the x-coordinate mod n, or 0.
proof fn lemma_ecdsa_r_lt_n(k: nat)
    ensures
        ecdsa_r(k) < p256_n(),
{
    hide(scalar_mult);
    lemma_p256_consts();
}

// RFC 6979 §2.4 step 4: s = k^-1 (h + r d) mod n on plain values, with k^-1 = k^(n - 2) (D4).
// The four inputs go into Montgomery form, and s comes back out.
#[cfg_attr(ct_check, ct::secret(d, h, k, r))]
fn ecdsa_s_exec(d: &[u64; 4], h: &[u64; 4], k: &[u64; 4], r: &[u64; 4]) -> (s: [u64; 4])
    requires
        v4(*d) < p256_n(),
        v4(*h) < p256_n(),
        1 <= v4(*k) < p256_n(),
        v4(*r) == ecdsa_r(v4(*k) as nat),
    ensures
        v4(s) == ecdsa_s(v4(*d) as nat, v4(*h) as nat, v4(*k) as nat),
{
    hide(ecdsa_r);
    hide(scalar_mult);
    hide(point_add);
    hide(spec_hmac_sha256);
    hide(spec_sha256);
    proof {
        lemma_mont_consts_n();
        lemma_exp_const_n();
        lemma_ecdsa_r_lt_n(v4(*k) as nat);
    }
    let dm = sc_in(d);
    let hm = sc_in(h);
    let km = sc_in(k);
    let rm = sc_in(r);
    let kinv = mont_pow(&km, &P256_N_MINUS_2, &N_LIMBS, N_MP, &ONE_N, Ghost(rinv_n()));
    let sm = sc_mul(kinv, sc_add(hm, sc_mul(rm, dm)));
    proof {
        let (n, hv, x) = (p256_n(), v4(*h), v4(*r) * v4(*d));
        let pk = pow(v4(*k), (n - 2) as nat);
        // kinv (h + (r d mod n) mod n) == k^(n - 2) (h + r d) (mod n)
        lemma_mod_add_cong(hv, x, n);
        lemma_mod_mul_cong(pk, hv + x, n);
    }
    sc_out(&sm)
}

// v || sep || x || b: the HMAC input of RFC 6979 §3.2 steps d and f.
#[cfg_attr(ct_check, ct::secret(v, x, b), ct::public(sep))]
fn cat97(v: &[u8; 32], sep: u8, x: &[u8], b: &[u8; 32]) -> (r: [u8; 97])
    requires
        x@.len() == 32,
    ensures
        r@ == v@ + seq![sep] + x@ + b@,
{
    let mut r = [0u8; 97];
    r[32] = sep;
    let mut i: usize = 0;
    while i < 32
        invariant
            i <= 32,
            x@.len() == 32,
            r@[32] == sep,
            forall|j: int| 0 <= j < i ==> r@[j] == v@[j] && r@[33 + j] == x@[j] && r@[65 + j] == b@[j],
        decreases 32 - i,
    {
        r[i] = v[i];
        r[33 + i] = x[i];
        r[65 + i] = b[i];
        i += 1;
    }
    assert(r@ =~= v@ + seq![sep] + x@ + b@);
    r
}

// t || 0x00: the HMAC input of RFC 6979 §3.2 step h.3.
#[cfg_attr(ct_check, ct::secret(t))]
fn cat33(t: &[u8; 32]) -> (r: [u8; 33])
    ensures
        r@ == t@ + seq![0x00u8],
{
    let mut r = [0u8; 33];
    let mut i: usize = 0;
    while i < 32
        invariant
            i <= 32,
            r@[32] == 0,
            forall|j: int| 0 <= j < i ==> r@[j] == t@[j],
        decreases 32 - i,
    {
        r[i] = t[i];
        i += 1;
    }
    assert(r@ =~= t@ + seq![0x00u8]);
    r
}

// RFC 6979 §3.2 steps b-g: (K, V) after step g.
#[cfg_attr(ct_check, ct::secret(x, h1))]
fn rfc6979_init_exec(x: &[u8], h1: &[u8; 32]) -> (r: ([u8; 32], [u8; 32]))
    requires
        x@.len() == 32,
    ensures
        (r.0@, r.1@) == rfc6979_init(x@, h1@),
{
    hide(spec_hmac_sha256);
    let b = bits2octets_exec(h1);
    let v0 = [0x01u8; 32];
    let k0 = [0x00u8; 32];
    proof {
        assert(v0@ =~= Seq::new(32, |i: int| 0x01u8));
        assert(k0@ =~= Seq::new(32, |i: int| 0x00u8));
    }
    let m0 = cat97(&v0, 0x00, x, &b);
    let k1 = hmac_sha256(&k0, &m0);
    let v1 = hmac_sha256(&k1, &v0);
    let m1 = cat97(&v1, 0x01, x, &b);
    let k2 = hmac_sha256(&k1, &m1);
    let v2 = hmac_sha256(&k2, &v1);
    (k2, v2)
}

// RFC 6979 §3.2 step h from (K, V): h.2 T = V' = HMAC_K(V), then h.3 K' = HMAC_K(T || 0x00) and
// V'' = HMAC_K'(T). Returns (T, K', V''), rfc6979_state's one transition.
#[cfg_attr(ct_check, ct::secret(k, v))]
fn rfc6979_next(k: &[u8; 32], v: &[u8; 32]) -> (r: ([u8; 32], [u8; 32], [u8; 32]))
    ensures
        r.0@ == spec_hmac_sha256(k@, v@),
        r.1@ == spec_hmac_sha256(k@, r.0@ + seq![0x00u8]),
        r.2@ == spec_hmac_sha256(r.1@, r.0@),
{
    hide(spec_hmac_sha256);
    let t = hmac_sha256(k, v);
    let m = cat33(&t);
    let k2 = hmac_sha256(k, &m);
    let v2 = hmac_sha256(&k2, &t);
    (t, k2, v2)
}

// rfc6979_k(i) and rfc6979_state(i + 1), unfolded once from rfc6979_state(i) in rfc6979_next's shapes.
proof fn lemma_rfc6979_step(x: Seq<u8>, h1: Seq<u8>, i: nat)
    ensures
        ({
            let (k, v) = rfc6979_state(x, h1, i);
            let t = spec_hmac_sha256(k, v);
            let k2 = spec_hmac_sha256(k, t + seq![0x00u8]);
            &&& rfc6979_k(x, h1, i) == os2ip(t)
            &&& rfc6979_state(x, h1, (i + 1) as nat) == (k2, spec_hmac_sha256(k2, t))
        }),
{
    hide(spec_hmac_sha256);
    hide(rfc6979_init);
}

// I2OSP(x, 32) round-trips through OS2IP for x < p < 2^256 = 256^32.
proof fn lemma_os2ip_i2osp_p(x: nat)
    requires
        x < p256_p(),
    ensures
        os2ip(i2osp(x, 32)) == x,
{
    lemma_p256_consts();
    reveal_with_fuel(pow, 33);
    assert(pow(256, 32) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int);
    lemma_os2ip_i2osp(x, 32);
}

// RFC 6979 §2.4 step 3: r = x(kG) mod n. kG != O for k in [1, n - 1] (Phase 5d), so there is no O case.
#[cfg_attr(ct_check, ct::secret(k))]
fn ecdsa_r_exec(k: &[u8; 32]) -> (r: [u64; 4])
    requires
        1 <= os2ip(k@) < p256_n(),
    ensures
        v4(r) == ecdsa_r(os2ip(k@)),
{
    hide(point_add);
    hide(scalar_mult);
    hide(finv);
    proof {
        lemma_g_on_curve();
    }
    let q = scalar_mult_ct(k, &g_point());
    proof {
        crate::p256_group::lemma_scalar_mult_g_nonzero(os2ip(k@));
        lemma_p256_consts();
    }
    let xb = fe_to_be(&q.x);
    proof {
        lemma_os2ip_i2osp_p(fe(q.x) as nat);
        assert(xb@.subrange(0, 32) =~= xb@);
    }
    reduce_n(&xb, 0)
}

// r || s, the output of p256_ecdsa_sign.
#[cfg_attr(ct_check, ct::secret(r, s))]
fn cat64(r: &[u8; 32], s: &[u8; 32]) -> (o: [u8; 64])
    ensures
        o@ == r@ + s@,
{
    let mut o = [0u8; 64];
    let mut i: usize = 0;
    while i < 32
        invariant
            i <= 32,
            forall|j: int| 0 <= j < i ==> o@[j] == r@[j] && o@[32 + j] == s@[j],
        decreases 32 - i,
    {
        o[i] = r[i];
        o[32 + i] = s[i];
        i += 1;
    }
    assert(o@ =~= r@ + s@);
    o
}

// Attempt indices satisfying least_suitable coincide.
proof fn lemma_least_suitable_unique(x: Seq<u8>, h1: Seq<u8>, i: nat, i2: nat)
    requires
        least_suitable(x, h1, i),
        least_suitable(x, h1, i2),
    ensures
        i == i2,
{
    hide(suitable);
    if i < i2 {
        assert(!suitable(x, h1, i));
    } else if i2 < i {
        assert(!suitable(x, h1, i2));
    }
}

// The first suitable attempt is the one the spec's choose picks.
proof fn lemma_least_suitable_choose(x: Seq<u8>, h1: Seq<u8>, i: nat)
    requires
        suitable(x, h1, i),
        forall|j: nat| j < i ==> !#[trigger] suitable(x, h1, j),
    ensures
        exists|c: nat| #[trigger] least_suitable(x, h1, c),
        (choose|c: nat| #[trigger] least_suitable(x, h1, c)) == i,
{
    hide(suitable);
    assert(least_suitable(x, h1, i));
    let c = choose|c: nat| #[trigger] least_suitable(x, h1, c);
    lemma_least_suitable_unique(x, h1, i, c);
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;
    use super::vecdata::*;

    // RFC 6979 A.2.5 (rfc6979.txt sha256 456e8f17558fdbd2…, lines 1810, 1831, 1866): x and the SHA-256 k for
    // "sample" and "test", copied by script.
    const X: [u8; 32] = [0xc9, 0xaf, 0xa9, 0xd8, 0x45, 0xba, 0x75, 0x16, 0x6b, 0x5c, 0x21, 0x57, 0x67, 0xb1, 0xd6, 0x93, 0x4e, 0x50, 0xc3, 0xdb, 0x36, 0xe8, 0x9b, 0x12, 0x7b, 0x8a, 0x62, 0x2b, 0x12, 0x0f, 0x67, 0x21];
    const K_SAMPLE: [u8; 32] = [0xa6, 0xe3, 0xc5, 0x7d, 0xd0, 0x1a, 0xbe, 0x90, 0x08, 0x65, 0x38, 0x39, 0x83, 0x55, 0xdd, 0x4c, 0x3b, 0x17, 0xaa, 0x87, 0x33, 0x82, 0xb0, 0xf2, 0x4d, 0x61, 0x29, 0x49, 0x3d, 0x8a, 0xad, 0x60];
    const K_TEST: [u8; 32] = [0xd1, 0x6b, 0x6a, 0xe8, 0x27, 0xf1, 0x71, 0x75, 0xe0, 0x40, 0x87, 0x1a, 0x1c, 0x7e, 0xc3, 0x50, 0x01, 0x92, 0xc4, 0xc9, 0x26, 0x77, 0x33, 0x6e, 0xc2, 0x53, 0x7a, 0xca, 0xee, 0x00, 0x08, 0xe0];

    // (h1, bits2octets(h1)) for h1 = n, n + 1, n - 1 and 2^256 - 1 (t5c5/gen.py).
    const B2O: [([u8; 32], [u8; 32]); 4] = [
        (
            [0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63, 0x25, 0x51],
            [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
        ),
        (
            [0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63, 0x25, 0x52],
            [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01],
        ),
        (
            [0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63, 0x25, 0x50],
            [0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63, 0x25, 0x50],
        ),
        (
            [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff],
            [0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x43, 0x19, 0x05, 0x52, 0x58, 0xe8, 0x61, 0x7b, 0x0c, 0x46, 0x35, 0x3d, 0x03, 0x9c, 0xda, 0xae],
        ),
    ];

    #[test]
    fn rfc6979_a25_k() {
        for (msg, want) in [(&b"sample"[..], K_SAMPLE), (&b"test"[..], K_TEST)] {
            let h1 = crate::sha256::sha256(msg);
            let (k, v) = rfc6979_init_exec(&X, &h1);
            let (t, _, _) = rfc6979_next(&k, &v);
            assert_eq!(t, want, "candidate k for {:?}", msg);
        }
    }

    #[test]
    fn bits2octets_reduces() {
        for (h1, want) in B2O {
            assert_eq!(bits2octets_exec(&h1), want, "h1 = {:02x?}", h1);
        }
    }

    #[test]
    fn cavp_siggen_file() {
        let mut n = 0;
        for r in rsp_records(&data("nist/SigGen.txt")).iter().filter(|r| r.get("section").map(|s| s == "P-256,SHA-256").unwrap_or(false) && r.contains_key("Msg")) {
            let (d, k) = (hex(&r["d"]), hex(&r["k"]));
            let h = crate::sha256::sha256(&hex(&r["Msg"]));
            let rl = ecdsa_r_exec(k.as_slice().try_into().unwrap());
            assert_eq!(limbs_to_be(&rl).to_vec(), hex(&r["R"]), "vector {n} r");
            let got = ecdsa_s_exec(&limbs_from_be(&d, 0), &reduce_n(&h, 0), &limbs_from_be(&k, 0), &rl);
            assert_eq!(limbs_to_be(&got).to_vec(), hex(&r["S"]), "vector {n} s");
            let mut q = vec![4u8];
            q.extend(hex(&r["Qx"]));
            q.extend(hex(&r["Qy"]));
            assert_eq!(crate::p256::p256_public_key(&d).map(|p| p.to_vec()), Some(q), "vector {n} Q");
            n += 1;
        }
        assert_eq!(n, 15);
    }
}

#[cfg(test)]
#[path = "../tests/vecdata/mod.rs"]
mod vecdata;
