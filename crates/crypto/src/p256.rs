//! P-256 (NIST SP 800-186 §3.2.1.3) with the SEC 1 v2 group law, point encoding and ECDH:
//! spec and exec signatures backed by the trusted shim.
#[allow(unused_imports)]
use crate::bytes::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::power::*;
#[allow(unused_imports)]
use crate::mont::*;

verus! {

/// SP 800-186 §3.2.1.3 p = 2^256 - 2^224 + 2^192 + 2^96 - 1, big-endian.
pub const P256_P: [u8; 32] = [
    0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];

/// SP 800-186 §3.2.1.3 n (order of G; cofactor h = 1), big-endian.
pub const P256_N: [u8; 32] = [
    0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63, 0x25, 0x51,
];

/// SP 800-186 §3.2.1.3 b, big-endian.
pub const P256_B: [u8; 32] = [
    0x5a, 0xc6, 0x35, 0xd8, 0xaa, 0x3a, 0x93, 0xe7, 0xb3, 0xeb, 0xbd, 0x55, 0x76, 0x98, 0x86, 0xbc,
    0x65, 0x1d, 0x06, 0xb0, 0xcc, 0x53, 0xb0, 0xf6, 0x3b, 0xce, 0x3c, 0x3e, 0x27, 0xd2, 0x60, 0x4b,
];

/// SP 800-186 §3.2.1.3 Gx, big-endian.
pub const P256_GX: [u8; 32] = [
    0x6b, 0x17, 0xd1, 0xf2, 0xe1, 0x2c, 0x42, 0x47, 0xf8, 0xbc, 0xe6, 0xe5, 0x63, 0xa4, 0x40, 0xf2,
    0x77, 0x03, 0x7d, 0x81, 0x2d, 0xeb, 0x33, 0xa0, 0xf4, 0xa1, 0x39, 0x45, 0xd8, 0x98, 0xc2, 0x96,
];

/// SP 800-186 §3.2.1.3 Gy, big-endian.
pub const P256_GY: [u8; 32] = [
    0x4f, 0xe3, 0x42, 0xe2, 0xfe, 0x1a, 0x7f, 0x9b, 0x8e, 0xe7, 0xeb, 0x4a, 0x7c, 0x0f, 0x9e, 0x16,
    0x2b, 0xce, 0x33, 0x57, 0x6b, 0x31, 0x5e, 0xce, 0xcb, 0xb6, 0x40, 0x68, 0x37, 0xbf, 0x51, 0xf5,
];

/// SP 800-186 §3.2.1.3 p.
pub open spec fn p256_p() -> int {
    os2ip(P256_P@) as int
}

/// SP 800-186 §3.2.1.3 n.
pub open spec fn p256_n() -> int {
    os2ip(P256_N@) as int
}

/// SP 800-186 §3.2.1.3 b. (The curve parameter a is -3, written inline below.)
pub open spec fn p256_b() -> int {
    os2ip(P256_B@) as int
}

/// Reduction into GF(p) (SEC 1 v2 §2.2.1 "(mod p)"); `%` on int is Euclidean, so the result is in [0, p).
pub open spec fn fmod(x: int) -> int {
    x % p256_p()
}

/// Inverse in GF(p) by Fermat's little theorem (p is prime): x^(p-2) mod p.
pub open spec fn finv(x: int) -> int {
    fmod(pow(x, (p256_p() - 2) as nat))
}

/// A point of E(F_p) (SEC 1 v2 §2.2.1): the point at infinity O, or affine (x, y).
pub enum SpecPoint {
    Infinity,
    Affine(int, int),
}

/// SP 800-186 §3.2.1.3 base point G = (Gx, Gy).
pub open spec fn p256_g() -> SpecPoint {
    SpecPoint::Affine(os2ip(P256_GX@) as int, os2ip(P256_GY@) as int)
}

/// SEC 1 v2 §2.2.1 defining equation y^2 = x^3 + ax + b (mod p) with a = -3 (SP 800-186 §3.2.1.3),
/// plus the [0, p - 1] coordinate range of SEC 1 v2 §2.3.6 step 1 and §3.2.2.1 step 2.
pub open spec fn on_curve(x: int, y: int) -> bool {
    0 <= x < p256_p() && 0 <= y < p256_p() && fmod(y * y) == fmod(x * x * x - 3 * x + p256_b())
}

/// SEC 1 v2 §2.2.1 addition rules 1-5, a = -3.
/// - Rules 1-2: O is the identity.
/// - Rule 3: x1 == x2 and y1 + y2 = 0 (mod p) gives O. It is tested before doubling, so doubling
///   a point with y1 = 0 gives O, as rule 5's precondition y1 != 0 requires.
/// - Rule 5 (x1 == x2 otherwise): lambda = (3 x1^2 + a) / (2 y1); x3 = lambda^2 - x1 - x2 equals
///   rule 5's lambda^2 - 2 x1 because x1 == x2.
/// - Rule 4 (x1 != x2): lambda = (y2 - y1) / (x2 - x1).
/// - Both: x3 = lambda^2 - x1 - x2, y3 = lambda (x1 - x3) - y1 (mod p).
/// Coordinates are compared with plain `==`: every point reaching here (G, a decoded point, or
/// an `fmod` output) has coordinates in [0, p).
pub open spec fn point_add(a: SpecPoint, b: SpecPoint) -> SpecPoint {
    match (a, b) {
        (SpecPoint::Infinity, _) => b,
        (_, SpecPoint::Infinity) => a,
        (SpecPoint::Affine(x1, y1), SpecPoint::Affine(x2, y2)) => {
            if x1 == x2 && fmod(y1 + y2) == 0 {
                SpecPoint::Infinity
            } else {
                let lambda = if x1 == x2 {
                    fmod((3 * x1 * x1 - 3) * finv(2 * y1))
                } else {
                    fmod((y2 - y1) * finv(x2 - x1))
                };
                let x3 = fmod(lambda * lambda - x1 - x2);
                let y3 = fmod(lambda * (x1 - x3) - y1);
                SpecPoint::Affine(x3, y3)
            }
        },
    }
}

/// SEC 1 v2 §2.2.1 scalar multiplication kP: P added to itself k times (0P = O).
/// Written for readability; it is never computed.
pub open spec fn scalar_mult(k: nat, pt: SpecPoint) -> SpecPoint
    decreases k,
{
    if k == 0 {
        SpecPoint::Infinity
    } else {
        point_add(pt, scalar_mult((k - 1) as nat, pt))
    }
}

/// SEC 1 v2 §3.2.1 step 1 and FIPS 186-5 Appendix A.2.2: a private key is an integer d in [1, n - 1],
/// here as a 32-octet big-endian string.
pub open spec fn scalar_valid(d: Seq<u8>) -> bool {
    d.len() == 32 && 1 <= os2ip(d) < p256_n()
}

/// SEC 1 v2 §2.3.3 steps 1 and 3 (no point compression): O is 0x00; otherwise
/// 0x04 || X || Y with X, Y the 32-octet field elements of §2.3.5. O is unreachable from a
/// valid scalar (n is prime and d in [1, n - 1]).
pub open spec fn sec1_encode(pt: SpecPoint) -> Seq<u8> {
    match pt {
        SpecPoint::Infinity => seq![0x00u8],
        SpecPoint::Affine(x, y) => seq![0x04u8] + i2osp(x as nat, 32) + i2osp(y as nat, 32),
    }
}

/// SEC 1 v2 §2.3.4 step 3 (3.1-3.5), restricted to the uncompressed form by RFC 8446 §4.2.8.2.
/// - Step 3.2: W must be 0x04. Every other length or prefix is rejected, including the
///   compressed form (step 2) and the 1-octet 0x00 (step 1, O): RFC 8446 §4.2.8.2 allows only
///   UncompressedPointRepresentation, and SEC 1 v2 §3.2.2.1 step 1 requires Q != O.
/// - Steps 3.3-3.4 (§2.3.6 step 1): x, y in [0, p - 1], carried by `on_curve`, so a
///   non-canonical x >= p is rejected.
/// - Step 3.5: the defining equation, carried by `on_curve`.
/// - SEC 1 v2 §3.2.2.1 step 4 (nQ = O) holds for every curve point because h = 1
///   (SP 800-186 §3.2.1.3), so no subgroup check is needed.
pub open spec fn sec1_decode(b: Seq<u8>) -> Option<SpecPoint> {
    if b.len() == 65 && b[0] == 0x04u8 {
        let x = os2ip(b.subrange(1, 33)) as int;
        let y = os2ip(b.subrange(33, 65)) as int;
        if on_curve(x, y) {
            Some(SpecPoint::Affine(x, y))
        } else {
            None
        }
    } else {
        None
    }
}

/// SEC 1 v2 §3.2.1 step 2: Q = dG, encoded per §2.3.3 (uncompressed). None for d outside [1, n - 1].
pub open spec fn spec_p256_public_key(d: Seq<u8>) -> Option<Seq<u8>> {
    if !scalar_valid(d) {
        None
    } else {
        Some(sec1_encode(scalar_mult(os2ip(d), p256_g())))
    }
}

/// SEC 1 v2 §3.3.1: P = d Q (step 1); None if P = O (step 2); z = xP (step 3), output as the
/// full 32-octet FE2OSP string with no leading-zero stripping (RFC 8446 §7.4.2, SEC 1 v2 §2.3.5).
/// None for an invalid private key or an undecodable peer value (RFC 8446 §4.2.8.2).
pub open spec fn spec_p256_ecdh(d: Seq<u8>, peer: Seq<u8>) -> Option<Seq<u8>> {
    if !scalar_valid(d) {
        None
    } else {
        match sec1_decode(peer) {
            None => None,
            Some(q) => match scalar_mult(os2ip(d), q) {
                SpecPoint::Infinity => None,
                SpecPoint::Affine(x, _) => Some(i2osp(x as nat, 32)),
            },
        }
    }
}

/// Trusted shim: the body is RustCrypto p256; the ensures is the trusted statement.
#[verifier::external_body]
pub fn p256_public_key(d: &[u8]) -> (r: Option<[u8; 65]>)
    requires
        d@.len() == 32,
    ensures
        r.deep_view() == spec_p256_public_key(d@),
{
    crate::shim::p256_public_key(d)
}

/// Trusted shim: the body is RustCrypto p256; the ensures is the trusted statement.
#[verifier::external_body]
pub fn p256_ecdh(d: &[u8], peer: &[u8]) -> (r: Option<[u8; 32]>)
    requires
        d@.len() == 32,
    ensures
        r.deep_view() == spec_p256_ecdh(d@, peer@),
{
    crate::shim::p256_ecdh(d, peer)
}

// ---- GF(p) in Montgomery form over crate::mont (R = 2^256); values from Task 1 Step 4 ----

const P_LIMBS: [u64; 4] = [0xffffffffffffffff, 0x00000000ffffffff, 0x0000000000000000, 0xffffffff00000001];

// -p^-1 mod 2^64.
const P_MP: u64 = 1;

// R^2 mod p, the encode multiplier.
const R2_P: [u64; 4] = [0x0000000000000003, 0xfffffffbffffffff, 0xfffffffffffffffe, 0x00000004fffffffd];

// R mod p, the Montgomery form of 1.
const ONE_MONT: [u64; 4] = [0x0000000000000001, 0xffffffff00000000, 0xffffffffffffffff, 0x00000000fffffffe];

// 3R mod p.
#[allow(dead_code)]  // used from Task 4
const THREE_MONT: [u64; 4] = [0x0000000000000003, 0xfffffffd00000000, 0xffffffffffffffff, 0x00000002fffffffc];

// bR mod p.
#[allow(dead_code)]  // used from Task 4
const B_MONT: [u64; 4] = [0xd89cdf6229c4bddf, 0xacf005cd78843090, 0xe5a220abf7212ed6, 0xdc30061d04874834];

// R^-1 mod p.
// A spec fn rather than a `spec const RINV_P`, which Verus lowers to a fn that trips the snake-case lint.
spec fn rinv_p() -> int {
    0xfffffffe00000003fffffffd0000000200000001fffffffe0000000300000000int
}

// p - 2, big-endian: the Fermat exponent.
const P256_P_MINUS_2: [u8; 32] = [
    0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfd,
];

// The SP 800-186 §3.2.1.3 constants as literals.
pub(crate) proof fn lemma_p256_consts()
    ensures
        p256_p() == 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff,
        p256_n() == 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551,
        p256_b() == 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b,
        os2ip(P256_GX@) == 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296,
        os2ip(P256_GY@) == 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5,
{
    assert(p256_p() == 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) by (compute_only);
    assert(p256_n() == 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551) by (compute_only);
    assert(p256_b() == 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b) by (compute_only);
    assert(os2ip(P256_GX@) == 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296) by (compute_only);
    assert(os2ip(P256_GY@) == 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5) by (compute_only);
}

// The Fermat exponent is p - 2.
proof fn lemma_exp_const_p()
    ensures
        os2ip(P256_P_MINUS_2@) == p256_p() - 2,
{
    assert(os2ip(P256_P_MINUS_2@) == p256_p() - 2) by (compute_only);
}

// Montgomery decode of canonical limbs into GF(p).
spec fn fe(l: [u64; 4]) -> int {
    mdec(v4(l), p256_p(), rinv_p())
}

// Canonical limbs: below p.
spec fn fe_ok(l: [u64; 4]) -> bool {
    v4(l) < p256_p()
}

// The Montgomery constants for p, checked by Z3 on literals.
proof fn lemma_mont_consts_p()
    ensures
        v4(P_LIMBS) == p256_p(),
        p256_p() > 1,
        (P_LIMBS[0] as int * P_MP as int + 1) % 0x1_0000_0000_0000_0000 == 0,
        (0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 * rinv_p()) % p256_p() == 1,
        v4(R2_P) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int % p256_p(),
        v4(ONE_MONT) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int % p256_p(),
        fe_ok(R2_P),
        fe_ok(ONE_MONT),
        fe_ok(THREE_MONT),
        fe_ok(B_MONT),
        fe(R2_P) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int % p256_p(),
        fe(B_MONT) == p256_b(),
        fe(ONE_MONT) == 1,
        fe(THREE_MONT) == 3,
{
    lemma_p256_consts();
}

// Cancelling R: if v < p and v * R == u (mod p), then v is the decode of u.
proof fn lemma_unmont(v: int, u: int)
    requires
        0 <= v < p256_p(),
        (v * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000) % p256_p() == u % p256_p(),
    ensures
        v == mdec(u, p256_p(), rinv_p()),
{
    let (p, rr) = (p256_p(), 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int);
    lemma_mont_consts_p();
    // u * ri == v * R * ri == v * (R * ri) == v (mod p)
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_left(u, rinv_p(), p);
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_left(v * rr, rinv_p(), p);
    assert((v * rr) * rinv_p() == v * (rr * rinv_p())) by {
        broadcast use vstd::arithmetic::mul::group_mul_properties;
    }
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_right(v, rr * rinv_p(), p);
    vstd::arithmetic::div_mod::lemma_small_mod(v as nat, p as nat);
}

// x * 1 == x for a product term Z3 does not simplify.
proof fn lemma_mul_one(x: int, y: int)
    requires
        y == 1,
    ensures
        x * y == x,
{
    assert(x * y == x) by (nonlinear_arith)
        requires
            y == 1,
    ;
}

// fe(r) == fmod(fe(a) * fe(b)).
// ct: secret a, b
#[allow(dead_code)]  // used from Task 4
fn fe_mul(a: [u64; 4], b: [u64; 4]) -> (r: [u64; 4])
    requires
        fe_ok(a),
        fe_ok(b),
    ensures
        fe_ok(r),
        fe(r) == fmod(fe(a) * fe(b)),
{
    proof {
        lemma_mont_consts_p();
    }
    let r = mont_mul(&a, &b, &P_LIMBS, P_MP);
    proof {
        lemma_mdec_mul(v4(r), v4(a), v4(b), p256_p(), 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int, rinv_p());
    }
    r
}

// fe(r) == fmod(fe(a) + fe(b)).
// ct: secret a, b
#[allow(dead_code)]  // used from Task 4
fn fe_add(a: [u64; 4], b: [u64; 4]) -> (r: [u64; 4])
    requires
        fe_ok(a),
        fe_ok(b),
    ensures
        fe_ok(r),
        fe(r) == fmod(fe(a) + fe(b)),
{
    proof {
        lemma_mont_consts_p();
    }
    let r = add_mod(&a, &b, &P_LIMBS);
    proof {
        lemma_mdec_add(v4(a), v4(b), p256_p(), rinv_p());
    }
    r
}

// fe(r) == fmod(fe(a) - fe(b)).
// ct: secret a, b
#[allow(dead_code)]  // used from Task 4
fn fe_sub(a: [u64; 4], b: [u64; 4]) -> (r: [u64; 4])
    requires
        fe_ok(a),
        fe_ok(b),
    ensures
        fe_ok(r),
        fe(r) == fmod(fe(a) - fe(b)),
{
    proof {
        lemma_mont_consts_p();
    }
    let r = sub_mod(&a, &b, &P_LIMBS);
    proof {
        lemma_mdec_sub(v4(a), v4(b), p256_p(), rinv_p());
    }
    r
}

// fe(r) == finv(fe(a)) == fe(a)^(p - 2) mod p (Fermat).
// ct: secret a
#[allow(dead_code)]  // used from Task 4
fn fe_inv(a: [u64; 4]) -> (r: [u64; 4])
    requires
        fe_ok(a),
    ensures
        fe_ok(r),
        fe(r) == finv(fe(a)),
{
    proof {
        lemma_mont_consts_p();
        lemma_exp_const_p();
    }
    mont_pow(&a, &P256_P_MINUS_2, &P_LIMBS, P_MP, &ONE_MONT, Ghost(rinv_p()))
}

// finv only sees its argument mod p.
proof fn lemma_finv_fmod(z: int)
    ensures
        finv(fmod(z)) == finv(z),
{
    lemma_p256_consts();
    vstd::arithmetic::power::lemma_pow_mod_noop(z, (p256_p() - 2) as nat, p256_p());
}

// The field element encoded by b[off..off + 32], or None if that integer is >= p.
// ct: public b, off (peer input only; never call on secret data)
// `d` is read only by proof code, which a plain `cargo build` erases.
#[allow(dead_code, unused_variables)]  // dead_code: used from Task 4
fn fe_from_be(b: &[u8], off: usize) -> (r: Option<[u64; 4]>)
    requires
        off + 32 <= b@.len(),
    ensures
        r.is_none() == (os2ip(b@.subrange(off as int, off + 32)) >= p256_p()),
        r matches Some(x) ==> fe_ok(x) && fe(x) == os2ip(b@.subrange(off as int, off + 32)),
{
    proof {
        lemma_mont_consts_p();
    }
    let x = limbs_from_be(b, off);
    let (d, bo) = sub4(&x, &P_LIMBS);
    proof {
        lemma_v4_bound(d);
    }
    // ct: branch on public input
    if bo == 0 {
        None
    } else {
        let r = mont_mul(&x, &R2_P, &P_LIMBS, P_MP);
        proof {
            let (p, rr, xv) = (p256_p(), 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int, v4(x));
            lemma_mdec_mul(v4(r), xv, v4(R2_P), p, rr, rinv_p());
            // (x ri mod p) (R mod p) == x (R ri) == x (mod p)
            lemma_mod_mul_cong(xv * rinv_p(), rr, p);
            assert((xv * rinv_p()) * rr == xv * (rr * rinv_p())) by {
                broadcast use vstd::arithmetic::mul::group_mul_properties;
            }
            vstd::arithmetic::div_mod::lemma_mul_mod_noop_right(xv, rr * rinv_p(), p);
            lemma_v4_bound(x);
            vstd::arithmetic::div_mod::lemma_small_mod(xv as nat, p as nat);
        }
        Some(r)
    }
}

// I2OSP(fe(a), 32): decode (multiply by 1), then the limbs as big-endian octets.
// ct: secret a
#[allow(dead_code)]  // used from Task 4
fn fe_to_be(a: &[u64; 4]) -> (r: [u8; 32])
    ensures
        r@ == i2osp(fe(*a) as nat, 32),
{
    proof {
        lemma_mont_consts_p();
    }
    let w1: [u64; 4] = [1, 0, 0, 0];
    let d = mont_mul(a, &w1, &P_LIMBS, P_MP);
    proof {
        lemma_mul_one(v4(*a), v4(w1));
        lemma_unmont(v4(d), v4(*a));
    }
    limbs_to_be(&d)
}

// 1 iff fe(a) == fe(b), without branching.
// ct: secret a, b
#[allow(dead_code)]  // used from Task 4
fn fe_eq(a: [u64; 4], b: [u64; 4]) -> (r: u64)
    requires
        fe_ok(a),
        fe_ok(b),
    ensures
        r <= 1,
        (r == 1) == (fe(a) == fe(b)),
{
    proof {
        lemma_mont_consts_p();
        if fe(a) == fe(b) {
            lemma_mdec_inj(a, b, p256_p(), rinv_p());
        }
    }
    eq4(&a, &b)
}

// 1 iff fe(a) == 0, without branching.
// ct: secret a
#[allow(dead_code)]  // used from Task 4
fn fe_is_zero(a: [u64; 4]) -> (r: u64)
    requires
        fe_ok(a),
    ensures
        r <= 1,
        (r == 1) == (fe(a) == 0),
{
    proof {
        lemma_mont_consts_p();
        let z: [u64; 4] = [0, 0, 0, 0];
        assert(v4(z) == 0);
        vstd::arithmetic::div_mod::lemma_small_mod(0, p256_p() as nat);
        if fe(a) == 0 {
            lemma_mdec_inj(a, z, p256_p(), rinv_p());
        }
    }
    is_zero4(&a)
}

} // verus!
