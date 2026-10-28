//! P-256 (NIST SP 800-186 §3.2.1.3) with the SEC 1 v2 group law, point encoding and ECDH:
//! spec and exec signatures backed by the trusted shim.
#[allow(unused_imports)]
use crate::bytes::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::power::*;

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

} // verus!
