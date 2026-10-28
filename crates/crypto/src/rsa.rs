//! RSASSA-PSS-SHA256 signing (RFC 8017 §8.1.1; rsa_pss_rsae_sha256 is RFC 8446 §4.2.3, salt length
//! 32, MGF1-SHA256): spec and an exec signature backed by the trusted shim. Signing only: no RSA
//! verification code exists.
#[allow(unused_imports)]
use crate::bytes::*;
#[allow(unused_imports)]
use crate::sha256::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::power::*;

verus! {

/// RFC 8017 §3.2 private key (n, e, d) with the primes p and q, as big-endian unsigned integers
/// (leading zeros allowed). The trusted shell fills it from the PKCS#8 key.
pub struct RsaPrivateKey {
    pub n: Vec<u8>,
    pub e: Vec<u8>,
    pub d: Vec<u8>,
    pub p: Vec<u8>,
    pub q: Vec<u8>,
}

/// The integers of an `RsaPrivateKey`, by OS2IP (RFC 8017 §4.2).
pub struct RsaKeySpec {
    pub n: nat,
    pub e: nat,
    pub d: nat,
    pub p: nat,
    pub q: nat,
}

impl View for RsaPrivateKey {
    type V = RsaKeySpec;

    open spec fn view(&self) -> RsaKeySpec {
        RsaKeySpec {
            n: os2ip(self.n@),
            e: os2ip(self.e@),
            d: os2ip(self.d@),
            p: os2ip(self.p@),
            q: os2ip(self.q@),
        }
    }
}

/// x is prime: x > 1 and no k in (1, x) divides it.
pub open spec fn is_prime(x: nat) -> bool {
    x > 1 && forall|k: nat| 1 < k < x ==> #[trigger] (x % k) != 0
}

/// Number of bits of x: 0 for 0, else the position of the leading one.
pub open spec fn bitlen(x: nat) -> nat
    decreases x,
{
    if x == 0 {
        0
    } else {
        1 + bitlen(x / 2)
    }
}

/// RFC 8017 §3.1-3.2 key validity, restricted to two primes and the 2048-4096-bit moduli we sign
/// with: n = p q, 3 <= e < n, and e d = 1 mod lambda(n) = lcm(p - 1, q - 1), i.e. modulo both
/// p - 1 and q - 1. Primality is not provable by any verified code, so it is a `requires` that
/// flows up to the trusted shell's key loading.
pub open spec fn rsa_key_wf(k: RsaKeySpec) -> bool {
    is_prime(k.p) && is_prime(k.q) && k.p != k.q && k.n == k.p * k.q && 3 <= k.e && k.e < k.n
        && (k.e * k.d) % ((k.p - 1) as nat) == 1 && (k.e * k.d) % ((k.q - 1) as nat) == 1
        && 2048 <= bitlen(k.n) <= 4096
}

/// RFC 8017 Appendix B.2.1 MGF1 with SHA-256 (hLen = 32): the concatenation of
/// Hash(seed || C) for C = I2OSP(counter, 4), counter = 0 .. n - 1 (step 3).
pub open spec fn mgf1_blocks(seed: Seq<u8>, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        mgf1_blocks(seed, (n - 1) as nat) + spec_sha256(seed + i2osp((n - 1) as nat, 4))
    }
}

/// RFC 8017 Appendix B.2.1 MGF1 with SHA-256: the leading `len` octets of the concatenation for
/// counter = 0 .. ceil(len / 32) - 1 (steps 3 and 4). `len` is at most 2^32 hLen (step 1), which
/// holds for every length this module passes.
pub open spec fn mgf1_sha256(seed: Seq<u8>, len: nat) -> Seq<u8> {
    mgf1_blocks(seed, (len + 31) / 32).subrange(0, len as int)
}

/// RFC 8017 §9.1.1 EMSA-PSS-ENCODE with SHA-256, sLen = hLen = 32, and the salt given by the
/// caller (step 4's random salt).
/// - Step 1 (message too long) is the `MAX_INPUT_LEN` requires; step 3 (encoding error) cannot
///   happen, since emLen >= 256 > 66 under `rsa_key_wf`.
/// - Step 2: mHash = Hash(M). Steps 5-6: M' = (0x00 x 8) || mHash || salt, H = Hash(M').
/// - Steps 7-9: DB = PS || 0x01 || salt, with PS = emLen - sLen - hLen - 2 zero octets;
///   maskedDB = DB xor MGF(H, emLen - hLen - 1).
/// - Step 11: set the leftmost 8 emLen - emBits bits of maskedDB to zero. Step 12: EM = maskedDB
///   || H || 0xbc.
pub open spec fn emsa_pss_encode(msg: Seq<u8>, em_bits: nat, salt: Seq<u8>) -> Seq<u8> {
    let em_len = (em_bits + 7) / 8;
    let m_hash = spec_sha256(msg);
    let hh = spec_sha256(Seq::new(8, |i: int| 0x00u8) + m_hash + salt);
    let db = Seq::new((em_len - 66) as nat, |i: int| 0x00u8) + seq![0x01u8] + salt;
    let masked = xor_bytes(db, mgf1_sha256(hh, (em_len - 33) as nat));
    let top = masked[0] & (0xffu8 >> ((8 * em_len - em_bits) as u8));
    masked.update(0, top) + hh + seq![0xbcu8]
}

/// RFC 8017 §8.1.1 RSASSA-PSS-SIGN.
/// - Step 1: EM = EMSA-PSS-ENCODE(M, modBits - 1), modBits = bitlen(n).
/// - Step 2a: m = OS2IP(EM). Step 2b: s = RSASP1(K, m) = m^d mod n (RFC 8017 §5.2.1, form (a);
///   the shim's CRT form (b) agrees for a well-formed key). m < 2^(modBits - 1) <= n, so
///   RSASP1's "message representative out of range" cannot occur.
/// - Step 2c: S = I2OSP(s, k), k = ceil(modBits / 8).
pub open spec fn spec_rsassa_pss_sign(k: RsaKeySpec, msg: Seq<u8>, salt: Seq<u8>) -> Seq<u8> {
    let mod_bits = bitlen(k.n);
    let em = emsa_pss_encode(msg, (mod_bits - 1) as nat, salt);
    let s = (pow(os2ip(em) as int, k.d) % (k.n as int)) as nat;
    i2osp(s, (mod_bits + 7) / 8)
}

/// Trusted shim: the body is RustCrypto rsa; the ensures is the trusted statement.
/// - The ensures is one-directional: the shim returns None, where the spec has a signature, when
///   RustCrypto rejects a key that `rsa_key_wf` allows (e >= 2^33) or when its fault check
///   fails.
/// - Primality in `rsa_key_wf` can be established by no verified code; it flows up to the
///   trusted shell's key loading.
#[verifier::external_body]
pub fn rsa_pss_sha256_sign(key: &RsaPrivateKey, msg: &[u8], salt: &[u8]) -> (r: Option<Vec<u8>>)
    requires
        rsa_key_wf(key@),
        msg@.len() <= MAX_INPUT_LEN,
        salt@.len() == 32,
    ensures
        r matches Some(s) ==> s@ == spec_rsassa_pss_sign(key@, msg@, salt@),
{
    crate::shim::rsa_pss_sign(&key.n, &key.e, &key.d, &key.p, &key.q, msg, salt)
}

} // verus!
