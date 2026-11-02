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
/// with: n = p q, 3 <= e < n, 0 < d < n (§3.2), and e d = 1 mod lambda(n) = lcm(p - 1, q - 1), i.e. modulo both
/// p - 1 and q - 1. Primality is not provable by any verified code, so it is a `requires` that
/// flows up to the trusted shell's key loading.
pub open spec fn rsa_key_wf(k: RsaKeySpec) -> bool {
    is_prime(k.p) && is_prime(k.q) && k.p != k.q && k.n == k.p * k.q && 3 <= k.e && k.e < k.n
        && 0 < k.d && k.d < k.n
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
///   RustCrypto rejects a key that `rsa_key_wf` allows: e >= 2^33 (`RsaPublicKey::MAX_PUB_EXPONENT`).
///   No other None is known; RustCrypto's CRT fault check cannot fail for a well-formed key.
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

proof fn lemma_mgf1_blocks_len(seed: Seq<u8>, n: nat)
    ensures
        mgf1_blocks(seed, n).len() == n * 32,
    decreases n,
{
    if n > 0 {
        lemma_mgf1_blocks_len(seed, (n - 1) as nat);
        lemma_spec_sha256_len(seed + i2osp((n - 1) as nat, 4));
    }
}

proof fn lemma_mgf1_len(seed: Seq<u8>, len: nat)
    ensures
        mgf1_sha256(seed, len).len() == len,
{
    lemma_mgf1_blocks_len(seed, (len + 31) / 32);
    assert(((len + 31) / 32) * 32 >= len) by (nonlinear_arith);
}

/// RFC 8017 Appendix B.2.1; verified against mgf1_sha256. 512 is the largest emLen we sign with.
#[allow(dead_code)] // used from Task 5, removed there.
#[cfg_attr(ct_check, ct::secret(seed), ct::public(len))]
fn mgf1_exec(seed: &[u8; 32], len: usize) -> (r: Vec<u8>)
    requires
        len <= 512,
    ensures
        r@ == mgf1_sha256(seed@, len as nat),
{
    hide(spec_sha256);
    let blocks: usize = (len + 31) / 32;
    let mut out: Vec<u8> = Vec::with_capacity(blocks * 32);
    let mut c: usize = 0;
    // ct: the loop count comes from the public len
    while c < blocks
        invariant
            blocks <= 16,
            c <= blocks,
            out@.len() == c * 32,
            out@ == mgf1_blocks(seed@, c as nat),
        decreases blocks - c,
    {
        let w = c as u32;
        let mut input: Vec<u8> = Vec::with_capacity(36);
        input.extend_from_slice(seed.as_slice());
        input.push((w >> 24) as u8);
        input.push((w >> 16) as u8);
        input.push((w >> 8) as u8);
        input.push(w as u8);
        proof {
            lemma_i2osp_be4(w);
            assert(input@ =~= seed@ + i2osp(c as nat, 4));
        }
        let h = sha256(input.as_slice());
        out.extend_from_slice(h.as_slice());
        c = c + 1;
        proof {
            assert(mgf1_blocks(seed@, c as nat) == mgf1_blocks(seed@, (c - 1) as nat) + spec_sha256(
                seed@ + i2osp((c - 1) as nat, 4),
            ));
        }
    }
    assert(blocks * 32 >= len) by (nonlinear_arith)
        requires
            blocks == (len + 31) / 32,
    ;
    let mut r: Vec<u8> = Vec::with_capacity(len);
    r.extend_from_slice(vstd::slice::slice_subrange(out.as_slice(), 0, len));
    assert(r@ =~= mgf1_sha256(seed@, len as nat));
    r
}

/// RFC 8017 §9.1.1 steps 2 and 5-12, in the order of the spec's let chain; verified against
/// emsa_pss_encode. 2047..=4095 are the emBits of the 2048-4096-bit moduli of `rsa_key_wf`.
#[allow(dead_code)] // used from Task 5, removed there.
#[cfg_attr(ct_check, ct::secret(salt, msg), ct::public(em_bits))]
fn emsa_pss_encode_exec(msg: &[u8], em_bits: usize, salt: &[u8]) -> (r: Vec<u8>)
    requires
        msg@.len() <= MAX_INPUT_LEN,
        salt@.len() == 32,
        2047 <= em_bits <= 4095,
    ensures
        r@ == emsa_pss_encode(msg@, em_bits as nat, salt@),
        r@.len() == (em_bits + 7) / 8,
{
    hide(spec_sha256);
    let em_len: usize = (em_bits + 7) / 8;
    let m_hash = sha256(msg);
    let mut mp: Vec<u8> = Vec::with_capacity(72);
    let mut i: usize = 0;
    // ct: a constant count
    while i < 8
        invariant
            i <= 8,
            mp@ == Seq::new(i as nat, |_j: int| 0x00u8),
        decreases 8 - i,
    {
        mp.push(0u8);
        i = i + 1;
        assert(mp@ =~= Seq::new(i as nat, |_j: int| 0x00u8));
    }
    mp.extend_from_slice(m_hash.as_slice());
    mp.extend_from_slice(salt);
    assert(mp@ =~= Seq::new(8, |_j: int| 0x00u8) + spec_sha256(msg@) + salt@);
    let hh = sha256(mp.as_slice());
    let ghost spec_hh = spec_sha256(Seq::new(8, |_j: int| 0x00u8) + spec_sha256(msg@) + salt@);
    let ps_len: usize = em_len - 66;
    let mut db: Vec<u8> = Vec::with_capacity(em_len - 33);
    let mut p: usize = 0;
    // ct: the loop count comes from the public em_bits
    while p < ps_len
        invariant
            p <= ps_len,
            db@ == Seq::new(p as nat, |_j: int| 0x00u8),
        decreases ps_len - p,
    {
        db.push(0u8);
        p = p + 1;
        assert(db@ =~= Seq::new(p as nat, |_j: int| 0x00u8));
    }
    db.push(1u8);
    db.extend_from_slice(salt);
    let ghost spec_db = Seq::new((em_len - 66) as nat, |_j: int| 0x00u8) + seq![0x01u8] + salt@;
    assert(db@ =~= spec_db);
    let mask = mgf1_exec(&hh, em_len - 33);
    proof {
        lemma_mgf1_len(hh@, (em_len - 33) as nat);
    }
    let mut out: Vec<u8> = Vec::with_capacity(em_len);
    let dbs = db.as_slice();
    let ms = mask.as_slice();
    let mut j: usize = 0;
    // ct: the loop count comes from the public em_bits
    while j < em_len - 33
        invariant
            em_len == (em_bits + 7) / 8,
            256 <= em_len <= 512,
            j <= em_len - 33,
            dbs@ == db@,
            ms@ == mask@,
            db@.len() == em_len - 33,
            mask@.len() == em_len - 33,
            out@.len() == j,
            forall|q: int| 0 <= q < j ==> #[trigger] out@[q] == db@[q] ^ mask@[q],
        decreases em_len - 33 - j,
    {
        out.push(dbs[j] ^ ms[j]);
        j = j + 1;
    }
    let ghost masked = xor_bytes(db@, mask@);
    assert(out@ =~= masked);
    // ct: the shift amount comes from the public em_bits
    let top: u8 = out.as_slice()[0] & (0xffu8 >> ((8 * em_len - em_bits) as u8));
    out.set(0, top);
    out.extend_from_slice(hh.as_slice());
    out.push(0xbcu8);
    assert(out@ =~= masked.update(0, top) + spec_hh + seq![0xbcu8]);
    out
}

} // verus!

#[cfg(test)]
#[path = "../tests/vecdata/mod.rs"]
mod vecdata;

#[cfg(test)]
mod tests {
    use super::vecdata::*;
    use super::*;
    use ::rsa::traits::PublicKeyParts;
    use ::rsa::BoxedUint;
    use sha2::Digest;

    fn u(b: &[u8]) -> BoxedUint {
        BoxedUint::from_be_slice_vartime(b)
    }

    // s^e mod n as em_len octets; the octets above em_len must be zero.
    fn recover_em(pubk: &::rsa::RsaPublicKey, sig: &[u8], em_len: usize) -> Vec<u8> {
        let s = BoxedUint::from_be_slice(sig, pubk.n_bits_precision()).unwrap();
        let m = ::rsa::hazmat::rsa_encrypt(pubk, &s).unwrap().to_be_bytes();
        let (hi, em) = m.split_at(m.len() - em_len);
        assert!(hi.iter().all(|&x| x == 0));
        em.to_vec()
    }

    #[test]
    fn emsa_matches_cavp() {
        let (mut nh, mut eh) = (String::new(), String::new());
        let mut count = 0;
        for r in rsp_records(&data("nist/SigGenPSS_186-3.txt")) {
            if r.contains_key("n") || r.contains_key("e") {
                // n, then e and d, each in its own blank-line record; keep the latest
                for (k, dst) in [("n", &mut nh), ("e", &mut eh)] {
                    if let Some(v) = r.get(k) {
                        *dst = v.clone();
                    }
                }
                continue;
            }
            if r.get("mod").map(|m| m == "3072") != Some(true) || r.get("SHAAlg").map(|a| a == "SHA256") != Some(true) {
                continue;
            }
            let pubk = ::rsa::RsaPublicKey::new(u(&hex(&nh)), u(&hex(&eh))).unwrap();
            let em = recover_em(&pubk, &hex(&r["S"]), 384);
            assert_eq!(emsa_pss_encode_exec(&hex(&r["Msg"]), 3071, &hex(&r["SaltVal"])), em, "vector {count}");
            count += 1;
        }
        assert_eq!(count, 10);
    }

    #[test]
    fn wycheproof_emsa_2048() {
        let j = parse_json(&data("wycheproof/rsa_pss_2048_sha256_mgf1_32_test.json"));
        let mut count = 0;
        for g in j.get("testGroups").arr() {
            let pk = g.get("publicKey");
            let pubk = ::rsa::RsaPublicKey::new(u(&hex(pk.get("modulus").str())), u(&hex(pk.get("publicExponent").str()))).unwrap();
            for t in g.get("tests").arr() {
                if t.get("result").str() != "valid" {
                    continue;
                }
                let em = recover_em(&pubk, &hex(t.get("sig").str()), 256);
                let hh: [u8; 32] = em[223..255].try_into().unwrap();
                let mask = mgf1_exec(&hh, 223);
                let salt: Vec<u8> = em[191..223].iter().zip(&mask[191..]).map(|(a, b)| a ^ b).collect();
                assert_eq!(emsa_pss_encode_exec(&hex(t.get("msg").str()), 2047, &salt), em, "tcId {}", t.get("tcId").num());
                count += 1;
            }
        }
        assert_eq!(count, 63);
    }

    // The 2052-bit key and signature of tests/rsa_pss.rs::pss_rsa2052_masking_kat: 5 bits cleared.
    #[test]
    fn emsa_mask_bits() {
        let p = hex("0359e29889111427d45e0a7d1b5c4fcd20e9385365d6ba47237a07f61f43b9749dbb0c4ca0eb731d3505fa1a9fc7f7523e6c50834c294e22c524e43aeeb0b55838130129e1f44cbd55f65573b7c241692a297239ab52fb2aeb9b83b5aaa35367c28d8a98818559deb516bebdd3ff5d2feefda32eb265a0e6b2045463b3752856d7");
        let q = hex("03a2b01240d78fc8bd35a783bc29d19d100eb37822718cbde0cc246fc1bb49532f7354f1b0aa87bc5ba741eb43e5542ee7611dc7907d37ed6573590269c94fcc528907746d7dca3d7dfaddeba94578e47d176de829c93365099f7f1dcd23b918bae692e04987b30c9e7082ff5f6594b456755ecc7c5938e8ec8bdd6b2c85bcc92d");
        let sig = hex("04a08314b43fed2b7ea3d175947e1680f6b9b515e96c5e597935b5fcbb51e4f9e4d297e3e95b9a7d2865c5aa3d71b394295be3a0d23684d892a92fe81041304162ae6c1500e67821c05d2d8f02b654517a2a5cb890cc513be2a1e89d05ebf6cbbaf4b7ad62d4c90645952724280d5784289a0555f4d040b8f26cfbada65ac5006bc98a5920f708144f89b52d8ee326e53a64738d409ab946000965fcd0a0e717d4af6bcd5cfed126fa0088531a9b8b5fda2aded8ddf5c5bd4e4c3ab596f118847be17ebab2ba75d03854011a515e854538bcc04cc2a208d8b3c75e8d050872d6290ce7bda30129bd9c8f91ee35561465242362a9cd961fd77cc09f4c8252e751bb");
        let k = ::rsa::RsaPrivateKey::from_p_q(u(&p), u(&q), BoxedUint::from(65537u32)).unwrap();
        let em = recover_em(&k.to_public_key(), &sig, 257);
        let salt: Vec<u8> = (0..32).collect();
        assert_eq!(em[0] >> 3, 0);
        assert_eq!(emsa_pss_encode_exec(b"TLS 1.3, server CertificateVerify", 2051, &salt), em);
    }

    #[test]
    fn emsa_len_2049() {
        let r = emsa_pss_encode_exec(b"m", 2048, &[7u8; 32]);
        assert_eq!(r.len(), 256);
        assert_eq!(r[255], 0xbc);
    }

    #[test]
    fn mgf1_one_block() {
        let seed = [0x5au8; 32];
        let mut m = seed.to_vec();
        m.extend_from_slice(&[0u8; 4]);
        assert_eq!(mgf1_exec(&seed, 20), sha2::Sha256::digest(&m)[..20]);
    }

    #[test]
    fn mgf1_len_zero() {
        assert!(mgf1_exec(&[1u8; 32], 0).is_empty());
    }
}
