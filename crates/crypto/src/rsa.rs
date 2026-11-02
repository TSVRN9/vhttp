//! RSASSA-PSS-SHA256 signing (RFC 8017 §8.1.1; rsa_pss_rsae_sha256 is RFC 8446 §4.2.3, salt length
//! 32, MGF1-SHA256): spec and verified exec. Signing only: no RSA
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
/// - Step 2a: m = OS2IP(EM). Step 2b: s = RSASP1(K, m) = m^d mod n (RFC 8017 §5.2.1, form (a)).
///   m < 2^(modBits - 1) <= n, so RSASP1's "message representative out of range" cannot occur.
/// - Step 2c: S = I2OSP(s, k), k = ceil(modBits / 8).
pub open spec fn spec_rsassa_pss_sign(k: RsaKeySpec, msg: Seq<u8>, salt: Seq<u8>) -> Seq<u8> {
    let mod_bits = bitlen(k.n);
    let em = emsa_pss_encode(msg, (mod_bits - 1) as nat, salt);
    let s = (pow(os2ip(em) as int, k.d) % (k.n as int)) as nat;
    i2osp(s, (mod_bits + 7) / 8)
}

/// RFC 8017 §8.1.1 with the public n and secret d apart, because ct labels are per parameter.
/// Primality in `rsa_key_wf` can be established by no verified code; it flows up to the trusted
/// shell's key loading.
#[cfg_attr(ct_check, ct::secret(d, salt, msg), ct::public(n))]
pub(crate) fn rsa_pss_sign_inner(n: &[u8], d: &[u8], msg: &[u8], salt: &[u8], Ghost(ks): Ghost<RsaKeySpec>) -> (r: Vec<u8>)
    requires
        rsa_key_wf(ks),
        ks.n == os2ip(n@),
        ks.d == os2ip(d@),
        msg@.len() <= MAX_INPUT_LEN,
        salt@.len() == 32,
    ensures
        r@ == spec_rsassa_pss_sign(ks, msg@, salt@),
{
    let bits = modulus_bits(n);
    let em = emsa_pss_encode_exec(msg, bits - 1, salt);
    let k: usize = (bits + 7) / 8;
    proof {
        lemma_wf_odd(ks);
        lemma_bitlen_bound(ks.n);
        lemma_pow2_256(k as nat);
        assert(8 * k >= bits);
        if (8 * k) > bits { lemma_pow2_strictly_increases(bits as nat, (8 * k) as nat); }
        lemma_os2ip_bound(em@);
        assert(em@.len() <= k);
        if (em@.len() < k) { lemma_pow_increases(256, em@.len(), k as nat); }
    }
    rsasp1(n, d, em.as_slice(), k)
}

/// Total: under `rsa_key_wf` the spec has no error case. Only projects the key's fields; e, p and
/// q are not read.
pub fn rsa_pss_sha256_sign(key: &RsaPrivateKey, msg: &[u8], salt: &[u8]) -> (r: Vec<u8>)
    requires
        rsa_key_wf(key@),
        msg@.len() <= MAX_INPUT_LEN,
        salt@.len() == 32,
    ensures
        r@ == spec_rsassa_pss_sign(key@, msg@, salt@),
{
    rsa_pss_sign_inner(key.n.as_slice(), key.d.as_slice(), msg, salt, Ghost(key@))
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
/// The length of msg is public: it sets the block count of sha256's loop. Only its content is secret.
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

#[allow(unused_imports)]
use crate::bignum::*;
#[allow(unused_imports)]
use crate::mont::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;

proof fn lemma_bitlen_step(x: nat, b: nat)
    requires b <= 1,
    ensures bitlen(2 * x + b) == (if 2 * x + b == 0 { 0 } else { 1 + bitlen(x) }),
{
    assert(((2 * x + b) as nat) / 2 == x);
}

proof fn lemma_bitlen_bound(x: nat)
    ensures x < pow2(bitlen(x)), x > 0 ==> pow2((bitlen(x) - 1) as nat) <= x,
    decreases x,
{
    lemma_pow2_unfold(1);
    lemma2_to64();
    if x > 0 {
        lemma_bitlen_bound(x / 2);
        lemma_pow2_unfold(bitlen(x));
        if x / 2 > 0 {
            lemma_pow2_unfold((bitlen(x) - 1) as nat);
        }
    }
}

proof fn lemma_pow2_256(j: nat)
    ensures pow2(8 * j) == pow(256, j),
    decreases j,
{
    reveal(pow);
    lemma2_to64();
    if j == 0 {
    } else {
        lemma_pow2_256((j - 1) as nat);
        lemma_pow2_adds(8 * (j - 1) as nat, 8);
        assert(8 * (j - 1) as nat + 8 == 8 * j);
        lemma_mul_is_commutative(pow(256, (j - 1) as nat), 256);
    }
}

/// The bit length of the public modulus. Only the low 512 octets are read, which the requires
/// makes enough. The only fn that branches on n.
#[verifier::spinoff_prover]
#[cfg_attr(ct_check, ct::public(n))]
fn modulus_bits(n: &[u8]) -> (r: usize)
    requires
        bitlen(os2ip(n@)) <= 4096,
    ensures
        r as nat == bitlen(os2ip(n@)),
{
    let ghost full = os2ip(n@);
    // ct: branch on the public length of n
    let start: usize = if n.len() > 512 { n.len() - 512 } else { 0 };
    let ghost tail = n@.subrange(start as int, n@.len() as int);
    proof {
        lemma_bitlen_bound(full);
        lemma_pow2_256(512);
        assert(pow2(4096) == pow(256, 512));
        if bitlen(full) < 4096 { lemma_pow2_strictly_increases(bitlen(full), 4096); }
        if n@.len() > 512 {
            lemma_os2ip_tail(n@, 512);
        }
        assert(start == 0 ==> tail =~= n@);
        assert(os2ip(tail) == full);
        assert(tail.take(0) =~= Seq::<u8>::empty());
    }
    let mut bits: usize = 0;
    let mut j: usize = start;
    // ct: loop on the public length of n
    while j < n.len()
        invariant
            start <= j <= n@.len(),
            n@.len() - start <= 512,
            tail == n@.subrange(start as int, n@.len() as int),
            bits <= 8 * (j - start),
            bits as nat == bitlen(os2ip(tail.take(j - start))),
        decreases n@.len() - j,
    {
        let byte = n[j];
        let ghost hi = os2ip(tail.take(j - start));
        let ghost mut ev: nat = hi;
        proof { bv_bit_u8(byte, 0); lemma2_to64(); lemma_mul_basics(hi as int); }
        let mut k: u8 = 0;
        // ct: a constant count
        while k < 8
            invariant
                k <= 8,
                start <= j < n@.len(),
                n@.len() - start <= 512,
                tail == n@.subrange(start as int, n@.len() as int),
                bits <= 8 * (j - start) + k,
                ev == hi * pow2(k as nat) + ((byte as u32) >> ((8 - k) as u32)),
                bits as nat == bitlen(ev),
            decreases 8 - k,
        {
            let bit = (byte >> (7 - k)) & 1;
            proof {
                bv_bit_u8(byte, k);
                lemma_pow2_unfold((k + 1) as nat);
                lemma_prefix_step(hi as int, pow2(k as nat) as int);
                lemma_bitlen_step(ev, bit as nat);
            }
            // ct: branch on the public modulus
            if bits > 0 || bit == 1 {
                proof {
                    if bits == 0 && bit != 1 { assert(false); }
                }
                bits = bits + 1;
            } else {
                proof {
                    assert(bitlen(ev) == 0);
                    assert(ev == 0) by { if ev > 0 { assert(bitlen(ev) >= 1); } }
                }
            }
            proof { ev = 2 * ev + bit as nat; }
            k = k + 1;
        }
        proof {
            let t = tail.take(j + 1 - start);
            assert(t.drop_last() =~= tail.take(j - start));
            assert(t.last() == byte);
        }
        j = j + 1;
    }
    proof { assert(tail.take(n@.len() - start) =~= tail); }
    bits
}

// One always-multiply step.
#[cfg_attr(ct_check, ct::secret(r, x, bit, m, mp), ct::public(nl))]
fn pow_step_ct(r: &[u64; 64], x: &[u64; 64], bit: u64, m: &[u64; 64], mp: u64, nl: usize, Ghost(ri): Ghost<int>, Ghost(xd): Ghost<int>, Ghost(ev): Ghost<nat>) -> (o: [u64; 64])
    requires
        1 <= nl <= 64,
        bit <= 1,
        (m[0] as int * mp as int + 1) % 0x1_0000_0000_0000_0000 == 0,
        limbs(m@, nl as nat) > 1,
        (wp(nl as nat) * ri) % limbs(m@, nl as nat) == 1,
        limbs(r@, nl as nat) < limbs(m@, nl as nat),
        limbs(x@, nl as nat) < limbs(m@, nl as nat),
        xd == mdec(limbs(x@, nl as nat), limbs(m@, nl as nat), ri),
        mdec(limbs(r@, nl as nat), limbs(m@, nl as nat), ri) == pow(xd, ev) % limbs(m@, nl as nat),
    ensures
        limbs(o@, nl as nat) < limbs(m@, nl as nat),
        mdec(limbs(o@, nl as nat), limbs(m@, nl as nat), ri) == pow(xd, 2 * ev + bit as nat) % limbs(m@, nl as nat),
{
    let ghost n = nl as nat;
    let ghost mm = limbs(m@, n);
    let s = mont_mul_n(r, r, m, mp, nl);
    proof {
        lemma_mdec_mul(limbs(s@, n), limbs(r@, n), limbs(r@, n), mm, wp(n), ri);
        lemma_pow_step(xd, ev, mm);
    }
    let t = mont_mul_n(&s, x, m, mp, nl);
    proof {
        lemma_mdec_mul(limbs(t@, n), limbs(s@, n), limbs(x@, n), mm, wp(n), ri);
        // xd is already reduced
        lemma_mod_twice(limbs(x@, n) * ri, mm);
        lemma_mul_mod_noop_right(pow(xd, 2 * ev) % mm, xd, mm);
        lemma_mul_mod_noop_left(pow(xd, 2 * ev), xd, mm);
    }
    select_n(bit, &t, &s, nl)
}

proof fn lemma_prefix_step(hi: int, p: int)
    ensures hi * (2 * p) == 2 * (hi * p),
{
    lemma_mul_is_associative(hi, 2, p);
    lemma_mul_is_commutative(hi, 2);
    lemma_mul_is_associative(2, hi, p);
}

// x^e in Montgomery form, 8k always-multiply steps: time depends on k and nl only.
// ponytail: no CRT or window, 7 ms at 2048 bits, 52 ms at 4096; a 4-bit window saves about 37%, CRT about 75%, at the cost of a general FLT proof
#[cfg_attr(ct_check, ct::secret(x, e, m, mp, one), ct::public(k, nl))]
fn mod_pow_ct(x: &[u64; 64], e: &[u8], k: usize, m: &[u64; 64], mp: u64, one: &[u64; 64], nl: usize, Ghost(ri): Ghost<int>) -> (r: [u64; 64])
    requires
        e@.len() == k,
        1 <= nl <= 64,
        (m[0] as int * mp as int + 1) % 0x1_0000_0000_0000_0000 == 0,
        limbs(m@, nl as nat) > 1,
        (wp(nl as nat) * ri) % limbs(m@, nl as nat) == 1,
        limbs(x@, nl as nat) < limbs(m@, nl as nat),
        limbs(one@, nl as nat) < limbs(m@, nl as nat),
        mdec(limbs(one@, nl as nat), limbs(m@, nl as nat), ri) == 1,
    ensures
        limbs(r@, nl as nat) < limbs(m@, nl as nat),
        mdec(limbs(r@, nl as nat), limbs(m@, nl as nat), ri) == pow(mdec(limbs(x@, nl as nat), limbs(m@, nl as nat), ri), os2ip(e@)) % limbs(m@, nl as nat),
{
    let ghost n = nl as nat;
    let ghost mm = limbs(m@, n);
    let ghost xd = mdec(limbs(x@, n), mm, ri);
    proof {
        lemma_pow0(xd);
        lemma_small_mod(1, mm as nat);
        assert(e@.take(0) =~= Seq::<u8>::empty());
    }
    let mut r = *one;
    let mut j: usize = 0;
    // ct: loop on the public k
    while j < k
        invariant
            e@.len() == k,
            j <= e@.len(),
            1 <= nl <= 64,
            (m[0] as int * mp as int + 1) % 0x1_0000_0000_0000_0000 == 0,
            n == nl as nat,
            mm == limbs(m@, n),
            mm > 1,
            (wp(n) * ri) % mm == 1,
            limbs(x@, n) < mm,
            xd == mdec(limbs(x@, n), mm, ri),
            limbs(r@, n) < mm,
            mdec(limbs(r@, n), mm, ri) == pow(xd, os2ip(e@.take(j as int))) % mm,
        decreases e@.len() - j,
    {
        let byte = e[j];
        let ghost hi = os2ip(e@.take(j as int));
        let ghost mut ev: nat = hi;
        proof { bv_bit_u8(byte, 0); lemma2_to64(); }
        let mut b: u8 = 0;
        // ct: a constant count
        while b < 8
            invariant
                b <= 8,
                1 <= nl <= 64,
                (m[0] as int * mp as int + 1) % 0x1_0000_0000_0000_0000 == 0,
                n == nl as nat,
                mm == limbs(m@, n),
                mm > 1,
                (wp(n) * ri) % mm == 1,
                limbs(x@, n) < mm,
                xd == mdec(limbs(x@, n), mm, ri),
                limbs(r@, n) < mm,
                ev == hi * pow2(b as nat) + ((byte as u32) >> ((8 - b) as u32)),
                mdec(limbs(r@, n), mm, ri) == pow(xd, ev) % mm,
            decreases 8 - b,
        {
            let bit = (byte >> (7 - b)) & 1;
            proof {
                bv_bit_u8(byte, b);
                lemma_pow2_unfold((b + 1) as nat);
                lemma_prefix_step(hi as int, pow2(b as nat) as int);
            }
            r = pow_step_ct(&r, x, bit as u64, m, mp, nl, Ghost(ri), Ghost(xd), Ghost(ev));
            proof { ev = 2 * ev + bit as nat; }
            b = b + 1;
        }
        proof {
            let t = e@.take(j + 1);
            assert(t.drop_last() =~= e@.take(j as int));
            assert(t.last() == byte);
        }
        j = j + 1;
    }
    proof { assert(e@.take(e@.len() as int) =~= e@); }
    r
}

proof fn lemma_prime_odd(p: nat, ed: nat)
    requires is_prime(p), ed % ((p - 1) as nat) == 1,
    ensures p % 2 == 1,
{
    if p == 2 {
        assert(ed % 1 == 0) by { lemma_small_mod(0, 1); lemma_fundamental_div_mod(ed as int, 1); }
        assert(false);
    } else {
        assert(1 < 2nat < p);
        assert(p % 2nat != 0);
    }
}

proof fn lemma_odd_mul(p: nat, q: nat)
    requires p % 2 == 1, q % 2 == 1,
    ensures (p * q) % 2 == 1,
{
    lemma_mul_mod_noop(p as int, q as int, 2);
}

proof fn lemma_wf_odd(k: RsaKeySpec)
    requires rsa_key_wf(k),
    ensures k.n % 2 == 1,
{
    lemma_prime_odd(k.p, k.e * k.d);
    lemma_prime_odd(k.q, k.e * k.d);
    lemma_odd_mul(k.p, k.q);
}

// (a * R) == b mod M, (R * ri) == 1 mod M gives a == (b * ri) mod M.
proof fn lemma_cancel(a: int, b: int, rr: int, ri: int, m: int)
    requires m > 1, (a * rr) % m == b % m, (rr * ri) % m == 1,
    ensures a % m == (b * ri) % m,
{
    lemma_mul_mod_noop_left(a * rr, ri, m);
    lemma_mul_mod_noop_left(b, ri, m);
    lemma_mul_is_associative(a, rr, ri);
    lemma_mul_mod_noop_right(a, rr * ri, m);
    lemma_mul_basics(a);
}

proof fn lemma_ri(ri: int, rr: int, m: int)
    requires m > 1, (ri * rr) % m == (1int * 1int) % m,
    ensures (rr * ri) % m == 1,
{
    lemma_mul_is_commutative(ri, rr);
    lemma_small_mod(1, m as nat);
}

proof fn lemma_to_mont(xv: int, a: int, rsq: int, rr: int, ri: int, m: int)
    requires
        m > 1,
        (xv * rr) % m == (a * rsq) % m,
        rsq == (rr * rr) % m,
        (rr * ri) % m == 1,
    ensures
        mdec(xv, m, ri) == a % m,
{
    // a * rsq == (a * rr) * rr
    lemma_mul_mod_noop_right(a, rr * rr, m);
    lemma_mul_is_associative(a, rr, rr);
    // xv == (a * rr) (mod m), by cancelling rr on both sides
    lemma_cancel(xv, (a * rr) * rr, rr, ri, m);
    lemma_mul_is_associative(a * rr, rr, ri);
    lemma_mul_mod_noop_right(a * rr, rr * ri, m);
    lemma_mul_basics(a * rr);
    // so xv * ri == a * (rr * ri) == a
    lemma_mul_mod_noop_left(xv, ri, m);
    lemma_mul_mod_noop_left(a * rr, ri, m);
    lemma_mul_is_associative(a, rr, ri);
    lemma_mul_mod_noop_right(a, rr * ri, m);
    lemma_mul_basics(a);
}

proof fn lemma_from_mont(s: int, r: int, rr: int, ri: int, m: int)
    requires
        m > 1,
        0 <= s < m,
        (s * rr) % m == (r * 1int) % m,
        (rr * ri) % m == 1,
    ensures
        s == mdec(r, m, ri),
{
    lemma_mul_basics(r);
    lemma_cancel(s, r, rr, ri, m);
    lemma_small_mod(s as nat, m as nat);
}

proof fn lemma_odd_low(mm: int, m0: u64)
    requires mm % 2 == 1, mm % 0x1_0000_0000_0000_0000 == m0 as int, mm >= 0,
    ensures m0 % 2 == 1,
{
    lemma_mod_mod(mm, 2, 0x8000_0000_0000_0000);
    assert(2int * 0x8000_0000_0000_0000 == 0x1_0000_0000_0000_0000);
}

proof fn lemma_rsq(nl: nat)
    ensures pow2(128 * nl) as int == wp(nl) * wp(nl),
{
    lemma_wp_256(nl);
    lemma_pow2_256(8 * nl);
    assert(8 * (8 * nl) == 64 * nl);
    lemma_pow2_adds(64 * nl, 64 * nl);
    assert(64 * nl + 64 * nl == 128 * nl);
}

/// RFC 8017 §5.2.1 RSASP1, form (a): m^d mod n as k octets.
/// nl comes from the public k. n, d and em may be any length, with leading zeros; their lengths are public: pad_be's copy depends on them. The exponent loop runs 8k bits whatever d's length.
#[verifier::spinoff_prover]
#[cfg_attr(ct_check, ct::secret(n, d, em), ct::public(k))]
fn rsasp1(n: &[u8], d: &[u8], em: &[u8], k: usize) -> (r: Vec<u8>)
    requires
        256 <= k <= 512,
        os2ip(n@) > 1,
        os2ip(n@) % 2 == 1,
        os2ip(n@) < pow(256, k as nat),
        os2ip(d@) < os2ip(n@),
        os2ip(em@) < pow(256, k as nat),
    ensures
        r@ == i2osp((pow(os2ip(em@) as int, os2ip(d@)) % (os2ip(n@) as int)) as nat, k as nat),
{
    let nl: usize = (k + 7) / 8;
    proof {
        lemma_pow_increases(256, k as nat, (8 * nl) as nat);
        lemma_wp_256(nl as nat);
    }
    let n_be = pad_be(n, 8 * nl);
    let d_be = pad_be(d, k);
    let em_be = pad_be(em, 8 * nl);
    let m = limbs_from_be_n(n_be.as_slice(), nl);
    let a = limbs_from_be_n(em_be.as_slice(), nl);
    let ghost nn = nl as nat;
    let ghost mm = limbs(m@, nn);
    let ghost aa = os2ip(em@) as int;
    let ghost dd = os2ip(d@);
    let ghost rr = wp(nn);
    proof {
        lemma_limbs_low(m@, nn);
        lemma_odd_low(mm, m[0]);
    }
    let mp = neg_inv64(m[0]);
    let mut unit = [0u64; 64];
    unit[0] = 1;
    proof {
        lemma_limbs_one(unit@, nn);
    }
    let _rinv = mont_mul_n(&unit, &unit, &m, mp, nl);
    let ghost ri = limbs(_rinv@, nn);
    proof { lemma_ri(ri, rr, mm); }
    // ponytail: about 0.3 ms at 2048 bits; cache it in the key if signing ever matters
    let r2 = pow2_mod(&m, nl, 128 * nl);
    proof {
        lemma_rsq(nn);
        assert(limbs(r2@, nn) == (rr * rr) % mm);
    }
    let one = mont_mul_n(&unit, &r2, &m, mp, nl);
    let x = mont_mul_n(&a, &r2, &m, mp, nl);
    proof {
        lemma_to_mont(limbs(one@, nn), 1, limbs(r2@, nn), rr, ri, mm);
        lemma_small_mod(1, mm as nat);
        lemma_to_mont(limbs(x@, nn), aa, limbs(r2@, nn), rr, ri, mm);
    }
    let rp = mod_pow_ct(&x, d_be.as_slice(), k, &m, mp, &one, nl, Ghost(ri));
    let s = mont_mul_n(&rp, &unit, &m, mp, nl);
    proof {
        lemma_limbs_bound(s@, nn);
        lemma_from_mont(limbs(s@, nn), limbs(rp@, nn), rr, ri, mm);
        lemma_pow_mod_noop(aa, dd, mm);
    }
    limbs_to_be_n(&s, nl, k)
}

} // verus!

#[cfg(test)]
#[path = "../tests/vecdata/mod.rs"]
mod vecdata;

#[cfg(test)]
mod tests {
    use super::vecdata::*;
    use super::*;
    use ::rsa::traits::{PrivateKeyParts, PublicKeyParts};
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

    // emLen = k - 1: EM has 256 octets under a 257-octet signature. RustCrypto's verify is the
    // independent check of EM; it binds EM to the salt that DB carries, compared last.
    #[test]
    fn emsa_len_2049() {
        let p = hex("01fa9ff01c702938f8290b7fe5099537cf6c0d0b48a1f9ef02a02614387c464ab96737256ee4d1cb82c27c71f748737adb1939bd1aa6732ea3da37355f1b516b6c7052da370af35f9df697cdf0da1d140f29fd9b87bd777f21523030824f3ce0ffab10b79aeb16dba61509d65841c38f8721db01fcb63dab8c82a82312de30ca63");
        let q = hex("cc0ecbe9727c4d3d1651a1be964f3f89e202875507f8686b1168565b262ace6724e33d24b23471ea83d13966f35c5aa8a2cdb9b556862c9f09b2c5afccec2868742a7b9b63a92e72a4145117a61fd8f33a74e2b1b32d45a08827cdc59dd8bc39c3a10fc341fd31a01b2362a0dad100c91ec4af744c23e68aba202b23da2403dd");
        let k = ::rsa::RsaPrivateKey::from_p_q(u(&p), u(&q), BoxedUint::from(65537u32)).unwrap();
        assert_eq!(k.n().bits(), 2049);
        let pubk = k.to_public_key();
        let (msg, salt) = (b"TLS 1.3, server CertificateVerify", [7u8; 32]);
        let em = emsa_pss_encode_exec(msg, 2048, &salt);
        assert_eq!(em.len(), 256);
        assert_eq!(em[255], 0xbc);
        let sig = rsasp1(&k.n().to_be_bytes(), &k.d().to_be_bytes(), &em, 257);
        assert_eq!(sig.len(), 257);
        pubk.verify(::rsa::Pss::<sha2::Sha256>::new_with_salt(32), &sha2::Sha256::digest(msg), &sig).unwrap();
        assert_eq!(recover_em(&pubk, &sig, 256), em);
        let hh: [u8; 32] = em[223..255].try_into().unwrap();
        let mask = mgf1_exec(&hh, 223);
        let got: Vec<u8> = em[191..223].iter().zip(&mask[191..]).map(|(a, b)| a ^ b).collect();
        assert_eq!(got, salt);
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

    // The groups of the Wycheproof sig_gen file at `bits` whose hash is SHA-256.
    fn sha256_groups(bits: usize) -> Vec<J> {
        let j = parse_json(&data(&format!("wycheproof/rsa_pkcs1_{bits}_sig_gen_test.json")));
        j.get("testGroups").arr().iter().filter(|g| g.get("sha").str() == "SHA-256").cloned().collect()
    }

    // The (n, d, e) of the first SHA-256 group, as the file has them: n carries a 00 prefix.
    fn key(bits: usize) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
        let g = sha256_groups(bits);
        let pk = g[0].get("privateKey");
        (hex(pk.get("modulus").str()), hex(pk.get("privateExponent").str()), hex(pk.get("publicExponent").str()))
    }

    // RFC 8017 §9.2 EMSA-PKCS1-v1_5 with SHA-256.
    fn pkcs1_em(msg: &[u8], k: usize) -> Vec<u8> {
        let di = hex("3031300d060960864801650304020105000420");
        let mut em = vec![0u8, 1];
        em.resize(k - di.len() - 32 - 1, 0xff);
        em.push(0);
        em.extend_from_slice(&di);
        em.extend_from_slice(&sha2::Sha256::digest(msg));
        em
    }

    #[test]
    fn wycheproof_rsasp1() {
        let mut count = 0;
        for bits in [2048, 3072, 4096] {
            for g in sha256_groups(bits) {
                let k = g.get("keySize").num() as usize / 8;
                let pk = g.get("privateKey");
                let (n, d) = (hex(pk.get("modulus").str()), hex(pk.get("privateExponent").str()));
                for t in g.get("tests").arr() {
                    let res = t.get("result").str();
                    if res != "valid" && res != "acceptable" {
                        continue;
                    }
                    let em = pkcs1_em(&hex(t.get("msg").str()), k);
                    assert_eq!(rsasp1(&n, &d, &em, k), hex(t.get("sig").str()), "tcId {}", t.get("tcId").num());
                    count += 1;
                }
            }
        }
        assert_eq!(count, 27);
    }

    #[test]
    fn rsasp1_small_result() {
        let (n, d, e) = key(2048);
        let pubk = ::rsa::RsaPublicKey::new(u(&n), u(&e)).unwrap();
        let s = BoxedUint::from_be_slice(&[1, 2], pubk.n_bits_precision()).unwrap();
        let m = ::rsa::hazmat::rsa_encrypt(&pubk, &s).unwrap().to_be_bytes();
        let mut want = vec![0u8; 254];
        want.extend_from_slice(&[1, 2]);
        assert_eq!(rsasp1(&n, &d, &m, 256), want);
    }

    #[test]
    fn rsasp1_edge_messages() {
        let (n, d, _) = key(2048);
        let k = 256;
        assert_eq!(n[0], 0);
        assert_eq!(d[k - 1] & 1, 1);
        let zero = vec![0u8; k];
        assert_eq!(rsasp1(&n, &d, &zero, k), zero);
        let mut one = zero.clone();
        one[k - 1] = 1;
        assert_eq!(rsasp1(&n, &d, &one, k), one);
        // n is odd, so n - 1 only clears the low bit
        let mut nm1 = n[1..].to_vec();
        nm1[k - 1] -= 1;
        assert_eq!(rsasp1(&n, &d, &nm1, k), nm1);
    }

    #[test]
    fn rsasp1_d_lengths() {
        let (n, d, _) = key(2048);
        let k = 256;
        let m = pkcs1_em(b"d lengths", k);
        // the key's d, then the shorter exponent its low 156 octets make
        for full in [&d[..], &d[100..]] {
            let stripped: Vec<u8> = full.iter().copied().skip_while(|&b| b == 0).collect();
            let mut prefixed = vec![0u8; 5];
            prefixed.extend_from_slice(&stripped);
            let mut padded = vec![0u8; k - stripped.len()];
            padded.extend_from_slice(&stripped);
            let want = rsasp1(&n, &stripped, &m, k);
            assert_eq!(want.len(), k);
            assert_eq!(rsasp1(&n, &prefixed, &m, k), want);
            assert_eq!(rsasp1(&n, &padded, &m, k), want);
        }
    }

    #[test]
    fn modulus_bits_edges() {
        let (n, _, _) = key(2048);
        assert_eq!(modulus_bits(&n[1..]), 2048);
        assert_eq!(modulus_bits(&n), 2048);
        let mut long = vec![0u8; 600];
        long.extend_from_slice(&n);
        assert_eq!(modulus_bits(&long), 2048);
        for (top, bits) in [(0x01u8, 2049), (0x0f, 2052)] {
            let mut x = vec![top];
            x.extend_from_slice(&[0u8; 256]);
            assert_eq!(modulus_bits(&x), bits);
        }
        let (n4, _, _) = key(4096);
        assert_eq!(n4.len(), 513);
        assert_eq!(modulus_bits(&n4), 4096);
    }

    // cargo test --release -p crypto rsa_speed -- --ignored --nocapture; on a hybrid CPU pin to a P-core (taskset -c 0 on this machine): cores differ by 1.8x
    #[test]
    #[ignore]
    fn rsa_speed() {
        for bits in [2048, 3072, 4096] {
            let (n, d, _) = key(bits);
            let k = bits / 8;
            let m = pkcs1_em(b"speed", k);
            let first = rsasp1(&n, &d, &m, k);
            let start = std::time::Instant::now();
            for _ in 0..20 {
                assert_eq!(rsasp1(&n, &d, &m, k), first);
            }
            println!("rsasp1 {bits}: {:.2} ms", start.elapsed().as_secs_f64() * 1e3 / 20.0);
        }
    }
}
