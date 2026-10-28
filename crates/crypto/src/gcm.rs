//! AES-128-GCM (NIST SP 800-38D, 96-bit IV, 128-bit tag): spec and verified exec.
#[allow(unused_imports)]
use crate::aes::*;
#[allow(unused_imports)]
use crate::bytes::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

/// SP 800-38D §5.2.1.1: len(P) <= 2^39 - 256 bits, i.e. 2^36 - 32 bytes.
pub const GCM_MAX_PT_LEN: usize = 0xF_FFFF_FFE0;

/// SP 800-38D §6.3 Algorithm 1, steps 2-3 from loop index i: bit x_i is `(x >> (127 - i)) & 1`.
pub open spec fn gf128_loop(x: u128, z: u128, v: u128, i: nat) -> u128
    decreases 128 - i,
{
    if i >= 128 {
        z
    } else {
        let z2 = if (x >> ((127 - i) as u128)) & 1 == 1 {
            z ^ v
        } else {
            z
        };
        let v2 = if v & 1 == 1 {
            (v >> 1) ^ (0xE1u128 << 120u128)
        } else {
            v >> 1
        };
        gf128_loop(x, z2, v2, i + 1)
    }
}

/// SP 800-38D §6.3 Algorithm 1: x . y in GF(2^128), Z0 = 0, V0 = Y, R = 11100001 || 0^120.
pub open spec fn gf128_mul(x: u128, y: u128) -> u128 {
    gf128_loop(x, 0, y, 0)
}

/// SP 800-38D §6.4: Y_0 = 0, Y_i = (Y_{i-1} xor X_i) . H, result Y_m.
pub open spec fn ghash(h: u128, x: Seq<u8>) -> u128
    recommends
        x.len() % 16 == 0,
    decreases x.len(),
{
    if x.len() < 16 {
        0
    } else {
        let n = (x.len() - 16) as nat;
        gf128_mul(ghash(h, x.subrange(0, n as int)) ^ (os2ip(x.subrange(n as int, x.len() as int)) as u128), h)
    }
}

/// SP 800-38D §6.2: increment the rightmost 32 bits of the block, mod 2^32, as a big-endian integer.
pub open spec fn inc32(cb: Seq<u8>) -> Seq<u8> {
    cb.subrange(0, 12) + i2osp((os2ip(cb.subrange(12, 16)) + 1) % 4294967296, 4)
}

/// SP 800-38D §6.5 GCTR: X_i xor CIPH_K(CB_i), CB_{i+1} = inc32(CB_i); a final partial block
/// uses the leading bytes of CIPH_K(CB_n).
pub open spec fn gctr(key: Seq<u8>, icb: Seq<u8>, x: Seq<u8>) -> Seq<u8>
    decreases x.len(),
{
    if x.len() == 0 {
        Seq::empty()
    } else {
        let n: int = if x.len() >= 16 {
            16
        } else {
            x.len() as int
        };
        let ks = spec_aes128_encrypt(key, icb);
        xor_bytes(x.subrange(0, n), ks.subrange(0, n)) + gctr(
            key,
            inc32(icb),
            x.subrange(n, x.len() as int),
        )
    }
}

/// Zero padding of `s` up to a multiple of 16 bytes (the 0^v and 0^u of SP 800-38D §7.1 step 4).
pub open spec fn zero_pad16(s: Seq<u8>) -> Seq<u8> {
    Seq::new(((16 - s.len() % 16) % 16) as nat, |i: int| 0u8)
}

/// SP 800-38D §7.1 step 2: J0 = IV || 0^31 || 1 for a 96-bit IV.
pub open spec fn gcm_j0(nonce: Seq<u8>) -> Seq<u8> {
    nonce + seq![0u8, 0u8, 0u8, 1u8]
}

/// SP 800-38D §7.1 steps 1, 2, 5, 6: T = GCTR_K(J0, S), S = GHASH_H(A || 0^v || C || 0^u || [len(A)]_64 || [len(C)]_64),
/// lengths in bits.
pub open spec fn gcm_tag(key: Seq<u8>, nonce: Seq<u8>, aad: Seq<u8>, c: Seq<u8>) -> Seq<u8> {
    let h = os2ip(spec_aes128_encrypt(key, Seq::new(16, |i: int| 0u8))) as u128;
    let s = ghash(
        h,
        aad + zero_pad16(aad) + c + zero_pad16(c) + i2osp(8 * aad.len(), 8) + i2osp(8 * c.len(), 8),
    );
    gctr(key, gcm_j0(nonce), i2osp(s as nat, 16))
}

/// SP 800-38D §7.1: C = GCTR_K(inc32(J0), P); the output is C || T.
pub open spec fn spec_gcm_seal(key: Seq<u8>, nonce: Seq<u8>, aad: Seq<u8>, pt: Seq<u8>) -> Seq<u8> {
    let c = gctr(key, inc32(gcm_j0(nonce)), pt);
    c + gcm_tag(key, nonce, aad, c)
}

/// SP 800-38D §7.2: None if the input is shorter than the tag or the tag does not match.
pub open spec fn spec_gcm_open(key: Seq<u8>, nonce: Seq<u8>, aad: Seq<u8>, ct: Seq<u8>) -> Option<
    Seq<u8>,
> {
    if ct.len() < 16 {
        None
    } else {
        let c = ct.subrange(0, ct.len() - 16);
        let t = ct.subrange(ct.len() - 16, ct.len() as int);
        if t != gcm_tag(key, nonce, aad, c) {
            None
        } else {
            Some(gctr(key, inc32(gcm_j0(nonce)), c))
        }
    }
}

// SP 800-38D §6.3 Algorithm 1 steps 3-4: one masked step, no branch on x or v.
proof fn bv_gf128_step(x: u128, z: u128, v: u128, s: u128) by (bit_vector)
    requires
        s < 128,
    ensures
        ((x >> s) & 1) * 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128
            <= 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128,
        (v & 1) * (0xE1u128 << 120u128) <= (0xE1u128 << 120u128),
        (z ^ (v & ((((x >> s) & 1) * 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128) as u128)))
            == (if (x >> s) & 1 == 1 {
            z ^ v
        } else {
            z
        }),
        ((v >> 1) ^ (((v & 1) * (0xE1u128 << 120u128)) as u128)) == (if v & 1 == 1 {
            (v >> 1) ^ (0xE1u128 << 120u128)
        } else {
            v >> 1
        }),
{
}

// SP 800-38D §6.3 Algorithm 1: constant-time x . y in GF(2^128).
// ponytail: 128 masked shift/xor steps per 16-byte block, ≈0.16 µs/block (release); upgrade:
// carry-less multiply (PCLMULQDQ) behind an equivalence lemma. 4-bit Shoup tables are faster
// but index by H, so not constant-time style
fn gf128_mul_exec(x: u128, y: u128) -> (r: u128)
    ensures
        r == gf128_mul(x, y),
{
    let mut z: u128 = 0;
    let mut v: u128 = y;
    let mut i: usize = 0;
    while i < 128
        invariant
            i <= 128,
            gf128_loop(x, z, v, i as nat) == gf128_mul(x, y),
        decreases 128 - i,
    {
        let s: u128 = (127 - i) as u128;
        proof {
            bv_gf128_step(x, z, v, s);
        }
        z = z ^ (v & (((x >> s) & 1) * 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128));
        v = (v >> 1) ^ ((v & 1) * (0xE1u128 << 120u128));
        i += 1;
    }
    z
}

// SP 800-38D §6.1: one big-endian byte shifted into a 128-bit accumulator.
proof fn bv_be128_step(acc: u128, b: u8, i: u128) by (bit_vector)
    requires
        i < 16,
        acc >> (8 * i) == 0,
    ensures
        acc < (1u128 << 120),
        ((acc << 8) | (b as u128)) >> (8 * (i + 1)) == 0,
        ((acc << 8) | (b as u128)) == acc * 256 + (b as u128),
{
}

proof fn bv_shr_zero() by (bit_vector)
    ensures
        0u128 >> 0u128 == 0,
{
}

// SP 800-38D §6.1: a 16-byte block as a 128-bit big-endian integer.
fn load_be128(src: &[u8], off: usize) -> (r: u128)
    requires
        off + 16 <= src@.len(),
    ensures
        r as nat == os2ip(src@.subrange(off as int, off + 16)),
{
    let ghost blk = src@.subrange(off as int, off + 16);
    let mut acc: u128 = 0;
    let mut i: usize = 0;
    assert(blk.take(0) =~= Seq::<u8>::empty());
    proof {
        bv_shr_zero();
    }
    while i < 16
        invariant
            off + 16 <= src.len(),
            blk == src@.subrange(off as int, off + 16),
            i <= 16,
            acc as nat == os2ip(blk.take(i as int)),
            acc >> (8 * (i as u128)) == 0,
        decreases 16 - i,
    {
        let b = src[off + i];
        proof {
            bv_be128_step(acc, b, i as u128);
            assert(blk.take(i + 1).drop_last() =~= blk.take(i as int));
        }
        acc = (acc << 8) | (b as u128);
        i += 1;
    }
    assert(blk.take(16) =~= blk);
    acc
}

proof fn bv_div256_u128(x: u128) by (bit_vector)
    ensures
        x / 256 == x >> 8,
        (x >> 8) / 256 == x >> 16,
        (x >> 16) / 256 == x >> 24,
        (x >> 24) / 256 == x >> 32,
        (x >> 32) / 256 == x >> 40,
        (x >> 40) / 256 == x >> 48,
        (x >> 48) / 256 == x >> 56,
        (x >> 56) / 256 == x >> 64,
        (x >> 64) / 256 == x >> 72,
        (x >> 72) / 256 == x >> 80,
        (x >> 80) / 256 == x >> 88,
        (x >> 88) / 256 == x >> 96,
        (x >> 96) / 256 == x >> 104,
        (x >> 104) / 256 == x >> 112,
        (x >> 112) / 256 == x >> 120,
        (x % 256) as u8 == x as u8,
        ((x >> 8) % 256) as u8 == (x >> 8) as u8,
        ((x >> 16) % 256) as u8 == (x >> 16) as u8,
        ((x >> 24) % 256) as u8 == (x >> 24) as u8,
        ((x >> 32) % 256) as u8 == (x >> 32) as u8,
        ((x >> 40) % 256) as u8 == (x >> 40) as u8,
        ((x >> 48) % 256) as u8 == (x >> 48) as u8,
        ((x >> 56) % 256) as u8 == (x >> 56) as u8,
        ((x >> 64) % 256) as u8 == (x >> 64) as u8,
        ((x >> 72) % 256) as u8 == (x >> 72) as u8,
        ((x >> 80) % 256) as u8 == (x >> 80) as u8,
        ((x >> 88) % 256) as u8 == (x >> 88) as u8,
        ((x >> 96) % 256) as u8 == (x >> 96) as u8,
        ((x >> 104) % 256) as u8 == (x >> 104) as u8,
        ((x >> 112) % 256) as u8 == (x >> 112) as u8,
        ((x >> 120) % 256) as u8 == (x >> 120) as u8,
{
}

/// I2OSP(x, 16) of a 128-bit block is its big-endian bytes.
proof fn lemma_i2osp_be16(x: u128)
    ensures
        i2osp(x as nat, 16) =~= seq![
            (x >> 120) as u8,
            (x >> 112) as u8,
            (x >> 104) as u8,
            (x >> 96) as u8,
            (x >> 88) as u8,
            (x >> 80) as u8,
            (x >> 72) as u8,
            (x >> 64) as u8,
            (x >> 56) as u8,
            (x >> 48) as u8,
            (x >> 40) as u8,
            (x >> 32) as u8,
            (x >> 24) as u8,
            (x >> 16) as u8,
            (x >> 8) as u8,
            x as u8,
        ],
{
    reveal_with_fuel(i2osp, 17);
    bv_div256_u128(x);
}

// SP 800-38D §6.1: a 128-bit integer as a 16-byte big-endian block.
fn store_be128(x: u128) -> (r: [u8; 16])
    ensures
        r@ == i2osp(x as nat, 16),
{
    let r = [
        (x >> 120) as u8,
        (x >> 112) as u8,
        (x >> 104) as u8,
        (x >> 96) as u8,
        (x >> 88) as u8,
        (x >> 80) as u8,
        (x >> 72) as u8,
        (x >> 64) as u8,
        (x >> 56) as u8,
        (x >> 48) as u8,
        (x >> 40) as u8,
        (x >> 32) as u8,
        (x >> 24) as u8,
        (x >> 16) as u8,
        (x >> 8) as u8,
        x as u8,
    ];
    proof {
        lemma_i2osp_be16(x);
    }
    assert(r@ =~= i2osp(x as nat, 16));
    r
}

// SP 800-38D §6.4 GHASH over data || 0^v, continuing from y = GHASH_H(s[0..off]).
fn ghash_padded(
    y: u128,
    h: u128,
    data: &[u8],
    Ghost(s): Ghost<Seq<u8>>,
    Ghost(off): Ghost<int>,
) -> (r: u128)
    requires
        0 <= off,
        off % 16 == 0,
        off + (data@ + zero_pad16(data@)).len() <= s.len(),
        s.subrange(off, off + (data@ + zero_pad16(data@)).len()) == data@ + zero_pad16(data@),
        y == ghash(h, s.take(off)),
    ensures
        r == ghash(h, s.take(off + (data@ + zero_pad16(data@)).len())),
{
    hide(spec_aes128_encrypt);
    hide(gf128_mul);
    let ghost p = data@ + zero_pad16(data@);
    let mut y = y;
    let mut i: usize = 0;
    let ghost mut nb: int = 0;
    while data.len() - i >= 16
        invariant
            0 <= off,
            off % 16 == 0,
            p == data@ + zero_pad16(data@),
            off + p.len() <= s.len(),
            s.subrange(off, off + p.len()) == p,
            i <= data.len(),
            i == 16 * nb,
            y == ghash(h, s.take(off + i)),
        decreases data.len() - i,
    {
        let blk = load_be128(data, i);
        proof {
            let t = s.take(off + i + 16);
            let tb = t.subrange(off + i, off + i + 16);
            assert forall|k: int| 0 <= k < 16 implies #[trigger] tb[k]
                == data@.subrange(i as int, i + 16)[k] by {
                assert(s.subrange(off, off + p.len())[i + k] == p[i + k]);
            }
            assert(t.subrange(0, off + i) =~= s.take(off + i));
            assert(tb =~= data@.subrange(i as int, i + 16));
            // SP 800-38D §6.4 step 4: one block of GHASH.
            assert(ghash(h, t) == gf128_mul(ghash(h, s.take(off + i)) ^ (os2ip(
                data@.subrange(i as int, i + 16),
            ) as u128), h));
        }
        y = gf128_mul_exec(y ^ blk, h);
        i += 16;
        proof {
            nb = nb + 1;
        }
    }
    // SP 800-38D §7.1 step 4: the last partial block, zero-padded to 16 bytes.
    let r = data.len() - i;
    proof {
        lemma_fundamental_div_mod_converse(data.len() as int, 16, nb, r as int);
    }
    if r > 0 {
        let mut buf = [0u8; 16];
        let mut j: usize = 0;
        while j < r
            invariant
                i + r == data.len(),
                r < 16,
                j <= r,
                forall|k: int| 0 <= k < j ==> buf@[k] == data@[i + k],
                forall|k: int| j <= k < 16 ==> buf@[k] == 0u8,
            decreases r - j,
        {
            buf[j] = data[i + j];
            j += 1;
        }
        let blk = load_be128(buf.as_slice(), 0);
        proof {
            assert(p.len() == i + 16);
            let t = s.take(off + i + 16);
            let tb = t.subrange(off + i, off + i + 16);
            assert forall|k: int| 0 <= k < 16 implies #[trigger] tb[k]
                == buf@[k] by {
                assert(s.subrange(off, off + p.len())[i + k] == p[i + k]);
            }
            assert(t.subrange(0, off + i) =~= s.take(off + i));
            assert(tb =~= buf@.subrange(0, 16));
            // SP 800-38D §6.4 step 4: the padded last block.
            assert(ghash(h, t) == gf128_mul(ghash(h, s.take(off + i)) ^ (os2ip(
                buf@.subrange(0, 16),
            ) as u128), h));
        }
        y = gf128_mul_exec(y ^ blk, h);
    } else {
        assert(p.len() == i);
    }
    y
}

// SP 800-38D §6.5, §7.1 step 2: the counter block nonce || [c]_32.
fn ctr_block(nonce: &[u8], c: u32) -> (r: [u8; 16])
    requires
        nonce@.len() == 12,
    ensures
        r@ == nonce@ + i2osp(c as nat, 4),
{
    let mut r = [0u8; 16];
    let mut i: usize = 0;
    while i < 12
        invariant
            nonce.len() == 12,
            i <= 12,
            forall|k: int| 0 <= k < i ==> r@[k] == nonce@[k],
        decreases 12 - i,
    {
        r[i] = nonce[i];
        i += 1;
    }
    r[12] = (c >> 24) as u8;
    r[13] = (c >> 16) as u8;
    r[14] = (c >> 8) as u8;
    r[15] = c as u8;
    proof {
        crate::sha256::lemma_i2osp_be4(c);
    }
    assert(r@ =~= nonce@ + i2osp(c as nat, 4));
    r
}

proof fn bv_u32_bytes(c: u32) by (bit_vector)
    ensures
        ((c >> 24) as u8) as u32 * 0x100_0000 + ((c >> 16) as u8) as u32 * 0x1_0000 + ((
        c >> 8) as u8) as u32 * 0x100 + (c as u8) as u32 == c,
{
}

proof fn lemma_wrapping_inc(c: u32)
    ensures
        vstd::wrapping::u32_specs::wrapping_add(c, 1) as nat == (c as nat + 1) % 0x1_0000_0000,
{
}

// SP 800-38D §6.2: inc32 of nonce || [c]_32 is nonce || [c + 1 mod 2^32]_32.
proof fn lemma_inc32(nonce: Seq<u8>, c: u32)
    requires
        nonce.len() == 12,
    ensures
        inc32(nonce + i2osp(c as nat, 4)) == nonce + i2osp(
            vstd::wrapping::u32_specs::wrapping_add(c, 1) as nat,
            4,
        ),
{
    let cb = nonce + i2osp(c as nat, 4);
    crate::sha256::lemma_i2osp_be4(c);
    assert(cb.subrange(0, 12) =~= nonce);
    let lo = cb.subrange(12, 16);
    assert(lo =~= i2osp(c as nat, 4));
    crate::sha256::lemma_os2ip4(lo);
    bv_u32_bytes(c);
    assert(os2ip(lo) == c as nat);
    lemma_wrapping_inc(c);
}

// SP 800-38D §7.1 step 2: J0 = nonce || [1]_32, and the first payload counter block is
// nonce || [2]_32.
proof fn lemma_j0(nonce: Seq<u8>)
    requires
        nonce.len() == 12,
    ensures
        gcm_j0(nonce) =~= nonce + i2osp(1, 4),
        inc32(gcm_j0(nonce)) =~= nonce + i2osp(2, 4),
{
    reveal_with_fuel(i2osp, 5);
    assert(i2osp(1, 4) =~= seq![0u8, 0u8, 0u8, 1u8]);
    lemma_inc32(nonce, 1);
    assert(vstd::wrapping::u32_specs::wrapping_add(1u32, 1) == 2);
}

/// SP 800-38D §6.5: GCTR preserves the length of its input.
pub proof fn lemma_gctr_len(key: Seq<u8>, icb: Seq<u8>, x: Seq<u8>)
    ensures
        gctr(key, icb, x).len() == x.len(),
    decreases x.len(),
{
    if x.len() > 0 {
        let n: int = if x.len() >= 16 {
            16
        } else {
            x.len() as int
        };
        lemma_gctr_len(key, inc32(icb), x.subrange(n, x.len() as int));
    }
}

// SP 800-38D §6.5 GCTR from counter block nonce || [c0]_32, appended to out.
fn gctr_append(
    rk: &[u8; 176],
    Ghost(key): Ghost<Seq<u8>>,
    nonce: &[u8],
    c0: u32,
    x: &[u8],
    out: &mut Vec<u8>,
)
    requires
        rk_ok(rk@, key),
        nonce@.len() == 12,
    ensures
        final(out)@ == old(out)@ + gctr(key, nonce@ + i2osp(c0 as nat, 4), x@),
{
    hide(spec_aes128_encrypt);
    hide(gf128_mul);
    hide(key_word);
    let ghost target = old(out)@ + gctr(key, nonce@ + i2osp(c0 as nat, 4), x@);
    let mut c = c0;
    let mut off: usize = 0;
    assert(x@.skip(0) =~= x@);
    while off < x.len()
        invariant
            rk_ok(rk@, key),
            nonce@.len() == 12,
            off <= x.len(),
            out@ + gctr(key, nonce@ + i2osp(c as nat, 4), x@.skip(off as int)) == target,
        decreases x.len() - off,
    {
        let ghost icb = nonce@ + i2osp(c as nat, 4);
        let ghost rest = x@.skip(off as int);
        let cb = ctr_block(nonce, c);
        let ks = encrypt_rk(rk, Ghost(key), cb.as_slice());
        let n: usize = if x.len() - off >= 16 {
            16
        } else {
            x.len() - off
        };
        let ghost o = out@;
        let mut j: usize = 0;
        while j < n
            invariant
                n <= 16,
                off + n <= x.len(),
                j <= n,
                out@.len() == o.len() + j,
                forall|k: int| 0 <= k < o.len() ==> #[trigger] out@[k] == o[k],
                forall|k: int| 0 <= k < j ==> out@[o.len() + k] == x@[off + k] ^ ks@[k],
            decreases n - j,
        {
            out.push(x[off + j] ^ ks[j]);
            j += 1;
        }
        proof {
            let xb = xor_bytes(rest.subrange(0, n as int), ks@.subrange(0, n as int));
            assert(out@ =~= o + xb);
            assert(rest.subrange(n as int, rest.len() as int) =~= x@.skip(off + n));
            lemma_inc32(nonce@, c);
            // SP 800-38D §6.5 steps 5-7: one block of GCTR.
            assert(gctr(key, icb, rest) == xb + gctr(key, inc32(icb), x@.skip(off + n)));
            assert(o + (xb + gctr(key, inc32(icb), x@.skip(off + n))) =~= out@ + gctr(
                key,
                inc32(icb),
                x@.skip(off + n),
            ));
        }
        c = c.wrapping_add(1);
        off += n;
    }
    assert(out@ + gctr(key, nonce@ + i2osp(c as nat, 4), x@.skip(off as int)) =~= out@);
}

// SP 800-38D §7.1 step 4: a zero-padded string is a whole number of blocks.
proof fn lemma_pad16(d: Seq<u8>)
    ensures
        (d + zero_pad16(d)).len() % 16 == 0,
{
    let l = d.len() as int;
    lemma_fundamental_div_mod(l, 16);
    lemma_mod_pos_bound(l, 16);
    if l % 16 == 0 {
        lemma_mod_multiples_basic(l / 16, 16);
    } else {
        lemma_mod_multiples_basic(l / 16 + 1, 16);
    }
}

// SP 800-38D §7.1 steps 1, 2, 5, 6: the tag GCTR_K(J0, GHASH_H(A || 0^v || C || 0^u || lengths)).
fn gcm_tag_exec(
    rk: &[u8; 176],
    Ghost(key): Ghost<Seq<u8>>,
    nonce: &[u8],
    aad: &[u8],
    c: &[u8],
) -> (t: [u8; 16])
    requires
        rk_ok(rk@, key),
        nonce@.len() == 12,
        aad@.len() <= MAX_INPUT_LEN,
        c@.len() <= GCM_MAX_PT_LEN,
    ensures
        t@ == gcm_tag(key, nonce@, aad@, c@),
{
    hide(spec_aes128_encrypt);
    hide(gf128_mul);
    hide(key_word);
    // SP 800-38D §7.1 step 1: H = CIPH_K(0^128).
    let zero = [0u8; 16];
    assert(zero@ =~= Seq::new(16, |i: int| 0u8));
    let hb = encrypt_rk(rk, Ghost(key), zero.as_slice());
    let h = load_be128(hb.as_slice(), 0);
    assert(hb@.subrange(0, 16) =~= hb@);
    let ghost pa = aad@ + zero_pad16(aad@);
    let ghost pc = c@ + zero_pad16(c@);
    let ghost ls = i2osp(8 * aad@.len(), 8) + i2osp(8 * c@.len(), 8);
    let ghost s = aad@ + zero_pad16(aad@) + c@ + zero_pad16(c@) + i2osp(8 * aad@.len(), 8) + i2osp(
        8 * c@.len(),
        8,
    );
    proof {
        lemma_i2osp_len(8 * aad@.len(), 8);
        lemma_i2osp_len(8 * c@.len(), 8);
        lemma_pad16(aad@);
        assert(s =~= pa + pc + ls);
        assert(s.subrange(0, pa.len() as int) =~= pa);
        assert(s.subrange(pa.len() as int, (pa.len() + pc.len()) as int) =~= pc);
        assert(s.subrange((pa.len() + pc.len()) as int, s.len() as int) =~= ls);
        assert(s.take(0).len() == 0);
    }
    // SP 800-38D §7.1 step 5: GHASH over A || 0^v, then C || 0^u.
    let y = ghash_padded(0, h, aad, Ghost(s), Ghost(0));
    let y = ghash_padded(y, h, c, Ghost(s), Ghost(pa.len() as int));
    // SP 800-38D §7.1 step 5: the last block, [len(A)]_64 || [len(C)]_64 in bits.
    let la: u64 = 8 * (aad.len() as u64);
    let lc: u64 = 8 * (c.len() as u64);
    let mut lb = [0u8; 16];
    lb[0] = (la >> 56) as u8;
    lb[1] = (la >> 48) as u8;
    lb[2] = (la >> 40) as u8;
    lb[3] = (la >> 32) as u8;
    lb[4] = (la >> 24) as u8;
    lb[5] = (la >> 16) as u8;
    lb[6] = (la >> 8) as u8;
    lb[7] = la as u8;
    lb[8] = (lc >> 56) as u8;
    lb[9] = (lc >> 48) as u8;
    lb[10] = (lc >> 40) as u8;
    lb[11] = (lc >> 32) as u8;
    lb[12] = (lc >> 24) as u8;
    lb[13] = (lc >> 16) as u8;
    lb[14] = (lc >> 8) as u8;
    lb[15] = lc as u8;
    proof {
        crate::sha256::lemma_i2osp_be8(la);
        crate::sha256::lemma_i2osp_be8(lc);
        assert(lb@ =~= ls);
    }
    let lbv = load_be128(lb.as_slice(), 0);
    proof {
        let n = (pa.len() + pc.len()) as int;
        assert(lb@.subrange(0, 16) =~= lb@);
        assert(s.take(s.len() as int) =~= s);
        assert(s.subrange(0, n) =~= s.take(n));
        // SP 800-38D §6.4 step 4: the length block of GHASH.
        assert(ghash(h, s) == gf128_mul(ghash(h, s.take(n)) ^ (os2ip(ls) as u128), h));
    }
    let y = gf128_mul_exec(y ^ lbv, h);
    // SP 800-38D §7.1 step 6: T = GCTR_K(J0, S), one full block.
    let cb = ctr_block(nonce, 1);
    let ks = encrypt_rk(rk, Ghost(key), cb.as_slice());
    let yb = store_be128(y);
    let mut t = [0u8; 16];
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            forall|k: int| 0 <= k < i ==> #[trigger] t@[k] == yb@[k] ^ ks@[k],
        decreases 16 - i,
    {
        t[i] = yb[i] ^ ks[i];
        i += 1;
    }
    proof {
        let x = i2osp(y as nat, 16);
        lemma_j0(nonce@);
        lemma_i2osp_len(y as nat, 16);
        assert(x.subrange(16, 16) =~= Seq::<u8>::empty());
        assert(gctr(key, inc32(gcm_j0(nonce@)), Seq::<u8>::empty()) == Seq::<u8>::empty());
        // SP 800-38D §6.5: GCTR on one full block.
        assert(gctr(key, gcm_j0(nonce@), x) == xor_bytes(
            x.subrange(0, 16),
            spec_aes128_encrypt(key, gcm_j0(nonce@)).subrange(0, 16),
        ) + gctr(key, inc32(gcm_j0(nonce@)), x.subrange(16, 16)));
        assert(t@ =~= gctr(key, gcm_j0(nonce@), x));
    }
    t
}

// The tag compare: one masked step, so diff stays 0 exactly while the bytes match.
proof fn bv_ctacc(acc: u8, a: u8, b: u8) by (bit_vector)
    ensures
        ((acc | (a ^ b)) == 0) == (acc == 0 && a == b),
{
}

/// SP 800-38D §7.1 (96-bit IV, 128-bit tag); verified against spec_gcm_seal.
pub fn aes128_gcm_seal(key: &[u8], nonce: &[u8], aad: &[u8], pt: &[u8]) -> (r: Vec<u8>)
    requires
        key@.len() == 16,
        nonce@.len() == 12,
        aad@.len() <= MAX_INPUT_LEN,
        pt@.len() <= GCM_MAX_PT_LEN,
    ensures
        r@ == spec_gcm_seal(key@, nonce@, aad@, pt@),
{
    hide(spec_aes128_encrypt);
    hide(gf128_mul);
    hide(key_word);
    let rk = expand_key(key);
    let mut out: Vec<u8> = Vec::with_capacity(pt.len() + 16);
    // SP 800-38D §7.1 step 3: C = GCTR_K(inc32(J0), P), inc32(J0) = nonce || [2]_32.
    proof {
        lemma_j0(nonce@);
    }
    gctr_append(&rk, Ghost(key@), nonce, 2, pt, &mut out);
    assert(out@ =~= gctr(key@, inc32(gcm_j0(nonce@)), pt@));
    proof {
        lemma_gctr_len(key@, inc32(gcm_j0(nonce@)), pt@);
    }
    // SP 800-38D §7.1 steps 4-7: the tag over A and C; the output is C || T.
    let t = gcm_tag_exec(&rk, Ghost(key@), nonce, aad, out.as_slice());
    out.extend_from_slice(t.as_slice());
    out
}

/// SP 800-38D §7.2; verified against spec_gcm_open. The tag is checked before any plaintext is produced.
pub fn aes128_gcm_open(key: &[u8], nonce: &[u8], aad: &[u8], ct: &[u8]) -> (r: Option<Vec<u8>>)
    requires
        key@.len() == 16,
        nonce@.len() == 12,
        aad@.len() <= MAX_INPUT_LEN,
        ct@.len() <= GCM_MAX_PT_LEN + 16,
    ensures
        r.deep_view() == spec_gcm_open(key@, nonce@, aad@, ct@),
{
    hide(spec_aes128_encrypt);
    hide(gf128_mul);
    hide(key_word);
    if ct.len() < 16 {
        return None;
    }
    let rk = expand_key(key);
    let n = ct.len() - 16;
    let c = vstd::slice::slice_subrange(ct, 0, n);
    // SP 800-38D §7.2 steps 2, 3, 5-7: T' over A and C.
    let t = gcm_tag_exec(&rk, Ghost(key@), nonce, aad, c);
    assert(t@ == gcm_tag(key@, nonce@, aad@, ct@.subrange(0, ct.len() - 16)));
    // SP 800-38D §7.2 step 8: compare T with T', all 16 bytes, no early exit.
    let mut diff: u8 = 0;
    let mut i: usize = 0;
    while i < 16
        invariant
            n + 16 == ct.len(),
            i <= 16,
            (diff == 0) == (ct@.subrange(n as int, n + i) =~= t@.take(i as int)),
        decreases 16 - i,
    {
        proof {
            bv_ctacc(diff, ct@[n + i], t@[i as int]);
            let s0 = ct@.subrange(n as int, n + i);
            let t0 = t@.take(i as int);
            let s1 = ct@.subrange(n as int, n + i + 1);
            let t1 = t@.take(i + 1);
            assert(s1 =~= s0.push(ct@[n + i]));
            assert(t1 =~= t0.push(t@[i as int]));
            if s1 =~= t1 {
                assert(s1.drop_last() =~= t1.drop_last());
                assert(s1[i as int] == t1[i as int]);
            }
        }
        diff = diff | (ct[n + i] ^ t[i]);
        i += 1;
    }
    assert(t@.take(16) =~= t@);
    assert((diff == 0) == (ct@.subrange(ct.len() - 16, ct.len() as int) == t@));
    // ponytail: the only branch on tag bytes; it reveals only accept/reject, which the caller
    // learns anyway
    if diff != 0 {
        return None;
    }
    // SP 800-38D §7.2 step 4: P = GCTR_K(inc32(J0), C), only after the tag matched.
    let mut out: Vec<u8> = Vec::with_capacity(c.len());
    proof {
        lemma_j0(nonce@);
    }
    gctr_append(&rk, Ghost(key@), nonce, 2, c, &mut out);
    assert(out@ =~= gctr(key@, inc32(gcm_j0(nonce@)), c@));
    Some(out)
}

} // verus!

#[cfg(test)]
mod tests {
    // GCM spec test case 2 (K = 0^128, P = 0^128): H, C and GHASH_H(A = {}, C).
    #[test]
    fn ghash_tc2() {
        let h = 0x66e94bd4ef8a2c3b884cfa59ca342b2eu128;
        assert_eq!(crate::aes::aes128_encrypt_block(&[0; 16], &[0; 16]), h.to_be_bytes());
        let c = 0x0388dace60b6a392f328c2b971b2fe78u128;
        let y = super::gf128_mul_exec(c, h);
        // the length block: len(A) = 0, len(C) = 128 bits
        assert_eq!(super::gf128_mul_exec(y ^ 128, h), 0xf38cbb1ad69223dcc3457ae5b6b0f885u128);
    }
}
