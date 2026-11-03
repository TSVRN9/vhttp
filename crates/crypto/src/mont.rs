//! Generic 4 x 64-bit Montgomery arithmetic (CIOS) for any odd modulus m < 2^256, shared by
//! GF(p) and the scalars mod n; limbs are little-endian and saturated.
#[allow(unused_imports)]
use crate::bytes::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;

verus! {

// Value of 4 little-endian limbs (weights are script-generated powers of 2^64).
pub(crate) open spec fn v4(l: [u64; 4]) -> int {
    l[0] as int + l[1] as int * 0x1_0000_0000_0000_0000 + l[2] as int * 0x1_0000_0000_0000_0000_0000_0000_0000_0000 + l[3] as int * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
}

// Value of the 5-limb CIOS accumulator.
pub(crate) open spec fn v5(l: [u64; 5]) -> int {
    l[0] as int + l[1] as int * 0x1_0000_0000_0000_0000 + l[2] as int * 0x1_0000_0000_0000_0000_0000_0000_0000_0000 + l[3] as int * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
        + l[4] as int * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
}

// Guard for the hand-placed weight literals: each is the previous one times 2^64.
pub(crate) proof fn lemma_weights()
    ensures
        0x1_0000_0000_0000_0000int == 0x1_0000_0000 * 0x1_0000_0000,
        0x1_0000_0000_0000_0000_0000_0000_0000_0000int == 0x1_0000_0000_0000_0000int * 0x1_0000_0000_0000_0000int,
        0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int == 0x1_0000_0000_0000_0000_0000_0000_0000_0000int * 0x1_0000_0000_0000_0000int,
        0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int * 0x1_0000_0000_0000_0000int,
        0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int * 0x1_0000_0000_0000_0000int,
{
}

// 4 limbs hold a value in [0, 2^256).
pub(crate) proof fn lemma_v4_bound(l: [u64; 4])
    ensures
        0 <= v4(l) < 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000,
{
}

// a * b + c + d fits in a u128 for 64-bit operands.
pub(crate) proof fn lemma_mac_bound(a: int, b: int, c: int, d: int)
    requires
        0 <= a < 0x1_0000_0000_0000_0000,
        0 <= b < 0x1_0000_0000_0000_0000,
        0 <= c < 0x1_0000_0000_0000_0000,
        0 <= d < 0x1_0000_0000_0000_0000,
    ensures
        0 <= a * b,
        a * b + c + d <= 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff,
{
    lemma_mul_upper_bound(a, 0xffff_ffff_ffff_ffff, b, 0xffff_ffff_ffff_ffff);
    lemma_mul_nonnegative(a, b);
}

// Splitting a u128 by cast and shift is its % and / by 2^64 (no exec division on secrets).
pub(crate) proof fn bv_split128(x: u128) by (bit_vector)
    ensures
        (x as u64) as u128 == x % 0x1_0000_0000_0000_0000u128,
        ((x >> 64u128) as u64) as u128 == x / 0x1_0000_0000_0000_0000u128,
{
}

// a * b + c + d as (low, high) limbs.
#[cfg_attr(ct_check, ct::secret(a, b, c, d))]
pub(crate) fn mac(a: u64, b: u64, c: u64, d: u64) -> (r: (u64, u64))
    ensures
        r.0 as int + r.1 as int * 0x1_0000_0000_0000_0000 == a as int * b as int + c as int + d as int,
{
    proof {
        lemma_mac_bound(a as int, b as int, c as int, d as int);
    }
    let x: u128 = (a as u128) * (b as u128) + (c as u128) + (d as u128);
    proof {
        bv_split128(x);
    }
    (x as u64, (x >> 64u128) as u64)
}

// a * v4(b) as a sum of limb products (each product an atom for the chain lemmas).
proof fn lemma_mul4(a: int, b: [u64; 4])
    ensures
        a * v4(b) == a * b[0] + (a * b[1]) * 0x1_0000_0000_0000_0000 + (a * b[2]) * 0x1_0000_0000_0000_0000_0000_0000_0000_0000 + (a * b[3]) * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000,
{
    broadcast use group_mul_properties;
}

// The CIOS quotient digit q = s0 * mp mod 2^64 clears the low limb.
pub(crate) proof fn lemma_q_zero(s0: int, mp: int, m0: int)
    requires
        0 <= s0,
        0 <= mp,
        0 <= m0,
        (m0 * mp + 1) % 0x1_0000_0000_0000_0000 == 0,
    ensures
        (s0 + ((s0 * mp) % 0x1_0000_0000_0000_0000) * m0) % 0x1_0000_0000_0000_0000 == 0,
{
    let w = 0x1_0000_0000_0000_0000int;
    let q = (s0 * mp) % w;
    lemma_mul_mod_noop_left(s0 * mp, m0, w);
    lemma_add_mod_noop(s0, q * m0, w);
    lemma_add_mod_noop(s0, s0 * mp * m0, w);
    lemma_mod_twice(q * m0, w);
    assert(s0 + s0 * mp * m0 == s0 * (m0 * mp + 1)) by (nonlinear_arith);
    lemma_mul_mod_noop_right(s0, m0 * mp + 1, w);
    lemma_mul_basics(s0);
    lemma_small_mod(0, w as nat);
}

// Linear carry-chain bookkeeping: the products p_j are atoms, so this is linear arithmetic.
proof fn lemma_chain4(
    p0: int,
    p1: int,
    p2: int,
    p3: int,
    t0: int,
    t1: int,
    t2: int,
    t3: int,
    t4: int,
    s0: int,
    s1: int,
    s2: int,
    s3: int,
    s4: int,
    s5: int,
    c0: int,
    c1: int,
    c2: int,
    c3: int,
)
    requires
        s0 + c0 * 0x1_0000_0000_0000_0000 == p0 + t0,
        s1 + c1 * 0x1_0000_0000_0000_0000 == p1 + t1 + c0,
        s2 + c2 * 0x1_0000_0000_0000_0000 == p2 + t2 + c1,
        s3 + c3 * 0x1_0000_0000_0000_0000 == p3 + t3 + c2,
        s4 + s5 * 0x1_0000_0000_0000_0000 == t4 + c3,
    ensures
        s0 + s1 * 0x1_0000_0000_0000_0000 + s2 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000 + s3 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 + s4 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 + s5 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 == p0 + p1 * 0x1_0000_0000_0000_0000 + p2
            * 0x1_0000_0000_0000_0000_0000_0000_0000_0000 + p3 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 + t0 + t1 * 0x1_0000_0000_0000_0000 + t2 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000 + t3 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 + t4 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000,
{
    let w = 0x1_0000_0000_0000_0000int;
    assert(w * (s1 + c1 * w) == w * (p1 + t1 + c0));
    assert(w * w * (s2 + c2 * w) == w * w * (p2 + t2 + c1));
    assert(w * w * w * (s3 + c3 * w) == w * w * w * (p3 + t3 + c2));
    assert(w * w * w * w * (s4 + s5 * w) == w * w * w * w * (t4 + c3));
    assert(w * w == 0x1_0000_0000_0000_0000_0000_0000_0000_0000);
    assert(w * w * w == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000);
    assert(w * w * w * w == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000);
    assert(w * w * w * w * w == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000);
}

// One CIOS row: r * 2^64 == t + ai * B + q * M, with r < 2M.
#[cfg_attr(ct_check, ct::secret(t, ai, b), ct::public(m, mp))]
// `z` is read only by proof code, which a plain `cargo build` erases.
#[allow(unused_variables)]
#[verifier::spinoff_prover]
fn mont_step(t: [u64; 5], ai: u64, b: [u64; 4], m: [u64; 4], mp: u64) -> (r: (
    [u64; 5],
    Ghost<int>,
))
    requires
        (m[0] as int * mp as int + 1) % 0x1_0000_0000_0000_0000 == 0,
        v4(b) < v4(m),
        v5(t) < 2 * v4(m),
    ensures
        v5(r.0) * 0x1_0000_0000_0000_0000 == v5(t) + ai as int * v4(b) + r.1@ * v4(m),
        0 <= r.1@ < 0x1_0000_0000_0000_0000,
        v5(r.0) < 2 * v4(m),
{
    let (s0, c0) = mac(ai, b[0], t[0], 0);
    let (s1, c1) = mac(ai, b[1], t[1], c0);
    let (s2, c2) = mac(ai, b[2], t[2], c1);
    let (s3, c3) = mac(ai, b[3], t[3], c2);
    let x: u128 = t[4] as u128 + c3 as u128;
    let s4 = x as u64;
    let s5 = (x >> 64u128) as u64;
    proof {
        bv_split128(x);
        lemma_fundamental_div_mod(x as int, 0x1_0000_0000_0000_0000int);
        lemma_mul4(ai as int, b);
    }
    proof {
        lemma_chain4(
            ai as int * b[0] as int,
            ai as int * b[1] as int,
            ai as int * b[2] as int,
            ai as int * b[3] as int,
            t[0] as int,
            t[1] as int,
            t[2] as int,
            t[3] as int,
            t[4] as int,
            s0 as int,
            s1 as int,
            s2 as int,
            s3 as int,
            s4 as int,
            s5 as int,
            c0 as int,
            c1 as int,
            c2 as int,
            c3 as int,
        );
    }
    proof {
        lemma_mac_bound(s0 as int, mp as int, 0, 0);
    }
    let pr: u128 = s0 as u128 * mp as u128;
    proof {
        bv_split128(pr);
    }
    let q: u64 = pr as u64;
    let (z, d0) = mac(q, m[0], s0, 0);
    proof {
        lemma_q_zero(s0 as int, mp as int, m[0] as int);
    }
    proof {
        lemma_mod_multiples_vanish(d0 as int, z as int, 0x1_0000_0000_0000_0000int);
        lemma_small_mod(z as nat, 0x1_0000_0000_0000_0000nat);
    }
    assert(z == 0);
    let (u0, d1) = mac(q, m[1], s1, d0);
    let (u1, d2) = mac(q, m[2], s2, d1);
    let (u2, d3) = mac(q, m[3], s3, d2);
    let y: u128 = s4 as u128 + d3 as u128;
    let u3 = y as u64;
    let y5 = (y >> 64u128) as u64;
    proof {
        bv_split128(y);
        lemma_fundamental_div_mod(y as int, 0x1_0000_0000_0000_0000int);
        lemma_mul4(q as int, m);
        lemma_chain4(
            q as int * m[0] as int,
            q as int * m[1] as int,
            q as int * m[2] as int,
            q as int * m[3] as int,
            s0 as int,
            s1 as int,
            s2 as int,
            s3 as int,
            s4 as int,
            z as int,
            u0 as int,
            u1 as int,
            u2 as int,
            u3 as int,
            y5 as int,
            d0 as int,
            d1 as int,
            d2 as int,
            d3 as int,
        );
        lemma_mul_upper_bound(ai as int, 0xffff_ffff_ffff_ffff, v4(b), v4(m));
        lemma_mul_upper_bound(q as int, 0xffff_ffff_ffff_ffff, v4(m), v4(m));
        lemma_mul_nonnegative(ai as int, v4(b));
        lemma_mul_nonnegative(q as int, v4(m));
    }
    let ghost total = v5(t) + ai as int * v4(b) + q as int * v4(m);
    assert(total < 2 * v4(m) * 0x1_0000_0000_0000_0000);
    assert(s5 as int + y5 as int <= 1);
    let u4: u64 = s5 + y5;
    let r = [u0, u1, u2, u3, u4];
    assert(v5(r) * 0x1_0000_0000_0000_0000 == total);
    (r, Ghost(q as int))
}

// Masked select: b == 1 picks x, b == 0 picks y.
pub(crate) proof fn bv_sel(x: u64, y: u64, b: u64) by (bit_vector)
    requires
        b <= 1,
    ensures
        ((x & (0u64.wrapping_sub(b))) | (y & !(0u64.wrapping_sub(b)))) == (if b == 1 {
            x
        } else {
            y
        }),
{
}

// a - b - bin as (low limb, borrow).
#[cfg_attr(ct_check, ct::secret(a, b, bin))]
pub(crate) fn sbb(a: u64, b: u64, bin: u64) -> (r: (u64, u64))
    requires
        bin <= 1,
    ensures
        r.1 <= 1,
        r.0 as int - r.1 as int * 0x1_0000_0000_0000_0000 == a as int - b as int - bin as int,
{
    let x: u128 = (a as u128) + 0x1_0000_0000_0000_0000u128 - (b as u128) - (bin as u128);
    proof {
        bv_split128(x);
        lemma_fundamental_div_mod(x as int, 0x1_0000_0000_0000_0000int);
    }
    let hi = (x >> 64u128) as u64;
    (x as u64, 1 - hi)
}

// Row accumulation: t4 * 2^256 == sum of the row products.
proof fn lemma_acc4(
    ab0: int,
    ab1: int,
    ab2: int,
    ab3: int,
    qm0: int,
    qm1: int,
    qm2: int,
    qm3: int,
    t1: int,
    t2: int,
    t3: int,
    t4: int,
)
    requires
        t1 * 0x1_0000_0000_0000_0000 == ab0 + qm0,
        t2 * 0x1_0000_0000_0000_0000 == t1 + ab1 + qm1,
        t3 * 0x1_0000_0000_0000_0000 == t2 + ab2 + qm2,
        t4 * 0x1_0000_0000_0000_0000 == t3 + ab3 + qm3,
    ensures
        t4 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 == (ab0 + ab1 * 0x1_0000_0000_0000_0000 + ab2 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000 + ab3 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000) + (qm0 + qm1 * 0x1_0000_0000_0000_0000 + qm2
            * 0x1_0000_0000_0000_0000_0000_0000_0000_0000 + qm3 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000),
{
    let w = 0x1_0000_0000_0000_0000int;
    assert(w * w * w * (t4 * w) == w * w * w * (t3 + ab3 + qm3));
    assert(w * w * (t3 * w) == w * w * (t2 + ab2 + qm2));
    assert(w * (t2 * w) == w * (t1 + ab1 + qm1));
    assert(w * w == 0x1_0000_0000_0000_0000_0000_0000_0000_0000);
    assert(w * w * w == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000);
    assert(w * w * w * w == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000);
}

// x times a 4-limb linear form, distributed limb by limb.
proof fn lemma_distr4(x: int, a0: int, a1: int, a2: int, a3: int)
    ensures
        x * (a0 + a1 * 0x1_0000_0000_0000_0000 + a2 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000 + a3 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000) == a0 * x + (a1 * x) * 0x1_0000_0000_0000_0000 + (a2 * x)
            * 0x1_0000_0000_0000_0000_0000_0000_0000_0000 + (a3 * x) * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000,
{
    broadcast use group_mul_properties;
}

// The final conditional subtract keeps r * 2^256 == a * b (mod m).
proof fn lemma_mont_final(t: int, ab: int, q: int, m: int, r: int)
    requires
        m > 0,
        t * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 == ab + q * m,
        r == t || r == t - m,
    ensures
        (r * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000) % m == ab % m,
{
    if r == t {
        lemma_mod_multiples_vanish(q, ab, m);
        lemma_mul_is_commutative(q, m);
    } else {
        assert(r * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 == ab + (q - 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000) * m) by {
            broadcast use group_mul_properties;
        }
        lemma_mod_multiples_vanish(q - 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000, ab, m);
        lemma_mul_is_commutative(q - 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000, m);
    }
}

// Linear borrow-chain bookkeeping for a 5-limb minus 4-limb subtract.
proof fn lemma_sub_chain(
    t0: int,
    t1: int,
    t2: int,
    t3: int,
    t4: int,
    m0: int,
    m1: int,
    m2: int,
    m3: int,
    d0: int,
    d1: int,
    d2: int,
    d3: int,
    d4: int,
    e0: int,
    e1: int,
    e2: int,
    e3: int,
    e4: int,
)
    requires
        d0 - e0 * 0x1_0000_0000_0000_0000 == t0 - m0,
        d1 - e1 * 0x1_0000_0000_0000_0000 == t1 - m1 - e0,
        d2 - e2 * 0x1_0000_0000_0000_0000 == t2 - m2 - e1,
        d3 - e3 * 0x1_0000_0000_0000_0000 == t3 - m3 - e2,
        d4 - e4 * 0x1_0000_0000_0000_0000 == t4 - e3,
    ensures
        d0 + d1 * 0x1_0000_0000_0000_0000 + d2 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000 + d3 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 + d4 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 - e4 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 == (t0 + t1 * 0x1_0000_0000_0000_0000 + t2
            * 0x1_0000_0000_0000_0000_0000_0000_0000_0000 + t3 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 + t4 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000) - (m0 + m1 * 0x1_0000_0000_0000_0000 + m2 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000 + m3 * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000),
{
    let w = 0x1_0000_0000_0000_0000int;
    assert(w * (d1 - e1 * w) == w * (t1 - m1 - e0));
    assert(w * w * (d2 - e2 * w) == w * w * (t2 - m2 - e1));
    assert(w * w * w * (d3 - e3 * w) == w * w * w * (t3 - m3 - e2));
    assert(w * w * w * w * (d4 - e4 * w) == w * w * w * w * (t4 - e3));
    assert(w * w == 0x1_0000_0000_0000_0000_0000_0000_0000_0000);
    assert(w * w * w == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000);
    assert(w * w * w * w == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000);
    assert(w * w * w * w * w == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000);
}

// Montgomery product: r < m and r * 2^256 == a * b (mod m).
#[cfg_attr(ct_check, ct::secret(a, b), ct::public(m, mp))]
// The row quotients and `d4` are read only by proof code, which a plain `cargo build` erases.
#[allow(unused_variables)]
#[verifier::spinoff_prover]
pub(crate) fn mont_mul(a: &[u64; 4], b: &[u64; 4], m: &[u64; 4], mp: u64) -> (r: [u64; 4])
    requires
        (m[0] as int * mp as int + 1) % 0x1_0000_0000_0000_0000 == 0,
        v4(*b) < v4(*m),
    ensures
        v4(r) < v4(*m),
        (v4(r) * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000) % v4(*m) == (v4(*a) * v4(*b)) % v4(*m),
{
    let (t1, q0) = mont_step([0u64; 5], a[0], *b, *m, mp);
    let (t2, q1) = mont_step(t1, a[1], *b, *m, mp);
    let (t3, q2) = mont_step(t2, a[2], *b, *m, mp);
    let (t, q3) = mont_step(t3, a[3], *b, *m, mp);
    let ghost qq = q0@ + q1@ * 0x1_0000_0000_0000_0000 + q2@ * 0x1_0000_0000_0000_0000_0000_0000_0000_0000 + q3@ * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;
    proof {
        lemma_acc4(
            a[0] as int * v4(*b),
            a[1] as int * v4(*b),
            a[2] as int * v4(*b),
            a[3] as int * v4(*b),
            q0@ * v4(*m),
            q1@ * v4(*m),
            q2@ * v4(*m),
            q3@ * v4(*m),
            v5(t1),
            v5(t2),
            v5(t3),
            v5(t),
        );
        lemma_distr4(v4(*b), a[0] as int, a[1] as int, a[2] as int, a[3] as int);
        lemma_distr4(v4(*m), q0@, q1@, q2@, q3@);
        lemma_mul_is_commutative(v4(*a), v4(*b));
        lemma_mul_is_commutative(qq, v4(*m));
    }
    assert(v5(t) * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 == v4(*a) * v4(*b) + qq * v4(*m));
    let (d0, e0) = sbb(t[0], m[0], 0);
    let (d1, e1) = sbb(t[1], m[1], e0);
    let (d2, e2) = sbb(t[2], m[2], e1);
    let (d3, e3) = sbb(t[3], m[3], e2);
    let (d4, e4) = sbb(t[4], 0, e3);
    proof {
        lemma_sub_chain(
            t[0] as int,
            t[1] as int,
            t[2] as int,
            t[3] as int,
            t[4] as int,
            m[0] as int,
            m[1] as int,
            m[2] as int,
            m[3] as int,
            d0 as int,
            d1 as int,
            d2 as int,
            d3 as int,
            d4 as int,
            e0 as int,
            e1 as int,
            e2 as int,
            e3 as int,
            e4 as int,
        );
        bv_sel(t[0], d0, e4);
        bv_sel(t[1], d1, e4);
        bv_sel(t[2], d2, e4);
        bv_sel(t[3], d3, e4);
    }
    let mask = 0u64.wrapping_sub(e4);
    let r = [
        (t[0] & mask) | (d0 & !mask),
        (t[1] & mask) | (d1 & !mask),
        (t[2] & mask) | (d2 & !mask),
        (t[3] & mask) | (d3 & !mask),
    ];
    proof {
        if e4 == 1 {
            assert(v5(t) < v4(*m));
            assert(t[4] == 0);
            assert(v4(r) == v5(t));
        } else {
            assert(d4 == 0);
            assert(v4(r) == v5(t) - v4(*m));
        }
        lemma_mont_final(v5(t), v4(*a) * v4(*b), qq, v4(*m), v4(r));
    }
    r
}

// a + b + cin as (low limb, carry).
#[cfg_attr(ct_check, ct::secret(a, b, cin))]
fn adc(a: u64, b: u64, cin: u64) -> (r: (u64, u64))
    requires
        cin <= 1,
    ensures
        r.1 <= 1,
        r.0 as int + r.1 as int * 0x1_0000_0000_0000_0000 == a as int + b as int + cin as int,
{
    let x: u128 = (a as u128) + (b as u128) + (cin as u128);
    proof {
        bv_split128(x);
        lemma_fundamental_div_mod(x as int, 0x1_0000_0000_0000_0000int);
    }
    (x as u64, (x >> 64u128) as u64)
}

// 4-limb add with carry out.
#[cfg_attr(ct_check, ct::secret(a, b))]
fn add4(a: &[u64; 4], b: &[u64; 4]) -> (r: ([u64; 4], u64))
    ensures
        r.1 <= 1,
        v4(r.0) + r.1 as int * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 == v4(*a) + v4(*b),
{
    let (s0, c0) = adc(a[0], b[0], 0);
    let (s1, c1) = adc(a[1], b[1], c0);
    let (s2, c2) = adc(a[2], b[2], c1);
    let (s3, c3) = adc(a[3], b[3], c2);
    proof {
        lemma_chain4(
            a[0] as int,
            a[1] as int,
            a[2] as int,
            a[3] as int,
            b[0] as int,
            b[1] as int,
            b[2] as int,
            b[3] as int,
            0,
            s0 as int,
            s1 as int,
            s2 as int,
            s3 as int,
            c3 as int,
            0,
            c0 as int,
            c1 as int,
            c2 as int,
            c3 as int,
        );
    }
    ([s0, s1, s2, s3], c3)
}

// 4-limb subtract with borrow out: the shared constant-time compare and subtract.
#[cfg_attr(ct_check, ct::secret(a, b))]
pub(crate) fn sub4(a: &[u64; 4], b: &[u64; 4]) -> (r: ([u64; 4], u64))
    ensures
        r.1 <= 1,
        v4(r.0) - r.1 as int * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 == v4(*a) - v4(*b),
{
    let (d0, e0) = sbb(a[0], b[0], 0);
    let (d1, e1) = sbb(a[1], b[1], e0);
    let (d2, e2) = sbb(a[2], b[2], e1);
    let (d3, e3) = sbb(a[3], b[3], e2);
    proof {
        lemma_sub_chain(
            a[0] as int,
            a[1] as int,
            a[2] as int,
            a[3] as int,
            e3 as int,
            b[0] as int,
            b[1] as int,
            b[2] as int,
            b[3] as int,
            d0 as int,
            d1 as int,
            d2 as int,
            d3 as int,
            0,
            e0 as int,
            e1 as int,
            e2 as int,
            e3 as int,
            0,
        );
    }
    ([d0, d1, d2, d3], e3)
}

// Masked 4-limb select: b == 1 picks x, b == 0 picks y.
#[cfg_attr(ct_check, ct::secret(b, x, y))]
pub(crate) fn select4(b: u64, x: &[u64; 4], y: &[u64; 4]) -> (r: [u64; 4])
    requires
        b <= 1,
    ensures
        r == (if b == 1 {
            *x
        } else {
            *y
        }),
{
    let mask = 0u64.wrapping_sub(b);
    let r = [
        (x[0] & mask) | (y[0] & !mask),
        (x[1] & mask) | (y[1] & !mask),
        (x[2] & mask) | (y[2] & !mask),
        (x[3] & mask) | (y[3] & !mask),
    ];
    proof {
        bv_sel(x[0], y[0], b);
        bv_sel(x[1], y[1], b);
        bv_sel(x[2], y[2], b);
        bv_sel(x[3], y[3], b);
        if b == 1 {
            assert(r =~= *x);
        } else {
            assert(r =~= *y);
        }
    }
    r
}

// OR-accumulate then fold the sign bit: 1 iff all four words are zero.
proof fn bv_ct_zero(x0: u64, x1: u64, x2: u64, x3: u64) by (bit_vector)
    ensures
        ((((x0 | x1 | x2 | x3) | 0u64.wrapping_sub(x0 | x1 | x2 | x3)) >> 63u64) ^ 1u64) <= 1,
        (((((x0 | x1 | x2 | x3) | 0u64.wrapping_sub(x0 | x1 | x2 | x3)) >> 63u64) ^ 1u64) == 1)
            == (x0 == 0 && x1 == 0 && x2 == 0 && x3 == 0),
{
}

// XOR is zero exactly on equal words.
proof fn bv_xor_eq(x: u64, y: u64) by (bit_vector)
    ensures
        ((x ^ y) == 0) == (x == y),
{
}

// 1 iff v4(a) == 0, without branching.
#[cfg_attr(ct_check, ct::secret(a))]
pub(crate) fn is_zero4(a: &[u64; 4]) -> (r: u64)
    ensures
        r <= 1,
        (r == 1) == (v4(*a) == 0),
{
    let acc = a[0] | a[1] | a[2] | a[3];
    proof {
        bv_ct_zero(a[0], a[1], a[2], a[3]);
    }
    ((acc | 0u64.wrapping_sub(acc)) >> 63u64) ^ 1u64
}

// 1 iff a == b limb for limb, without branching.
#[cfg_attr(ct_check, ct::secret(a, b))]
pub(crate) fn eq4(a: &[u64; 4], b: &[u64; 4]) -> (r: u64)
    ensures
        r <= 1,
        (r == 1) == (*a == *b),
{
    let (x0, x1, x2, x3) = (a[0] ^ b[0], a[1] ^ b[1], a[2] ^ b[2], a[3] ^ b[3]);
    let acc = x0 | x1 | x2 | x3;
    proof {
        bv_ct_zero(x0, x1, x2, x3);
        bv_xor_eq(a[0], b[0]);
        bv_xor_eq(a[1], b[1]);
        bv_xor_eq(a[2], b[2]);
        bv_xor_eq(a[3], b[3]);
        if a[0] == b[0] && a[1] == b[1] && a[2] == b[2] && a[3] == b[3] {
            assert(*a =~= *b);
        }
    }
    ((acc | 0u64.wrapping_sub(acc)) >> 63u64) ^ 1u64
}

// (a + b) mod m for a, b < m: add, then a masked conditional subtract.
#[cfg_attr(ct_check, ct::secret(a, b), ct::public(m))]
pub(crate) fn add_mod(a: &[u64; 4], b: &[u64; 4], m: &[u64; 4]) -> (r: [u64; 4])
    requires
        v4(*a) < v4(*m),
        v4(*b) < v4(*m),
    ensures
        v4(r) == (v4(*a) + v4(*b)) % v4(*m),
{
    let (s, c) = add4(a, b);
    let (d, bo) = sub4(&s, m);
    // keep s iff the 5-limb sum (c, s) is below m: c == 0 and the subtract borrowed
    let (_, keep) = sbb(c, 0, bo);
    let r = select4(keep, &s, &d);
    proof {
        let t = v4(*a) + v4(*b);
        let mm = v4(*m);
        lemma_v4_bound(s);
        lemma_v4_bound(d);
        lemma_v4_bound(*m);
        if keep == 1 {
            lemma_fundamental_div_mod_converse_mod(t, mm, 0, t);
        } else {
            lemma_fundamental_div_mod_converse_mod(t, mm, 1, t - mm);
        }
    }
    r
}

// (a - b) mod m (Euclidean) for a, b < m: subtract, then a masked conditional add of m.
#[cfg_attr(ct_check, ct::secret(a, b), ct::public(m))]
pub(crate) fn sub_mod(a: &[u64; 4], b: &[u64; 4], m: &[u64; 4]) -> (r: [u64; 4])
    requires
        v4(*a) < v4(*m),
        v4(*b) < v4(*m),
    ensures
        v4(r) == (v4(*a) - v4(*b)) % v4(*m),
{
    let (d, bo) = sub4(a, b);
    let (e, _) = add4(&d, m);
    let r = select4(bo, &e, &d);
    proof {
        let t = v4(*a) - v4(*b);
        let mm = v4(*m);
        lemma_v4_bound(d);
        lemma_v4_bound(e);
        lemma_v4_bound(*m);
        if bo == 1 {
            lemma_fundamental_div_mod_converse_mod(t, mm, -1, t + mm);
        } else {
            lemma_fundamental_div_mod_converse_mod(t, mm, 0, t);
        }
    }
    r
}

// x % m and y % m may replace x and y under +.
pub(crate) proof fn lemma_mod_add_cong(x: int, y: int, m: int)
    requires
        m > 0,
    ensures
        ((x % m) + (y % m)) % m == (x + y) % m,
        ((x % m) + y) % m == (x + y) % m,
        (x + (y % m)) % m == (x + y) % m,
{
    lemma_add_mod_noop(x, y, m);
    lemma_add_mod_noop_right(x, y, m);
    lemma_add_mod_noop_right(y, x, m);
}

// x % m and y % m may replace x and y under -.
pub(crate) proof fn lemma_mod_sub_cong(x: int, y: int, m: int)
    requires
        m > 0,
    ensures
        ((x % m) - (y % m)) % m == (x - y) % m,
        ((x % m) - y) % m == (x - y) % m,
        (x - (y % m)) % m == (x - y) % m,
{
    lemma_sub_mod_noop(x, y, m);
    lemma_sub_mod_noop_right(x, y, m);
    lemma_sub_mod_noop(x % m, y, m);
    lemma_mod_twice(x, m);
}

// x % m and y % m may replace x and y under *.
pub(crate) proof fn lemma_mod_mul_cong(x: int, y: int, m: int)
    requires
        m > 0,
    ensures
        ((x % m) * (y % m)) % m == (x * y) % m,
        ((x % m) * y) % m == (x * y) % m,
        (x * (y % m)) % m == (x * y) % m,
{
    lemma_mul_mod_noop(x, y, m);
    lemma_mul_mod_noop_left(x, y, m);
    lemma_mul_mod_noop_right(x, y, m);
}

// Montgomery decode: v * R^-1 mod m, with ri standing for R^-1.
pub(crate) open spec fn mdec(v: int, m: int, ri: int) -> int {
    (v * ri) % m
}

// From mont_mul's ensures (r * rr == a * b mod m) and rr * ri == 1 mod m: decode commutes with *.
pub(crate) proof fn lemma_mdec_mul(r: int, a: int, b: int, m: int, rr: int, ri: int)
    requires
        m > 1,
        (rr * ri) % m == 1,
        (r * rr) % m == (a * b) % m,
    ensures
        mdec(r, m, ri) == (mdec(a, m, ri) * mdec(b, m, ri)) % m,
{
    // mdec(a) * mdec(b) == a*b*ri*ri == r*rr*ri*ri == r*ri (mod m)
    lemma_mul_mod_noop(a * ri, b * ri, m);
    assert((a * ri) * (b * ri) == (a * b) * (ri * ri)) by {
        broadcast use group_mul_properties;
    }
    lemma_mul_mod_noop_left(a * b, ri * ri, m);
    lemma_mul_mod_noop_left(r * rr, ri * ri, m);
    assert((r * rr) * (ri * ri) == (r * ri) * (rr * ri)) by {
        broadcast use group_mul_properties;
    }
    lemma_mul_mod_noop_right(r * ri, rr * ri, m);
    lemma_mul_basics(r * ri);
}

// Decode commutes with + mod m.
pub(crate) proof fn lemma_mdec_add(a: int, b: int, m: int, ri: int)
    requires
        m > 0,
    ensures
        mdec((a + b) % m, m, ri) == (mdec(a, m, ri) + mdec(b, m, ri)) % m,
{
    lemma_mul_mod_noop_left(a + b, ri, m);
    assert((a + b) * ri == a * ri + b * ri) by {
        broadcast use group_mul_properties;
    }
    lemma_add_mod_noop(a * ri, b * ri, m);
}

// Decode commutes with - mod m.
pub(crate) proof fn lemma_mdec_sub(a: int, b: int, m: int, ri: int)
    requires
        m > 0,
    ensures
        mdec((a - b) % m, m, ri) == (mdec(a, m, ri) - mdec(b, m, ri)) % m,
{
    lemma_mul_mod_noop_left(a - b, ri, m);
    assert((a - b) * ri == a * ri - b * ri) by {
        broadcast use group_mul_properties;
    }
    lemma_sub_mod_noop(a * ri, b * ri, m);
}

// Equal 4-limb values are equal limbs.
proof fn lemma_v4_inj(a: [u64; 4], b: [u64; 4])
    requires
        v4(a) == v4(b),
    ensures
        a == b,
{
    let w = 0x1_0000_0000_0000_0000int;
    let (a3, b3) = (a[3] as int, b[3] as int);
    let (a2, b2) = (a[2] as int + a3 * w, b[2] as int + b3 * w);
    let (a1, b1) = (a[1] as int + a2 * w, b[1] as int + b2 * w);
    assert(v4(a) == a1 * w + a[0] as int);
    assert(v4(b) == b1 * w + b[0] as int);
    lemma_fundamental_div_mod_converse(v4(a), w, a1, a[0] as int);
    lemma_fundamental_div_mod_converse(v4(b), w, b1, b[0] as int);
    lemma_fundamental_div_mod_converse(a1, w, a2, a[1] as int);
    lemma_fundamental_div_mod_converse(b1, w, b2, b[1] as int);
    lemma_fundamental_div_mod_converse(a2, w, a3, a[2] as int);
    lemma_fundamental_div_mod_converse(b2, w, b3, b[2] as int);
    assert(a =~= b);
}

// Canonical limbs (< m) with equal decodes are equal, since R is invertible mod m.
pub(crate) proof fn lemma_mdec_inj(a: [u64; 4], b: [u64; 4], m: int, ri: int)
    requires
        v4(a) < m,
        v4(b) < m,
        (0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 * ri) % m == 1,
        mdec(v4(a), m, ri) == mdec(v4(b), m, ri),
    ensures
        a == b,
{
    let (x, y, rr) = (v4(a), v4(b), 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int);
    lemma_v4_bound(a);
    lemma_v4_bound(b);
    // x == x * (ri * rr) == (x * ri) * rr (mod m), and likewise for y
    lemma_mul_mod_noop_left(x * ri, rr, m);
    lemma_mul_mod_noop_left(y * ri, rr, m);
    assert((x * ri) * rr == x * (rr * ri)) by {
        broadcast use group_mul_properties;
    }
    assert((y * ri) * rr == y * (rr * ri)) by {
        broadcast use group_mul_properties;
    }
    lemma_mul_mod_noop_right(x, rr * ri, m);
    lemma_mul_mod_noop_right(y, rr * ri, m);
    lemma_mul_basics(x);
    lemma_mul_basics(y);
    lemma_small_mod(x as nat, m as nat);
    lemma_small_mod(y as nat, m as nat);
    lemma_v4_inj(a, b);
}

// R mod m decodes to 1.
pub(crate) proof fn lemma_mdec_one(m: int, ri: int)
    requires
        m > 0,
        (0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 * ri) % m == 1,
    ensures
        mdec(0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int % m, m, ri) == 1,
{
    lemma_mul_mod_noop_left(0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int, ri, m);
}

// One square-and-multiply step on exponents: e -> 2e (square) and 2e -> 2e + 1 (multiply).
pub(crate) proof fn lemma_pow_step(x: int, e: nat, m: int)
    requires
        m > 0,
    ensures
        ((pow(x, e) % m) * (pow(x, e) % m)) % m == pow(x, 2 * e) % m,
        ((pow(x, 2 * e) % m) * x) % m == pow(x, 2 * e + 1) % m,
{
    lemma_pow_adds(x, e, e);
    lemma_mul_mod_noop(pow(x, e), pow(x, e), m);
    lemma_pow_adds(x, 2 * e, 1);
    lemma_pow1(x);
    lemma_mul_mod_noop_left(pow(x, 2 * e), x, m);
}

// Bit k (MSB first) of byte b extends the k-bit prefix b >> (8 - k): prefix' == 2 * prefix + bit.
pub(crate) proof fn bv_bit_u8(b: u8, k: u8) by (bit_vector)
    requires
        k < 8,
    ensures
        ((b >> ((7 - k) as u8)) & 1) <= 1,
        ((b as u32) >> ((7 - k) as u32)) == 2 * ((b as u32) >> ((8 - k) as u32)) + (((b >> ((7
            - k) as u8)) & 1) as u32),
        (b as u32) >> 8u32 == 0,
        (b as u32) >> 0u32 == b as u32,
{
}

// x^e in Montgomery form, by square-and-multiply over the public big-endian exponent e.
#[cfg_attr(ct_check, ct::secret(x), ct::public(e, m, mp, one))]
// ponytail: plain square-and-multiply over the public exponent, 256 squarings + popcount(e) multiplies (≈12 µs per fe_inv, release, Task 8 p256_speed median: 6.1 ms per scalar mult / 512 point ops of one inversion each); upgrade: a fixed addition chain (~115 fewer multiplies) with one exponent-arithmetic proof per step
pub(crate) fn mont_pow(
    x: &[u64; 4],
    e: &[u8; 32],
    m: &[u64; 4],
    mp: u64,
    one: &[u64; 4],
    Ghost(ri): Ghost<int>,
) -> (r: [u64; 4])
    requires
        (m[0] as int * mp as int + 1) % 0x1_0000_0000_0000_0000 == 0,
        (0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 * ri) % v4(*m) == 1,
        v4(*x) < v4(*m),
        v4(*one) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int % v4(*m),
    ensures
        v4(r) < v4(*m),
        mdec(v4(r), v4(*m), ri) == pow(mdec(v4(*x), v4(*m), ri), os2ip(e@)) % v4(*m),
{
    let ghost mm = v4(*m);
    let ghost xd = mdec(v4(*x), mm, ri);
    proof {
        lemma_v4_bound(*x);
        lemma_mdec_one(mm, ri);
        lemma_pow0(xd);
        lemma_small_mod(1, mm as nat);
        assert(e@.take(0) =~= Seq::<u8>::empty());
    }
    let mut r = *one;
    let mut j: usize = 0;
    while j < 32
        invariant
            j <= 32,
            (m[0] as int * mp as int + 1) % 0x1_0000_0000_0000_0000 == 0,
            mm == v4(*m),
            1 < mm,
            (0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 * ri) % mm == 1,
            v4(*x) < mm,
            xd == mdec(v4(*x), mm, ri),
            v4(r) < mm,
            mdec(v4(r), mm, ri) == pow(xd, os2ip(e@.take(j as int))) % mm,
        decreases 32 - j,
    {
        let byte = e[j];
        let ghost hi = os2ip(e@.take(j as int));
        let ghost mut ev: nat = hi;
        proof {
            bv_bit_u8(byte, 0);
            lemma2_to64();
        }
        let mut k: u8 = 0;
        while k < 8
            invariant
                k <= 8,
                (m[0] as int * mp as int + 1) % 0x1_0000_0000_0000_0000 == 0,
                mm == v4(*m),
                1 < mm,
                (0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 * ri) % mm == 1,
                v4(*x) < mm,
                xd == mdec(v4(*x), mm, ri),
                v4(r) < mm,
                ev == hi * pow2(k as nat) + ((byte as u32) >> ((8 - k) as u32)),
                mdec(v4(r), mm, ri) == pow(xd, ev) % mm,
            decreases 8 - k,
        {
            let ghost r0 = r;
            r = mont_mul(&r, &r, m, mp);
            proof {
                lemma_mdec_mul(v4(r), v4(r0), v4(r0), mm, 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int, ri);
                lemma_pow_step(xd, ev, mm);
                bv_bit_u8(byte, k);
                lemma_pow2_unfold((k + 1) as nat);
                assert(hi * pow2((k + 1) as nat) == 2 * (hi * pow2(k as nat))) by {
                    broadcast use group_mul_properties;
                }
            }
            let bit = (byte >> (7 - k)) & 1;
            // ct: branch on a bit of the public exponent
            if bit == 1 {
                let ghost r1 = r;
                r = mont_mul(&r, x, m, mp);
                proof {
                    lemma_mdec_mul(v4(r), v4(r1), v4(*x), mm, 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000int, ri);
                }
            }
            proof {
                ev = 2 * ev + bit as nat;
            }
            k = k + 1;
        }
        proof {
            let t = e@.take(j + 1);
            assert(t.drop_last() =~= e@.take(j as int));
            assert(t.last() == byte);
        }
        j = j + 1;
    }
    proof {
        assert(e@.take(32) =~= e@);
    }
    r
}

// 256^4 and 256^8 as literals.
proof fn lemma_pow256()
    ensures
        pow(256, 4) == 0x1_0000_0000,
        pow(256, 8) == 0x1_0000_0000_0000_0000,
{
    reveal_with_fuel(pow, 9);
}

// Eight bytes, big-endian, in one u64.
proof fn bv_be64(b0: u64, b1: u64, b2: u64, b3: u64, b4: u64, b5: u64, b6: u64, b7: u64) by (bit_vector)
    requires
        b0 < 256,
        b1 < 256,
        b2 < 256,
        b3 < 256,
        b4 < 256,
        b5 < 256,
        b6 < 256,
        b7 < 256,
    ensures
        (b0 << 56u64) | (b1 << 48u64) | (b2 << 40u64) | (b3 << 32u64) | (b4 << 24u64) | (b5
            << 16u64) | (b6 << 8u64) | b7 == b0 * 0x100_0000_0000_0000 + b1 * 0x1_0000_0000_0000
            + b2 * 0x100_0000_0000 + b3 * 0x1_0000_0000 + b4 * 0x100_0000 + b5 * 0x1_0000 + b6
            * 0x100 + b7,
{
}

// OS2IP of eight octets as a linear form.
proof fn lemma_os2ip_be8(s: Seq<u8>)
    requires
        s.len() == 8,
    ensures
        os2ip(s) == s[0] * 0x100_0000_0000_0000 + s[1] * 0x1_0000_0000_0000 + s[2]
            * 0x100_0000_0000 + s[3] * 0x1_0000_0000 + s[4] * 0x100_0000 + s[5] * 0x1_0000 + s[6]
            * 0x100 + s[7],
{
    let (a, b) = (s.subrange(0, 4), s.subrange(4, 8));
    assert(s =~= a + b);
    lemma_os2ip_append(a, b);
    crate::sha256::lemma_os2ip4(a);
    crate::sha256::lemma_os2ip4(b);
    lemma_pow256();
}

// The u64 whose big-endian bytes are b[off..off + 8].
#[cfg_attr(ct_check, ct::secret(b), ct::public(off))]
pub(crate) fn load_be64(b: &[u8], off: usize) -> (r: u64)
    requires
        off + 8 <= b@.len(),
    ensures
        r as int == os2ip(b@.subrange(off as int, off + 8)),
{
    let (b0, b1, b2, b3) = (b[off] as u64, b[off + 1] as u64, b[off + 2] as u64, b[off + 3] as u64);
    let (b4, b5, b6, b7) = (b[off + 4] as u64, b[off + 5] as u64, b[off + 6] as u64, b[off + 7] as u64);
    proof {
        bv_be64(b0, b1, b2, b3, b4, b5, b6, b7);
        lemma_os2ip_be8(b@.subrange(off as int, off + 8));
    }
    (b0 << 56u64) | (b1 << 48u64) | (b2 << 40u64) | (b3 << 32u64) | (b4 << 24u64) | (b5 << 16u64)
        | (b6 << 8u64) | b7
}

// Limbs of the big-endian 32-octet integer b[off..off + 32].
#[cfg_attr(ct_check, ct::secret(b), ct::public(off))]
pub(crate) fn limbs_from_be(b: &[u8], off: usize) -> (r: [u64; 4])
    requires
        off + 32 <= b@.len(),
    ensures
        v4(r) == os2ip(b@.subrange(off as int, off + 32)),
{
    proof {
        assert(b@.len() == b.len());
    }
    let r = [load_be64(b, off + 24), load_be64(b, off + 16), load_be64(b, off + 8), load_be64(b, off)];
    proof {
        let s = b@.subrange(off as int, off + 32);
        let (q0, q1, q2, q3) = (s.subrange(0, 8), s.subrange(8, 16), s.subrange(16, 24), s.subrange(24, 32));
        assert(q0 =~= b@.subrange(off as int, off + 8));
        assert(q1 =~= b@.subrange(off + 8, off + 16));
        assert(q2 =~= b@.subrange(off + 16, off + 24));
        assert(q3 =~= b@.subrange(off + 24, off + 32));
        assert(s =~= ((q0 + q1) + q2) + q3);
        lemma_os2ip_append(q0, q1);
        lemma_os2ip_append(q0 + q1, q2);
        lemma_os2ip_append((q0 + q1) + q2, q3);
        lemma_pow256();
    }
    r
}

// I2OSP(v4(l), 32): the limbs as 32 big-endian octets.
#[cfg_attr(ct_check, ct::secret(l))]
pub(crate) fn limbs_to_be(l: &[u64; 4]) -> (r: [u8; 32])
    ensures
        r@ == i2osp(v4(*l) as nat, 32),
{
    let (a, b, c, d) = (l[3], l[2], l[1], l[0]);
    let r = [
        (a >> 56) as u8, (a >> 48) as u8, (a >> 40) as u8, (a >> 32) as u8,
        (a >> 24) as u8, (a >> 16) as u8, (a >> 8) as u8, a as u8,
        (b >> 56) as u8, (b >> 48) as u8, (b >> 40) as u8, (b >> 32) as u8,
        (b >> 24) as u8, (b >> 16) as u8, (b >> 8) as u8, b as u8,
        (c >> 56) as u8, (c >> 48) as u8, (c >> 40) as u8, (c >> 32) as u8,
        (c >> 24) as u8, (c >> 16) as u8, (c >> 8) as u8, c as u8,
        (d >> 56) as u8, (d >> 48) as u8, (d >> 40) as u8, (d >> 32) as u8,
        (d >> 24) as u8, (d >> 16) as u8, (d >> 8) as u8, d as u8,
    ];
    proof {
        let w = 0x1_0000_0000_0000_0000int;
        let v2 = l[2] as int + l[3] as int * w;
        let v3 = l[1] as int + v2 * w;
        let v = v4(*l);
        assert(v == v3 * w + l[0] as int);
        lemma_pow256();
        lemma_fundamental_div_mod_converse(v, w, v3, l[0] as int);
        lemma_fundamental_div_mod_converse(v3, w, v2, l[1] as int);
        lemma_fundamental_div_mod_converse(v2, w, l[3] as int, l[2] as int);
        lemma_i2osp_append(v as nat, 24, 8);
        lemma_i2osp_append(v3 as nat, 16, 8);
        lemma_i2osp_append(v2 as nat, 8, 8);
        crate::sha256::lemma_i2osp_be8(a);
        crate::sha256::lemma_i2osp_be8(b);
        crate::sha256::lemma_i2osp_be8(c);
        crate::sha256::lemma_i2osp_be8(d);
        assert(r@ =~= i2osp(v as nat, 32));
    }
    r
}

} // verus!
