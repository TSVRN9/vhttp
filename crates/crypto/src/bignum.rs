//! Constant-time bignum over `[u64; 64]`: Montgomery multiply (CIOS), masked select, the inverse
//! of the modulus mod 2^64, powers of two mod m, and big-endian conversion.
#[allow(unused_imports)]
use crate::bytes::*;
#[allow(unused_imports)]
use crate::mont::*;
#[allow(unused_imports)]
use crate::sha256::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// Value of base 2^64 digit i.
pub(crate) open spec fn wp(i: nat) -> int { pow(0x1_0000_0000_0000_0000, i) }

pub(crate) proof fn lemma_wp(i: nat)
    ensures wp(0) == 1, wp(i) > 0, wp(i + 1) == wp(i) * 0x1_0000_0000_0000_0000,
{
    reveal(pow);
    lemma_pow_positive(0x1_0000_0000_0000_0000, i);
    assert(pow(0x1_0000_0000_0000_0000, i + 1) == 0x1_0000_0000_0000_0000 * pow(0x1_0000_0000_0000_0000, ((i + 1) - 1) as nat));
    assert(((i + 1) - 1) as nat == i);
    lemma_mul_is_commutative(0x1_0000_0000_0000_0000, pow(0x1_0000_0000_0000_0000, i));
}

pub(crate) open spec fn limbs(s: Seq<u64>, n: nat) -> int
    decreases n,
{
    if n == 0 { 0 } else { limbs(s, (n - 1) as nat) + s[n - 1] as int * wp((n - 1) as nat) }
}

pub(crate) proof fn lemma_limbs_ext(a: Seq<u64>, b: Seq<u64>, n: nat)
    requires forall|i: int| 0 <= i < n ==> a[i] == b[i],
    ensures limbs(a, n) == limbs(b, n),
    decreases n,
{
    if n > 0 { lemma_limbs_ext(a, b, (n - 1) as nat); }
}

pub(crate) proof fn lemma_limbs_bound(a: Seq<u64>, n: nat)
    requires n <= a.len(),
    ensures 0 <= limbs(a, n) < wp(n),
    decreases n,
{
    lemma_wp(0);
    if n > 0 {
        let k = (n - 1) as nat;
        lemma_limbs_bound(a, k);
        lemma_wp(k);
        let x = a[k as int] as int;
        lemma_mul_nonnegative(x, wp(k));
        lemma_mul_inequality(x, 0xffff_ffff_ffff_ffff, wp(k));
        assert(0xffff_ffff_ffff_ffff * wp(k) + wp(k) == 0x1_0000_0000_0000_0000 * wp(k));
        lemma_mul_is_commutative(wp(k), 0x1_0000_0000_0000_0000);
    }
}

// low limb
pub(crate) proof fn lemma_limbs_low(a: Seq<u64>, n: nat)
    requires 1 <= n <= a.len(),
    ensures limbs(a, n) % 0x1_0000_0000_0000_0000 == a[0] as int,
    decreases n,
{
    let w = 0x1_0000_0000_0000_0000int;
    lemma_wp(0);
    if n == 1 {
        assert(limbs(a, 0) == 0);
        lemma_mul_basics(a[0] as int);
        lemma_small_mod(a[0] as nat, w as nat);
    } else {
        let k = (n - 2) as nat;
        lemma_limbs_low(a, (n - 1) as nat);
        lemma_wp(k);
        let x = a[n - 1] as int;
        assert(x * wp((n - 1) as nat) == (x * wp(k)) * w) by {
            assert(((n - 1) as nat) == k + 1);
            lemma_mul_is_associative(x, wp(k), w);
        }
        lemma_mod_multiples_vanish(x * wp(k), limbs(a, (n - 1) as nat), w);
        lemma_mul_is_commutative(x * wp(k), w);
    }
}

pub(crate) proof fn lemma_limbs_shift(a: Seq<u64>, b: Seq<u64>, n: nat)
    requires forall|i: int| 0 <= i < n ==> b[i] == a[i + 1],
    ensures limbs(a, n + 1) == a[0] as int + 0x1_0000_0000_0000_0000 * limbs(b, n),
    decreases n,
{
    let w = 0x1_0000_0000_0000_0000int;
    lemma_wp(0);
    if n == 0 {
        assert(limbs(a, 1) == limbs(a, 0) + a[0] as int * wp(0));
        lemma_mul_basics(a[0] as int);
    } else {
        let k = (n - 1) as nat;
        lemma_limbs_shift(a, b, k);
        lemma_wp(k);
        assert(limbs(a, n + 1) == limbs(a, n) + a[n as int] as int * wp(n));
        assert(limbs(b, n) == limbs(b, k) + b[k as int] as int * wp(k));
        assert(k + 1 == n);
        lemma_shift_atom(b[k as int] as int, wp(k), w);
        lemma_mul_is_distributive_add(w, limbs(b, k), b[k as int] as int * wp(k));
    }
}

proof fn lemma_d1(x: int, y: int, z: int, w: int)
    ensures x * (y + z * w) == x * y + (x * z) * w,
{ broadcast use group_mul_properties; }

proof fn lemma_d2(a: int, b: int, w: int, v: int)
    ensures (a + b * w) * v == a * v + b * (v * w),
{ broadcast use group_mul_properties; }

proof fn lemma_d2s(a: int, b: int, w: int, v: int)
    ensures (a - b * w) * v == a * v - b * (v * w),
{ broadcast use group_mul_properties; }

proof fn lemma_d3(a: int, b: int, c: int, v: int)
    ensures (a + b + c) * v == a * v + b * v + c * v,
{ broadcast use group_mul_properties; }

proof fn lemma_d3s(a: int, b: int, c: int, v: int)
    ensures (a - b - c) * v == a * v - b * v - c * v,
{ broadcast use group_mul_properties; }

proof fn lemma_shift_atom(x: int, wk: int, w: int)
    ensures x * (wk * w) == w * (x * wk),
{ broadcast use group_mul_properties; }

proof fn lemma_w2(w: int, v: int)
    ensures ((v * w) * w) == (w * w) * v,
{ broadcast use group_mul_properties; }

// one addmul limb, products as atoms.
proof fn lemma_addmul_step(r: int, c: int, t: int, ab: int, wj: int, s: int, c2: int, abj: int, tj: int)
    requires
        r + c * wj == t + ab,
        s + c2 * 0x1_0000_0000_0000_0000 == abj + tj + c,
    ensures
        (r + s * wj) + c2 * (wj * 0x1_0000_0000_0000_0000) == (t + tj * wj) + (ab + abj * wj),
{
    let w = 0x1_0000_0000_0000_0000int;
    assert((s + c2 * w) * wj == (abj + tj + c) * wj);
    lemma_d2(s, c2, w, wj);
    lemma_d3(abj, tj, c, wj);
}

proof fn lemma_top_limbs(s: Seq<u64>, n: nat)
    ensures
        limbs(s, n + 2) == limbs(s, n) + s[n as int] as int * wp(n) + s[n as int + 1] as int * wp(n + 1),
{
    assert(n + 2 == (n + 1) + 1);
    assert(limbs(s, n + 1) == limbs(s, n) + s[n as int] as int * wp(n));
}

// carry into the top two limbs: no overflow, and the sum is preserved.
proof fn lemma_addmul_top(tl: int, tt: int, ab: int, rl: int, c: int, vn: int, vn1: int, vn2: int, tn: int, tn1: int, lo: int, hi: int)
    requires
        tt == tl + tn * vn + tn1 * vn1,
        vn1 == vn * 0x1_0000_0000_0000_0000,
        vn2 == vn1 * 0x1_0000_0000_0000_0000,
        vn > 0,
        rl >= 0,
        rl + c * vn == tl + ab,
        lo + hi * 0x1_0000_0000_0000_0000 == tn + c,
        lo >= 0,
        tt + ab < vn2,
    ensures
        hi + tn1 < 0x1_0000_0000_0000_0000,
        rl + lo * vn + (hi + tn1) * vn1 == tt + ab,
{
    let w = 0x1_0000_0000_0000_0000int;
    assert((lo + hi * w) * vn == (tn + c) * vn);
    lemma_d2(lo, hi, w, vn);
    lemma_mul_is_distributive_add_other_way(vn, tn, c);
    lemma_mul_is_distributive_add_other_way(vn1, hi, tn1);
    assert(rl + lo * vn + (hi + tn1) * vn1 == tt + ab);
    if hi + tn1 >= w {
        lemma_mul_nonnegative(lo, vn);
        lemma_mul_inequality(w, hi + tn1, vn1);
        lemma_mul_is_commutative(w, vn1);
    }
}

// t += a * b, over nl + 2 limbs.
#[cfg_attr(ct_check, ct::secret(t, a, b), ct::public(nl))]
fn addmul(t: &mut [u64; 66], a: u64, b: &[u64; 64], nl: usize)
    requires
        1 <= nl <= 64,
        limbs(old(t)@, nl as nat + 2) + a as int * limbs(b@, nl as nat) < wp(nl as nat + 2),
    ensures
        limbs(final(t)@, nl as nat + 2) == limbs(old(t)@, nl as nat + 2) + a as int * limbs(b@, nl as nat),
{
    let ghost t0 = t@;
    let mut c: u64 = 0;
    let mut j: usize = 0;
    proof { lemma_wp(0); }
    // ct: loop on the public nl
    while j < nl
        invariant
            1 <= nl <= 64,
            j <= nl,
            t@.len() == 66, t0.len() == 66,
            forall|i: int| j <= i < 66 ==> #[trigger] t@[i] == t0[i],
            limbs(t@, j as nat) + c as int * wp(j as nat) == limbs(t0, j as nat) + a as int * limbs(b@, j as nat),
        decreases nl - j,
    {
        let ghost tb = t@;
        let (s, c2) = mac(a, b[j], t[j], c);
        t[j] = s;
        proof {
            let jn = j as nat;
            lemma_wp(jn);
            lemma_limbs_ext(t@, tb, jn);
            assert(limbs(t@, jn + 1) == limbs(t@, jn) + s as int * wp(jn));
            assert(limbs(t0, jn + 1) == limbs(t0, jn) + t0[j as int] as int * wp(jn));
            assert(limbs(b@, jn + 1) == limbs(b@, jn) + b@[j as int] as int * wp(jn));
            lemma_addmul_step(limbs(tb, jn), c as int, limbs(t0, jn), a as int * limbs(b@, jn), wp(jn), s as int, c2 as int, a as int * b@[j as int] as int, t0[j as int] as int);
            lemma_d1(a as int, limbs(b@, jn), b@[j as int] as int, wp(jn));
        }
        c = c2;
        j = j + 1;
    }
    let ghost tn = t@;
    let ghost n = nl as nat;
    let x: u128 = t[nl] as u128 + c as u128;
    proof { bv_split128(x); lemma_fundamental_div_mod(x as int, 0x1_0000_0000_0000_0000int); }
    let lo = x as u64;
    let hi = (x >> 64u128) as u64;
    proof {
        lemma_top_limbs(t0, n);
        lemma_wp(n);
        lemma_wp(n + 1);
        lemma_limbs_bound(tn, n);
        lemma_addmul_top(limbs(t0, n), limbs(t0, n + 2), a as int * limbs(b@, n), limbs(tn, n), c as int, wp(n), wp(n + 1), wp(n + 2), t0[nl as int] as int, t0[nl as int + 1] as int, lo as int, hi as int);
    }
    let top: u64 = t[nl + 1] + hi;
    t[nl] = lo;
    t[nl + 1] = top;
    proof {
        lemma_limbs_ext(t@, tn, n);
        lemma_top_limbs(t@, n);
    }
}

// t := t / 2^64, for t[0] == 0.
#[cfg_attr(ct_check, ct::secret(t), ct::public(nl))]
fn shift_down(t: &mut [u64; 66], nl: usize)
    requires
        1 <= nl <= 64,
        old(t)@[0] == 0,
    ensures
        limbs(final(t)@, nl as nat + 2) * 0x1_0000_0000_0000_0000 == limbs(old(t)@, nl as nat + 2),
{
    let ghost t0 = t@;
    let mut j: usize = 0;
    // ct: loop on the public nl
    while j <= nl
        invariant
            1 <= nl <= 64,
            j <= nl + 1,
            t@.len() == 66,
            forall|i: int| 0 <= i < j ==> #[trigger] t@[i] == t0[i + 1],
            forall|i: int| j <= i < 66 ==> #[trigger] t@[i] == t0[i],
        decreases nl + 1 - j,
    {
        t[j] = t[j + 1];
        j = j + 1;
    }
    t[nl + 1] = 0;
    proof {
        let n = nl as nat;
        lemma_limbs_shift(t0, t@, n + 1);
        assert(n + 2 == (n + 1) + 1);
        assert(limbs(t@, n + 2) == limbs(t@, n + 1) + t@[nl as int + 1] as int * wp(n + 1));
        lemma_mul_basics(wp(n + 1));
        lemma_mul_is_commutative(limbs(t@, n + 2), 0x1_0000_0000_0000_0000);
    }
}

// q * M mod W only sees m0.
proof fn lemma_row_zero(t1: int, s0: int, q: int, mm: int, m0: int, mp: int)
    requires
        0 <= s0, 0 <= mp, 0 <= m0,
        t1 % 0x1_0000_0000_0000_0000 == s0,
        mm % 0x1_0000_0000_0000_0000 == m0,
        q == (s0 * mp) % 0x1_0000_0000_0000_0000,
        (m0 * mp + 1) % 0x1_0000_0000_0000_0000 == 0,
    ensures
        (t1 + q * mm) % 0x1_0000_0000_0000_0000 == 0,
{
    let w = 0x1_0000_0000_0000_0000int;
    lemma_q_zero(s0, mp, m0);
    lemma_mul_mod_noop_right(q, mm, w);
    lemma_add_mod_noop(t1, q * mm, w);
    lemma_add_mod_noop(s0, q * m0, w);
}

proof fn lemma_row_bound(t0: int, a: int, bb: int, mm: int, v0: int, v1: int, v2: int)
    requires
        0 <= a < 0x1_0000_0000_0000_0000,
        0 <= bb < mm, mm < v0,
        0 <= t0 < 2 * mm,
        v1 == v0 * 0x1_0000_0000_0000_0000,
        v2 == v1 * 0x1_0000_0000_0000_0000,
    ensures
        t0 + a * bb < v2,
        0 <= a * bb <= 0xffff_ffff_ffff_ffff * mm,
{
    lemma_mul_upper_bound(a, 0xffff_ffff_ffff_ffff, bb, mm);
    lemma_mul_nonnegative(a, bb);
    assert(0x1_0000_0000_0000_0000 * mm <= 0x1_0000_0000_0000_0000 * v0) by {
        lemma_mul_inequality(mm, v0, 0x1_0000_0000_0000_0000);
    }
    lemma_mul_is_commutative(v0, 0x1_0000_0000_0000_0000);
}

proof fn lemma_row_bound2(t0: int, a: int, q: int, bb: int, mm: int, v0: int, v1: int, v2: int)
    requires
        0 <= a < 0x1_0000_0000_0000_0000,
        0 <= q < 0x1_0000_0000_0000_0000,
        0 <= bb < mm, mm < v0,
        0 <= t0 < 2 * mm,
        v1 == v0 * 0x1_0000_0000_0000_0000,
        v2 == v1 * 0x1_0000_0000_0000_0000,
    ensures
        t0 + a * bb + q * mm < v2,
{
    lemma_mul_upper_bound(a, 0xffff_ffff_ffff_ffff, bb, mm);
    lemma_mul_upper_bound(q, 0xffff_ffff_ffff_ffff, mm, mm);
    lemma_mul_inequality(mm, v0, 0x1_0000_0000_0000_0000);
    lemma_mul_is_commutative(v0, 0x1_0000_0000_0000_0000);
}

proof fn lemma_row_end(tf: int, t0: int, a: int, q: int, bb: int, mm: int)
    requires
        0 <= a < 0x1_0000_0000_0000_0000,
        0 <= q < 0x1_0000_0000_0000_0000,
        0 <= bb < mm,
        0 <= t0 < 2 * mm,
        tf * 0x1_0000_0000_0000_0000 == t0 + a * bb + q * mm,
    ensures
        tf < 2 * mm,
{
    lemma_mul_upper_bound(a, 0xffff_ffff_ffff_ffff, bb, mm);
    lemma_mul_upper_bound(q, 0xffff_ffff_ffff_ffff, mm, mm);
    if tf >= 2 * mm {
        lemma_mul_inequality(2 * mm, tf, 0x1_0000_0000_0000_0000);
    }
}

// One CIOS row: r * 2^64 == t + ai * B + q * M, with r < 2M.
#[cfg_attr(ct_check, ct::secret(t, ai, b, m, mp), ct::public(nl))]
fn mont_row(t: &mut [u64; 66], ai: u64, b: &[u64; 64], m: &[u64; 64], mp: u64, nl: usize) -> (q: Ghost<int>)
    requires
        1 <= nl <= 64,
        (m[0] as int * mp as int + 1) % 0x1_0000_0000_0000_0000 == 0,
        limbs(b@, nl as nat) < limbs(m@, nl as nat),
        limbs(old(t)@, nl as nat + 2) < 2 * limbs(m@, nl as nat),
    ensures
        limbs(final(t)@, nl as nat + 2) * 0x1_0000_0000_0000_0000 == limbs(old(t)@, nl as nat + 2) + ai as int * limbs(b@, nl as nat) + q@ * limbs(m@, nl as nat),
        0 <= q@ < 0x1_0000_0000_0000_0000,
        limbs(final(t)@, nl as nat + 2) < 2 * limbs(m@, nl as nat),
{
    let ghost n = nl as nat;
    let ghost mm = limbs(m@, n);
    let ghost bb = limbs(b@, n);
    let ghost t0 = limbs(t@, n + 2);
    proof {
        lemma_limbs_bound(m@, n);
        lemma_limbs_bound(b@, n);
        lemma_limbs_bound(t@, n + 2);
        lemma_wp(n);
        lemma_wp(n + 1);
        lemma_row_bound(t0, ai as int, bb, mm, wp(n), wp(n + 1), wp(n + 2));
    }
    addmul(t, ai, b, nl);
    let ghost t1 = limbs(t@, n + 2);
    let ghost ts = t@;
    let s0 = t[0];
    proof { lemma_mac_bound(s0 as int, mp as int, 0, 0); }
    let pr: u128 = s0 as u128 * mp as u128;
    proof { bv_split128(pr); }
    let q: u64 = pr as u64;
    proof {
        lemma_row_bound2(t0, ai as int, q as int, bb, mm, wp(n), wp(n + 1), wp(n + 2));
    }
    addmul(t, q, m, nl);
    proof {
        lemma_limbs_low(m@, n);
        lemma_limbs_low(ts, n + 2);
        lemma_row_zero(t1, s0 as int, q as int, mm, m[0] as int, mp as int);
        lemma_limbs_low(t@, n + 2);
    }
    shift_down(t, nl);
    proof {
        lemma_row_end(limbs(t@, n + 2), t0, ai as int, q as int, bb, mm);
    }
    Ghost(q as int)
}

proof fn lemma_acc_r(x: int, y: int, wi: int, b: int)
    ensures (x + y * wi) * b == x * b + (y * b) * wi,
{ broadcast use group_mul_properties; }

proof fn lemma_acc(t: int, tn: int, wi: int, a_i: int, ai: int, b: int, qq: int, q: int, m: int)
    requires
        t * wi == a_i * b + qq * m,
        tn * 0x1_0000_0000_0000_0000 == t + ai * b + q * m,
    ensures
        tn * (wi * 0x1_0000_0000_0000_0000) == (a_i + ai * wi) * b + (qq + q * wi) * m,
{
    let w = 0x1_0000_0000_0000_0000int;
    assert((tn * w) * wi == (t + ai * b + q * m) * wi);
    lemma_mul_is_associative(tn, wi, w);
    lemma_mul_is_commutative(wi, w);
    lemma_mul_is_associative(tn, w, wi);
    lemma_d3(t, ai * b, q * m, wi);
    lemma_acc_r(a_i, ai, wi, b);
    lemma_acc_r(qq, q, wi, m);
}

proof fn lemma_mont_final(t: int, ab: int, q: int, m: int, r: int, rr: int)
    requires
        m > 0,
        t * rr == ab + q * m,
        r == t || r == t - m,
    ensures
        (r * rr) % m == ab % m,
{
    if r == t {
        lemma_mod_multiples_vanish(q, ab, m);
        lemma_mul_is_commutative(q, m);
    } else {
        assert(r * rr == ab + (q - rr) * m) by { broadcast use group_mul_properties; }
        lemma_mod_multiples_vanish(q - rr, ab, m);
        lemma_mul_is_commutative(q - rr, m);
    }
}

proof fn lemma_sub_step(dl: int, e: int, tl: int, ml: int, v: int, x: int, e2: int, ti: int, mi: int)
    requires
        dl - e * v == tl - ml,
        x - e2 * 0x1_0000_0000_0000_0000 == ti - mi - e,
    ensures
        (dl + x * v) - e2 * (v * 0x1_0000_0000_0000_0000) == (tl + ti * v) - (ml + mi * v),
{
    let w = 0x1_0000_0000_0000_0000int;
    assert((x - e2 * w) * v == (ti - mi - e) * v);
    lemma_d2s(x, e2, w, v);
    lemma_d3s(ti, mi, e, v);
}

// d - e * R == t - m on nl limbs.
#[cfg_attr(ct_check, ct::secret(t, m), ct::public(nl))]
fn sub_n(t: &[u64; 66], m: &[u64; 64], nl: usize) -> (r: ([u64; 64], u64))
    requires
        1 <= nl <= 64,
    ensures
        r.1 <= 1,
        limbs(r.0@, nl as nat) - r.1 as int * wp(nl as nat) == limbs(t@, nl as nat) - limbs(m@, nl as nat),
{
    let mut d = [0u64; 64];
    let mut e: u64 = 0;
    let mut j: usize = 0;
    proof { lemma_wp(0); lemma_mul_basics(wp(0)); }
    // ct: loop on the public nl
    while j < nl
        invariant
            1 <= nl <= 64,
            j <= nl,
            e <= 1,
            d@.len() == 64,
            limbs(d@, j as nat) - e as int * wp(j as nat) == limbs(t@, j as nat) - limbs(m@, j as nat),
        decreases nl - j,
    {
        let ghost d0 = d@;
        let (x, e2) = sbb(t[j], m[j], e);
        d[j] = x;
        proof {
            let jn = j as nat;
            lemma_wp(jn);
            lemma_limbs_ext(d@, d0, jn);
            assert(limbs(d@, jn + 1) == limbs(d@, jn) + x as int * wp(jn));
            assert(limbs(t@, jn + 1) == limbs(t@, jn) + t@[j as int] as int * wp(jn));
            assert(limbs(m@, jn + 1) == limbs(m@, jn) + m@[j as int] as int * wp(jn));
            lemma_sub_step(limbs(d0, jn), e as int, limbs(t@, jn), limbs(m@, jn), wp(jn), x as int, e2 as int, t@[j as int] as int, m@[j as int] as int);
        }
        e = e2;
        j = j + 1;
    }
    (d, e)
}

// the case analysis of the final subtract, on atoms.
proof fn lemma_cond_final(tt: int, tl: int, tn: int, tn1: int, mm: int, dl: int, e: int, dn: int, en: int, vn: int, vn1: int)
    requires
        tt == tl + tn * vn + tn1 * vn1,
        vn1 == vn * 0x1_0000_0000_0000_0000,
        vn > 0,
        0 <= tl < vn,
        0 <= dl < vn,
        0 < mm < vn,
        0 <= tn < 0x1_0000_0000_0000_0000,
        0 <= tn1 < 0x1_0000_0000_0000_0000,
        0 <= dn < 0x1_0000_0000_0000_0000,
        tt < 2 * mm,
        dl - e * vn == tl - mm,
        dn - en * 0x1_0000_0000_0000_0000 == tn - e,
        en == 0 || en == 1,
    ensures
        en == 1 ==> tt == tl && tt < mm,
        en == 0 ==> dl == tt - mm,
{
    let w = 0x1_0000_0000_0000_0000int;
    lemma_mul_nonnegative(tn, vn);
    lemma_mul_nonnegative(tn1, vn1);
    lemma_mul_nonnegative(dn, vn);
    if tn1 >= 1 {
        lemma_mul_inequality(1, tn1, vn1);
        lemma_mul_inequality(2, w, vn);
    }
    assert(tn1 == 0);
    lemma_mul_basics(vn1);
    if tn >= 2 {
        lemma_mul_inequality(2, tn, vn);
    }
    assert((dn - en * w) * vn == (tn - e) * vn);
    lemma_d2s(dn, en, w, vn);
    lemma_mul_is_distributive_sub_other_way(vn, tn, e);
    lemma_mul_is_commutative(vn, tn);
    lemma_mul_is_commutative(vn, e);
    // dl + dn vn - en vn1 == tt - mm
    if en == 1 {
        lemma_mul_inequality(dn, 0xffff_ffff_ffff_ffff, vn);
        lemma_mul_basics(vn1);
        if tn >= 1 {
            lemma_mul_inequality(1, tn, vn);
        }
        lemma_mul_basics(vn);
    } else {
        if dn >= 1 {
            lemma_mul_inequality(1, dn, vn);
        }
        lemma_mul_basics(vn);
    }
}

// All ones for 1, zero for 0.
// Not inlined: seen as sext(i1) in a limb loop, the mask becomes a loop-unswitched branch on the secret bit in release builds, which the MIR checker cannot see.
#[inline(never)]
#[cfg_attr(ct_check, ct::secret(b))]
pub(crate) fn ct_mask(b: u64) -> (r: u64)
    ensures
        r == 0u64.wrapping_sub(b),
{
    0u64.wrapping_sub(b)
}

// t - m if t >= m, else t, over the nl + 2 limb value t < 2m.
#[cfg_attr(ct_check, ct::secret(t, m), ct::public(nl))]
fn cond_sub(t: &[u64; 66], m: &[u64; 64], nl: usize) -> (r: [u64; 64])
    requires
        1 <= nl <= 64,
        limbs(m@, nl as nat) > 0,
        limbs(m@, nl as nat) < wp(nl as nat),
        limbs(t@, nl as nat + 2) < 2 * limbs(m@, nl as nat),
    ensures
        limbs(r@, nl as nat) < limbs(m@, nl as nat),
        limbs(r@, nl as nat) == limbs(t@, nl as nat + 2) || limbs(r@, nl as nat) == limbs(t@, nl as nat + 2) - limbs(m@, nl as nat),
{
    let ghost n = nl as nat;
    let (d, e) = sub_n(t, m, nl);
    let (_dn, en) = sbb(t[nl], 0, e);
    let mask = ct_mask(en);
    let mut r = [0u64; 64];
    let mut j: usize = 0;
    // ct: loop on the public nl
    while j < nl
        invariant
            1 <= nl <= 64,
            j <= nl,
            en <= 1,
            mask == 0u64.wrapping_sub(en),
            r@.len() == 64,
            forall|i: int| 0 <= i < j ==> #[trigger] r@[i] == (if en == 1 { t@[i] } else { d@[i] }),
        decreases nl - j,
    {
        let v = (t[j] & mask) | (d[j] & !mask);
        proof { bv_sel(t[j as int], d[j as int], en); }
        r[j] = v;
        j = j + 1;
    }
    proof {
        lemma_limbs_bound(t@, n);
        lemma_limbs_bound(d@, n);
        lemma_top_limbs(t@, n);
        lemma_wp(n);
        lemma_cond_final(limbs(t@, n + 2), limbs(t@, n), t@[nl as int] as int, t@[nl as int + 1] as int, limbs(m@, n), limbs(d@, n), e as int, _dn as int, en as int, wp(n), wp(n + 1));
        if en == 1 {
            lemma_limbs_ext(r@, t@, n);
        } else {
            lemma_limbs_ext(r@, d@, n);
        }
    }
    r
}

// Montgomery product: r < m and r * R == a * b (mod m), R = wp(nl).
#[cfg_attr(ct_check, ct::secret(a, b, m, mp), ct::public(nl))]
pub(crate) fn mont_mul_n(a: &[u64; 64], b: &[u64; 64], m: &[u64; 64], mp: u64, nl: usize) -> (r: [u64; 64])
    requires
        1 <= nl <= 64,
        (m[0] as int * mp as int + 1) % 0x1_0000_0000_0000_0000 == 0,
        limbs(b@, nl as nat) < limbs(m@, nl as nat),
    ensures
        limbs(r@, nl as nat) < limbs(m@, nl as nat),
        (limbs(r@, nl as nat) * wp(nl as nat)) % limbs(m@, nl as nat) == (limbs(a@, nl as nat) * limbs(b@, nl as nat)) % limbs(m@, nl as nat),
{
    let ghost n = nl as nat;
    let ghost mm = limbs(m@, n);
    let ghost bb = limbs(b@, n);
    let mut t = [0u64; 66];
    let ghost mut qq: int = 0;
    let mut i: usize = 0;
    proof {
        lemma_limbs_bound(b@, n);
        lemma_wp(0);
        lemma_limbs_zero(t@, n + 2);
        assert(limbs(a@, 0) == 0);
        lemma_mul_basics(bb);
        lemma_mul_basics(mm);
        lemma_mul_basics(wp(0));
    }
    // ct: loop on the public nl
    while i < nl
        invariant
            1 <= nl <= 64,
            i <= nl,
            n == nl as nat,
            mm == limbs(m@, n),
            bb == limbs(b@, n),
            bb < mm,
            0 <= bb,
            (m[0] as int * mp as int + 1) % 0x1_0000_0000_0000_0000 == 0,
            limbs(t@, n + 2) < 2 * mm,
            limbs(t@, n + 2) * wp(i as nat) == limbs(a@, i as nat) * bb + qq * mm,
        decreases nl - i,
    {
        let ghost tv = limbs(t@, n + 2);
        let _q = mont_row(&mut t, a[i], b, m, mp, nl);
        proof {
            let inn = i as nat;
            lemma_wp(inn);
            assert(limbs(a@, inn + 1) == limbs(a@, inn) + a@[i as int] as int * wp(inn));
            lemma_acc(tv, limbs(t@, n + 2), wp(inn), limbs(a@, inn), a@[i as int] as int, bb, qq, _q@, mm);
            qq = qq + _q@ * wp(inn);
        }
        i = i + 1;
    }
    proof { lemma_limbs_bound(m@, n); }
    let r = cond_sub(&t, m, nl);
    proof {
        lemma_mont_final(limbs(t@, n + 2), limbs(a@, n) * bb, qq, mm, limbs(r@, n), wp(n));
    }
    r
}

pub(crate) proof fn lemma_limbs_zero(s: Seq<u64>, n: nat)
    requires forall|i: int| 0 <= i < n ==> s[i] == 0,
    ensures limbs(s, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_limbs_zero(s, (n - 1) as nat);
        lemma_mul_basics(wp((n - 1) as nat));
    }
}

// masked select over nl limbs.
#[cfg_attr(ct_check, ct::secret(b, x, y), ct::public(nl))]
pub(crate) fn select_n(b: u64, x: &[u64; 64], y: &[u64; 64], nl: usize) -> (r: [u64; 64])
    requires b <= 1, nl <= 64,
    ensures limbs(r@, nl as nat) == limbs((if b == 1 { *x } else { *y })@, nl as nat),
{
    let mask = ct_mask(b);
    let mut r = [0u64; 64];
    let mut j: usize = 0;
    // ct: loop on the public nl
    while j < nl
        invariant
            j <= nl <= 64, b <= 1,
            mask == 0u64.wrapping_sub(b),
            r@.len() == 64,
            forall|i: int| 0 <= i < j ==> #[trigger] r@[i] == (if b == 1 { x@[i] } else { y@[i] }),
        decreases nl - j,
    {
        let v = (x[j] & mask) | (y[j] & !mask);
        proof { bv_sel(x[j as int], y[j as int], b); }
        r[j] = v;
        j = j + 1;
    }
    proof { lemma_limbs_ext(r@, (if b == 1 { *x } else { *y })@, nl as nat); }
    r
}

// --- mp by Newton ---
proof fn lemma_newton_math(n: int, y: int, k: int)
    requires k > 1, (n * y) % k == 1,
    ensures (n * (y * (2 - n * y))) % (k * k) == 1,
{
    let c = (n * y) / k;
    lemma_fundamental_div_mod(n * y, k);
    let v = n * y;
    assert(v == k * c + 1);
    assert(n * (y * (2 - v)) == v * (2 - v)) by { lemma_mul_is_associative(n, y, 2 - v); }
    assert(v * (2 - v) == 1 + (-(c * c)) * (k * k)) by (nonlinear_arith) requires v == k * c + 1;
    lemma_mul_is_commutative(-(c * c), k * k);
    assert(k * k > 1) by (nonlinear_arith) requires k > 1;
    lemma_mod_multiples_vanish(-(c * c), 1, k * k);
    lemma_small_mod(1, (k * k) as nat);
}

// r ≡ z (mod W) and k2 | W carry n * r ≡ n * z (mod k2).
proof fn lemma_newton_lift(n: int, r: int, z: int, w: int, k2: int)
    requires
        w > 0, k2 > 0,
        r % w == z % w,
        w % k2 == 0,
    ensures
        (n * r) % k2 == (n * z) % k2,
{
    let c = w / k2;
    lemma_fundamental_div_mod(w, k2);
    lemma_mul_is_commutative(k2, c);
    if c <= 0 { lemma_mul_inequality(c, 0, k2); lemma_mul_basics(k2); }
    lemma_mod_mod(r, k2, c);
    lemma_mod_mod(z, k2, c);
    lemma_mul_mod_noop_right(n, r, k2);
    lemma_mul_mod_noop_right(n, z, k2);
}

#[cfg_attr(ct_check, ct::secret(n, y))]
fn newton_step(n: u64, y: u64) -> (r: u64)
    ensures (r as int) % 0x1_0000_0000_0000_0000 == (y as int * (2 - n as int * y as int)) % 0x1_0000_0000_0000_0000,
{
    let ghost w = 0x1_0000_0000_0000_0000int;
    proof { lemma_mac_bound(n as int, y as int, 0, 0); }
    let a: u128 = n as u128 * y as u128;
    proof { bv_split128(a); }
    let t: u64 = a as u64;
    let u: u64 = 2u64.wrapping_sub(t);
    proof {
        lemma_mac_bound(y as int, u as int, 0, 0);
        // u == 2 - t + j W
        assert((u as int) % w == (2 - n as int * y as int) % w) by {
            let v = n as int * y as int;
            lemma_sub_mod_noop_right(2, v, w);
            lemma_small_mod(u as nat, w as nat);
            if t <= 2 {
                lemma_small_mod((2 - t) as nat, w as nat);
            } else {
                lemma_mod_add_multiples_vanish(2 - (t as int), w);
                lemma_small_mod(u as nat, w as nat);
            }
        }
    }
    let b: u128 = y as u128 * u as u128;
    proof {
        bv_split128(b);
        lemma_mul_mod_noop_right(y as int, u as int, w);
        lemma_mul_mod_noop_right(y as int, 2 - n as int * y as int, w);
        lemma_small_mod((b as u64) as nat, w as nat);
        lemma_small_mod((y as int * u as int % w) as nat, w as nat);
    }
    b as u64
}

pub(crate) open spec fn k_at(i: nat) -> int
    decreases i,
{
    if i == 0 { 2 } else { k_at((i - 1) as nat) * k_at((i - 1) as nat) }
}

proof fn lemma_k_at(i: nat)
    requires i < 6,
    ensures
        k_at(i) > 1,
        k_at(i + 1) > 1,
        0x1_0000_0000_0000_0000int % k_at(i + 1) == 0,
{
    assert(k_at(1) == 4 && 0x1_0000_0000_0000_0000int % k_at(1) == 0) by (compute_only);
    assert(k_at(2) == 16 && 0x1_0000_0000_0000_0000int % k_at(2) == 0) by (compute_only);
    assert(k_at(3) == 256 && 0x1_0000_0000_0000_0000int % k_at(3) == 0) by (compute_only);
    assert(k_at(4) == 0x1_0000 && 0x1_0000_0000_0000_0000int % k_at(4) == 0) by (compute_only);
    assert(k_at(5) == 0x1_0000_0000 && 0x1_0000_0000_0000_0000int % k_at(5) == 0) by (compute_only);
    assert(k_at(6) == 0x1_0000_0000_0000_0000 && 0x1_0000_0000_0000_0000int % k_at(6) == 0) by (compute_only);
    assert(i == 0 || i == 1 || i == 2 || i == 3 || i == 4 || i == 5);
}

proof fn lemma_neg_inv(n: int, y: int, mp: int, w: int)
    requires
        w == 0x1_0000_0000_0000_0000int,
        (n * y) % w == 1,
        y != 0,
        mp == w - y,
    ensures
        (n * mp + 1) % w == 0,
{
    let c = (n * y) / w;
    lemma_fundamental_div_mod(n * y, w);
    lemma_mul_is_distributive_sub(n, w, y);
    lemma_mul_is_commutative(n, w);
    lemma_mul_is_distributive_sub(w, n, c);
    lemma_mul_is_commutative(w, n - c);
    lemma_mod_multiples_basic(n - c, w);
}

// m[0] * mp == -1 mod 2^64 for odd m0.
#[cfg_attr(ct_check, ct::secret(m0))]
pub(crate) fn neg_inv64(m0: u64) -> (mp: u64)
    requires m0 % 2 == 1,
    ensures (m0 as int * mp as int + 1) % 0x1_0000_0000_0000_0000 == 0,
{
    let ghost n = m0 as int;
    let ghost w = 0x1_0000_0000_0000_0000int;
    let mut y: u64 = 1;
    proof {
        lemma_mul_basics(n);
        assert(k_at(0) == 2);
        assert(k_at(6) == 0x1_0000_0000_0000_0000int) by (compute_only);
    }
    let mut i: usize = 0;
    // ct: fixed count
    while i < 6
        invariant
            i <= 6,
            n == m0 as int,
            w == 0x1_0000_0000_0000_0000int,
            k_at(6) == w,
            (n * y as int) % k_at(i as nat) == 1,
        decreases 6 - i,
    {
        let ghost y0 = y as int;
        y = newton_step(m0, y);
        proof {
            let inn = i as nat;
            lemma_k_at(inn);
            assert(k_at(inn + 1) == k_at(inn) * k_at(inn));
            lemma_newton_math(n, y0, k_at(inn));
            lemma_newton_lift(n, y as int, y0 * (2 - n * y0), w, k_at(inn + 1));
        }
        i = i + 1;
    }
    let mp = 0u64.wrapping_sub(y);
    proof {
        assert((n * y as int) % w == 1);
        if y == 0 {
            lemma_mul_basics(n);
            lemma_small_mod(0, w as nat);
        }
        lemma_neg_inv(n, y as int, mp as int, w);
    }
    mp
}

// --- big-endian conversion ---
pub(crate) proof fn lemma_wp_256(j: nat)
    ensures wp(j) == pow(256, 8 * j), wp(j) > 0,
    decreases j,
{
    reveal(pow);
    if j == 0 {
    } else {
        lemma_wp_256((j - 1) as nat);
        lemma_pow_adds(256, 8 * (j - 1) as nat, 8);
        assert(8 * (j - 1) as nat + 8 == 8 * j);
        assert(pow(256, 8) == 0x1_0000_0000_0000_0000) by { reveal_with_fuel(pow, 9); }
        lemma_mul_is_commutative(pow(0x1_0000_0000_0000_0000, (j - 1) as nat), 0x1_0000_0000_0000_0000);
    }
    lemma_pow_positive(0x1_0000_0000_0000_0000, j);
}

proof fn lemma_os2ip_zeros(n: nat)
    ensures os2ip(Seq::new(n, |_i: int| 0u8)) == 0,
    decreases n,
{
    if n > 0 {
        assert(Seq::new(n, |_i: int| 0u8).drop_last() =~= Seq::new((n - 1) as nat, |_i: int| 0u8));
        lemma_os2ip_zeros((n - 1) as nat);
    }
}

#[cfg_attr(ct_check, ct::secret(b), ct::public(len))]
pub(crate) fn pad_be(b: &[u8], len: usize) -> (r: Vec<u8>)
    requires
        os2ip(b@) < pow(256, len as nat),
    ensures
        r@.len() == len,
        os2ip(r@) == os2ip(b@),
{
    let mut r: Vec<u8> = Vec::with_capacity(len);
    // ct: branch on public lengths
    if b.len() >= len {
        let t = vstd::slice::slice_subrange(b, b.len() - len, b.len());
        proof { lemma_os2ip_tail(b@, len as nat); }
        r.extend_from_slice(t);
        assert(r@ =~= b@.subrange(b@.len() - len, b@.len() as int));
    } else {
        let z = len - b.len();
        let mut i: usize = 0;
        // ct: loop on public lengths
        while i < z
            invariant i <= z, r@ == Seq::new(i as nat, |_j: int| 0u8),
            decreases z - i,
        {
            r.push(0u8);
            i = i + 1;
            assert(r@ =~= Seq::new(i as nat, |_j: int| 0u8));
        }
        let ghost zs = r@;
        r.extend_from_slice(b);
        proof {
            assert(r@ =~= zs + b@);
            assert(i == z);
            lemma_os2ip_append(zs, b@);
            lemma_os2ip_zeros(z as nat);
            lemma_mul_basics(pow(256, b@.len()));
        }
    }
    r
}

// Limbs of the big-endian 8 * nl octets.
#[verifier::spinoff_prover]
#[cfg_attr(ct_check, ct::secret(b), ct::public(nl))]
pub(crate) fn limbs_from_be_n(b: &[u8], nl: usize) -> (r: [u64; 64])
    requires
        nl <= 64,
        b@.len() == 8 * nl,
    ensures
        limbs(r@, nl as nat) == os2ip(b@),
{
    let mut r = [0u64; 64];
    let mut j: usize = 0;
    proof {
        assert(b@.subrange(8 * nl, 8 * nl) =~= Seq::<u8>::empty());
    }
    // ct: loop on the public nl
    while j < nl
        invariant
            j <= nl <= 64,
            b@.len() == 8 * nl,
            r@.len() == 64,
            limbs(r@, j as nat) == os2ip(b@.subrange(8 * (nl - j), 8 * nl as int)),
        decreases nl - j,
    {
        let ghost r0 = r@;
        let off = 8 * (nl - 1 - j);
        let v = load_be64(b, off);
        r[j] = v;
        proof {
            let jn = j as nat;
            let q = b@.subrange(off as int, off + 8);
            let t = b@.subrange(off + 8, 8 * nl as int);
            assert(off + 8 == 8 * (nl - j));
            assert(b@.subrange(off as int, 8 * nl as int) =~= q + t);
            assert(t.len() == 8 * jn);
            lemma_os2ip_append(q, t);
            lemma_wp_256(jn);
            lemma_limbs_ext(r@, r0, jn);
            lemma_mul_is_commutative(v as int, wp(jn));
            assert(limbs(r@, jn + 1) == limbs(r@, jn) + v as int * wp(jn));
            assert(8 * (nl - (j + 1)) == off);
        }
        j = j + 1;
    }
    proof { assert(b@.subrange(0, 8 * nl as int) =~= b@); }
    r
}

// big-endian octets of limbs, low k octets.
#[verifier::spinoff_prover]
#[cfg_attr(ct_check, ct::secret(l), ct::public(nl, k))]
pub(crate) fn limbs_to_be_n(l: &[u64; 64], nl: usize, k: usize) -> (r: Vec<u8>)
    requires
        1 <= nl <= 64,
        8 * (nl - 1) < k <= 8 * nl,
        limbs(l@, nl as nat) < pow(256, k as nat),
    ensures
        r@ == i2osp(limbs(l@, nl as nat) as nat, k as nat),
{
    let total: usize = 8 * nl;
    let mut out: Vec<u8> = Vec::with_capacity(total);
    let mut z: usize = 0;
    // ct: loop on the public nl
    while z < total
        invariant z <= total, out@.len() == z, total == 8 * nl,
        decreases total - z,
    {
        out.push(0u8);
        z = z + 1;
    }
    let mut j: usize = 0;
    proof {
        assert(out@.subrange(total as int, total as int) =~= Seq::<u8>::empty());
    }
    // ct: loop on the public nl
    while j < nl
        invariant
            j <= nl <= 64,
            total == 8 * nl,
            out@.len() == total,
            os2ip(out@.subrange(8 * (nl - j), total as int)) == limbs(l@, j as nat),
        decreases nl - j,
    {
        let v = l[j];
        let off = 8 * (nl - 1 - j);
        let ghost before = out@;
        out.set(off, (v >> 56) as u8);
        out.set(off + 1, (v >> 48) as u8);
        out.set(off + 2, (v >> 40) as u8);
        out.set(off + 3, (v >> 32) as u8);
        out.set(off + 4, (v >> 24) as u8);
        out.set(off + 5, (v >> 16) as u8);
        out.set(off + 6, (v >> 8) as u8);
        out.set(off + 7, v as u8);
        proof {
            let jn = j as nat;
            let q = out@.subrange(off as int, off + 8);
            let t = out@.subrange(off + 8, total as int);
            assert(off + 8 == 8 * (nl - j));
            lemma_i2osp_be8(v);
            assert(q =~= i2osp(v as nat, 8));
            vstd::arithmetic::power::lemma_pow_positive(256, 8);
            assert(pow(256, 8) == 0x1_0000_0000_0000_0000) by { reveal_with_fuel(pow, 9); }
            lemma_os2ip_i2osp(v as nat, 8);
            assert(t =~= before.subrange(off + 8, total as int));
            assert(out@.subrange(off as int, total as int) =~= q + t);
            assert(t.len() == 8 * jn);
            lemma_os2ip_append(q, t);
            lemma_wp_256(jn);
            lemma_mul_is_commutative(v as int, wp(jn));
            assert(limbs(l@, jn + 1) == limbs(l@, jn) + v as int * wp(jn));
            assert(8 * (nl - (j + 1)) == off);
        }
        j = j + 1;
    }
    let ghost lv = limbs(l@, nl as nat);
    proof {
        assert(8 * (nl - j) == 0);
        assert(out@.subrange(0, total as int) =~= out@);
        assert(os2ip(out@) == lv);
        lemma_os2ip_tail(out@, k as nat);
    }
    let mut r: Vec<u8> = Vec::with_capacity(k);
    r.extend_from_slice(vstd::slice::slice_subrange(out.as_slice(), total - k, total));
    proof {
        assert(r@ =~= out@.subrange(out@.len() - k as nat, out@.len() as int));
        lemma_i2osp_os2ip(r@);
    }
    r
}

proof fn lemma_double_mod(p: int, x: int, m: int)
    requires m > 0, x == p % m,
    ensures (2 * x) % m == (2 * p) % m,
{
    lemma_mul_mod_noop_right(2, p, m);
}

proof fn lemma_cond_is_mod(rv: int, t: int, m: int)
    requires m > 0, 0 <= t < 2 * m, 0 <= rv < m, rv == t || rv == t - m,
    ensures rv == t % m,
{
    if rv == t {
        lemma_small_mod(t as nat, m as nat);
    } else {
        lemma_fundamental_div_mod_converse(t, m, 1, rv);
    }
}

#[verifier::spinoff_prover]
#[cfg_attr(ct_check, ct::secret(m), ct::public(nl, count))]
pub(crate) fn pow2_mod(m: &[u64; 64], nl: usize, count: usize) -> (r: [u64; 64])
    requires
        1 <= nl <= 64,
        limbs(m@, nl as nat) > 1,
    ensures
        limbs(r@, nl as nat) == pow2(count as nat) as int % limbs(m@, nl as nat),
{
    let ghost n = nl as nat;
    let ghost mm = limbs(m@, n);
    let mut r = [0u64; 64];
    r[0] = 1;
    proof {
        lemma_limbs_one(r@, n);
        lemma2_to64();
        lemma_small_mod(1, mm as nat);
        lemma_limbs_bound(m@, n);
        lemma_wp(n);
        lemma_wp(n + 1);
    }
    let mut i: usize = 0;
    // ct: loop on the public count
    while i < count
        invariant
            1 <= nl <= 64,
            n == nl as nat,
            mm == limbs(m@, n),
            mm > 1,
            mm < wp(n),
            wp(n + 1) == wp(n) * 0x1_0000_0000_0000_0000,
            wp(n + 2) == wp(n + 1) * 0x1_0000_0000_0000_0000,
            i <= count,
            0 <= limbs(r@, n) < mm,
            limbs(r@, n) == pow2(i as nat) as int % mm,
        decreases count - i,
    {
        let mut t = [0u64; 66];
        let ghost rv = limbs(r@, n);
        proof {
            lemma_limbs_zero(t@, n + 2);
            lemma_mul_basics(rv);
            assert(wp(n + 2) > 2 * wp(n)) by(nonlinear_arith)
                requires wp(n + 1) == wp(n) * 0x1_0000_0000_0000_0000, wp(n + 2) == wp(n + 1) * 0x1_0000_0000_0000_0000, wp(n) > 0;
        }
        addmul(&mut t, 1, &r, nl);
        addmul(&mut t, 1, &r, nl);
        r = cond_sub(&t, m, nl);
        proof {
            let tv = limbs(t@, n + 2);
            assert(tv == 2 * rv);
            lemma_limbs_bound(r@, n);
            lemma_cond_is_mod(limbs(r@, n), tv, mm);
            lemma_double_mod(pow2(i as nat) as int, rv, mm);
            lemma_pow2_unfold(i as nat + 1);
        }
        i = i + 1;
    }
    r
}

pub(crate) proof fn lemma_limbs_one(s: Seq<u64>, n: nat)
    requires 1 <= n, s[0] == 1, forall|i: int| 1 <= i < n ==> s[i] == 0,
    ensures limbs(s, n) == 1,
    decreases n,
{
    lemma_wp(0);
    if n == 1 {
        assert(limbs(s, 0) == 0);
        lemma_mul_basics(1);
    } else {
        lemma_limbs_one(s, (n - 1) as nat);
        lemma_mul_basics(wp((n - 1) as nat));
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    fn xorshift(s: &mut u64) -> u64 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        *s
    }

    fn limb(x: u64) -> [u64; 64] {
        let mut a = [0u64; 64];
        a[0] = x;
        a
    }

    #[test]
    fn neg_inv64_kat() {
        assert_eq!(neg_inv64(1), u64::MAX);
        let mut s = 0x9e37_79b9_7f4a_7c15u64;
        let mut ms = vec![1, 3, u64::MAX];
        ms.extend((0..1000).map(|_| xorshift(&mut s) | 1));
        for m0 in ms {
            assert_eq!(m0.wrapping_mul(neg_inv64(m0)).wrapping_add(1), 0, "m0 = {m0:#x}");
        }
    }

    #[test]
    fn mont_mul_one_limb() {
        let mut s = 0x0123_4567_89ab_cdefu64;
        for _ in 0..1000 {
            let m = xorshift(&mut s) | 1;
            if m == 1 {
                continue;
            }
            let a = xorshift(&mut s);
            let b = xorshift(&mut s) % m;
            let mp = neg_inv64(m);
            let r = mont_mul_n(&limb(a), &limb(b), &limb(m), mp, 1);
            assert!(r[0] < m);
            let (mm, lhs) = (m as u128, ((r[0] as u128) << 64) % m as u128);
            assert_eq!(lhs, (a as u128 * b as u128) % mm, "a {a:#x} b {b:#x} m {m:#x}");
        }
    }

    #[test]
    fn select_picks_by_bit() {
        let (x, y) = (limb(7), limb(9));
        assert_eq!(select_n(1, &x, &y, 1)[0], 7);
        assert_eq!(select_n(0, &x, &y, 1)[0], 9);
    }

    #[test]
    fn pow2_mod_kat() {
        let mut s = 0xfeed_face_cafe_beefu64;
        for _ in 0..16 {
            let m = xorshift(&mut s) | 1;
            for count in 0..=127usize {
                let r = pow2_mod(&limb(m), 1, count);
                assert_eq!(r[0] as u128, (1u128 << count) % m as u128, "m {m:#x} count {count}");
            }
        }
    }

    #[test]
    fn limbs_be_round_trip() {
        let mut s = 0x1357_9bdf_0246_8aceu64;
        for nl in [32usize, 33, 64] {
            for k in [8 * nl, 8 * nl - 7] {
                let mut input = vec![0u8; 8 * nl];
                for b in input[8 * nl - k..].iter_mut() {
                    *b = xorshift(&mut s) as u8;
                }
                let l = limbs_from_be_n(&input, nl);
                assert_eq!(limbs_to_be_n(&l, nl, k), &input[8 * nl - k..], "nl {nl} k {k}");
            }
        }
    }

    #[test]
    fn pad_be_lengths() {
        assert_eq!(pad_be(&[1, 2], 4), [0, 0, 1, 2]);
        assert_eq!(pad_be(&[1, 2], 2), [1, 2]);
        assert_eq!(pad_be(&[0, 0, 1, 2], 2), [1, 2]);
        assert_eq!(pad_be(&[], 2), [0, 0]);
        assert!(pad_be(&[0], 0).is_empty());
    }
}
