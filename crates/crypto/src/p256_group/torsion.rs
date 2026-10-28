//! No 2-torsion on P-256: f(x) = x^3 - 3x + b has no root in GF(p).
//! At a root r, r^p == r (FLT) and r^p == g(r) for g = x^p mod f (computed in GF(p)[x]/f), so
//! g(r) - r == 0; the checked Bezout certificate u f + v (g - x) == 1 then evaluates to 0 == 1.
#![allow(non_snake_case)]
#[allow(unused_imports)]
use super::field::*;
#[allow(unused_imports)]
use super::nt::*;
#[allow(unused_imports)]
use super::torsion_cert::*;
#[allow(unused_imports)]
use crate::p256::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power::*;

verus! {

// ---------------------------------------------------------------------------------------------
// GF(p)[x] / f, f = x^3 - 3x + b (evaluable by `compute_only`: literal constants only)
// ---------------------------------------------------------------------------------------------

/// c0 + c1 x + c2 x^2 mod f.
pub(crate) struct Q2 {
    pub(crate) c0: int,
    pub(crate) c1: int,
    pub(crate) c2: int,
}

pub(crate) open spec fn X() -> Q2 {
    Q2 { c0: 0, c1: 1, c2: 0 }
}

pub(crate) open spec fn ONE() -> Q2 {
    Q2 { c0: 1, c1: 0, c2: 0 }
}

/// a b, reduced by x^3 == 3x - b and x^4 == 3x^2 - b x; d3, d4 are reduced first so every
/// intermediate stays below 2^600.
pub(crate) open spec fn qmul(a: Q2, b: Q2) -> Q2 {
    let d0 = a.c0 * b.c0;
    let d1 = a.c0 * b.c1 + a.c1 * b.c0;
    let d2 = a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0;
    let d3 = (a.c1 * b.c2 + a.c2 * b.c1) % P_LIT();
    let d4 = (a.c2 * b.c2) % P_LIT();
    Q2 {
        c0: (d0 - B_LIT() * d3) % P_LIT(),
        c1: (d1 + 3 * d3 - B_LIT() * d4) % P_LIT(),
        c2: (d2 + 3 * d4) % P_LIT(),
    }
}

/// a^e by square-and-multiply on e / 2.
pub(crate) open spec fn qpow(a: Q2, e: nat) -> Q2
    decreases e,
{
    if e == 0 {
        ONE()
    } else {
        let s = qpow(a, e / 2);
        let s2 = qmul(s, s);
        if e % 2 == 0 {
            s2
        } else {
            qmul(s2, a)
        }
    }
}

/// `qpow` resumed from s == a^(e >> k) through the low k bits of e (one chunk).
pub(crate) open spec fn qpow_ext(s: Q2, a: Q2, e: nat, k: nat) -> Q2
    decreases k,
{
    if k == 0 {
        s
    } else {
        let h = qpow_ext(s, a, e / 2, (k - 1) as nat);
        let s2 = qmul(h, h);
        if e % 2 == 0 {
            s2
        } else {
            qmul(s2, a)
        }
    }
}

/// a(r) (over the integers).
pub(crate) open spec fn qev(a: Q2, r: int) -> int {
    a.c0 + a.c1 * r + a.c2 * (r * r)
}

/// The coefficients of u f + v (g - x), u = u.0 + u.1 x, all 0 mod p except the constant 1.
pub(crate) open spec fn bez_ok(u: (int, int), v: Q2, g: Q2) -> bool {
    let h0 = g.c0;
    let h1 = g.c1 - 1;
    let h2 = g.c2;
    (u.0 * B_LIT() + v.c0 * h0) % P_LIT() == 1 && (u.1 * B_LIT() - 3 * u.0 + v.c0 * h1 + v.c1
        * h0) % P_LIT() == 0 && (-3 * u.1 + v.c0 * h2 + v.c1 * h1 + v.c2 * h0) % P_LIT() == 0 && (
    u.0 + v.c1 * h2 + v.c2 * h1) % P_LIT() == 0 && (u.1 + v.c2 * h2) % P_LIT() == 0
}

/// Exponent-prefix split of `qpow`.
pub(crate) proof fn lemma_qpow_ext(a: Q2, e: nat, k: nat)
    requires
        shr(e, k) > 0,
    ensures
        qpow(a, e) == qpow_ext(qpow(a, shr(e, k)), a, e, k),
    decreases k,
{
    hide(qmul);
    if k > 0 {
        lemma_shr_pos(e, k);
        lemma_qpow_ext(a, e / 2, (k - 1) as nat);
    }
}

// ---------------------------------------------------------------------------------------------
// Polynomial identities and mod steps
// ---------------------------------------------------------------------------------------------

/// (z + x k) == (z + (x mod p) k) mod p.
proof fn lemma_mod_term(z: int, x: int, k: int, p: int)
    requires
        p > 0,
    ensures
        (z + x * k) % p == (z + (x % p) * k) % p,
{
    lemma_mul_mod_noop_left(x, k, p);
    lemma_add_mod_noop(z, x * k, p);
    lemma_add_mod_noop(z, (x % p) * k, p);
}

/// (z + k m) == z mod p when m == 0 mod p.
proof fn lemma_mod_drop(z: int, k: int, m: int, p: int)
    requires
        p > 0,
        m % p == 0,
    ensures
        (z + k * m) % p == z % p,
{
    lemma_mul_mod_noop_right(k, m, p);
    lemma_small_mod(0, p as nat);
    lemma_add_mod_noop(z, k * m, p);
    lemma_mod_twice(z, p);
}

/// (z + m k) == z mod p when m == 0 mod p.
proof fn lemma_mod_drop_l(z: int, m: int, k: int, p: int)
    requires
        p > 0,
        m % p == 0,
    ensures
        (z + m * k) % p == z % p,
{
    lemma_mul_is_commutative(m, k);
    lemma_mod_drop(z, k, m, p);
}

// Products are distributed one step at a time: Z3's nonlinear_arith exceeds --rlimit 4 on
// these identities whole.

proof fn lemma_dist3(x: int, y: int, z: int, m: int)
    ensures
        (x + y + z) * m == x * m + y * m + z * m,
{
    lemma_mul_is_distributive_add_other_way(m, x + y, z);
    lemma_mul_is_distributive_add_other_way(m, x, y);
}

/// (a m)(b n) == (a b)(m n).
proof fn lemma_mono(a: int, m: int, b: int, n: int)
    ensures
        (a * m) * (b * n) == (a * b) * (m * n),
{
    lemma_mul_is_associative(a, m, b * n);
    lemma_mul_is_associative(m, b, n);
    lemma_mul_is_commutative(m, b);
    lemma_mul_is_associative(b, m, n);
    lemma_mul_is_associative(a, b, m * n);
}

/// (a m) b == (a b) m.
proof fn lemma_swap(a: int, m: int, b: int)
    ensures
        (a * m) * b == (a * b) * m,
{
    lemma_mul_is_associative(a, m, b);
    lemma_mul_is_commutative(m, b);
    lemma_mul_is_associative(a, b, m);
}

/// r^i r^j == r^(i + j) for the monomials used here.
proof fn lemma_monos(r: int)
    ensures
        r * (r * r) == r * r * r,
        (r * r) * (r * r) == r * r * r * r,
        r * (r * r * r) == r * r * r * r,
{
    lemma_mul_is_commutative(r, r * r);
    lemma_mul_is_associative(r * r, r, r);
    lemma_mul_is_commutative(r, r * r * r);
}

/// Product of two quadratics, by monomial.
proof fn lemma_qq_expand(a0: int, a1: int, a2: int, b0: int, b1: int, b2: int, r: int)
    ensures
        (a0 + a1 * r + a2 * (r * r)) * (b0 + b1 * r + b2 * (r * r)) == a0 * b0 + (a0 * b1 + a1
            * b0) * r + (a0 * b2 + a1 * b1 + a2 * b0) * (r * r) + (a1 * b2 + a2 * b1) * (r * r
            * r) + (a2 * b2) * (r * r * r * r),
{
    let s = r * r;
    let t = r * r * r;
    let bp = b0 + b1 * r + b2 * s;
    lemma_monos(r);
    lemma_dist3(a0, a1 * r, a2 * s, bp);
    // a0 bp
    lemma_mul_is_distributive_add(a0, b0 + b1 * r, b2 * s);
    lemma_mul_is_distributive_add(a0, b0, b1 * r);
    lemma_mul_is_associative(a0, b1, r);
    lemma_mul_is_associative(a0, b2, s);
    // (a1 r) bp
    lemma_mul_is_distributive_add(a1 * r, b0 + b1 * r, b2 * s);
    lemma_mul_is_distributive_add(a1 * r, b0, b1 * r);
    lemma_swap(a1, r, b0);
    lemma_mono(a1, r, b1, r);
    lemma_mono(a1, r, b2, s);
    // (a2 s) bp
    lemma_mul_is_distributive_add(a2 * s, b0 + b1 * r, b2 * s);
    lemma_mul_is_distributive_add(a2 * s, b0, b1 * r);
    lemma_swap(a2, s, b0);
    lemma_mono(a2, s, b1, r);
    lemma_mul_is_commutative(s, r);
    lemma_mono(a2, s, b2, s);
    // the grouped coefficients
    lemma_mul_is_distributive_add_other_way(r, a0 * b1, a1 * b0);
    lemma_dist3(a0 * b2, a1 * b1, a2 * b0, s);
    lemma_mul_is_distributive_add_other_way(t, a1 * b2, a2 * b1);
}

/// (y0 + y1 r) f(r) by monomial, f = x^3 - 3x + b.
proof fn lemma_lf_expand(y0: int, y1: int, r: int)
    ensures
        (y0 + y1 * r) * (r * r * r - 3 * r + B_LIT()) == y0 * B_LIT() + (y1 * B_LIT() - 3 * y0) * r
            + (-3 * y1) * (r * r) + y0 * (r * r * r) + y1 * (r * r * r * r),
{
    let t = r * r * r;
    let b = B_LIT();
    lemma_monos(r);
    let y = y0 + y1 * r;
    assert(r * r * r - 3 * r + b == t + (-3) * r + b);
    lemma_mul_is_distributive_add(y, t + (-3) * r, b);
    lemma_mul_is_distributive_add(y, t, (-3) * r);
    // y t
    lemma_mul_is_distributive_add_other_way(t, y0, y1 * r);
    lemma_mul_is_associative(y1, r, t);
    // y (-3 r)
    lemma_mul_is_distributive_add_other_way((-3) * r, y0, y1 * r);
    lemma_mul_is_associative(y0, -3, r);
    lemma_mono(y1, r, -3, r);
    // y b
    lemma_mul_is_distributive_add_other_way(b, y0, y1 * r);
    lemma_swap(y1, r, b);
    // the grouped coefficient
    lemma_mul_is_distributive_add_other_way(r, y1 * b, -3 * y0);
}

/// The reduction identity: d0 + d1 r + .. + e4 r^4 == c(r) + (e3 + e4 r) f(r).
proof fn lemma_reduce_expand(d0: int, d1: int, d2: int, e3: int, e4: int, r: int)
    ensures
        d0 + d1 * r + d2 * (r * r) + e3 * (r * r * r) + e4 * (r * r * r * r) == (d0 - B_LIT()
            * e3) + (d1 + 3 * e3 - B_LIT() * e4) * r + (d2 + 3 * e4) * (r * r) + (e3 + e4 * r) * (
        r * r * r - 3 * r + B_LIT()),
{
    let b = B_LIT();
    let s = r * r;
    lemma_lf_expand(e3, e4, r);
    lemma_mul_is_commutative(b, e3);
    lemma_mul_is_commutative(b, e4);
    // the r terms
    lemma_mul_is_distributive_sub_other_way(r, d1 + 3 * e3, b * e4);
    lemma_mul_is_distributive_add_other_way(r, d1, 3 * e3);
    lemma_mul_is_distributive_sub_other_way(r, e4 * b, 3 * e3);
    // the r^2 terms
    lemma_mul_is_distributive_add_other_way(s, d2, 3 * e4);
    lemma_mul_is_associative(3, e4, s);
    lemma_mul_is_associative(-3, e4, s);
}

/// The Bezout identity's left side, by monomial.
proof fn lemma_bez_expand(
    u0: int,
    u1: int,
    v0: int,
    v1: int,
    v2: int,
    h0: int,
    h1: int,
    h2: int,
    r: int,
)
    ensures
        (u0 + u1 * r) * (r * r * r - 3 * r + B_LIT()) + (v0 + v1 * r + v2 * (r * r)) * (h0 + h1
            * r + h2 * (r * r)) == (u0 * B_LIT() + v0 * h0) + (u1 * B_LIT() - 3 * u0 + v0 * h1
            + v1 * h0) * r + (-3 * u1 + v0 * h2 + v1 * h1 + v2 * h0) * (r * r) + (u0 + v1 * h2
            + v2 * h1) * (r * r * r) + (u1 + v2 * h2) * (r * r * r * r),
{
    let s = r * r;
    let t = r * r * r;
    let w = r * r * r * r;
    lemma_qq_expand(v0, v1, v2, h0, h1, h2, r);
    lemma_lf_expand(u0, u1, r);
    lemma_mul_is_distributive_add_other_way(r, u1 * B_LIT() - 3 * u0, v0 * h1 + v1 * h0);
    lemma_mul_is_distributive_add_other_way(s, -3 * u1, v0 * h2 + v1 * h1 + v2 * h0);
    lemma_mul_is_distributive_add_other_way(t, u0, v1 * h2 + v2 * h1);
    lemma_mul_is_distributive_add_other_way(w, u1, v2 * h2);
}

/// The reduced coefficients evaluate like the unreduced ones, mod p.
proof fn lemma_qev_mod(c0: int, c1: int, c2: int, r: int, p: int)
    requires
        p > 0,
    ensures
        (c0 % p + (c1 % p) * r + (c2 % p) * (r * r)) % p == (c0 + c1 * r + c2 * (r * r)) % p,
{
    lemma_mod_term(c0 % p + (c1 % p) * r, c2, r * r, p);
    lemma_mod_term(c0 % p + c2 * (r * r), c1, r, p);
    lemma_mod_term(c1 * r + c2 * (r * r), c0, 1, p);
}

// ---------------------------------------------------------------------------------------------
// Evaluation at a root of f
// ---------------------------------------------------------------------------------------------

pub(crate) proof fn lemma_qmul_ev(a: Q2, b: Q2, r: int)
    requires
        fmod(r * r * r - 3 * r + p256_b()) == 0,
    ensures
        fmod(qev(qmul(a, b), r)) == fmod(qev(a, r) * qev(b, r)),
{
    lemma_group_consts();
    let p = P_LIT();
    let bb = B_LIT();
    let s = r * r;
    let t = r * r * r;
    let w = r * r * r * r;
    let d0 = a.c0 * b.c0;
    let d1 = a.c0 * b.c1 + a.c1 * b.c0;
    let d2 = a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0;
    let d3 = a.c1 * b.c2 + a.c2 * b.c1;
    let d4 = a.c2 * b.c2;
    let e3 = d3 % p;
    let e4 = d4 % p;
    let c0 = d0 - bb * e3;
    let c1 = d1 + 3 * e3 - bb * e4;
    let c2 = d2 + 3 * e4;
    // a(r) b(r) == d(r) exactly
    lemma_qq_expand(a.c0, a.c1, a.c2, b.c0, b.c1, b.c2, r);
    // d(r) == d0 + .. + e3 r^3 + e4 r^4 (mod p)
    lemma_mod_term(d0 + d1 * r + d2 * s + d3 * t, d4, w, p);
    lemma_mod_term(d0 + d1 * r + d2 * s + e4 * w, d3, t, p);
    // == c(r) + (e3 + e4 r) f(r) == c(r) (mod p)
    lemma_reduce_expand(d0, d1, d2, e3, e4, r);
    lemma_mod_drop(c0 + c1 * r + c2 * s, e3 + e4 * r, t - 3 * r + bb, p);
    // and c(r) == qev(qmul(a, b), r) (mod p)
    lemma_qev_mod(c0, c1, c2, r, p);
}

/// Squaring step of `lemma_qpow_ev`.
proof fn lemma_qpow_sq(h: Q2, k: nat, r: int)
    requires
        fmod(r * r * r - 3 * r + p256_b()) == 0,
        fmod(qev(h, r)) == fmod(pow(r, k)),
    ensures
        fmod(qev(qmul(h, h), r)) == fmod(pow(r, k + k)),
{
    let p = p256_p();
    lemma_qmul_ev(h, h, r);
    // h(r) h(r) == r^k r^k == r^(2k) (mod p)
    lemma_mul_mod_noop_general(qev(h, r), qev(h, r), p);
    lemma_mul_mod_noop_general(pow(r, k), pow(r, k), p);
    lemma_pow_adds(r, k, k);
}

/// Multiply-by-x step of `lemma_qpow_ev`.
proof fn lemma_qpow_x(s: Q2, j: nat, r: int)
    requires
        fmod(r * r * r - 3 * r + p256_b()) == 0,
        fmod(qev(s, r)) == fmod(pow(r, j)),
    ensures
        fmod(qev(qmul(s, X()), r)) == fmod(pow(r, j + 1)),
{
    let p = p256_p();
    lemma_qmul_ev(s, X(), r);
    assert(qev(X(), r) == r);
    // s(r) r == r^j r == r^(j + 1) (mod p)
    lemma_mul_mod_noop_left(qev(s, r), r, p);
    lemma_mul_mod_noop_left(pow(r, j), r, p);
    lemma_pow_adds(r, j, 1);
    lemma_pow1(r);
}

pub(crate) proof fn lemma_qpow_ev(e: nat, r: int)
    requires
        fmod(r * r * r - 3 * r + p256_b()) == 0,
    ensures
        fmod(qev(qpow(X(), e), r)) == fmod(pow(r, e)),
    decreases e,
{
    hide(qmul);
    if e == 0 {
        lemma_pow0(r);
        lemma_mul_basics(r);
        lemma_mul_basics(r * r);
    } else {
        let k = e / 2;
        let h = qpow(X(), k);
        lemma_qpow_ev(k, r);
        lemma_qpow_sq(h, k, r);
        if e % 2 == 1 {
            lemma_qpow_x(qmul(h, h), k + k, r);
        }
    }
}

/// x^3 - 3x + b has no root mod p.
pub(crate) proof fn lemma_no_2_torsion(x: int)
    ensures
        fmod(x * x * x - 3 * x + p256_b()) != 0,
{
    lemma_group_consts();
    let p = p256_p();
    let b = p256_b();
    if fmod(x * x * x - 3 * x + b) == 0 {
        // x != 0: else f(x) == b (mod p), and 0 < b < p
        if fmod(x) == 0 {
            lemma_mod_drop(-3 * x + b, x * x, x, p);
            lemma_mod_drop(b, -3, x, p);
            lemma_small_mod(b as nat, p as nat);
            assert(false);
        }
        // x^p == x (FLT) and x^p == g(x), so g(x) == x (mod p)
        let pp = p as nat;
        lemma_flt_p(x);
        lemma_pow_adds(x, (pp - 1) as nat, 1);
        lemma_pow1(x);
        lemma_mul_mod_noop_left(pow(x, (pp - 1) as nat), x, p);
        lemma_qpow_ev(pp, x);
        lemma_xp_mod_f();
        let g = XP_POLY();
        assert(fmod(qev(g, x)) == fmod(x));
        // h = g - x vanishes at x
        let h1 = g.c1 - 1;
        lemma_mul_is_distributive_sub_other_way(x, g.c1, 1);
        let hx = g.c0 + h1 * x + g.c2 * (x * x);
        assert(hx == qev(g, x) - x);
        lemma_sub_mod_noop(qev(g, x), x, p);
        assert(fmod(hx) == 0);
        // u(x) f(x) + v(x) h(x) == 1 (Bezout, mod p), but both terms are 0 (mod p)
        lemma_bezout_cert();
        let u = U();
        let v = V();
        let e0 = u.0 * b + v.c0 * g.c0;
        let e1 = u.1 * b - 3 * u.0 + v.c0 * h1 + v.c1 * g.c0;
        let e2 = -3 * u.1 + v.c0 * g.c2 + v.c1 * h1 + v.c2 * g.c0;
        let e3 = u.0 + v.c1 * g.c2 + v.c2 * h1;
        let e4 = u.1 + v.c2 * g.c2;
        let s = x * x;
        let t = x * x * x;
        let w = x * x * x * x;
        lemma_bez_expand(u.0, u.1, v.c0, v.c1, v.c2, g.c0, h1, g.c2, x);
        lemma_mod_drop_l(e0 + e1 * x + e2 * s + e3 * t, e4, w, p);
        lemma_mod_drop_l(e0 + e1 * x + e2 * s, e3, t, p);
        lemma_mod_drop_l(e0 + e1 * x, e2, s, p);
        lemma_mod_drop_l(e0, e1, x, p);
        let fx = x * x * x - 3 * x + b;
        let ux = u.0 + u.1 * x;
        let vx = v.c0 + v.c1 * x + v.c2 * s;
        lemma_mod_drop(vx * hx, ux, fx, p);
        lemma_mod_drop(0, vx, hx, p);
        assert(false);
    }
}

} // verus!
