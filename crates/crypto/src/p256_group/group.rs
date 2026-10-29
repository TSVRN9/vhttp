//! Closure and associativity of the frozen spec's `point_add` (SEC 1 v2 §2.2.1 rules 1-5, a = -3).
//! Curve points are encoded as RCB projective triples; `point_add`'s case split is mapped onto the
//! complete law (`rcb`) branch by branch through `rcb`'s correspondence identities, and
//! associativity is `assoc_id`'s curve identity decoded.
#[allow(unused_imports)]
use super::assoc_id::*;
#[allow(unused_imports)]
use super::field::*;
#[allow(unused_imports)]
use super::rcb::*;
#[allow(unused_imports)]
use super::red::*;
#[allow(unused_imports)]
use super::torsion::*;
#[allow(unused_imports)]
use crate::p256::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Encoding
// ---------------------------------------------------------------------------------------------

pub open spec fn curve_pt(p: SpecPoint) -> bool {
    p is Infinity || (p is Affine && on_curve(p->0, p->1))
}

/// O as (0 : 1 : 0), (x, y) as (x : y : 1).
pub(crate) open spec fn enc(p: SpecPoint) -> Proj {
    match p {
        SpecPoint::Infinity => Proj { x: 0, y: 1, z: 0 },
        SpecPoint::Affine(x, y) => Proj { x, y, z: 1 },
    }
}

pub(crate) open spec fn dec(a: Proj) -> SpecPoint {
    if fmod(a.z) != 0 {
        SpecPoint::Affine(fmod(a.x * finv(a.z)), fmod(a.y * finv(a.z)))
    } else {
        SpecPoint::Infinity
    }
}

/// A reduced triple that is a curve point or (0 : y : 0) with y != 0.
pub(crate) open spec fn valid(a: Proj) -> bool {
    &&& 0 <= a.x < p256_p() && 0 <= a.y < p256_p() && 0 <= a.z < p256_p()
    &&& (fmod(a.z) != 0 && curve_pt(dec(a))) || (fmod(a.z) == 0 && fmod(a.x) == 0 && fmod(a.y) != 0)
}

pub(crate) open spec fn neg(p: SpecPoint) -> SpecPoint {
    match p {
        SpecPoint::Infinity => SpecPoint::Infinity,
        SpecPoint::Affine(x, y) => SpecPoint::Affine(x, P_LIT() - y),
    }
}

// ---------------------------------------------------------------------------------------------
// GF(p) glue: congruences, cancellation, division
// ---------------------------------------------------------------------------------------------

proof fn lemma_fm(a: int, b: int)
    ensures
        fm(a, b) == fmod(a * b),
        fmod(fm(a, b)) == fmod(a * b),
{
    lemma_md(a * b);
}

proof fn lemma_cg_sub(a: int, b: int, c: int, d: int)
    requires
        fmod(a) == fmod(c),
        fmod(b) == fmod(d),
    ensures
        fmod(a - b) == fmod(c - d),
{
    lemma_group_consts();
    lemma_sub_mod_noop(a, b, p256_p());
    lemma_sub_mod_noop(c, d, p256_p());
}

proof fn lemma_sub0(a: int, b: int)
    ensures
        fmod(a - b) == 0 <==> fmod(a) == fmod(b),
{
    lemma_group_consts();
    lemma_sub_mod_noop(a, b, p256_p());
    lemma_mod_bound(a, p256_p());
    lemma_mod_bound(b, p256_p());
}

proof fn lemma_small(x: int)
    requires
        0 <= x < p256_p(),
    ensures
        fmod(x) == x,
{
    lemma_group_consts();
    lemma_small_mod(x as nat, p256_p() as nat);
}

proof fn lemma_mod_range(x: int)
    ensures
        0 <= fmod(x) < p256_p(),
        fmod(fmod(x)) == fmod(x),
{
    lemma_md(x);
    lemma_mod_bound(x, P_LIT());
}

/// a == 0 (mod p) makes every multiple 0.
proof fn lemma_mul0(a: int, b: int)
    requires
        fmod(a) == 0,
    ensures
        fmod(a * b) == 0,
        fmod(b * a) == 0,
{
    lemma_group_consts();
    lemma_mul_mod_noop_left(a, b, p256_p());
    lemma_mul_is_commutative(a, b);
}

proof fn lemma_nz_mul(a: int, b: int)
    requires
        fmod(a) != 0,
        fmod(b) != 0,
    ensures
        fmod(a * b) != 0,
{
    if fmod(a * b) == 0 {
        lemma_no_zero_div(a, b);
    }
}

proof fn lemma_cancel(a: int, b: int, c: int)
    requires
        fmod(a * c) == fmod(b * c),
        fmod(c) != 0,
    ensures
        fmod(a) == fmod(b),
{
    lemma_mul_is_distributive_sub_other_way(c, a, b);
    lemma_sub0(a * c, b * c);
    lemma_no_zero_div(a - b, c);
    lemma_sub0(a, b);
}

/// a == b c with c != 0 gives a / c == b.
proof fn lemma_div(a: int, b: int, c: int)
    requires
        fmod(a) == fmod(b * c),
        fmod(c) != 0,
    ensures
        fmod(a * finv(c)) == fmod(b),
{
    hide(finv);
    let i = finv(c);
    lemma_finv_mul(c);
    lemma_cg_mul(a, i, b * c, i);
    lemma_mul_is_associative(b, c, i);
    lemma_small(1);
    lemma_cg_mul(b, c * i, b, 1);
}

/// (a / c) c == a.
proof fn lemma_undiv(a: int, c: int)
    requires
        fmod(c) != 0,
    ensures
        fmod(fmod(a * finv(c)) * c) == fmod(a),
{
    hide(finv);
    let i = finv(c);
    lemma_finv_mul(c);
    lemma_mod_range(a * i);
    lemma_cg_mul(fmod(a * i), c, a * i, c);
    lemma_mul_is_associative(a, i, c);
    lemma_mul_is_commutative(i, c);
    lemma_small(1);
    lemma_cg_mul(a, c * i, a, 1);
}

/// Two reduced values equal mod p are equal.
proof fn lemma_range_eq(x: int, y: int)
    requires
        0 <= x < p256_p(),
        0 <= y < p256_p(),
        fmod(x) == fmod(y),
    ensures
        x == y,
{
    lemma_small(x);
    lemma_small(y);
}

// Monomial reorders over int (one `nonlinear_arith` normalisation each, no `%`; the pattern of
// rcb::lemma_rcb_inf_l). Distribution over sums is by hand-applied vstd lemmas below.
proof fn lemma_nl_sq(a: int, b: int)
    ensures
        (a * b) * (a * b) == (a * a) * (b * b),
{
    assert((a * b) * (a * b) == (a * a) * (b * b)) by (nonlinear_arith);
}

proof fn lemma_nl_cube(a: int, b: int)
    ensures
        ((a * b) * (a * b)) * (a * b) == ((a * a) * a) * (b * (b * b)),
{
    assert(((a * b) * (a * b)) * (a * b) == ((a * a) * a) * (b * (b * b))) by (nonlinear_arith);
}

proof fn lemma_nl_ab3(a: int, b: int)
    ensures
        (a * b) * (b * b) == a * (b * (b * b)),
{
    assert((a * b) * (b * b) == a * (b * (b * b))) by (nonlinear_arith);
}

proof fn lemma_nl_swap(a: int, b: int, c: int, d: int)
    ensures
        (a * b) * (c * d) == (a * d) * (b * c),
{
    assert((a * b) * (c * d) == (a * d) * (b * c)) by (nonlinear_arith);
}

proof fn lemma_nl_rot(v: int, d: int, z: int)
    ensures
        (v * d) * z == (v * z) * d,
{
    assert((v * d) * z == (v * z) * d) by (nonlinear_arith);
}

proof fn lemma_nl_clo(a: int, c: int, x: int, b: int, k: int)
    ensures
        a * k - (c * k - x * k + b * k) == (a - (c - x + b)) * k,
{
    lemma_mul_is_distributive_sub_other_way(k, a, c - x + b);
    lemma_mul_is_distributive_add_other_way(k, c - x, b);
    lemma_mul_is_distributive_sub_other_way(k, c, x);
}

// ---------------------------------------------------------------------------------------------
// Chord / tangent decoding (shared by the x1 != x2 and doubling branches)
// ---------------------------------------------------------------------------------------------

/// `rcb::chord` and `rcb::dbl` both have this shape: d2 = d^2, d3 = d^3,
/// xn = ln^2 - sm d2, yn = ln (x0 d2 - xn) - y0 d3.
pub(crate) open spec fn ch_ok(c: Ch<int>, d: int, ln: int, sm: int, x0: int, y0: int) -> bool {
    &&& c.d2 == fm(d, d)
    &&& c.d3 == fm(c.d2, d)
    &&& c.xn == fm(ln, ln) - fm(sm, c.d2)
    &&& c.yn == fm(ln, fm(x0, c.d2) - c.xn) - fm(y0, c.d3)
}

/// point_add's x3 and y3 for slope lam.
pub(crate) open spec fn ch_x3(lam: int, sm: int) -> int {
    fmod(lam * lam - sm)
}

pub(crate) open spec fn ch_y3(lam: int, x0: int, y0: int, x3: int) -> int {
    fmod(lam * (x0 - x3) - y0)
}

proof fn lemma_ch_x(c: Ch<int>, d: int, ln: int, sm: int, x0: int, y0: int, lam: int)
    requires
        ch_ok(c, d, ln, sm, x0, y0),
        fmod(lam * d) == fmod(ln),
    ensures
        fmod(ch_x3(lam, sm) * c.d2) == fmod(c.xn),
{
    let x3 = ch_x3(lam, sm);
    let l2 = lam * lam - sm;
    lemma_mod_range(l2);
    lemma_fm(d, d);
    lemma_cg_mul(x3, c.d2, l2, d * d);
    lemma_mul_is_distributive_sub_other_way(d * d, lam * lam, sm);
    lemma_nl_sq(lam, d);
    lemma_cg_mul(lam * d, lam * d, ln, ln);
    lemma_fm(ln, ln);
    lemma_cg_mul(sm, d * d, sm, c.d2);
    lemma_fm(sm, c.d2);
    lemma_cg_sub((lam * d) * (lam * d), sm * (d * d), fm(ln, ln), fm(sm, c.d2));
}

proof fn lemma_ch_y(c: Ch<int>, d: int, ln: int, sm: int, x0: int, y0: int, lam: int)
    requires
        ch_ok(c, d, ln, sm, x0, y0),
        fmod(lam * d) == fmod(ln),
        fmod(ch_x3(lam, sm) * c.d2) == fmod(c.xn),
    ensures
        fmod(ch_y3(lam, x0, y0, ch_x3(lam, sm)) * c.d3) == fmod(c.yn),
{
    let x3 = ch_x3(lam, sm);
    let y3 = ch_y3(lam, x0, y0, x3);
    let (dd, e) = (c.d2, c.d3);
    let u = x0 - x3;
    let m = lam * u - y0;
    lemma_mod_range(m);
    lemma_fm(dd, d);
    // y3 e == (lam u - y0)(dd d) == (lam d)(u dd) - y0 (dd d)
    lemma_cg_mul(y3, e, m, dd * d);
    lemma_mul_is_distributive_sub_other_way(dd * d, lam * u, y0);
    lemma_nl_swap(lam, u, dd, d);
    // u dd == x0 dd - x3 dd == fm(x0, dd) - xn
    lemma_mul_is_distributive_sub_other_way(dd, x0, x3);
    lemma_fm(x0, dd);
    lemma_cg_sub(x0 * dd, x3 * dd, fm(x0, dd), c.xn);
    lemma_cg_mul(lam * d, u * dd, ln, fm(x0, dd) - c.xn);
    lemma_fm(ln, fm(x0, dd) - c.xn);
    lemma_cg_mul(y0, dd * d, y0, e);
    lemma_fm(y0, e);
    lemma_cg_sub(
        (lam * d) * (u * dd),
        y0 * (dd * d),
        fm(ln, fm(x0, dd) - c.xn),
        fm(y0, e),
    );
}

/// From an identity n D == N z and v D == N: n / z == v.
proof fn lemma_dec_coord(n: int, z: int, v: int, dd: int, nn: int)
    requires
        fmod(fm(n, dd) - fm(nn, z)) == 0,
        fmod(v * dd) == fmod(nn),
        fmod(dd) != 0,
        fmod(z) != 0,
        0 <= v < p256_p(),
    ensures
        fmod(n * finv(z)) == v,
{
    hide(finv);
    lemma_sub0(fm(n, dd), fm(nn, z));
    lemma_fm(n, dd);
    lemma_fm(nn, z);
    lemma_cg_mul(nn, z, v * dd, z);
    lemma_nl_rot(v, dd, z);
    lemma_cancel(n, v * z, dd);
    lemma_div(n, v, z);
    lemma_small(v);
}

/// d3^2 == d2^3.
proof fn lemma_d3sq(d: int, dd: int, e: int)
    requires
        dd == fm(d, d),
        e == fm(dd, d),
    ensures
        fmod(e * e) == fmod(dd * (dd * dd)),
{
    lemma_fm(d, d);
    lemma_fm(dd, d);
    lemma_cg_mul(e, e, dd * d, dd * d);
    lemma_nl_sq(dd, d);
    lemma_cg_mul(dd * dd, d * d, dd * dd, dd);
    lemma_mul_is_associative(dd, dd, dd);
}

/// The four terms of clo(xn, yn, D) with xn == X D, yn == Y E, E^2 == D^3, as multiples of D^3.
proof fn lemma_clo_terms(d: int, dd: int, e: int, xv: int, yv: int, xn: int, yn: int)
    requires
        dd == fm(d, d),
        e == fm(dd, d),
        fmod(xv * dd) == fmod(xn),
        fmod(yv * e) == fmod(yn),
    ensures
        fmod(fm(yn, yn)) == fmod((yv * yv) * (dd * (dd * dd))),
        fmod(fm(fm(xn, xn), xn)) == fmod(((xv * xv) * xv) * (dd * (dd * dd))),
        fmod(3 * fm(xn, fm(dd, dd))) == fmod((3 * xv) * (dd * (dd * dd))),
        fmod(fm(B_LIT(), fm(dd, fm(dd, dd)))) == fmod(B_LIT() * (dd * (dd * dd))),
{
    let k = dd * (dd * dd);
    let (xd, ye) = (xv * dd, yv * e);
    // yn^2
    lemma_fm(yn, yn);
    lemma_cg_mul(yn, yn, ye, ye);
    lemma_nl_sq(yv, e);
    lemma_d3sq(d, dd, e);
    lemma_cg_mul(yv * yv, e * e, yv * yv, k);
    // xn^3
    lemma_fm(xn, xn);
    lemma_fm(fm(xn, xn), xn);
    lemma_cg_mul(xn, xn, xd, xd);
    lemma_cg_mul(fm(xn, xn), xn, xd * xd, xd);
    lemma_nl_cube(xv, dd);
    // 3 xn D^2
    lemma_fm(dd, dd);
    lemma_fm(xn, fm(dd, dd));
    lemma_cg_mul(xn, fm(dd, dd), xd, dd * dd);
    lemma_nl_ab3(xv, dd);
    lemma_cg_mul(3, fm(xn, fm(dd, dd)), 3, xv * k);
    lemma_mul_is_associative(3, xv, k);
    // b D^3
    lemma_fm(dd, fm(dd, dd));
    lemma_cg_mul(dd, fm(dd, dd), dd, dd * dd);
    lemma_fm(B_LIT(), fm(dd, fm(dd, dd)));
    lemma_cg_mul(B_LIT(), fm(dd, fm(dd, dd)), B_LIT(), k);
}

proof fn lemma_ch_clo(c: Ch<int>, d: int, xv: int, yv: int)
    requires
        c.d2 == fm(d, d),
        c.d3 == fm(c.d2, d),
        fmod(d) != 0,
        fmod(xv * c.d2) == fmod(c.xn),
        fmod(yv * c.d3) == fmod(c.yn),
        fmod(clo(c.xn, c.yn, c.d2)) == 0,
        0 <= xv < p256_p(),
        0 <= yv < p256_p(),
    ensures
        on_curve(xv, yv),
{
    lemma_group_consts();
    let dd = c.d2;
    let k = dd * (dd * dd);
    lemma_clo_terms(d, dd, c.d3, xv, yv, c.xn, c.yn);
    let (t1, t2, t3, t4) = (
        fm(c.yn, c.yn),
        fm(fm(c.xn, c.xn), c.xn),
        3 * fm(c.xn, fm(dd, dd)),
        fm(B_LIT(), fm(dd, fm(dd, dd))),
    );
    let (a, cc, x3, bk) = (yv * yv, (xv * xv) * xv, 3 * xv, B_LIT() * k);
    lemma_cg_sub(t2, t3, cc * k, x3 * k);
    lemma_cg_add(t2 - t3, t4, cc * k - x3 * k, bk);
    lemma_cg_sub(t1, t2 - t3 + t4, a * k, cc * k - x3 * k + bk);
    assert(clo(c.xn, c.yn, dd) == t1 - (t2 - t3 + t4));
    let ecurve = a - (cc - x3 + B_LIT());
    lemma_nl_clo(a, cc, x3, B_LIT(), k);
    lemma_fm(d, d);
    lemma_nz_mul(d, d);
    lemma_nz_mul(dd, dd);
    lemma_nz_mul(dd, dd * dd);
    lemma_no_zero_div(ecurve, k);
    lemma_sub0(a, cc - x3 + B_LIT());
}

/// Decoding a chord/tangent RCB output: dec(o) is point_add's (x3, y3), on the curve.
proof fn lemma_ch_dec(o: Proj, c: Ch<int>, d: int, ln: int, sm: int, x0: int, y0: int, lam: int)
    requires
        ch_ok(c, d, ln, sm, x0, y0),
        fmod(d) != 0,
        fmod(o.z) != 0,
        fmod(lam * d) == fmod(ln),
        fmod(fm(o.x, c.d2) - fm(c.xn, o.z)) == 0,
        fmod(fm(o.y, c.d3) - fm(c.yn, o.z)) == 0,
        fmod(clo(c.xn, c.yn, c.d2)) == 0,
    ensures
        dec(o) == SpecPoint::Affine(ch_x3(lam, sm), ch_y3(lam, x0, y0, ch_x3(lam, sm))),
        on_curve(ch_x3(lam, sm), ch_y3(lam, x0, y0, ch_x3(lam, sm))),
{
    hide(finv);
    let x3 = ch_x3(lam, sm);
    let y3 = ch_y3(lam, x0, y0, x3);
    lemma_mod_range(lam * lam - sm);
    lemma_mod_range(lam * (x0 - x3) - y0);
    lemma_ch_x(c, d, ln, sm, x0, y0, lam);
    lemma_ch_y(c, d, ln, sm, x0, y0, lam);
    lemma_fm(d, d);
    lemma_fm(c.d2, d);
    lemma_nz_mul(d, d);
    lemma_nz_mul(c.d2, d);
    lemma_dec_coord(o.x, o.z, x3, c.d2, c.xn);
    lemma_dec_coord(o.y, o.z, y3, c.d3, c.yn);
    lemma_ch_clo(c, d, x3, y3);
}

// ---------------------------------------------------------------------------------------------
// Completeness: W(x1, x2) != 0 (D2: a root of W gives a root of f, against no 2-torsion)
// ---------------------------------------------------------------------------------------------

/// RES1 without its 16 W term: 2 r0^2 - s r0 r1 - (t + 3) r1^2.
pub(crate) open spec fn res1_core(x1: int, x2: int) -> int {
    let s = x1 + x2;
    let a = r0_val(x1, x2);
    let b = r1_val(x1, x2);
    2 * fm(a, a) - fm(fm(s, a), b) - fm(fm(x1, x2) + 3, fm(b, b))
}

proof fn lemma_fv(x: int)
    ensures
        fmod(fv(x)) == fmod(x * x * x - 3 * x + p256_b()),
{
    lemma_group_consts();
    lemma_fm(x, x);
    lemma_fm(fm(x, x), x);
    lemma_cg_mul(fm(x, x), x, x * x, x);
    lemma_cg_sub(fm(fm(x, x), x), 3 * x, x * x * x, 3 * x);
    lemma_cg_add(fm(fm(x, x), x) - 3 * x, B_LIT(), x * x * x - 3 * x, B_LIT());
}

/// 8 f(e) == 0 contradicts no 2-torsion.
proof fn lemma_w_tail(e: int)
    requires
        fmod(8 * fv(e)) == 0,
    ensures
        false,
{
    lemma_group_consts();
    lemma_small(8);
    lemma_no_zero_div(8, fv(e));
    lemma_fv(e);
    lemma_no_2_torsion(e);
}

proof fn lemma_nl_bse(b: int, s: int, e: int)
    ensures
        (b * b) * (s * e) == (s * (e * b)) * b,
{
    assert((b * b) * (s * e) == (s * (e * b)) * b) by (nonlinear_arith);
}

proof fn lemma_nl_q(b: int, e: int, s: int, t: int)
    ensures
        (b * b) * (2 * (e * e) + s * e - t) == 2 * ((e * b) * (e * b)) + (s * (e * b)) * b - t * (b * b),
{
    let (bb, ee) = (b * b, e * e);
    lemma_mul_is_distributive_sub(bb, 2 * ee + s * e, t);
    lemma_mul_is_distributive_add(bb, 2 * ee, s * e);
    lemma_mul_is_associative(bb, 2, ee);
    lemma_mul_is_commutative(bb, 2);
    lemma_mul_is_associative(2, bb, ee);
    lemma_nl_sq(e, b);
    lemma_mul_is_commutative(bb, ee);
    lemma_nl_bse(b, s, e);
    lemma_mul_is_commutative(bb, t);
}

proof fn lemma_nl_neg(s: int, a: int, b: int)
    ensures
        (-a) * (-a) == a * a,
        (s * (-a)) * b == -((s * a) * b),
{
    lemma_mul_cancels_negatives(a, a);
    lemma_mul_unary_negation(s, a);
    lemma_mul_unary_negation(s * a, b);
}

/// r1^2 q(e) == RES1 core when r1 e == -r0.
proof fn lemma_w_q(a: int, b: int, s: int, t: int, e: int)
    requires
        fmod(e * b) == fmod(-a),
    ensures
        fmod(fm(b, b) * (2 * fm(e, e) + fm(s, e) - t)) == fmod(
            2 * fm(a, a) - fm(fm(s, a), b) - fm(t, fm(b, b)),
        ),
{
    let eb = e * b;
    // q == 2 e^2 + s e - t
    lemma_fm(e, e);
    lemma_fm(s, e);
    lemma_cg_mul(2, fm(e, e), 2, e * e);
    lemma_cg_add(2 * fm(e, e), fm(s, e), 2 * (e * e), s * e);
    lemma_cg_sub(2 * fm(e, e) + fm(s, e), t, 2 * (e * e) + s * e, t);
    lemma_fm(b, b);
    lemma_cg_mul(fm(b, b), 2 * fm(e, e) + fm(s, e) - t, b * b, 2 * (e * e) + s * e - t);
    lemma_nl_q(b, e, s, t);
    // substitute e b == -a
    lemma_nl_neg(s, a, b);
    lemma_cg_mul(eb, eb, -a, -a);
    lemma_fm(a, a);
    lemma_cg_mul(2, eb * eb, 2, fm(a, a));
    lemma_cg_mul(s, eb, s, -a);
    lemma_cg_mul(s * eb, b, s * (-a), b);
    lemma_fm(s, a);
    lemma_fm(fm(s, a), b);
    lemma_cg_mul(fm(s, a), b, s * a, b);
    lemma_cg_sub(0, (s * a) * b, 0, fm(fm(s, a), b));
    lemma_fm(t, fm(b, b));
    lemma_cg_mul(t, b * b, t, fm(b, b));
    lemma_cg_add(2 * (eb * eb), (s * eb) * b, 2 * fm(a, a), -fm(fm(s, a), b));
    lemma_cg_sub(
        2 * (eb * eb) + (s * eb) * b,
        t * (b * b),
        2 * fm(a, a) + -fm(fm(s, a), b),
        fm(t, fm(b, b)),
    );
}

/// D2 case r1 != 0: e = -r0 / r1 is a root of q, hence of 8 f.
#[verifier::spinoff_prover]
proof fn lemma_w_r1(x1: int, x2: int)
    requires
        fmod(res1_core(x1, x2)) == 0,
        fmod(r1_val(x1, x2)) != 0,
    ensures
        false,
{
    hide(finv);
    hide(r0_val);
    hide(r1_val);
    hide(fv);
    let (a, b, s, t) = (r0_val(x1, x2), r1_val(x1, x2), x1 + x2, fm(x1, x2) + 3);
    let e = fmod((-a) * finv(b));
    lemma_undiv(-a, b);
    lemma_w_q(a, b, s, t, e);
    let q = q_val(x1, x2, e);
    assert(q == 2 * fm(e, e) + fm(s, e) - t);
    lemma_fm(b, b);
    lemma_nz_mul(b, b);
    lemma_no_zero_div(fm(b, b), q);
    lemma_res2(x1, x2, e);
    let (f1, f2) = (fm(q, 4 * e - 2 * s), fm(b, e));
    let xx = 8 * fv(e) - f1 - f2 - a;
    assert(xx == id_res2(x1, x2, e));
    lemma_fm(q, 4 * e - 2 * s);
    lemma_mul0(q, 4 * e - 2 * s);
    lemma_fm(b, e);
    lemma_mul_is_commutative(b, e);
    lemma_cg_add(xx, f1, 0, 0);
    lemma_cg_add(xx + f1, f2, 0, -a);
    lemma_cg_add(xx + f1 + f2, a, -a, a);
    assert(xx + f1 + f2 + a == 8 * fv(e));
    lemma_small(0);
    lemma_w_tail(e);
}

/// D2 case r1 == 0: then r0 == 0, and e = (x1 + x2) / 2 makes 8 f(e) == q(e) (4e - 2s) == 0.
#[verifier::spinoff_prover]
proof fn lemma_w_r0(x1: int, x2: int)
    requires
        fmod(res1_core(x1, x2)) == 0,
        fmod(r1_val(x1, x2)) == 0,
    ensures
        false,
{
    hide(finv);
    hide(r0_val);
    hide(r1_val);
    hide(fv);
    lemma_group_consts();
    let (a, b, s, t) = (r0_val(x1, x2), r1_val(x1, x2), x1 + x2, fm(x1, x2) + 3);
    // r0 == 0
    let (g2, g3) = (fm(fm(s, a), b), fm(t, fm(b, b)));
    lemma_fm(fm(s, a), b);
    lemma_mul0(b, fm(s, a));
    lemma_fm(b, b);
    lemma_mul0(b, b);
    lemma_fm(t, fm(b, b));
    lemma_mul0(fm(b, b), t);
    lemma_cg_add(res1_core(x1, x2), g2, 0, 0);
    lemma_cg_add(res1_core(x1, x2) + g2, g3, 0, 0);
    assert(res1_core(x1, x2) + g2 + g3 == 2 * fm(a, a));
    lemma_small(0);
    lemma_small(2);
    lemma_no_zero_div(2, fm(a, a));
    lemma_fm(a, a);
    lemma_no_zero_div(a, a);
    // e = s / 2
    let e = fmod(s * finv(2));
    lemma_undiv(s, 2);
    lemma_cg_mul(2, e * 2, 2, s);
    assert(4 * e == 2 * (e * 2));
    lemma_sub0(4 * e, 2 * s);
    let q = q_val(x1, x2, e);
    let (f1, f2) = (fm(q, 4 * e - 2 * s), fm(b, e));
    lemma_res2(x1, x2, e);
    let xx = 8 * fv(e) - f1 - f2 - a;
    assert(xx == id_res2(x1, x2, e));
    lemma_fm(q, 4 * e - 2 * s);
    lemma_mul0(4 * e - 2 * s, q);
    lemma_fm(b, e);
    lemma_mul0(b, e);
    lemma_cg_add(xx, f1, 0, 0);
    lemma_cg_add(xx + f1, f2, 0, 0);
    lemma_cg_add(xx + f1 + f2, a, 0, 0);
    assert(xx + f1 + f2 + a == 8 * fv(e));
    lemma_w_tail(e);
}

/// D2: W(x1, x2) != 0 (mod p) for all x1, x2.
pub(crate) proof fn lemma_w_nonzero(x1: int, x2: int)
    ensures
        fmod(w_val(x1, x2)) != 0,
{
    hide(r0_val);
    hide(r1_val);
    hide(w_val);
    let w = w_val(x1, x2);
    if fmod(w) == 0 {
        lemma_res1(x1, x2);
        assert(id_res1(x1, x2) == res1_core(x1, x2) + 16 * w);
        lemma_mul0(w, 16);
        lemma_small(0);
        lemma_cg_sub(id_res1(x1, x2), 16 * w, 0, 0);
        if fmod(r1_val(x1, x2)) != 0 {
            lemma_w_r1(x1, x2);
        } else {
            lemma_w_r0(x1, x2);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Affine inputs: point_add's three branches against rcb
// ---------------------------------------------------------------------------------------------

proof fn lemma_on3(x0: int, y0: int, x1: int, y1: int, x2: int, y2: int)
    requires
        on_curve(x0, y0),
        on_curve(x1, y1),
        on_curve(x2, y2),
    ensures
        on3(seq![x0, x1, x2], seq![y0, y1, y2]),
{
    let (xs, ys) = (seq![x0, x1, x2], seq![y0, y1, y2]);
    assert(xs[0] == x0 && xs[1] == x1 && xs[2] == x2);
    assert(ys[0] == y0 && ys[1] == y1 && ys[2] == y2);
    assert forall|i: int| 0 <= i < 3 implies #[trigger] on_pt(xs[i], ys[i]) by {
        if i == 0 {
        } else if i == 1 {
        } else {
        }
    }
}

proof fn lemma_rcb_range(a: Proj, b: Proj)
    ensures
        0 <= rcb(a, b).x < p256_p(),
        0 <= rcb(a, b).y < p256_p(),
        0 <= rcb(a, b).z < p256_p(),
{
    lemma_group_consts();
}

/// valid(a) ==> a.y != 0: an affine (X, 0) on the curve would be a root of f.
proof fn lemma_valid_y(a: Proj)
    requires
        valid(a),
    ensures
        fmod(a.y) != 0,
{
    hide(finv);
    if fmod(a.z) != 0 && fmod(a.y) == 0 {
        lemma_mul0(a.y, finv(a.z));
        let xv = fmod(a.x * finv(a.z));
        assert(dec(a) == SpecPoint::Affine(xv, 0));
        lemma_small(0);
        lemma_no_2_torsion(xv);
    }
}

proof fn lemma_valid_pt(a: Proj)
    requires
        valid(a),
    ensures
        curve_pt(dec(a)),
{
    hide(finv);
}

proof fn lemma_nl_dsq(a: int, b: int)
    ensures
        (a - b) * (a + b) == a * a - b * b,
{
    lemma_mul_is_distributive_sub_other_way(a + b, a, b);
    lemma_mul_is_distributive_add(a, a, b);
    lemma_mul_is_distributive_add(b, a, b);
    lemma_mul_is_commutative(a, b);
}

/// Rule 5's precondition, on the curve: same x and y1 + y2 != 0 force y2 == y1.
proof fn lemma_dbl_y_eq(x: int, y1: int, y2: int)
    requires
        on_curve(x, y1),
        on_curve(x, y2),
        fmod(y1 + y2) != 0,
    ensures
        y1 == y2,
{
    lemma_sub0(y1 * y1, y2 * y2);
    lemma_nl_dsq(y1, y2);
    lemma_no_zero_div(y1 - y2, y1 + y2);
    lemma_sub0(y1, y2);
    lemma_range_eq(y1, y2);
}

/// Rule 4 (x1 != x2): chord. Z3 != 0 by I4 and W != 0.
#[verifier::spinoff_prover]
proof fn lemma_aff_chord(x1: int, y1: int, x2: int, y2: int)
    requires
        on_curve(x1, y1),
        on_curve(x2, y2),
        x1 != x2,
    ensures
        valid(rcb(enc(SpecPoint::Affine(x1, y1)), enc(SpecPoint::Affine(x2, y2)))),
        dec(rcb(enc(SpecPoint::Affine(x1, y1)), enc(SpecPoint::Affine(x2, y2)))) == point_add(
            SpecPoint::Affine(x1, y1),
            SpecPoint::Affine(x2, y2),
        ),
{
    hide(rcb);
    hide(finv);
    hide(w_val);
    lemma_group_consts();
    let (p, q) = (SpecPoint::Affine(x1, y1), SpecPoint::Affine(x2, y2));
    let (xs, ys) = (seq![x1, x2, x1], seq![y1, y2, y1]);
    lemma_on3(x1, y1, x2, y2, x1, y1);
    assert(xs[0] == x1 && xs[1] == x2 && ys[0] == y1 && ys[1] == y2);
    assert(pt(xs, ys, 0) == enc(p) && pt(xs, ys, 1) == enc(q));
    let o = rcb(enc(p), enc(q));
    let om = rcb(pt(xs, ys, 0), ptm(xs, ys));
    let c = chord(xs, ys);
    lemma_id_chord_x(xs, ys);
    lemma_id_chord_y(xs, ys);
    lemma_id_chord_z(xs, ys);
    lemma_id_closure_chord(xs, ys);
    let d = x2 - x1;
    assert(fmod(d) != 0);
    // Z3 != 0: Z3(P, Q) Z3(P, -Q) == d^3 W(x1, x2), and d, W != 0
    let w = w_val(x1, x2);
    lemma_w_nonzero(x1, x2);
    lemma_fm(d, d);
    lemma_nz_mul(d, d);
    lemma_fm(c.d2, d);
    lemma_nz_mul(c.d2, d);
    lemma_fm(c.d3, w);
    lemma_nz_mul(c.d3, w);
    if fmod(o.z) == 0 {
        lemma_fm(o.z, om.z);
        lemma_mul0(o.z, om.z);
        lemma_sub0(fm(o.z, om.z), fm(c.d3, w));
    }
    let lam = fmod((y2 - y1) * finv(x2 - x1));
    lemma_undiv(y2 - y1, x2 - x1);
    lemma_ch_dec(o, c, d, y2 - y1, x1 + x2, x1, y1, lam);
    lemma_rcb_range(enc(p), enc(q));
    assert(lam * lam - x1 - x2 == lam * lam - (x1 + x2));
}

/// Rule 5 (doubling, y != 0). Z3 == 8 y f(x) != 0 by I7.
#[verifier::spinoff_prover]
proof fn lemma_aff_dbl(x: int, y: int)
    requires
        on_curve(x, y),
        fmod(y + y) != 0,
    ensures
        valid(rcb(enc(SpecPoint::Affine(x, y)), enc(SpecPoint::Affine(x, y)))),
        dec(rcb(enc(SpecPoint::Affine(x, y)), enc(SpecPoint::Affine(x, y)))) == point_add(
            SpecPoint::Affine(x, y),
            SpecPoint::Affine(x, y),
        ),
{
    hide(rcb);
    hide(finv);
    hide(fv);
    lemma_group_consts();
    let p = SpecPoint::Affine(x, y);
    let (xs, ys) = (seq![x, x, x], seq![y, y, y]);
    lemma_on3(x, y, x, y, x, y);
    assert(xs[0] == x && ys[0] == y);
    assert(pt(xs, ys, 0) == enc(p));
    let o = rcb(enc(p), enc(p));
    let c = dbl(xs, ys);
    lemma_id_dbl_x(xs, ys);
    lemma_id_dbl_y(xs, ys);
    lemma_id_dbl_z(xs, ys);
    lemma_id_closure_dbl(xs, ys);
    let e = 2 * y;
    assert(e == y + y);
    // Z3 == 8 y f(x), with f(x) == y^2 != 0
    if fmod(y) == 0 {
        lemma_mul0(y, 2);
    }
    lemma_fv(x);
    lemma_nz_mul(y, y);
    lemma_small(8);
    lemma_nz_mul(8, y);
    lemma_nz_mul(8 * y, fv(x));
    lemma_fm(8 * y, fv(x));
    lemma_sub0(o.z, fm(8 * y, fv(x)));
    // the spec's slope numerator 3 x x - 3 against dbl's 3 fm(x, x) - 3
    let ln = 3 * fm(x, x) - 3;
    let lam = fmod((3 * x * x - 3) * finv(2 * y));
    lemma_undiv(3 * x * x - 3, 2 * y);
    lemma_fm(x, x);
    lemma_mul_is_associative(3, x, x);
    lemma_cg_mul(3, fm(x, x), 3, x * x);
    lemma_cg_sub(3 * fm(x, x), 3, 3 * (x * x), 3);
    lemma_ch_dec(o, c, e, ln, 2 * x, x, y, lam);
    lemma_rcb_range(enc(p), enc(p));
    assert(lam * lam - x - x == lam * lam - 2 * x);
}

/// Rule 3 (x1 == x2, y1 + y2 == 0): P + (-P). I8a-c give X3 == Z3 == 0 and Y3 == Y3(P, P) != 0.
#[verifier::spinoff_prover]
proof fn lemma_aff_inv(x: int, y1: int, y2: int)
    requires
        on_curve(x, y1),
        on_curve(x, y2),
        fmod(y1 + y2) == 0,
    ensures
        valid(rcb(enc(SpecPoint::Affine(x, y1)), enc(SpecPoint::Affine(x, y2)))),
        dec(rcb(enc(SpecPoint::Affine(x, y1)), enc(SpecPoint::Affine(x, y2)))) is Infinity,
{
    hide(rcb);
    hide(finv);
    lemma_group_consts();
    let (p, q) = (SpecPoint::Affine(x, y1), SpecPoint::Affine(x, y2));
    // 1. no 2-torsion at x: y1 != 0, so y2 == p - y1
    lemma_no_2_torsion(x);
    if y1 == 0 {
        lemma_mul_basics(y1);
    }
    assert(y1 + y2 == P_LIT());
    // 2. I8a-c at (x, y1) against (x : p - y1 : 1)
    let (xs, ys) = (seq![x, x, x], seq![y1, y1, y1]);
    lemma_on3(x, y1, x, y1, x, y1);
    assert(xs[0] == x && ys[0] == y1);
    assert(pt(xs, ys, 0) == enc(p) && ptn(xs, ys) == enc(q));
    lemma_id_inv_x(xs, ys);
    lemma_id_inv_z(xs, ys);
    lemma_id_inv_y(xs, ys);
    let o = rcb(enc(p), enc(q));
    let o2 = rcb(enc(p), enc(p));
    // 3. doubling on (p, p): 0 < 2 y1 < 2p and p is odd
    assert(fmod(y1 + y1) != 0);
    lemma_aff_dbl(x, y1);
    // 4. no 2-torsion at 2P: Y3(P, P) != 0
    lemma_valid_y(o2);
    lemma_sub0(o.y, o2.y);
    lemma_rcb_range(enc(p), enc(q));
}

/// point_add on affine curve points is decoded rcb, split on the spec's exact conditions.
pub(crate) proof fn lemma_rcb_correct_aff(p: SpecPoint, q: SpecPoint)
    requires
        p is Affine && curve_pt(p),
        q is Affine && curve_pt(q),
    ensures
        valid(rcb(enc(p), enc(q))),
        dec(rcb(enc(p), enc(q))) == point_add(p, q),
{
    hide(rcb);
    hide(finv);
    hide(valid);
    hide(dec);
    let (x1, y1, x2, y2) = (p->0, p->1, q->0, q->1);
    if x1 != x2 {
        lemma_aff_chord(x1, y1, x2, y2);
    } else if fmod(y1 + y2) == 0 {
        lemma_aff_inv(x1, y1, y2);
    } else {
        lemma_dbl_y_eq(x1, y1, y2);
        assert(q == p);
        lemma_aff_dbl(x1, y1);
    }
}

// ---------------------------------------------------------------------------------------------
// General valid inputs: scaling, O inputs
// ---------------------------------------------------------------------------------------------

pub(crate) proof fn lemma_dec_enc(p: SpecPoint)
    requires
        curve_pt(p),
    ensures
        dec(enc(p)) == p,
{
    hide(finv);
    lemma_group_consts();
    lemma_small(0);
    lemma_small(1);
    if p is Affine {
        lemma_finv_one();
        lemma_small(p->0);
        lemma_small(p->1);
    }
}

pub(crate) proof fn lemma_enc_valid(p: SpecPoint)
    requires
        curve_pt(p),
    ensures
        valid(enc(p)),
{
    hide(finv);
    lemma_group_consts();
    lemma_dec_enc(p);
    lemma_small(0);
    lemma_small(1);
}

proof fn lemma_sc_coord(k: int, n: int, z: int)
    requires
        fmod(k) != 0,
        fmod(z) != 0,
    ensures
        fmod(fmod(k * n) * finv(fmod(k * z))) == fmod(n * finv(z)),
{
    hide(finv);
    let v = fmod(n * finv(z));
    lemma_undiv(n, z);
    lemma_mod_range(n * finv(z));
    lemma_mod_range(k * z);
    lemma_mod_range(k * n);
    lemma_cg_mul(v, fmod(k * z), v, k * z);
    lemma_mul_is_associative(v, k, z);
    lemma_mul_is_commutative(v, k);
    lemma_mul_is_associative(k, v, z);
    lemma_cg_mul(k, v * z, k, n);
    lemma_nz_mul(k, z);
    lemma_div(fmod(k * n), v, fmod(k * z));
}

/// Scaling by k != 0 keeps valid and dec.
proof fn lemma_sc(k: int, a: Proj)
    requires
        fmod(k) != 0,
        valid(a),
    ensures
        valid(sc(k, a)),
        dec(sc(k, a)) == dec(a),
{
    hide(finv);
    lemma_mod_range(k * a.x);
    lemma_mod_range(k * a.y);
    lemma_mod_range(k * a.z);
    if fmod(a.z) != 0 {
        lemma_nz_mul(k, a.z);
        lemma_sc_coord(k, a.x, a.z);
        lemma_sc_coord(k, a.y, a.z);
    } else {
        lemma_mul0(a.z, k);
        lemma_mul0(a.x, k);
        lemma_nz_mul(k, a.y);
    }
}

/// An affine valid triple is its decoding scaled by its z.
proof fn lemma_split(a: Proj)
    requires
        valid(a),
        fmod(a.z) != 0,
    ensures
        dec(a) is Affine,
        curve_pt(dec(a)),
        a == sc(a.z, enc(dec(a))),
{
    hide(finv);
    let (xv, yv) = (fmod(a.x * finv(a.z)), fmod(a.y * finv(a.z)));
    lemma_undiv(a.x, a.z);
    lemma_undiv(a.y, a.z);
    lemma_mul_is_commutative(xv, a.z);
    lemma_mul_is_commutative(yv, a.z);
    lemma_small(a.x);
    lemma_small(a.y);
    lemma_small(a.z);
    assert(enc(dec(a)) == Proj { x: xv, y: yv, z: 1 });
    let b = sc(a.z, Proj { x: xv, y: yv, z: 1 });
    assert(b.x == a.x);
    assert(b.y == a.y);
    lemma_mul_basics(a.z);
    assert(b.z == a.z);
    assert(b == a);
}

/// O + B: rcb((0 : y : 0), B) == (y^2 B.y) B, with y, B.y != 0.
#[verifier::spinoff_prover]
proof fn lemma_correct_inf_l(a: Proj, b: Proj)
    requires
        valid(a),
        valid(b),
        fmod(a.z) == 0,
    ensures
        valid(rcb(a, b)),
        dec(rcb(a, b)) == dec(b),
{
    hide(rcb);
    hide(finv);
    hide(sc);
    lemma_small(a.x);
    lemma_small(a.z);
    assert(a == Proj { x: 0, y: a.y, z: 0 });
    lemma_rcb_inf_l(a.y, b);
    lemma_valid_y(a);
    lemma_valid_y(b);
    lemma_nz_mul(a.y, a.y);
    lemma_nz_mul(a.y * a.y, b.y);
    lemma_sc(a.y * a.y * b.y, b);
}

/// Both affine: rcb(z1 E1, z2 E2) == z1^2 z2^2 rcb(E1, E2).
#[verifier::spinoff_prover]
proof fn lemma_correct_aa(a: Proj, b: Proj)
    requires
        valid(a),
        valid(b),
        fmod(a.z) != 0,
        fmod(b.z) != 0,
    ensures
        valid(rcb(a, b)),
        dec(rcb(a, b)) == point_add(dec(a), dec(b)),
{
    hide(rcb);
    hide(finv);
    hide(sc);
    hide(valid);
    hide(dec);
    hide(point_add);
    let (pa, pb) = (dec(a), dec(b));
    let (ea, eb) = (enc(pa), enc(pb));
    lemma_split(a);
    lemma_split(b);
    lemma_rcb_scale_l(a.z, ea, sc(b.z, eb));
    lemma_rcb_scale_r(b.z, ea, eb);
    lemma_rcb_correct_aff(pa, pb);
    lemma_nz_mul(b.z, b.z);
    lemma_sc(b.z * b.z, rcb(ea, eb));
    lemma_nz_mul(a.z, a.z);
    lemma_sc(a.z * a.z, sc(b.z * b.z, rcb(ea, eb)));
}

pub(crate) proof fn lemma_rcb_correct(a: Proj, b: Proj)
    requires
        valid(a),
        valid(b),
    ensures
        valid(rcb(a, b)),
        dec(rcb(a, b)) == point_add(dec(a), dec(b)),
{
    hide(rcb);
    hide(finv);
    hide(valid);
    if fmod(a.z) == 0 {
        lemma_correct_inf_l(a, b);
    } else if fmod(b.z) == 0 {
        lemma_rcb_symm(a, b);
        lemma_correct_inf_l(b, a);
    } else {
        lemma_correct_aa(a, b);
    }
}

// ---------------------------------------------------------------------------------------------
// Projective equality and the exports
// ---------------------------------------------------------------------------------------------

/// n w == m z with z, w != 0 gives n / z == m / w.
proof fn lemma_cross(n: int, z: int, m: int, w: int)
    requires
        fmod(fm(n, w) - fm(m, z)) == 0,
        fmod(z) != 0,
        fmod(w) != 0,
    ensures
        fmod(n * finv(z)) == fmod(m * finv(w)),
{
    hide(finv);
    let v = fmod(n * finv(z));
    lemma_undiv(n, z);
    lemma_mod_range(n * finv(z));
    lemma_sub0(fm(n, w), fm(m, z));
    lemma_fm(n, w);
    lemma_fm(m, z);
    lemma_cg_mul(n, w, v * z, w);
    lemma_nl_rot(v, z, w);
    lemma_cancel(v * w, m, z);
    lemma_div(m, v, w);
}

/// Valid triples with vanishing 2x2 minors decode to the same point.
pub(crate) proof fn lemma_dec_prop(a: Proj, b: Proj)
    requires
        valid(a),
        valid(b),
        fmod(minor(0, a, b)) == 0,
        fmod(minor(1, a, b)) == 0,
        fmod(minor(2, a, b)) == 0,
    ensures
        dec(a) == dec(b),
{
    hide(finv);
    if fmod(a.z) != 0 && fmod(b.z) != 0 {
        lemma_cross(a.x, a.z, b.x, b.z);
        lemma_cross(a.y, a.z, b.y, b.z);
    } else if fmod(a.z) != 0 || fmod(b.z) != 0 {
        // minor 2: a.y b.z == b.y a.z, with exactly one z zero and both y nonzero
        lemma_sub0(fm(a.y, b.z), fm(b.y, a.z));
        lemma_fm(a.y, b.z);
        lemma_fm(b.y, a.z);
        if fmod(a.z) == 0 {
            lemma_mul0(a.z, b.y);
            lemma_nz_mul(a.y, b.z);
        } else {
            lemma_mul0(b.z, a.y);
            lemma_nz_mul(b.y, a.z);
        }
    }
}

pub(crate) proof fn lemma_point_add_closed(p: SpecPoint, q: SpecPoint)
    requires
        curve_pt(p),
        curve_pt(q),
    ensures
        curve_pt(point_add(p, q)),
{
    hide(finv);
    hide(rcb);
    if p is Affine && q is Affine {
        lemma_rcb_correct_aff(p, q);
        lemma_valid_pt(rcb(enc(p), enc(q)));
    }
}

#[verifier::spinoff_prover]
proof fn lemma_assoc_aff(p: SpecPoint, q: SpecPoint, r: SpecPoint)
    requires
        p is Affine && curve_pt(p),
        q is Affine && curve_pt(q),
        r is Affine && curve_pt(r),
    ensures
        point_add(point_add(p, q), r) == point_add(p, point_add(q, r)),
{
    hide(rcb);
    hide(finv);
    hide(dec);
    hide(valid);
    hide(point_add);
    hide(minor);
    let (xs, ys) = (seq![p->0, q->0, r->0], seq![p->1, q->1, r->1]);
    lemma_on3(p->0, p->1, q->0, q->1, r->0, r->1);
    assert(xs[0] == p->0 && xs[1] == q->0 && xs[2] == r->0);
    assert(ys[0] == p->1 && ys[1] == q->1 && ys[2] == r->1);
    let (e0, e1, e2) = (enc(p), enc(q), enc(r));
    assert(pt(xs, ys, 0) == e0 && pt(xs, ys, 1) == e1 && pt(xs, ys, 2) == e2);
    let (lhs, rhs) = (rcb(rcb(e0, e1), e2), rcb(e0, rcb(e1, e2)));
    lemma_rcb_assoc_minors(xs, ys);
    assert(assoc_lr(xs, ys) == (lhs, rhs));
    lemma_enc_valid(p);
    lemma_enc_valid(q);
    lemma_enc_valid(r);
    lemma_dec_enc(p);
    lemma_dec_enc(q);
    lemma_dec_enc(r);
    lemma_rcb_correct_aff(p, q);
    lemma_rcb_correct_aff(q, r);
    lemma_rcb_correct(rcb(e0, e1), e2);
    lemma_rcb_correct(e0, rcb(e1, e2));
    lemma_dec_prop(lhs, rhs);
}

pub(crate) proof fn lemma_point_add_assoc(p: SpecPoint, q: SpecPoint, r: SpecPoint)
    requires
        curve_pt(p),
        curve_pt(q),
        curve_pt(r),
    ensures
        point_add(point_add(p, q), r) == point_add(p, point_add(q, r)),
{
    hide(finv);
    if p is Affine && q is Affine && r is Affine {
        lemma_assoc_aff(p, q, r);
    }
}

// ---------------------------------------------------------------------------------------------
// Spot vectors on G (Review Focus 1 and 5)
// ---------------------------------------------------------------------------------------------

/// G is on the curve (ground evaluation).
#[verifier::spinoff_prover]
proof fn lemma_spot_g_on()
    ensures
        curve_pt(G_LIT()),
{
    lemma_group_consts();
    assert(on_curve(GX_LIT(), GY_LIT()));
}

/// rcb(G, -G).z == 0, by ground evaluation with the two cross products as literals.
#[verifier::spinoff_prover]
proof fn lemma_spot_inv_z()
    ensures
        rcb(
            Proj { x: GX_LIT(), y: GY_LIT(), z: 1 },
            Proj { x: GX_LIT(), y: P_LIT() - GY_LIT(), z: 1 },
        ).z == 0,
{
    let a = Proj { x: GX_LIT(), y: GY_LIT(), z: 1 };
    let b = Proj { x: GX_LIT(), y: P_LIT() - GY_LIT(), z: 1 };
    let o = rcb(a, b);
    assert(fm(GX_LIT(), GY_LIT())
        == 58908126177458906251578054527685290833723497900791240663493461173334367443134int);
    assert(fm(GX_LIT(), P_LIT() - GY_LIT())
        == 56883963032897342511119392421722282696362645514499073532040170135532730410817int);
    assert(fm(GY_LIT(), 1) == GY_LIT());
    assert(fm(P_LIT() - GY_LIT(), 1) == P_LIT() - GY_LIT());
    let (r, s) = (fm(a.y, b.z) + fm(b.y, a.z), fm(a.x, b.y) + fm(b.x, a.y));
    assert(r == P_LIT() && s == P_LIT());
    let v = fm(a.y, b.y) - 3 * (fm(a.x, b.z) + fm(b.x, a.z)) + fm(3 * B_LIT(), fm(a.z, b.z));
    let q = 3 * fm(a.x, b.x) - 3 * fm(a.z, b.z);
    lemma_mod_multiples_basic(v, P_LIT());
    lemma_mod_multiples_basic(q, P_LIT());
    lemma_mul_is_commutative(v, P_LIT());
    lemma_mul_is_commutative(q, P_LIT());
    assert(fm(r, v) == 0 && fm(s, q) == 0);
    assert(o.z == (fm(r, v) + fm(s, q)) % P_LIT());
}

/// G + (-G) decodes to O; G + G (y != 0) is valid and affine.
#[verifier::spinoff_prover]
proof fn lemma_group_spot() {
    hide(finv);
    hide(rcb);
    lemma_group_consts();
    let g = G_LIT();
    lemma_spot_g_on();
    let (a, b) = (enc(g), enc(neg(g)));
    assert(a == Proj { x: GX_LIT(), y: GY_LIT(), z: 1 });
    assert(b == Proj { x: GX_LIT(), y: P_LIT() - GY_LIT(), z: 1 });
    lemma_spot_inv_z();
    assert(dec(rcb(a, b)) is Infinity);
    lemma_rcb_correct_aff(g, g);
    assert(valid(rcb(a, a)));
    assert(fmod(GY_LIT() + GY_LIT()) != 0);
    assert(dec(rcb(a, a)) is Affine);
}

} // verus!
