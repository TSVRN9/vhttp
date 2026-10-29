//! Curve-reduced formal polynomials in three points (x_i, y_i) of y^2 = x^3 - 3x + b, and the
//! grid identity theorem. An `RF` holds 8 components indexed by a bitmask s over {y0, y1, y2}:
//! its value is sum_s (prod_{i in s} y_i) * a[s](x0, x1, x2). Products reduce y_i^2 to
//! f(x_i) = x_i^3 - 3x_i + b, so on the curve (`on3`) `rf_mul` is multiplication mod p.
//! Identity theorem: if every component's tracked x-degree is below the grid sizes and the value
//! vanishes at every grid point under all 8 y-sign choices, then each component vanishes on the
//! grid (Hadamard inversion; y != 0 at grid points), hence everywhere (`poly::lemma_grid`), so the
//! value vanishes at every curve point.
#[allow(unused_imports)]
use super::field::*;
#[allow(unused_imports)]
use super::poly::*;
#[allow(unused_imports)]
use crate::p256::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Bits of a component index (u8: xor/and evaluate under compute; Z3 sees them via lemma_bits)
// ---------------------------------------------------------------------------------------------

pub(crate) open spec fn bit(s: u8, i: int) -> bool {
    if i == 0 {
        s % 2 == 1
    } else if i == 1 {
        s / 2 % 2 == 1
    } else {
        s / 4 % 2 == 1
    }
}

pub(crate) open spec fn b01(s: u8, i: int) -> int {
    if bit(s, i) {
        1
    } else {
        0
    }
}

/// s ^ r on 3-bit indices, in arithmetic Z3 can evaluate on literals.
pub(crate) open spec fn xr(s: u8, r: u8) -> int {
    (s % 2 + r % 2) % 2 + 2 * ((s / 2 % 2 + r / 2 % 2) % 2) + 4 * ((s / 4 % 2 + r / 4 % 2) % 2)
}

// ---------------------------------------------------------------------------------------------
// Values
// ---------------------------------------------------------------------------------------------

pub(crate) type RF = Seq<MP>;

pub(crate) type RD = Seq<Seq<int>>;

pub(crate) open spec fn yf(ys: Seq<int>, s: u8, i: int) -> int {
    if bit(s, i) {
        ys[i]
    } else {
        1
    }
}

/// prod_{i in s} ys[i].
pub(crate) open spec fn yw(ys: Seq<int>, s: u8) -> int {
    yf(ys, s, 0) * yf(ys, s, 1) * yf(ys, s, 2)
}

pub(crate) open spec fn ra(a: RF, xs: Seq<int>, ys: Seq<int>, s: u8) -> int {
    yw(ys, s) * ev(a[s as int], xs)
}

/// sum_s yw(ys, s) * ev(a[s], xs).
pub(crate) open spec fn rval(a: RF, xs: Seq<int>, ys: Seq<int>) -> int {
    ra(a, xs, ys, 0) + ra(a, xs, ys, 1) + ra(a, xs, ys, 2) + ra(a, xs, ys, 3) + ra(a, xs, ys, 4)
        + ra(a, xs, ys, 5) + ra(a, xs, ys, 6) + ra(a, xs, ys, 7)
}

pub(crate) open spec fn on_pt(x: int, y: int) -> bool {
    fmod(y * y) == fmod(x * x * x - 3 * x + p256_b())
}

/// Three points on the curve (mod p).
pub(crate) open spec fn on3(xs: Seq<int>, ys: Seq<int>) -> bool {
    xs.len() == 3 && ys.len() == 3 && forall|i: int| 0 <= i < 3 ==> #[trigger] on_pt(xs[i], ys[i])
}

// ---------------------------------------------------------------------------------------------
// Formal operations
// ---------------------------------------------------------------------------------------------

pub(crate) open spec fn fxv(x: int) -> int {
    x * x * x + -3 * x + B_LIT()
}

/// x_i^3 - 3 x_i + b.
pub(crate) open spec fn fx(i: nat) -> MP {
    padd(padd(pmul(pmul(px(i), px(i)), px(i)), pmul(pk(-3), px(i))), pk(B_LIT()))
}

pub(crate) open spec fn fxs(m: u8, i: nat) -> MP {
    if bit(m, i as int) {
        fx(i)
    } else {
        pk(1)
    }
}

/// prod_{i in m} f(x_i).
pub(crate) open spec fn fxp(m: u8) -> MP {
    pmul(pmul(fxs(m, 0), fxs(m, 1)), fxs(m, 2))
}

pub(crate) open spec fn ff(xs: Seq<int>, m: u8, i: int) -> int {
    if bit(m, i) {
        fxv(xs[i])
    } else {
        1
    }
}

pub(crate) open spec fn fw(xs: Seq<int>, m: u8) -> int {
    ff(xs, m, 0) * ff(xs, m, 1) * ff(xs, m, 2)
}

pub(crate) open spec fn rf_add(a: RF, b: RF) -> RF {
    Seq::new(8, |s: int| padd(a[s], b[s]))
}

pub(crate) open spec fn rf_k(c: int) -> RF {
    Seq::new(
        8,
        |s: int|
            if s == 0 {
                pk(c)
            } else {
                pk(0)
            },
    )
}

pub(crate) open spec fn rf_x(i: nat) -> RF {
    Seq::new(
        8,
        |s: int|
            if s == 0 {
                px(i)
            } else {
                pk(0)
            },
    )
}

/// The component index of y_i.
pub(crate) open spec fn yb(i: nat) -> int {
    if i == 0 {
        1
    } else if i == 1 {
        2
    } else {
        4
    }
}

pub(crate) open spec fn rf_y(i: nat) -> RF {
    Seq::new(
        8,
        |s: int|
            if s == yb(i) {
                pk(1)
            } else {
                pk(0)
            },
    )
}

/// a[s] * b[s ^ r] * prod_{i in s & (s ^ r)} f(x_i): y^s y^(s^r) = y^r prod_{i in s & (s^r)} y_i^2.
pub(crate) open spec fn rf_term(a: RF, b: RF, s: u8, r: u8) -> MP {
    pmul(pmul(a[s as int], b[(s ^ r) as int]), fxp(s & (s ^ r)))
}

/// sum_{s <= k} rf_term(a, b, s, r).
pub(crate) open spec fn rf_part(a: RF, b: RF, r: u8, k: nat) -> MP
    decreases k,
{
    if k == 0 {
        rf_term(a, b, 0, r)
    } else {
        padd(rf_part(a, b, r, (k - 1) as nat), rf_term(a, b, k as u8, r))
    }
}

/// Component r: sum_s a[s] * b[s ^ r] * prod_{i in s & (s ^ r)} f(x_i).
pub(crate) open spec fn rf_mul(a: RF, b: RF) -> RF {
    Seq::new(8, |r: int| rf_part(a, b, r as u8, 7))
}

// ---------------------------------------------------------------------------------------------
// Degree tables (8 x 3; a row [-1, -1, -1] is a component that evaluates to 0)
// ---------------------------------------------------------------------------------------------

pub(crate) open spec fn rsent() -> Seq<int> {
    seq![-1int, -1, -1]
}

pub(crate) open spec fn rz(row: Seq<int>) -> bool {
    row[0] < 0
}

pub(crate) open spec fn imax(a: int, b: int) -> int {
    if a >= b {
        a
    } else {
        b
    }
}

pub(crate) open spec fn rmax(u: Seq<int>, v: Seq<int>) -> Seq<int> {
    if rz(u) {
        v
    } else if rz(v) {
        u
    } else {
        seq![imax(u[0], v[0]), imax(u[1], v[1]), imax(u[2], v[2])]
    }
}

pub(crate) open spec fn rd_add(da: RD, db: RD) -> RD {
    Seq::new(8, |s: int| rmax(da[s], db[s]))
}

pub(crate) open spec fn rd_k() -> RD {
    Seq::new(
        8,
        |s: int|
            if s == 0 {
                seq![0int, 0, 0]
            } else {
                rsent()
            },
    )
}

pub(crate) open spec fn unit(i: nat) -> Seq<int> {
    seq![
        if i == 0 {
            1int
        } else {
            0
        },
        if i == 1 {
            1int
        } else {
            0
        },
        if i == 2 {
            1int
        } else {
            0
        },
    ]
}

pub(crate) open spec fn rd_x(i: nat) -> RD {
    Seq::new(
        8,
        |s: int|
            if s == 0 {
                unit(i)
            } else {
                rsent()
            },
    )
}

pub(crate) open spec fn rd_y(i: nat) -> RD {
    Seq::new(
        8,
        |s: int|
            if s == yb(i) {
                seq![0int, 0, 0]
            } else {
                rsent()
            },
    )
}

/// The degree of rf_term(a, b, s, r): da[s] + db[s ^ r] + 3 per variable in s & (s ^ r).
pub(crate) open spec fn rd_pair(da: RD, db: RD, s: u8, r: u8) -> Seq<int> {
    let u = da[s as int];
    let v = db[(s ^ r) as int];
    let m = s & (s ^ r);
    if rz(u) || rz(v) {
        rsent()
    } else {
        seq![u[0] + v[0] + 3 * b01(m, 0), u[1] + v[1] + 3 * b01(m, 1), u[2] + v[2] + 3 * b01(m, 2)]
    }
}

pub(crate) open spec fn rd_part(da: RD, db: RD, r: u8, k: nat) -> Seq<int>
    decreases k,
{
    if k == 0 {
        rd_pair(da, db, 0, r)
    } else {
        rmax(rd_part(da, db, r, (k - 1) as nat), rd_pair(da, db, k as u8, r))
    }
}

pub(crate) open spec fn rd_mul(da: RD, db: RD) -> RD {
    Seq::new(8, |r: int| rd_part(da, db, r as u8, 7))
}

pub(crate) open spec fn dn(row: Seq<int>) -> Seq<nat> {
    seq![row[0] as nat, row[1] as nat, row[2] as nat]
}

/// Exactly 0 everywhere (over int).
pub(crate) open spec fn zero_ev(c: MP) -> bool {
    forall|xs: Seq<int>| #[trigger] ev(c, xs) == 0
}

pub(crate) open spec fn agree(q: MP, c: MP) -> bool {
    forall|xs: Seq<int>| #![trigger ev(q, xs)] #![trigger ev(c, xs)] ev(q, xs) == ev(c, xs)
}

/// c is bounded by row: zero for a sentinel row; else it agrees everywhere with a polynomial of
/// structural degree <= row (zero-valued products from `rf_mul` carry arbitrary structure).
pub(crate) open spec fn rrow(c: MP, row: Seq<int>) -> bool {
    row.len() == 3 && if rz(row) {
        zero_ev(c)
    } else {
        row[1] >= 0 && row[2] >= 0 && exists|q: MP| #[trigger] fits(q, dn(row)) && agree(q, c)
    }
}

pub(crate) open spec fn rfits(a: RF, d: RD) -> bool {
    a.len() == 8 && d.len() == 8 && forall|s: int| 0 <= s < 8 ==> #[trigger] rrow(a[s], d[s])
}

// ---------------------------------------------------------------------------------------------
// Hadamard
// ---------------------------------------------------------------------------------------------

pub(crate) open spec fn ng(sig: u8, s: u8, i: int) -> bool {
    bit(sig, i) && bit(s, i)
}

/// (-1)^|sig & s|.
pub(crate) open spec fn chi(sig: u8, s: u8) -> int {
    if (ng(sig, s, 0) != ng(sig, s, 1)) != ng(sig, s, 2) {
        -1
    } else {
        1
    }
}

/// k * v for k = 1 or -1 (as a case split, so that Z3 sees literal signs).
pub(crate) open spec fn pm1(k: int, v: int) -> int {
    if k == 1 {
        v
    } else {
        -v
    }
}

/// yw(ys, s) * c[s] (opaque: the Hadamard sums treat it as an atom).
#[verifier::opaque]
pub(crate) open spec fn hw(ys: Seq<int>, c: Seq<int>, s: u8) -> int {
    yw(ys, s) * c[s as int]
}

/// chi(sig, s) * yw(ys, s) * c[s].
pub(crate) open spec fn hterm(sig: u8, c: Seq<int>, ys: Seq<int>, s: u8) -> int {
    pm1(chi(sig, s), hw(ys, c, s))
}

/// sum_s chi(sig, s) * yw(ys, s) * c[s].
#[verifier::opaque]
pub(crate) open spec fn hsum(sig: u8, c: Seq<int>, ys: Seq<int>) -> int {
    hterm(sig, c, ys, 0) + hterm(sig, c, ys, 1) + hterm(sig, c, ys, 2) + hterm(sig, c, ys, 3)
        + hterm(sig, c, ys, 4) + hterm(sig, c, ys, 5) + hterm(sig, c, ys, 6) + hterm(sig, c, ys, 7)
}

/// ys with y_i negated for each i in sig.
pub(crate) open spec fn sgn(sig: u8, ys: Seq<int>) -> Seq<int> {
    seq![
        if bit(sig, 0) {
            -ys[0]
        } else {
            ys[0]
        },
        if bit(sig, 1) {
            -ys[1]
        } else {
            ys[1]
        },
        if bit(sig, 2) {
            -ys[2]
        } else {
            ys[2]
        },
    ]
}

// ---------------------------------------------------------------------------------------------
// Grids
// ---------------------------------------------------------------------------------------------

pub(crate) open spec fn gpt(g: Seq<Seq<int>>, i: int, j: int, l: int) -> Seq<int> {
    seq![g[0][i], g[1][j], g[2][l]]
}

pub(crate) open spec fn in_box(g: Seq<Seq<int>>, i: int, j: int, l: int) -> bool {
    0 <= i < g[0].len() && 0 <= j < g[1].len() && 0 <= l < g[2].len()
}

pub(crate) open spec fn gk_ok(gx: Seq<Seq<int>>, gy: Seq<Seq<int>>, k: int) -> bool {
    gy[k].len() == gx[k].len() && distinct_mod_p(gx[k])
}

pub(crate) open spec fn gpt_ok(x: int, y: int) -> bool {
    on_pt(x, y) && fmod(y) != 0
}

/// Three x-grids, distinct mod p, with curve y-values y != 0.
pub(crate) open spec fn grid_ok(gx: Seq<Seq<int>>, gy: Seq<Seq<int>>) -> bool {
    &&& gx.len() == 3
    &&& gy.len() == 3
    &&& forall|k: int| 0 <= k < 3 ==> #[trigger] gk_ok(gx, gy, k)
    &&& forall|k: int, t: int|
        0 <= k < 3 && 0 <= t < gx[k].len() ==> #[trigger] gpt_ok(gx[k][t], gy[k][t])
}

/// Every non-sentinel degree is below its grid's size.
pub(crate) open spec fn deg_fits(d: RD, gx: Seq<Seq<int>>) -> bool {
    forall|s: int, k: int| 0 <= s < 8 && 0 <= k < 3 && !rz(d[s]) ==> #[trigger] d[s][k] < gx[k].len()
}

/// The value vanishes at every grid point under every y-sign choice.
pub(crate) open spec fn signs_vanish(g: RF, gx: Seq<Seq<int>>, gy: Seq<Seq<int>>) -> bool {
    forall|i: int, j: int, l: int, sig: u8|
        in_box(gx, i, j, l) && sig < 8 ==> fmod(
            #[trigger] rval(g, gpt(gx, i, j, l), sgn(sig, gpt(gy, i, j, l))),
        ) == 0
}

/// Chunked grid checks: c(i, j, l) for lo <= l < hi.
pub(crate) open spec fn cells_ok(c: spec_fn(int, int, int) -> bool, i: int, j: int, lo: int, hi: int) -> bool
    decreases hi - lo,
{
    if lo >= hi {
        true
    } else {
        c(i, j, lo) && cells_ok(c, i, j, lo + 1, hi)
    }
}

// ---------------------------------------------------------------------------------------------
// Arithmetic helpers
// ---------------------------------------------------------------------------------------------

proof fn lemma_bits(s: u8, t: u8)
    requires
        s < 8,
        t < 8,
    ensures
        (s ^ t) < 8,
        (s & t) < 8,
        s ^ (s ^ t) == t,
        (s ^ t) as int == xr(s, t),
        forall|i: int| 0 <= i < 3 ==> (#[trigger] bit(s ^ t, i)) == (bit(s, i) != bit(t, i)),
        forall|i: int| 0 <= i < 3 ==> (#[trigger] bit(s & t, i)) == (bit(s, i) && bit(t, i)),
{
    assert((s ^ t) < 8 && (s & t) < 8 && s ^ (s ^ t) == t
        && (((s ^ t) % 2 == 1) == ((s % 2 == 1) != (t % 2 == 1)))
        && (((s ^ t) / 2 % 2 == 1) == ((s / 2 % 2 == 1) != (t / 2 % 2 == 1)))
        && (((s ^ t) / 4 % 2 == 1) == ((s / 4 % 2 == 1) != (t / 4 % 2 == 1)))
        && (((s & t) % 2 == 1) == ((s % 2 == 1) && (t % 2 == 1)))
        && (((s & t) / 2 % 2 == 1) == ((s / 2 % 2 == 1) && (t / 2 % 2 == 1)))
        && (((s & t) / 4 % 2 == 1) == ((s / 4 % 2 == 1) && (t / 4 % 2 == 1)))) by (bit_vector)
        requires
            s < 8u8,
            t < 8u8,
    ;
    assert((s ^ t) == (s % 2 + t % 2) % 2 + 2 * ((s / 2 % 2 + t / 2 % 2) % 2)
        + 4 * ((s / 4 % 2 + t / 4 % 2) % 2)) by (bit_vector)
        requires
            s < 8u8,
            t < 8u8,
    ;
}

proof fn lemma_mul4(a: int, b: int, c: int, d: int)
    ensures
        (a * b) * (c * d) == (a * c) * (b * d),
{
    lemma_mul_is_associative(a, b, c * d);
    lemma_mul_is_associative(b, c, d);
    lemma_mul_is_commutative(b, c);
    lemma_mul_is_associative(c, b, d);
    lemma_mul_is_associative(a, c, b * d);
}

proof fn lemma_cong_add(a: int, b: int, c: int, d: int)
    requires
        fmod(a) == fmod(c),
        fmod(b) == fmod(d),
    ensures
        fmod(a + b) == fmod(c + d),
{
    lemma_group_consts();
    lemma_add_mod_noop(a, b, p256_p());
    lemma_add_mod_noop(c, d, p256_p());
}

proof fn lemma_cong_mul(a: int, b: int, c: int, d: int)
    requires
        fmod(a) == fmod(c),
        fmod(b) == fmod(d),
    ensures
        fmod(a * b) == fmod(c * d),
{
    lemma_group_consts();
    lemma_mul_mod_noop_general(a, b, p256_p());
    lemma_mul_mod_noop_general(c, d, p256_p());
}

proof fn lemma_zero_mul(k: int, h: int)
    requires
        fmod(h) == 0,
    ensures
        fmod(k * h) == 0,
{
    lemma_group_consts();
    lemma_mul_mod_noop_right(k, h, p256_p());
}

proof fn lemma_cong8(
    a0: int,
    a1: int,
    a2: int,
    a3: int,
    a4: int,
    a5: int,
    a6: int,
    a7: int,
    b0: int,
    b1: int,
    b2: int,
    b3: int,
    b4: int,
    b5: int,
    b6: int,
    b7: int,
)
    requires
        fmod(a0) == fmod(b0),
        fmod(a1) == fmod(b1),
        fmod(a2) == fmod(b2),
        fmod(a3) == fmod(b3),
        fmod(a4) == fmod(b4),
        fmod(a5) == fmod(b5),
        fmod(a6) == fmod(b6),
        fmod(a7) == fmod(b7),
    ensures
        fmod(a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) == fmod(b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7),
{
    lemma_cong_add(a0, a1, b0, b1);
    lemma_cong_add(a0 + a1, a2, b0 + b1, b2);
    lemma_cong_add(a0 + a1 + a2, a3, b0 + b1 + b2, b3);
    lemma_cong_add(a0 + a1 + a2 + a3, a4, b0 + b1 + b2 + b3, b4);
    lemma_cong_add(a0 + a1 + a2 + a3 + a4, a5, b0 + b1 + b2 + b3 + b4, b5);
    lemma_cong_add(a0 + a1 + a2 + a3 + a4 + a5, a6, b0 + b1 + b2 + b3 + b4 + b5, b6);
    lemma_cong_add(a0 + a1 + a2 + a3 + a4 + a5 + a6, a7, b0 + b1 + b2 + b3 + b4 + b5 + b6, b7);
}

proof fn lemma_zero8(a0: int, a1: int, a2: int, a3: int, a4: int, a5: int, a6: int, a7: int)
    requires
        fmod(a0) == 0,
        fmod(a1) == 0,
        fmod(a2) == 0,
        fmod(a3) == 0,
        fmod(a4) == 0,
        fmod(a5) == 0,
        fmod(a6) == 0,
        fmod(a7) == 0,
    ensures
        fmod(a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) == 0,
{
    lemma_group_consts();
    lemma_cong8(a0, a1, a2, a3, a4, a5, a6, a7, 0, 0, 0, 0, 0, 0, 0, 0);
}

proof fn lemma_dist8(u: int, v0: int, v1: int, v2: int, v3: int, v4: int, v5: int, v6: int, v7: int)
    ensures
        u * (v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7) == u * v0 + u * v1 + u * v2 + u * v3 + u * v4 + u
            * v5 + u * v6 + u * v7,
{
    lemma_mul_is_distributive_add(u, v0, v1);
    lemma_mul_is_distributive_add(u, v0 + v1, v2);
    lemma_mul_is_distributive_add(u, v0 + v1 + v2, v3);
    lemma_mul_is_distributive_add(u, v0 + v1 + v2 + v3, v4);
    lemma_mul_is_distributive_add(u, v0 + v1 + v2 + v3 + v4, v5);
    lemma_mul_is_distributive_add(u, v0 + v1 + v2 + v3 + v4 + v5, v6);
    lemma_mul_is_distributive_add(u, v0 + v1 + v2 + v3 + v4 + v5 + v6, v7);
}

// ---------------------------------------------------------------------------------------------
// f(x_i) and its degree
// ---------------------------------------------------------------------------------------------

proof fn lemma_ev_fx(i: nat, xs: Seq<int>)
    requires
        i < xs.len(),
    ensures
        ev(fx(i), xs) == fxv(xs[i as int]),
{
    let x = px(i);
    lemma_ev_x(i, xs);
    lemma_ev_mul(x, x, xs);
    lemma_ev_mul(pmul(x, x), x, xs);
    lemma_ev_mul(pk(-3), x, xs);
    lemma_ev_add(pmul(pmul(x, x), x), pmul(pk(-3), x), xs);
    lemma_ev_add(padd(pmul(pmul(x, x), x), pmul(pk(-3), x)), pk(B_LIT()), xs);
}

proof fn lemma_ev_fxp(m: u8, xs: Seq<int>)
    requires
        xs.len() == 3,
    ensures
        ev(fxp(m), xs) == fw(xs, m),
{
    lemma_ev_fx(0, xs);
    lemma_ev_fx(1, xs);
    lemma_ev_fx(2, xs);
    lemma_ev_mul(fxs(m, 0), fxs(m, 1), xs);
    lemma_ev_mul(pmul(fxs(m, 0), fxs(m, 1)), fxs(m, 2), xs);
}

/// c in position i, else 0.
pub(crate) open spec fn e3(i: nat, c: nat) -> Seq<nat> {
    seq![
        if i == 0 {
            c
        } else {
            0nat
        },
        if i == 1 {
            c
        } else {
            0nat
        },
        if i == 2 {
            c
        } else {
            0nat
        },
    ]
}

pub(crate) open spec fn fdeg(m: u8) -> Seq<nat> {
    seq![(3 * b01(m, 0)) as nat, (3 * b01(m, 1)) as nat, (3 * b01(m, 2)) as nat]
}

proof fn lemma_fits_fx(i: nat)
    requires
        i < 3,
    ensures
        fits(fx(i), e3(i, 3)),
{
    let x = px(i);
    let z = seq![0nat, 0nat, 0nat];
    lemma_fits_x(i, e3(i, 1));
    lemma_fits_mul(x, x, e3(i, 1), e3(i, 1));
    assert(dsum(e3(i, 1), e3(i, 1)) =~= e3(i, 2));
    lemma_fits_mul(pmul(x, x), x, e3(i, 2), e3(i, 1));
    assert(dsum(e3(i, 2), e3(i, 1)) =~= e3(i, 3));
    lemma_fits_mul(pk(-3), x, z, e3(i, 1));
    assert(dsum(z, e3(i, 1)) =~= e3(i, 1));
    lemma_fits_add(pmul(pmul(x, x), x), pmul(pk(-3), x), e3(i, 3), e3(i, 1));
    assert(dmax(e3(i, 3), e3(i, 1)) =~= e3(i, 3));
    lemma_fits_add(padd(pmul(pmul(x, x), x), pmul(pk(-3), x)), pk(B_LIT()), e3(i, 3), z);
    assert(dmax(e3(i, 3), z) =~= e3(i, 3));
}

proof fn lemma_fits_fxs(m: u8, i: nat)
    requires
        i < 3,
    ensures
        fits(fxs(m, i), e3(i, (3 * b01(m, i as int)) as nat)),
{
    if bit(m, i as int) {
        lemma_fits_fx(i);
    }
}

proof fn lemma_fits_fxp(m: u8)
    ensures
        fits(fxp(m), fdeg(m)),
{
    let c0 = (3 * b01(m, 0)) as nat;
    let c1 = (3 * b01(m, 1)) as nat;
    let c2 = (3 * b01(m, 2)) as nat;
    lemma_fits_fxs(m, 0);
    lemma_fits_fxs(m, 1);
    lemma_fits_fxs(m, 2);
    lemma_fits_mul(fxs(m, 0), fxs(m, 1), e3(0, c0), e3(1, c1));
    assert(dsum(e3(0, c0), e3(1, c1)) =~= seq![c0, c1, 0nat]);
    lemma_fits_mul(pmul(fxs(m, 0), fxs(m, 1)), fxs(m, 2), seq![c0, c1, 0nat], e3(2, c2));
    assert(dsum(seq![c0, c1, 0nat], e3(2, c2)) =~= fdeg(m));
}

// ---------------------------------------------------------------------------------------------
// Degree tracking
// ---------------------------------------------------------------------------------------------

proof fn lemma_rrow_wit(c: MP, row: Seq<int>, q: MP)
    requires
        row.len() == 3,
        !rz(row),
        row[1] >= 0,
        row[2] >= 0,
        fits(q, dn(row)),
        agree(q, c),
    ensures
        rrow(c, row),
{
}

proof fn lemma_rrow_add(c1: MP, r1: Seq<int>, c2: MP, r2: Seq<int>)
    requires
        rrow(c1, r1),
        rrow(c2, r2),
    ensures
        rrow(padd(c1, c2), rmax(r1, r2)),
{
    let c = padd(c1, c2);
    if rz(r1) && rz(r2) {
        assert forall|xs: Seq<int>| #[trigger] ev(c, xs) == 0 by {
            lemma_ev_add(c1, c2, xs);
        }
    } else if rz(r1) {
        let q2 = choose|q: MP| #[trigger] fits(q, dn(r2)) && agree(q, c2);
        assert forall|xs: Seq<int>| #[trigger] ev(q2, xs) == ev(c, xs) by {
            lemma_ev_add(c1, c2, xs);
        }
        lemma_rrow_wit(c, r2, q2);
    } else if rz(r2) {
        let q1 = choose|q: MP| #[trigger] fits(q, dn(r1)) && agree(q, c1);
        assert forall|xs: Seq<int>| #[trigger] ev(q1, xs) == ev(c, xs) by {
            lemma_ev_add(c1, c2, xs);
        }
        lemma_rrow_wit(c, r1, q1);
    } else {
        let q1 = choose|q: MP| #[trigger] fits(q, dn(r1)) && agree(q, c1);
        let q2 = choose|q: MP| #[trigger] fits(q, dn(r2)) && agree(q, c2);
        let q = padd(q1, q2);
        lemma_fits_add(q1, q2, dn(r1), dn(r2));
        assert(dmax(dn(r1), dn(r2)) =~= dn(rmax(r1, r2)));
        assert forall|xs: Seq<int>| #[trigger] ev(q, xs) == ev(c, xs) by {
            lemma_ev_add(c1, c2, xs);
            lemma_ev_add(q1, q2, xs);
        }
        lemma_rrow_wit(c, rmax(r1, r2), q);
    }
}

/// The per-pair step of lemma_rfits_mul: the term's degree is da[s] + db[s ^ r] plus the
/// 3 per variable that the reduction y_i^2 -> f(x_i) adds.
proof fn lemma_rfits_mul_term(a: RF, b: RF, da: RD, db: RD, s: u8, r: u8)
    requires
        rfits(a, da),
        rfits(b, db),
        s < 8,
        r < 8,
    ensures
        rrow(rf_term(a, b, s, r), rd_pair(da, db, s, r)),
{
    lemma_bits(s, r);
    let t = s ^ r;
    let m = s & t;
    let ca = a[s as int];
    let cb = b[t as int];
    let u = da[s as int];
    let v = db[t as int];
    assert(rrow(ca, u));
    assert(rrow(cb, v));
    let c = rf_term(a, b, s, r);
    if rz(u) || rz(v) {
        assert forall|xs: Seq<int>| #[trigger] ev(c, xs) == 0 by {
            lemma_ev_mul(ca, cb, xs);
            lemma_ev_mul(pmul(ca, cb), fxp(m), xs);
            if rz(u) {
                assert(ev(ca, xs) == 0);
            } else {
                assert(ev(cb, xs) == 0);
            }
            lemma_mul_basics(ev(ca, xs));
            lemma_mul_basics(ev(cb, xs));
            lemma_mul_basics(ev(fxp(m), xs));
        }
    } else {
        let qa = choose|q: MP| #[trigger] fits(q, dn(u)) && agree(q, ca);
        let qb = choose|q: MP| #[trigger] fits(q, dn(v)) && agree(q, cb);
        let w = pmul(pmul(qa, qb), fxp(m));
        lemma_fits_mul(qa, qb, dn(u), dn(v));
        lemma_fits_fxp(m);
        lemma_fits_mul(pmul(qa, qb), fxp(m), dsum(dn(u), dn(v)), fdeg(m));
        assert(dsum(dsum(dn(u), dn(v)), fdeg(m)) =~= dn(rd_pair(da, db, s, r)));
        assert forall|xs: Seq<int>| #[trigger] ev(w, xs) == ev(c, xs) by {
            lemma_ev_mul(ca, cb, xs);
            lemma_ev_mul(pmul(ca, cb), fxp(m), xs);
            lemma_ev_mul(qa, qb, xs);
            lemma_ev_mul(pmul(qa, qb), fxp(m), xs);
            assert(ev(qa, xs) == ev(ca, xs));
            assert(ev(qb, xs) == ev(cb, xs));
        }
        lemma_rrow_wit(c, rd_pair(da, db, s, r), w);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rfits_part(a: RF, b: RF, da: RD, db: RD, r: u8, k: nat)
    requires
        rfits(a, da),
        rfits(b, db),
        r < 8,
        k <= 7,
    ensures
        rrow(rf_part(a, b, r, k), rd_part(da, db, r, k)),
    decreases k,
{
    lemma_rfits_mul_term(a, b, da, db, k as u8, r);
    if k > 0 {
        let k1 = (k - 1) as nat;
        lemma_rfits_part(a, b, da, db, r, k1);
        lemma_rrow_add(
            rf_part(a, b, r, k1),
            rd_part(da, db, r, k1),
            rf_term(a, b, k as u8, r),
            rd_pair(da, db, k as u8, r),
        );
    }
}

pub(crate) proof fn lemma_rfits_add(a: RF, b: RF, da: RD, db: RD)
    requires
        rfits(a, da),
        rfits(b, db),
    ensures
        rfits(rf_add(a, b), rd_add(da, db)),
{
    assert forall|s: int| 0 <= s < 8 implies #[trigger] rrow(rf_add(a, b)[s], rd_add(da, db)[s]) by {
        assert(rrow(a[s], da[s]) && rrow(b[s], db[s]));
        lemma_rrow_add(a[s], da[s], b[s], db[s]);
    }
}

pub(crate) proof fn lemma_rfits_mul(a: RF, b: RF, da: RD, db: RD)
    requires
        rfits(a, da),
        rfits(b, db),
    ensures
        rfits(rf_mul(a, b), rd_mul(da, db)),
{
    assert forall|r: int| 0 <= r < 8 implies #[trigger] rrow(rf_mul(a, b)[r], rd_mul(da, db)[r]) by {
        lemma_rfits_part(a, b, da, db, r as u8, 7);
    }
}

pub(crate) proof fn lemma_rfits_k(c: int)
    ensures
        rfits(rf_k(c), rd_k()),
{
    assert forall|s: int| 0 <= s < 8 implies #[trigger] rrow(rf_k(c)[s], rd_k()[s]) by {
        if s == 0 {
            lemma_rrow_wit(pk(c), seq![0int, 0, 0], pk(c));
        } else {
            assert forall|xs: Seq<int>| #[trigger] ev(pk(0), xs) == 0 by {}
        }
    }
}

pub(crate) proof fn lemma_rfits_x(i: nat)
    requires
        i < 3,
    ensures
        rfits(rf_x(i), rd_x(i)),
{
    assert forall|s: int| 0 <= s < 8 implies #[trigger] rrow(rf_x(i)[s], rd_x(i)[s]) by {
        if s == 0 {
            lemma_fits_x(i, dn(unit(i)));
            lemma_rrow_wit(px(i), unit(i), px(i));
        } else {
            assert forall|xs: Seq<int>| #[trigger] ev(pk(0), xs) == 0 by {}
        }
    }
}

pub(crate) proof fn lemma_rfits_y(i: nat)
    requires
        i < 3,
    ensures
        rfits(rf_y(i), rd_y(i)),
{
    assert forall|s: int| 0 <= s < 8 implies #[trigger] rrow(rf_y(i)[s], rd_y(i)[s]) by {
        if s == yb(i) {
            lemma_rrow_wit(pk(1), seq![0int, 0, 0], pk(1));
        } else {
            assert forall|xs: Seq<int>| #[trigger] ev(pk(0), xs) == 0 by {}
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Homomorphism
// ---------------------------------------------------------------------------------------------

proof fn lemma_ra_add(a: RF, b: RF, xs: Seq<int>, ys: Seq<int>, s: u8)
    requires
        s < 8,
    ensures
        ra(rf_add(a, b), xs, ys, s) == ra(a, xs, ys, s) + ra(b, xs, ys, s),
{
    lemma_ev_add(a[s as int], b[s as int], xs);
    lemma_mul_is_distributive_add(yw(ys, s), ev(a[s as int], xs), ev(b[s as int], xs));
}

pub(crate) proof fn lemma_rf_add_hom(a: RF, b: RF, xs: Seq<int>, ys: Seq<int>)
    ensures
        rval(rf_add(a, b), xs, ys) == rval(a, xs, ys) + rval(b, xs, ys),
{
    lemma_ra_add(a, b, xs, ys, 0);
    lemma_ra_add(a, b, xs, ys, 1);
    lemma_ra_add(a, b, xs, ys, 2);
    lemma_ra_add(a, b, xs, ys, 3);
    lemma_ra_add(a, b, xs, ys, 4);
    lemma_ra_add(a, b, xs, ys, 5);
    lemma_ra_add(a, b, xs, ys, 6);
    lemma_ra_add(a, b, xs, ys, 7);
}

proof fn lemma_ra_k0(a: RF, xs: Seq<int>, ys: Seq<int>, s: u8)
    requires
        a[s as int] == pk(0),
    ensures
        ra(a, xs, ys, s) == 0,
{
    lemma_mul_basics(yw(ys, s));
}

/// The components other than s0 are pk(0).
proof fn lemma_rval_one(a: RF, xs: Seq<int>, ys: Seq<int>, s0: u8)
    requires
        s0 < 8,
        forall|s: int| 0 <= s < 8 && s != s0 ==> #[trigger] a[s] == pk(0),
    ensures
        rval(a, xs, ys) == ra(a, xs, ys, s0),
{
    if s0 != 0 { lemma_ra_k0(a, xs, ys, 0); }
    if s0 != 1 { lemma_ra_k0(a, xs, ys, 1); }
    if s0 != 2 { lemma_ra_k0(a, xs, ys, 2); }
    if s0 != 3 { lemma_ra_k0(a, xs, ys, 3); }
    if s0 != 4 { lemma_ra_k0(a, xs, ys, 4); }
    if s0 != 5 { lemma_ra_k0(a, xs, ys, 5); }
    if s0 != 6 { lemma_ra_k0(a, xs, ys, 6); }
    if s0 != 7 { lemma_ra_k0(a, xs, ys, 7); }
}

pub(crate) proof fn lemma_rval_k(c: int, xs: Seq<int>, ys: Seq<int>)
    ensures
        rval(rf_k(c), xs, ys) == c,
{
    lemma_rval_one(rf_k(c), xs, ys, 0);
    assert(yw(ys, 0) == 1);
    lemma_mul_basics(c);
}

pub(crate) proof fn lemma_rval_x(i: nat, xs: Seq<int>, ys: Seq<int>)
    requires
        i < xs.len(),
    ensures
        rval(rf_x(i), xs, ys) == xs[i as int],
{
    lemma_ev_x(i, xs);
    lemma_rval_one(rf_x(i), xs, ys, 0);
    assert(yw(ys, 0) == 1);
    lemma_mul_basics(xs[i as int]);
}

pub(crate) proof fn lemma_rval_y(i: nat, xs: Seq<int>, ys: Seq<int>)
    requires
        i < 3,
    ensures
        rval(rf_y(i), xs, ys) == ys[i as int],
{
    let s0 = yb(i) as u8;
    lemma_rval_one(rf_y(i), xs, ys, s0);
    lemma_mul_basics(ys[i as int]);
    let e = ev(rf_y(i)[s0 as int], xs);
    if i == 0 {
        assert(yf(ys, 1, 0) == ys[0] && yf(ys, 1, 1) == 1 && yf(ys, 1, 2) == 1);
        lemma_mul_basics(ys[0]);
    } else if i == 1 {
        assert(yf(ys, 2, 0) == 1 && yf(ys, 2, 1) == ys[1] && yf(ys, 2, 2) == 1);
        lemma_mul_basics(ys[1]);
    } else {
        assert(yf(ys, 4, 0) == 1 && yf(ys, 4, 1) == 1 && yf(ys, 4, 2) == ys[2]);
        lemma_mul_basics(ys[2]);
    }
    assert(yw(ys, s0) == ys[i as int]);
    assert(e == 1);
}

/// One bit of y^s y^t == y^(s^t) prod_{i in s&t} y_i^2, with y_i^2 == f(x_i) mod p.
proof fn lemma_bit_sq(xs: Seq<int>, ys: Seq<int>, s: u8, t: u8, i: int)
    requires
        on3(xs, ys),
        s < 8,
        t < 8,
        0 <= i < 3,
    ensures
        fmod(yf(ys, s, i) * yf(ys, t, i)) == fmod(yf(ys, s ^ t, i) * ff(xs, s & t, i)),
{
    lemma_bits(s, t);
    lemma_group_consts();
    assert(on_pt(xs[i], ys[i]));
    assert(bit(s ^ t, i) == (bit(s, i) != bit(t, i)));
    assert(bit(s & t, i) == (bit(s, i) && bit(t, i)));
}

proof fn lemma_yw_mul(xs: Seq<int>, ys: Seq<int>, s: u8, t: u8)
    requires
        on3(xs, ys),
        s < 8,
        t < 8,
    ensures
        fmod(yw(ys, s) * yw(ys, t)) == fmod(yw(ys, s ^ t) * fw(xs, s & t)),
{
    let (u0, u1, u2) = (yf(ys, s, 0), yf(ys, s, 1), yf(ys, s, 2));
    let (v0, v1, v2) = (yf(ys, t, 0), yf(ys, t, 1), yf(ys, t, 2));
    let (w0, w1, w2) = (yf(ys, s ^ t, 0), yf(ys, s ^ t, 1), yf(ys, s ^ t, 2));
    let (f0, f1, f2) = (ff(xs, s & t, 0), ff(xs, s & t, 1), ff(xs, s & t, 2));
    lemma_mul4(u0 * u1, u2, v0 * v1, v2);
    lemma_mul4(u0, u1, v0, v1);
    lemma_bit_sq(xs, ys, s, t, 0);
    lemma_bit_sq(xs, ys, s, t, 1);
    lemma_bit_sq(xs, ys, s, t, 2);
    lemma_cong_mul(u0 * v0, u1 * v1, w0 * f0, w1 * f1);
    lemma_cong_mul((u0 * v0) * (u1 * v1), u2 * v2, (w0 * f0) * (w1 * f1), w2 * f2);
    lemma_mul4(w0, f0, w1, f1);
    lemma_mul4(w0 * w1, f0 * f1, w2, f2);
}

pub(crate) open spec fn tt(a: RF, b: RF, xs: Seq<int>, ys: Seq<int>, s: u8, r: u8) -> int {
    ra(a, xs, ys, s) * ra(b, xs, ys, s ^ r)
}

proof fn lemma_term_hom(a: RF, b: RF, xs: Seq<int>, ys: Seq<int>, s: u8, r: u8)
    requires
        on3(xs, ys),
        s < 8,
        r < 8,
    ensures
        fmod(yw(ys, r) * ev(rf_term(a, b, s, r), xs)) == fmod(tt(a, b, xs, ys, s, r)),
{
    lemma_bits(s, r);
    let t = s ^ r;
    let m = s & t;
    let ea = ev(a[s as int], xs);
    let eb = ev(b[t as int], xs);
    let p = ea * eb;
    let f = fw(xs, m);
    lemma_ev_mul(a[s as int], b[t as int], xs);
    lemma_ev_mul(pmul(a[s as int], b[t as int]), fxp(m), xs);
    lemma_ev_fxp(m, xs);
    // yw(r) (p f) == (yw(r) f) p
    lemma_mul_is_commutative(p, f);
    lemma_mul_is_associative(yw(ys, r), f, p);
    // yw(r) f == yw(s ^ t) f(s & t) == yw(s) yw(t) mod p
    lemma_yw_mul(xs, ys, s, t);
    lemma_cong_mul(yw(ys, r) * f, p, yw(ys, s) * yw(ys, t), p);
    lemma_mul4(yw(ys, s), yw(ys, t), ea, eb);
}

pub(crate) open spec fn tpart(a: RF, b: RF, xs: Seq<int>, ys: Seq<int>, r: u8, k: nat) -> int
    decreases k,
{
    if k == 0 {
        tt(a, b, xs, ys, 0, r)
    } else {
        tpart(a, b, xs, ys, r, (k - 1) as nat) + tt(a, b, xs, ys, k as u8, r)
    }
}

#[verifier::spinoff_prover]
proof fn lemma_part_hom(a: RF, b: RF, xs: Seq<int>, ys: Seq<int>, r: u8, k: nat)
    requires
        on3(xs, ys),
        r < 8,
        k <= 7,
    ensures
        fmod(yw(ys, r) * ev(rf_part(a, b, r, k), xs)) == fmod(tpart(a, b, xs, ys, r, k)),
    decreases k,
{
    lemma_term_hom(a, b, xs, ys, k as u8, r);
    if k > 0 {
        let k1 = (k - 1) as nat;
        let e1 = ev(rf_part(a, b, r, k1), xs);
        let e2 = ev(rf_term(a, b, k as u8, r), xs);
        lemma_part_hom(a, b, xs, ys, r, k1);
        lemma_ev_add(rf_part(a, b, r, k1), rf_term(a, b, k as u8, r), xs);
        lemma_mul_is_distributive_add(yw(ys, r), e1, e2);
        lemma_cong_add(
            yw(ys, r) * e1,
            yw(ys, r) * e2,
            tpart(a, b, xs, ys, r, k1),
            tt(a, b, xs, ys, k as u8, r),
        );
    }
}

/// Row r of the double sum: sum_s ra(a, s) ra(b, s ^ r).
pub(crate) open spec fn trow(a: RF, b: RF, xs: Seq<int>, ys: Seq<int>, r: u8) -> int {
    tt(a, b, xs, ys, 0, r) + tt(a, b, xs, ys, 1, r) + tt(a, b, xs, ys, 2, r) + tt(a, b, xs, ys, 3, r)
        + tt(a, b, xs, ys, 4, r) + tt(a, b, xs, ys, 5, r) + tt(a, b, xs, ys, 6, r)
        + tt(a, b, xs, ys, 7, r)
}

proof fn lemma_ra_mul(a: RF, b: RF, xs: Seq<int>, ys: Seq<int>, r: u8)
    requires
        on3(xs, ys),
        r < 8,
    ensures
        fmod(ra(rf_mul(a, b), xs, ys, r)) == fmod(trow(a, b, xs, ys, r)),
{
    lemma_part_hom(a, b, xs, ys, r, 7);
    assert(tpart(a, b, xs, ys, r, 7) == trow(a, b, xs, ys, r)) by {
        reveal_with_fuel(tpart, 8);
    }
}

/// sum_r ra(b, s ^ r).
pub(crate) open spec fn vperm(b: RF, xs: Seq<int>, ys: Seq<int>, s: u8) -> int {
    ra(b, xs, ys, s ^ 0) + ra(b, xs, ys, s ^ 1) + ra(b, xs, ys, s ^ 2) + ra(b, xs, ys, s ^ 3)
        + ra(b, xs, ys, s ^ 4) + ra(b, xs, ys, s ^ 5) + ra(b, xs, ys, s ^ 6) + ra(b, xs, ys, s ^ 7)
}

/// r -> s ^ r permutes [0, 8).
proof fn lemma_perm(b: RF, xs: Seq<int>, ys: Seq<int>, s: u8)
    requires
        s < 8,
    ensures
        vperm(b, xs, ys, s) == rval(b, xs, ys),
{
    lemma_bits(s, 0);
    lemma_bits(s, 1);
    lemma_bits(s, 2);
    lemma_bits(s, 3);
    lemma_bits(s, 4);
    lemma_bits(s, 5);
    lemma_bits(s, 6);
    lemma_bits(s, 7);
    if s == 0 {
    } else if s == 1 {
    } else if s == 2 {
    } else if s == 3 {
    } else if s == 4 {
    } else if s == 5 {
    } else if s == 6 {
    } else {
    }
}

proof fn lemma_row_dist(a: RF, b: RF, xs: Seq<int>, ys: Seq<int>, s: u8)
    requires
        s < 8,
    ensures
        ra(a, xs, ys, s) * rval(b, xs, ys) == tt(a, b, xs, ys, s, 0) + tt(a, b, xs, ys, s, 1)
            + tt(a, b, xs, ys, s, 2) + tt(a, b, xs, ys, s, 3) + tt(a, b, xs, ys, s, 4)
            + tt(a, b, xs, ys, s, 5) + tt(a, b, xs, ys, s, 6) + tt(a, b, xs, ys, s, 7),
{
    lemma_perm(b, xs, ys, s);
    lemma_dist8(
        ra(a, xs, ys, s),
        ra(b, xs, ys, s ^ 0),
        ra(b, xs, ys, s ^ 1),
        ra(b, xs, ys, s ^ 2),
        ra(b, xs, ys, s ^ 3),
        ra(b, xs, ys, s ^ 4),
        ra(b, xs, ys, s ^ 5),
        ra(b, xs, ys, s ^ 6),
        ra(b, xs, ys, s ^ 7),
    );
}

/// sum_r trow(r) == rval(a) rval(b) (exact).
proof fn lemma_trows(a: RF, b: RF, xs: Seq<int>, ys: Seq<int>)
    ensures
        trow(a, b, xs, ys, 0) + trow(a, b, xs, ys, 1) + trow(a, b, xs, ys, 2) + trow(a, b, xs, ys, 3)
            + trow(a, b, xs, ys, 4) + trow(a, b, xs, ys, 5) + trow(a, b, xs, ys, 6)
            + trow(a, b, xs, ys, 7) == rval(a, xs, ys) * rval(b, xs, ys),
{
    let vb = rval(b, xs, ys);
    lemma_row_dist(a, b, xs, ys, 0);
    lemma_row_dist(a, b, xs, ys, 1);
    lemma_row_dist(a, b, xs, ys, 2);
    lemma_row_dist(a, b, xs, ys, 3);
    lemma_row_dist(a, b, xs, ys, 4);
    lemma_row_dist(a, b, xs, ys, 5);
    lemma_row_dist(a, b, xs, ys, 6);
    lemma_row_dist(a, b, xs, ys, 7);
    lemma_dist8(
        vb,
        ra(a, xs, ys, 0),
        ra(a, xs, ys, 1),
        ra(a, xs, ys, 2),
        ra(a, xs, ys, 3),
        ra(a, xs, ys, 4),
        ra(a, xs, ys, 5),
        ra(a, xs, ys, 6),
        ra(a, xs, ys, 7),
    );
    lemma_mul_is_commutative(vb, rval(a, xs, ys));
    lemma_mul_is_commutative(vb, ra(a, xs, ys, 0));
    lemma_mul_is_commutative(vb, ra(a, xs, ys, 1));
    lemma_mul_is_commutative(vb, ra(a, xs, ys, 2));
    lemma_mul_is_commutative(vb, ra(a, xs, ys, 3));
    lemma_mul_is_commutative(vb, ra(a, xs, ys, 4));
    lemma_mul_is_commutative(vb, ra(a, xs, ys, 5));
    lemma_mul_is_commutative(vb, ra(a, xs, ys, 6));
    lemma_mul_is_commutative(vb, ra(a, xs, ys, 7));
}

pub(crate) proof fn lemma_rf_mul_hom(a: RF, b: RF, xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        fmod(rval(rf_mul(a, b), xs, ys)) == fmod(rval(a, xs, ys) * rval(b, xs, ys)),
{
    let m = rf_mul(a, b);
    lemma_ra_mul(a, b, xs, ys, 0);
    lemma_ra_mul(a, b, xs, ys, 1);
    lemma_ra_mul(a, b, xs, ys, 2);
    lemma_ra_mul(a, b, xs, ys, 3);
    lemma_ra_mul(a, b, xs, ys, 4);
    lemma_ra_mul(a, b, xs, ys, 5);
    lemma_ra_mul(a, b, xs, ys, 6);
    lemma_ra_mul(a, b, xs, ys, 7);
    lemma_cong8(
        ra(m, xs, ys, 0),
        ra(m, xs, ys, 1),
        ra(m, xs, ys, 2),
        ra(m, xs, ys, 3),
        ra(m, xs, ys, 4),
        ra(m, xs, ys, 5),
        ra(m, xs, ys, 6),
        ra(m, xs, ys, 7),
        trow(a, b, xs, ys, 0),
        trow(a, b, xs, ys, 1),
        trow(a, b, xs, ys, 2),
        trow(a, b, xs, ys, 3),
        trow(a, b, xs, ys, 4),
        trow(a, b, xs, ys, 5),
        trow(a, b, xs, ys, 6),
        trow(a, b, xs, ys, 7),
    );
    lemma_trows(a, b, xs, ys);
}

/// Linking a formal value to a plain one, mod p.
pub(crate) proof fn lemma_lk_add(a: RF, b: RF, xs: Seq<int>, ys: Seq<int>, va: int, vb: int)
    requires
        fmod(rval(a, xs, ys)) == fmod(va),
        fmod(rval(b, xs, ys)) == fmod(vb),
    ensures
        fmod(rval(rf_add(a, b), xs, ys)) == fmod(va + vb),
{
    lemma_rf_add_hom(a, b, xs, ys);
    lemma_cong_add(rval(a, xs, ys), rval(b, xs, ys), va, vb);
}

pub(crate) proof fn lemma_lk_mul(a: RF, b: RF, xs: Seq<int>, ys: Seq<int>, va: int, vb: int)
    requires
        on3(xs, ys),
        fmod(rval(a, xs, ys)) == fmod(va),
        fmod(rval(b, xs, ys)) == fmod(vb),
    ensures
        fmod(rval(rf_mul(a, b), xs, ys)) == fmod(va * vb),
{
    lemma_rf_mul_hom(a, b, xs, ys);
    lemma_cong_mul(rval(a, xs, ys), rval(b, xs, ys), va, vb);
}

// ---------------------------------------------------------------------------------------------
// Signs and Hadamard inversion
// ---------------------------------------------------------------------------------------------

/// sgb(n, v) = -v if n else v.
pub(crate) open spec fn sgb(n: bool, v: int) -> int {
    if n {
        -v
    } else {
        v
    }
}

proof fn lemma_sgb_mul(n: bool, a: int, m: bool, b: int)
    ensures
        sgb(n, a) * sgb(m, b) == sgb(n != m, a * b),
{
    lemma_mul_unary_negation(a, b);
    lemma_mul_cancels_negatives(a, b);
}

proof fn lemma_yw_sgn(ys: Seq<int>, sig: u8, s: u8)
    ensures
        yw(sgn(sig, ys), s) == pm1(chi(sig, s), yw(ys, s)),
{
    let zs = sgn(sig, ys);
    let (n0, n1, n2) = (ng(sig, s, 0), ng(sig, s, 1), ng(sig, s, 2));
    let (u0, u1, u2) = (yf(ys, s, 0), yf(ys, s, 1), yf(ys, s, 2));
    assert(zs[0] == sgb(bit(sig, 0), ys[0]) && zs[1] == sgb(bit(sig, 1), ys[1]) && zs[2] == sgb(
        bit(sig, 2),
        ys[2],
    ));
    assert(yf(zs, s, 0) == sgb(n0, u0));
    assert(yf(zs, s, 1) == sgb(n1, u1));
    assert(yf(zs, s, 2) == sgb(n2, u2));
    lemma_sgb_mul(n0, u0, n1, u1);
    lemma_sgb_mul(n0 != n1, u0 * u1, n2, u2);
}

pub(crate) open spec fn cv(g: RF, xs: Seq<int>) -> Seq<int> {
    Seq::new(8, |s: int| ev(g[s], xs))
}

proof fn lemma_ra_sgn(g: RF, xs: Seq<int>, ys: Seq<int>, sig: u8, s: u8)
    requires
        s < 8,
    ensures
        ra(g, xs, sgn(sig, ys), s) == hterm(sig, cv(g, xs), ys, s),
{
    reveal(hw);
    lemma_yw_sgn(ys, sig, s);
    lemma_mul_unary_negation(yw(ys, s), ev(g[s as int], xs));
}

proof fn lemma_rval_sgn(g: RF, xs: Seq<int>, ys: Seq<int>, sig: u8)
    ensures
        rval(g, xs, sgn(sig, ys)) == hsum(sig, cv(g, xs), ys),
{
    reveal(hsum);
    lemma_ra_sgn(g, xs, ys, sig, 0);
    lemma_ra_sgn(g, xs, ys, sig, 1);
    lemma_ra_sgn(g, xs, ys, sig, 2);
    lemma_ra_sgn(g, xs, ys, sig, 3);
    lemma_ra_sgn(g, xs, ys, sig, 4);
    lemma_ra_sgn(g, xs, ys, sig, 5);
    lemma_ra_sgn(g, xs, ys, sig, 6);
    lemma_ra_sgn(g, xs, ys, sig, 7);
}

pub(crate) open spec fn hinv(c: Seq<int>, ys: Seq<int>, s: u8) -> int {
    pm1(chi(0, s), hsum(0, c, ys)) + pm1(chi(1, s), hsum(1, c, ys)) + pm1(chi(2, s), hsum(2, c, ys))
        + pm1(chi(3, s), hsum(3, c, ys)) + pm1(chi(4, s), hsum(4, c, ys)) + pm1(chi(5, s), hsum(5, c, ys))
        + pm1(chi(6, s), hsum(6, c, ys)) + pm1(chi(7, s), hsum(7, c, ys))
}

/// sum_sig chi(sig, s) chi(sig, t) == 8 [s == t].
proof fn lemma_hinv(c: Seq<int>, ys: Seq<int>, s: u8)
    requires
        s < 8,
    ensures
        hinv(c, ys, s) == 8 * hw(ys, c, s),
{
    reveal(hsum);
    if s == 0 {
    } else if s == 1 {
    } else if s == 2 {
    } else if s == 3 {
    } else if s == 4 {
    } else if s == 5 {
    } else if s == 6 {
    } else {
    }
}

proof fn lemma_yw_nz(ys: Seq<int>, s: u8)
    requires
        forall|i: int| 0 <= i < 3 ==> fmod(#[trigger] ys[i]) != 0,
    ensures
        fmod(yw(ys, s)) != 0,
{
    lemma_group_consts();
    let (u0, u1, u2) = (yf(ys, s, 0), yf(ys, s, 1), yf(ys, s, 2));
    assert(fmod(ys[0]) != 0 && fmod(ys[1]) != 0 && fmod(ys[2]) != 0);
    assert(fmod(u0) != 0 && fmod(u1) != 0 && fmod(u2) != 0);
    if fmod(u0 * u1) == 0 {
        lemma_no_zero_div(u0, u1);
    }
    if fmod(yw(ys, s)) == 0 {
        lemma_no_zero_div(u0 * u1, u2);
    }
}

proof fn lemma_hadamard_at(c: Seq<int>, ys: Seq<int>, t: u8)
    requires
        t < 8,
        forall|i: int| 0 <= i < 3 ==> fmod(#[trigger] ys[i]) != 0,
        fmod(hsum(0, c, ys)) == 0 && fmod(hsum(1, c, ys)) == 0,
        fmod(hsum(2, c, ys)) == 0 && fmod(hsum(3, c, ys)) == 0,
        fmod(hsum(4, c, ys)) == 0 && fmod(hsum(5, c, ys)) == 0,
        fmod(hsum(6, c, ys)) == 0 && fmod(hsum(7, c, ys)) == 0,
    ensures
        fmod(c[t as int]) == 0,
{
    lemma_group_consts();
    lemma_hinv(c, ys, t);
    lemma_zero_mul(-1, hsum(0, c, ys));
    lemma_zero_mul(-1, hsum(1, c, ys));
    lemma_zero_mul(-1, hsum(2, c, ys));
    lemma_zero_mul(-1, hsum(3, c, ys));
    lemma_zero_mul(-1, hsum(4, c, ys));
    lemma_zero_mul(-1, hsum(5, c, ys));
    lemma_zero_mul(-1, hsum(6, c, ys));
    lemma_zero_mul(-1, hsum(7, c, ys));
    lemma_zero8(
        pm1(chi(0, t), hsum(0, c, ys)),
        pm1(chi(1, t), hsum(1, c, ys)),
        pm1(chi(2, t), hsum(2, c, ys)),
        pm1(chi(3, t), hsum(3, c, ys)),
        pm1(chi(4, t), hsum(4, c, ys)),
        pm1(chi(5, t), hsum(5, c, ys)),
        pm1(chi(6, t), hsum(6, c, ys)),
        pm1(chi(7, t), hsum(7, c, ys)),
    );
    let w = yw(ys, t) * c[t as int];
    reveal(hw);
    lemma_no_zero_div(8, w);
    lemma_yw_nz(ys, t);
    lemma_no_zero_div(yw(ys, t), c[t as int]);
}

pub(crate) proof fn lemma_hadamard(c: Seq<int>, ys: Seq<int>)
    requires
        forall|i: int| 0 <= i < 3 ==> fmod(#[trigger] ys[i]) != 0,
        forall|sig: u8| sig < 8 ==> fmod(#[trigger] hsum(sig, c, ys)) == 0,
    ensures
        forall|s: int| 0 <= s < 8 ==> fmod(#[trigger] c[s]) == 0,
{
    assert(fmod(hsum(0, c, ys)) == 0 && fmod(hsum(1, c, ys)) == 0 && fmod(hsum(2, c, ys)) == 0
        && fmod(hsum(3, c, ys)) == 0);
    assert(fmod(hsum(4, c, ys)) == 0 && fmod(hsum(5, c, ys)) == 0 && fmod(hsum(6, c, ys)) == 0
        && fmod(hsum(7, c, ys)) == 0);
    assert forall|s: int| 0 <= s < 8 implies fmod(#[trigger] c[s]) == 0 by {
        lemma_hadamard_at(c, ys, s as u8);
    }
}

// ---------------------------------------------------------------------------------------------
// The identity theorem
// ---------------------------------------------------------------------------------------------

/// At a grid point, every component vanishes.
proof fn lemma_id_pt(g: RF, gx: Seq<Seq<int>>, gy: Seq<Seq<int>>, i: int, j: int, l: int)
    requires
        grid_ok(gx, gy),
        signs_vanish(g, gx, gy),
        in_box(gx, i, j, l),
    ensures
        forall|s: int| 0 <= s < 8 ==> fmod(#[trigger] ev(g[s], gpt(gx, i, j, l))) == 0,
{
    let xs = gpt(gx, i, j, l);
    let ys = gpt(gy, i, j, l);
    let c = cv(g, xs);
    assert(gk_ok(gx, gy, 0) && gk_ok(gx, gy, 1) && gk_ok(gx, gy, 2));
    assert(gpt_ok(gx[0][i], gy[0][i]) && gpt_ok(gx[1][j], gy[1][j]) && gpt_ok(gx[2][l], gy[2][l]));
    assert forall|k: int| 0 <= k < 3 implies fmod(#[trigger] ys[k]) != 0 by {
        if k == 0 {
        } else if k == 1 {
        } else {
        }
    }
    assert forall|sig: u8| sig < 8 implies fmod(#[trigger] hsum(sig, c, ys)) == 0 by {
        lemma_rval_sgn(g, xs, ys, sig);
        assert(fmod(rval(g, gpt(gx, i, j, l), sgn(sig, gpt(gy, i, j, l)))) == 0);
    }
    lemma_hadamard(c, ys);
    assert forall|s: int| 0 <= s < 8 implies fmod(#[trigger] ev(g[s], xs)) == 0 by {
        assert(c[s] == ev(g[s], xs));
    }
}

/// Each component vanishes everywhere.
proof fn lemma_id_comp(g: RF, d: RD, gx: Seq<Seq<int>>, gy: Seq<Seq<int>>, s: int)
    requires
        rfits(g, d),
        grid_ok(gx, gy),
        deg_fits(d, gx),
        signs_vanish(g, gx, gy),
        0 <= s < 8,
    ensures
        forall|xs: Seq<int>| xs.len() == 3 ==> fmod(#[trigger] ev(g[s], xs)) == 0,
{
    lemma_group_consts();
    let row = d[s];
    assert(rrow(g[s], row));
    if rz(row) {
        assert forall|xs: Seq<int>| xs.len() == 3 implies fmod(#[trigger] ev(g[s], xs)) == 0 by {
            assert(ev(g[s], xs) == 0);
        }
    } else {
        let q = choose|q: MP| #[trigger] fits(q, dn(row)) && agree(q, g[s]);
        let ds = dn(row);
        assert forall|k: int| 0 <= k < gx.len() implies #[trigger] gx[k].len() > ds[k]
            && distinct_mod_p(gx[k]) by {
            assert(d[s][k] < gx[k].len());
            assert(gk_ok(gx, gy, k));
        }
        assert forall|xs: Seq<int>| in_grid(xs, gx) implies fmod(#[trigger] ev(q, xs)) == 0 by {
            assert(gx[0].contains(xs[0]) && gx[1].contains(xs[1]) && gx[2].contains(xs[2]));
            let i = choose|i: int| 0 <= i < gx[0].len() && gx[0][i] == xs[0];
            let j = choose|j: int| 0 <= j < gx[1].len() && gx[1][j] == xs[1];
            let l = choose|l: int| 0 <= l < gx[2].len() && gx[2][l] == xs[2];
            assert(xs =~= gpt(gx, i, j, l));
            lemma_id_pt(g, gx, gy, i, j, l);
            assert(ev(q, xs) == ev(g[s], xs));
        }
        lemma_grid(q, ds, gx);
        assert forall|xs: Seq<int>| xs.len() == 3 implies fmod(#[trigger] ev(g[s], xs)) == 0 by {
            assert(ev(q, xs) == ev(g[s], xs));
        }
    }
}

proof fn lemma_ra_zero(g: RF, xs: Seq<int>, ys: Seq<int>, s: u8)
    requires
        fmod(ev(g[s as int], xs)) == 0,
    ensures
        fmod(ra(g, xs, ys, s)) == 0,
{
    lemma_zero_mul(yw(ys, s), ev(g[s as int], xs));
}

/// Grid vanishing under all y-signs, with degrees below the grid sizes, implies vanishing at
/// every curve point.
pub(crate) proof fn lemma_identity(g: RF, d: RD, gx: Seq<Seq<int>>, gy: Seq<Seq<int>>)
    requires
        rfits(g, d),
        grid_ok(gx, gy),
        deg_fits(d, gx),
        signs_vanish(g, gx, gy),
    ensures
        forall|xs: Seq<int>, ys: Seq<int>| on3(xs, ys) ==> fmod(#[trigger] rval(g, xs, ys)) == 0,
{
    lemma_id_comp(g, d, gx, gy, 0);
    lemma_id_comp(g, d, gx, gy, 1);
    lemma_id_comp(g, d, gx, gy, 2);
    lemma_id_comp(g, d, gx, gy, 3);
    lemma_id_comp(g, d, gx, gy, 4);
    lemma_id_comp(g, d, gx, gy, 5);
    lemma_id_comp(g, d, gx, gy, 6);
    lemma_id_comp(g, d, gx, gy, 7);
    assert forall|xs: Seq<int>, ys: Seq<int>| on3(xs, ys) implies fmod(#[trigger] rval(g, xs, ys))
        == 0 by {
        lemma_ra_zero(g, xs, ys, 0);
        lemma_ra_zero(g, xs, ys, 1);
        lemma_ra_zero(g, xs, ys, 2);
        lemma_ra_zero(g, xs, ys, 3);
        lemma_ra_zero(g, xs, ys, 4);
        lemma_ra_zero(g, xs, ys, 5);
        lemma_ra_zero(g, xs, ys, 6);
        lemma_ra_zero(g, xs, ys, 7);
        lemma_zero8(
            ra(g, xs, ys, 0),
            ra(g, xs, ys, 1),
            ra(g, xs, ys, 2),
            ra(g, xs, ys, 3),
            ra(g, xs, ys, 4),
            ra(g, xs, ys, 5),
            ra(g, xs, ys, 6),
            ra(g, xs, ys, 7),
        );
    }
}

/// Grid points under any y-sign choice are curve points.
pub(crate) proof fn lemma_grid_on3(gx: Seq<Seq<int>>, gy: Seq<Seq<int>>, i: int, j: int, l: int, sig: u8)
    requires
        grid_ok(gx, gy),
        in_box(gx, i, j, l),
    ensures
        on3(gpt(gx, i, j, l), sgn(sig, gpt(gy, i, j, l))),
{
    let xs = gpt(gx, i, j, l);
    let y0 = gpt(gy, i, j, l);
    let ys = sgn(sig, y0);
    assert(gpt_ok(gx[0][i], gy[0][i]) && gpt_ok(gx[1][j], gy[1][j]) && gpt_ok(gx[2][l], gy[2][l]));
    lemma_mul_cancels_negatives(y0[0], y0[0]);
    lemma_mul_cancels_negatives(y0[1], y0[1]);
    lemma_mul_cancels_negatives(y0[2], y0[2]);
    assert(on_pt(xs[0], ys[0]) && on_pt(xs[1], ys[1]) && on_pt(xs[2], ys[2]));
    assert forall|k: int| 0 <= k < 3 implies #[trigger] on_pt(xs[k], ys[k]) by {
        if k == 0 {
        } else if k == 1 {
        } else {
        }
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_cells_forall(c: spec_fn(int, int, int) -> bool, i: int, j: int, lo: int, hi: int)
    requires
        cells_ok(c, i, j, lo, hi),
    ensures
        forall|l: int| lo <= l < hi ==> #[trigger] c(i, j, l),
    decreases hi - lo,
{
    if lo < hi {
        lemma_cells_forall(c, i, j, lo + 1, hi);
    }
}

// ---------------------------------------------------------------------------------------------
// Smoke: (y0 + y1)^2 - f(x0) - f(x1) - 2 y0 y1 == 0 on the curve, on a 4 x 4 x 1 grid
// ---------------------------------------------------------------------------------------------

pub(crate) open spec fn rf_neg(a: RF) -> RF {
    rf_mul(rf_k(-1), a)
}

pub(crate) open spec fn rd_neg(d: RD) -> RD {
    rd_mul(rd_k(), d)
}

pub(crate) open spec fn rf_fx(i: nat) -> RF {
    rf_add(rf_add(rf_mul(rf_mul(rf_x(i), rf_x(i)), rf_x(i)), rf_mul(rf_k(-3), rf_x(i))), rf_k(B_LIT()))
}

pub(crate) open spec fn rd_fx(i: nat) -> RD {
    rd_add(rd_add(rd_mul(rd_mul(rd_x(i), rd_x(i)), rd_x(i)), rd_mul(rd_k(), rd_x(i))), rd_k())
}

pub(crate) open spec fn sm_g() -> RF {
    let y = rf_add(rf_y(0), rf_y(1));
    rf_add(
        rf_add(rf_add(rf_mul(y, y), rf_neg(rf_fx(0))), rf_neg(rf_fx(1))),
        rf_neg(rf_mul(rf_k(2), rf_mul(rf_y(0), rf_y(1)))),
    )
}

pub(crate) open spec fn sm_d() -> RD {
    let y = rd_add(rd_y(0), rd_y(1));
    rd_add(
        rd_add(rd_add(rd_mul(y, y), rd_neg(rd_fx(0))), rd_neg(rd_fx(1))),
        rd_neg(rd_mul(rd_k(), rd_mul(rd_y(0), rd_y(1)))),
    )
}

/// The plain value of sm_g (same association).
pub(crate) open spec fn sm_val(xs: Seq<int>, ys: Seq<int>) -> int {
    let y = ys[0] + ys[1];
    y * y + -1 * fxv(xs[0]) + -1 * fxv(xs[1]) + -1 * (2 * (ys[0] * ys[1]))
}

/// The first 4 x >= 0 with f(x) a nonzero square mod p, and square roots (python3 -I, sha256
/// prefix 8c4e4d24c181 of the (x, y) list).
pub(crate) open spec fn sm_x() -> Seq<int> {
    seq![0int, 5, 6, 8]
}

pub(crate) open spec fn sm_y() -> Seq<int> {
    seq![
        46263761741508638697010950048709651021688891777877937875096931459006746039284int,
        31468013646237722594854082025316614106172411895747863909393730389177298123724int,
        24739918328848417526480033809572464882617473122143770809273908485596236620747int,
        82784132184742902406611976374283817475915538652053173371854007222633983132083int,
    ]
}

pub(crate) open spec fn sm_gx() -> Seq<Seq<int>> {
    seq![sm_x(), sm_x(), seq![sm_x()[0]]]
}

pub(crate) open spec fn sm_gy() -> Seq<Seq<int>> {
    seq![sm_y(), sm_y(), seq![sm_y()[0]]]
}

#[verifier::opaque]
pub(crate) open spec fn sm_cell(i: int, j: int, l: int) -> bool {
    let xs = gpt(sm_gx(), i, j, l);
    let ys = gpt(sm_gy(), i, j, l);
    &&& sm_val(xs, sgn(0, ys)) % P_LIT() == 0
    &&& sm_val(xs, sgn(1, ys)) % P_LIT() == 0
    &&& sm_val(xs, sgn(2, ys)) % P_LIT() == 0
    &&& sm_val(xs, sgn(3, ys)) % P_LIT() == 0
    &&& sm_val(xs, sgn(4, ys)) % P_LIT() == 0
    &&& sm_val(xs, sgn(5, ys)) % P_LIT() == 0
    &&& sm_val(xs, sgn(6, ys)) % P_LIT() == 0
    &&& sm_val(xs, sgn(7, ys)) % P_LIT() == 0
}

pub(crate) open spec fn sm_c() -> spec_fn(int, int, int) -> bool {
    |i: int, j: int, l: int| sm_cell(i, j, l)
}

pub(crate) open spec fn sm_cells() -> bool {
    &&& cells_ok(sm_c(), 0, 0, 0, 1) && cells_ok(sm_c(), 0, 1, 0, 1)
    &&& cells_ok(sm_c(), 0, 2, 0, 1) && cells_ok(sm_c(), 0, 3, 0, 1)
    &&& cells_ok(sm_c(), 1, 0, 0, 1) && cells_ok(sm_c(), 1, 1, 0, 1)
    &&& cells_ok(sm_c(), 1, 2, 0, 1) && cells_ok(sm_c(), 1, 3, 0, 1)
    &&& cells_ok(sm_c(), 2, 0, 0, 1) && cells_ok(sm_c(), 2, 1, 0, 1)
    &&& cells_ok(sm_c(), 2, 2, 0, 1) && cells_ok(sm_c(), 2, 3, 0, 1)
    &&& cells_ok(sm_c(), 3, 0, 0, 1) && cells_ok(sm_c(), 3, 1, 0, 1)
    &&& cells_ok(sm_c(), 3, 2, 0, 1) && cells_ok(sm_c(), 3, 3, 0, 1)
}

/// gpt_ok with literal constants.
#[verifier::opaque]
pub(crate) open spec fn pt_lit(x: int, y: int) -> bool {
    (y * y) % P_LIT() == fxv(x) % P_LIT() && y % P_LIT() != 0
}

pub(crate) open spec fn sm_pts() -> bool {
    &&& pt_lit(sm_x()[0], sm_y()[0])
    &&& pt_lit(sm_x()[1], sm_y()[1])
    &&& pt_lit(sm_x()[2], sm_y()[2])
    &&& pt_lit(sm_x()[3], sm_y()[3])
}

pub(crate) open spec fn row_ok(row: Seq<int>, n: Seq<int>) -> bool {
    rz(row) || (row[0] < n[0] && row[1] < n[1] && row[2] < n[2])
}

pub(crate) open spec fn deg_ok(d: RD, n: Seq<int>) -> bool {
    &&& row_ok(d[0], n) && row_ok(d[1], n) && row_ok(d[2], n) && row_ok(d[3], n)
    &&& row_ok(d[4], n) && row_ok(d[5], n) && row_ok(d[6], n) && row_ok(d[7], n)
}

/// lemma_identity's premises for the smoke.
pub(crate) open spec fn sm_pre() -> bool {
    &&& rfits(sm_g(), sm_d())
    &&& grid_ok(sm_gx(), sm_gy())
    &&& deg_fits(sm_d(), sm_gx())
    &&& signs_vanish(sm_g(), sm_gx(), sm_gy())
}

proof fn lemma_sm_fx(i: nat, xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
        i < 3,
    ensures
        fmod(rval(rf_fx(i), xs, ys)) == fmod(fxv(xs[i as int])),
{
    let x = rf_x(i);
    let v = xs[i as int];
    lemma_rval_x(i, xs, ys);
    lemma_rval_k(-3, xs, ys);
    lemma_rval_k(B_LIT(), xs, ys);
    lemma_lk_mul(x, x, xs, ys, v, v);
    lemma_lk_mul(rf_mul(x, x), x, xs, ys, v * v, v);
    lemma_lk_mul(rf_k(-3), x, xs, ys, -3, v);
    lemma_lk_add(rf_mul(rf_mul(x, x), x), rf_mul(rf_k(-3), x), xs, ys, v * v * v, -3 * v);
    lemma_lk_add(
        rf_add(rf_mul(rf_mul(x, x), x), rf_mul(rf_k(-3), x)),
        rf_k(B_LIT()),
        xs,
        ys,
        v * v * v + -3 * v,
        B_LIT(),
    );
}

/// On the curve, sm_g's value is sm_val mod p.
proof fn lemma_sm_link(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        fmod(rval(sm_g(), xs, ys)) == fmod(sm_val(xs, ys)),
{
    let (y0, y1) = (rf_y(0), rf_y(1));
    let y = rf_add(y0, y1);
    let (v0, v1) = (ys[0], ys[1]);
    let n = rf_k(-1);
    lemma_rval_y(0, xs, ys);
    lemma_rval_y(1, xs, ys);
    lemma_rval_k(-1, xs, ys);
    lemma_rval_k(2, xs, ys);
    lemma_rf_add_hom(y0, y1, xs, ys);
    lemma_lk_mul(y, y, xs, ys, v0 + v1, v0 + v1);
    lemma_sm_fx(0, xs, ys);
    lemma_sm_fx(1, xs, ys);
    lemma_lk_mul(n, rf_fx(0), xs, ys, -1, fxv(xs[0]));
    lemma_lk_mul(n, rf_fx(1), xs, ys, -1, fxv(xs[1]));
    lemma_lk_mul(y0, y1, xs, ys, v0, v1);
    lemma_lk_mul(rf_k(2), rf_mul(y0, y1), xs, ys, 2, v0 * v1);
    lemma_lk_mul(n, rf_mul(rf_k(2), rf_mul(y0, y1)), xs, ys, -1, 2 * (v0 * v1));
    let t1 = rf_add(rf_mul(y, y), rf_neg(rf_fx(0)));
    lemma_lk_add(rf_mul(y, y), rf_neg(rf_fx(0)), xs, ys, (v0 + v1) * (v0 + v1), -1 * fxv(xs[0]));
    let w1 = (v0 + v1) * (v0 + v1) + -1 * fxv(xs[0]);
    lemma_lk_add(t1, rf_neg(rf_fx(1)), xs, ys, w1, -1 * fxv(xs[1]));
    lemma_lk_add(
        rf_add(t1, rf_neg(rf_fx(1))),
        rf_neg(rf_mul(rf_k(2), rf_mul(y0, y1))),
        xs,
        ys,
        w1 + -1 * fxv(xs[1]),
        -1 * (2 * (v0 * v1)),
    );
}

proof fn lemma_rfits_fx(i: nat)
    requires
        i < 3,
    ensures
        rfits(rf_fx(i), rd_fx(i)),
{
    let (x, dx) = (rf_x(i), rd_x(i));
    lemma_rfits_x(i);
    lemma_rfits_k(-3);
    lemma_rfits_k(B_LIT());
    lemma_rfits_mul(x, x, dx, dx);
    lemma_rfits_mul(rf_mul(x, x), x, rd_mul(dx, dx), dx);
    lemma_rfits_mul(rf_k(-3), x, rd_k(), dx);
    lemma_rfits_add(rf_mul(rf_mul(x, x), x), rf_mul(rf_k(-3), x), rd_mul(rd_mul(dx, dx), dx), rd_mul(rd_k(), dx));
    lemma_rfits_add(
        rf_add(rf_mul(rf_mul(x, x), x), rf_mul(rf_k(-3), x)),
        rf_k(B_LIT()),
        rd_add(rd_mul(rd_mul(dx, dx), dx), rd_mul(rd_k(), dx)),
        rd_k(),
    );
}

proof fn lemma_sm_rfits()
    ensures
        rfits(sm_g(), sm_d()),
{
    let (y0, y1, dy0, dy1) = (rf_y(0), rf_y(1), rd_y(0), rd_y(1));
    let (y, dy) = (rf_add(y0, y1), rd_add(dy0, dy1));
    lemma_rfits_y(0);
    lemma_rfits_y(1);
    lemma_rfits_k(-1);
    lemma_rfits_k(2);
    lemma_rfits_fx(0);
    lemma_rfits_fx(1);
    lemma_rfits_add(y0, y1, dy0, dy1);
    lemma_rfits_mul(y, y, dy, dy);
    lemma_rfits_mul(rf_k(-1), rf_fx(0), rd_k(), rd_fx(0));
    lemma_rfits_mul(rf_k(-1), rf_fx(1), rd_k(), rd_fx(1));
    lemma_rfits_mul(y0, y1, dy0, dy1);
    lemma_rfits_mul(rf_k(2), rf_mul(y0, y1), rd_k(), rd_mul(dy0, dy1));
    lemma_rfits_mul(rf_k(-1), rf_mul(rf_k(2), rf_mul(y0, y1)), rd_k(), rd_mul(rd_k(), rd_mul(dy0, dy1)));
    lemma_rfits_add(rf_mul(y, y), rf_neg(rf_fx(0)), rd_mul(dy, dy), rd_neg(rd_fx(0)));
    let (t1, e1) = (rf_add(rf_mul(y, y), rf_neg(rf_fx(0))), rd_add(rd_mul(dy, dy), rd_neg(rd_fx(0))));
    lemma_rfits_add(t1, rf_neg(rf_fx(1)), e1, rd_neg(rd_fx(1)));
    lemma_rfits_add(
        rf_add(t1, rf_neg(rf_fx(1))),
        rf_neg(rf_mul(rf_k(2), rf_mul(y0, y1))),
        rd_add(e1, rd_neg(rd_fx(1))),
        rd_neg(rd_mul(rd_k(), rd_mul(dy0, dy1))),
    );
}

/// The grid premises from the literal checks.
proof fn lemma_sm_grid()
    requires
        sm_pts(),
    ensures
        grid_ok(sm_gx(), sm_gy()),
{
    lemma_group_consts();
    let (gx, gy) = (sm_gx(), sm_gy());
    assert(distinct_mod_p(sm_x()));
    assert(distinct_mod_p(seq![sm_x()[0]]));
    assert(gk_ok(gx, gy, 0) && gk_ok(gx, gy, 1) && gk_ok(gx, gy, 2));
    assert forall|k: int| 0 <= k < 3 implies #[trigger] gk_ok(gx, gy, k) by {
        if k == 0 {
        } else if k == 1 {
        } else {
        }
    }
    assert forall|t: int| 0 <= t < 4 implies #[trigger] gpt_ok(sm_x()[t], sm_y()[t]) by {
        assert(pt_lit(sm_x()[t], sm_y()[t])) by {
            assert(t == 0 || t == 1 || t == 2 || t == 3);
        }
        reveal(pt_lit);
    }
    assert forall|k: int, t: int| 0 <= k < 3 && 0 <= t < gx[k].len() implies #[trigger] gpt_ok(
        gx[k][t],
        gy[k][t],
    ) by {
        if k < 2 {
            assert(gx[k] == sm_x() && gy[k] == sm_y());
        } else {
            assert(gx[k][t] == sm_x()[0] && gy[k][t] == sm_y()[0]);
        }
        assert(gpt_ok(sm_x()[t], sm_y()[t]) || gpt_ok(sm_x()[0], sm_y()[0]));
    }
}

proof fn lemma_sm_deg()
    requires
        deg_ok(sm_d(), seq![4int, 4, 1]),
    ensures
        deg_fits(sm_d(), sm_gx()),
{
    let gx = sm_gx();
    assert forall|s: int, k: int| 0 <= s < 8 && 0 <= k < 3 && !rz(sm_d()[s]) implies #[trigger] sm_d()[s][k]
        < gx[k].len() by {
        assert(row_ok(sm_d()[s], seq![4int, 4, 1])) by {
            assert(s == 0 || s == 1 || s == 2 || s == 3 || s == 4 || s == 5 || s == 6 || s == 7);
        }
        assert(k == 0 || k == 1 || k == 2);
    }
}

pub(crate) proof fn lemma_identity_smoke()
    ensures
        sm_pre(),
        forall|xs: Seq<int>, ys: Seq<int>| on3(xs, ys) ==> fmod(#[trigger] sm_val(xs, ys)) == 0,
{
    lemma_group_consts();
    assert(sm_pts() && deg_ok(sm_d(), seq![4int, 4, 1]) && sm_cells()) by (compute_only);
    lemma_sm_rfits();
    lemma_sm_grid();
    lemma_sm_deg();
    lemma_sm_signs();
    lemma_identity(sm_g(), sm_d(), sm_gx(), sm_gy());
    assert forall|xs: Seq<int>, ys: Seq<int>| on3(xs, ys) implies fmod(#[trigger] sm_val(xs, ys))
        == 0 by {
        lemma_sm_link(xs, ys);
        assert(fmod(rval(sm_g(), xs, ys)) == 0);
    }
}

proof fn lemma_sm_cell(i: int, j: int, l: int, sig: u8)
    requires
        sm_cells(),
        in_box(sm_gx(), i, j, l),
        sig < 8,
    ensures
        sm_val(gpt(sm_gx(), i, j, l), sgn(sig, gpt(sm_gy(), i, j, l))) % P_LIT() == 0,
{
    assert(cells_ok(sm_c(), i, j, 0, 1)) by {
        assert(i == 0 || i == 1 || i == 2 || i == 3);
        assert(j == 0 || j == 1 || j == 2 || j == 3);
    }
    lemma_cells_forall(sm_c(), i, j, 0, 1);
    assert(sm_cell(i, j, l));
    reveal(sm_cell);
    assert(sig == 0 || sig == 1 || sig == 2 || sig == 3 || sig == 4 || sig == 5 || sig == 6 || sig
        == 7);
}

proof fn lemma_sm_signs()
    requires
        sm_cells(),
        grid_ok(sm_gx(), sm_gy()),
    ensures
        signs_vanish(sm_g(), sm_gx(), sm_gy()),
{
    lemma_group_consts();
    let (gx, gy) = (sm_gx(), sm_gy());
    assert forall|i: int, j: int, l: int, sig: u8| in_box(gx, i, j, l) && sig < 8 implies fmod(
        #[trigger] rval(sm_g(), gpt(gx, i, j, l), sgn(sig, gpt(gy, i, j, l))),
    ) == 0 by {
        lemma_grid_on3(gx, gy, i, j, l, sig);
        lemma_sm_link(gpt(gx, i, j, l), sgn(sig, gpt(gy, i, j, l)));
        lemma_sm_cell(i, j, l, sig);
    }
}

pub(crate) proof fn lemma_identity_nonvacuous()
    ensures
        sm_pre(),
        sm_d()[0] == seq![3int, 3, 0],
        on3(seq![GX_LIT(), GX_LIT(), GX_LIT()], seq![GY_LIT(), GY_LIT(), GY_LIT()]),
        fmod(rval(sm_g(), seq![GX_LIT(), GX_LIT(), GX_LIT()], seq![GY_LIT(), GY_LIT(), GY_LIT()]))
            == 0,
{
    lemma_group_consts();
    assert(pt_lit(GX_LIT(), GY_LIT()) && sm_d()[0] == seq![3int, 3, 0]) by (compute_only);
    lemma_identity_smoke();
    let xs = seq![GX_LIT(), GX_LIT(), GX_LIT()];
    let ys = seq![GY_LIT(), GY_LIT(), GY_LIT()];
    reveal(pt_lit);
    assert(on_pt(GX_LIT(), GY_LIT()));
    assert forall|i: int| 0 <= i < 3 implies #[trigger] on_pt(xs[i], ys[i]) by {
        assert(xs[i] == GX_LIT() && ys[i] == GY_LIT());
    }
    lemma_sm_link(xs, ys);
    assert(fmod(sm_val(xs, ys)) == 0);
}

} // verus!
