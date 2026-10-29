//! The complete projective addition law for y^2 = x^3 - 3x + b (Renes-Costello-Batina 2016,
//! eq. (1) with a = -3), in three mirrors: plain values mod p (`rcb`, evaluated by `compute_only`
//! on the grid), curve-reduced formal polynomials (`rcb_f`, never computed) and their degree
//! tables (`rcb_d`, computed). On top of it, the small correspondence identities (chord, doubling,
//! P + (-P), closure of the curve), each proved by grid evaluation through `red::lemma_identity`,
//! and the two y-free resultant identities behind completeness, through `poly::lemma_grid`.
#[allow(unused_imports)]
use super::field::*;
#[allow(unused_imports)]
use super::grid_small::*;
#[allow(unused_imports)]
use super::poly::*;
#[allow(unused_imports)]
use super::red::*;
#[allow(unused_imports)]
use crate::p256::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;

verus! {

// ---------------------------------------------------------------------------------------------
// The plain formula
// ---------------------------------------------------------------------------------------------

pub struct Proj {
    pub x: int,
    pub y: int,
    pub z: int,
}

/// a * b mod p.
pub(crate) open spec fn fm(a: int, b: int) -> int {
    (a * b) % P_LIT()
}

// RCB 2016 eq. (1), a = -3: a^2 = 9, b3 = 3b.
pub(crate) open spec fn rcb(a: Proj, b: Proj) -> Proj {
    let b3 = 3 * B_LIT();
    let t0 = fm(a.x, b.z) + fm(b.x, a.z);
    let y12 = fm(a.y, b.y);
    let z12 = fm(a.z, b.z);
    let bz = fm(b3, z12);
    let u = y12 + 3 * t0 - bz;
    let v = y12 - 3 * t0 + bz;
    let w = -3 * fm(a.x, b.x) + fm(b3, t0) - 9 * z12;
    let s = fm(a.x, b.y) + fm(b.x, a.y);
    let r = fm(a.y, b.z) + fm(b.y, a.z);
    let q = 3 * fm(a.x, b.x) - 3 * z12;
    Proj {
        x: (fm(s, u) - fm(r, w)) % P_LIT(),
        y: (fm(v, u) + fm(q, w)) % P_LIT(),
        z: (fm(r, v) + fm(s, q)) % P_LIT(),
    }
}

/// k * a, coordinatewise mod p.
pub(crate) open spec fn sc(k: int, a: Proj) -> Proj {
    Proj { x: fmod(k * a.x), y: fmod(k * a.y), z: fmod(k * a.z) }
}

// ---------------------------------------------------------------------------------------------
// Formal and degree mirrors
// ---------------------------------------------------------------------------------------------

pub(crate) struct PF {
    pub x: RF,
    pub y: RF,
    pub z: RF,
}

pub(crate) struct PD {
    pub x: RD,
    pub y: RD,
    pub z: RD,
}

pub(crate) open spec fn rf_sub(a: RF, b: RF) -> RF {
    rf_add(a, rf_neg(b))
}

pub(crate) open spec fn rf_sc(c: int, a: RF) -> RF {
    rf_mul(rf_k(c), a)
}

pub(crate) open spec fn rd_sub(a: RD, b: RD) -> RD {
    rd_add(a, rd_neg(b))
}

pub(crate) open spec fn rd_sc(a: RD) -> RD {
    rd_mul(rd_k(), a)
}

pub(crate) open spec fn rcb_f(a: PF, b: PF) -> PF {
    let b3 = rf_k(3 * B_LIT());
    let t0 = rf_add(rf_mul(a.x, b.z), rf_mul(b.x, a.z));
    let y12 = rf_mul(a.y, b.y);
    let z12 = rf_mul(a.z, b.z);
    let bz = rf_mul(b3, z12);
    let u = rf_sub(rf_add(y12, rf_sc(3, t0)), bz);
    let v = rf_add(rf_sub(y12, rf_sc(3, t0)), bz);
    let w = rf_sub(rf_add(rf_sc(-3, rf_mul(a.x, b.x)), rf_mul(b3, t0)), rf_sc(9, z12));
    let s = rf_add(rf_mul(a.x, b.y), rf_mul(b.x, a.y));
    let r = rf_add(rf_mul(a.y, b.z), rf_mul(b.y, a.z));
    let q = rf_sub(rf_sc(3, rf_mul(a.x, b.x)), rf_sc(3, z12));
    PF {
        x: rf_sub(rf_mul(s, u), rf_mul(r, w)),
        y: rf_add(rf_mul(v, u), rf_mul(q, w)),
        z: rf_add(rf_mul(r, v), rf_mul(s, q)),
    }
}

pub(crate) open spec fn rcb_d(a: PD, b: PD) -> PD {
    let b3 = rd_k();
    let t0 = rd_add(rd_mul(a.x, b.z), rd_mul(b.x, a.z));
    let y12 = rd_mul(a.y, b.y);
    let z12 = rd_mul(a.z, b.z);
    let bz = rd_mul(b3, z12);
    let u = rd_sub(rd_add(y12, rd_sc(t0)), bz);
    let v = rd_add(rd_sub(y12, rd_sc(t0)), bz);
    let w = rd_sub(rd_add(rd_sc(rd_mul(a.x, b.x)), rd_mul(b3, t0)), rd_sc(z12));
    let s = rd_add(rd_mul(a.x, b.y), rd_mul(b.x, a.y));
    let r = rd_add(rd_mul(a.y, b.z), rd_mul(b.y, a.z));
    let q = rd_sub(rd_sc(rd_mul(a.x, b.x)), rd_sc(z12));
    PD {
        x: rd_sub(rd_mul(s, u), rd_mul(r, w)),
        y: rd_add(rd_mul(v, u), rd_mul(q, w)),
        z: rd_add(rd_mul(r, v), rd_mul(s, q)),
    }
}

// ---------------------------------------------------------------------------------------------
// Identity building blocks (plain, formal, degree)
// ---------------------------------------------------------------------------------------------

/// The affine point (xs[i], ys[i]) as (x : y : 1).
pub(crate) open spec fn pt(xs: Seq<int>, ys: Seq<int>, i: int) -> Proj {
    Proj { x: xs[i], y: ys[i], z: 1 }
}

pub(crate) open spec fn pt_f(i: nat) -> PF {
    PF { x: rf_x(i), y: rf_y(i), z: rf_k(1) }
}

pub(crate) open spec fn pt_d(i: nat) -> PD {
    PD { x: rd_x(i), y: rd_y(i), z: rd_k() }
}

/// Affine chord or tangent data: x3 = xn / d2, y3 = yn / d3 with d3^2 = d2^3.
pub(crate) struct Ch<T> {
    pub d2: T,
    pub d3: T,
    pub xn: T,
    pub yn: T,
}

/// Chord through (x0, y0), (x1, y1): d = x1 - x0, lambda = (y1 - y0) / d.
pub(crate) open spec fn chord(xs: Seq<int>, ys: Seq<int>) -> Ch<int> {
    let d = xs[1] - xs[0];
    let ln = ys[1] - ys[0];
    let d2 = fm(d, d);
    let d3 = fm(d2, d);
    let xn = fm(ln, ln) - fm(xs[0] + xs[1], d2);
    let yn = fm(ln, fm(xs[0], d2) - xn) - fm(ys[0], d3);
    Ch { d2, d3, xn, yn }
}

pub(crate) open spec fn chord_f() -> Ch<RF> {
    let d = rf_sub(rf_x(1), rf_x(0));
    let ln = rf_sub(rf_y(1), rf_y(0));
    let d2 = rf_mul(d, d);
    let d3 = rf_mul(d2, d);
    let xn = rf_sub(rf_mul(ln, ln), rf_mul(rf_add(rf_x(0), rf_x(1)), d2));
    let yn = rf_sub(rf_mul(ln, rf_sub(rf_mul(rf_x(0), d2), xn)), rf_mul(rf_y(0), d3));
    Ch { d2, d3, xn, yn }
}

pub(crate) open spec fn chord_d() -> Ch<RD> {
    let d = rd_sub(rd_x(1), rd_x(0));
    let ln = rd_sub(rd_y(1), rd_y(0));
    let d2 = rd_mul(d, d);
    let d3 = rd_mul(d2, d);
    let xn = rd_sub(rd_mul(ln, ln), rd_mul(rd_add(rd_x(0), rd_x(1)), d2));
    let yn = rd_sub(rd_mul(ln, rd_sub(rd_mul(rd_x(0), d2), xn)), rd_mul(rd_y(0), d3));
    Ch { d2, d3, xn, yn }
}

/// Tangent at (x0, y0): e = 2 y0, lambda = (3 x0^2 - 3) / e.
pub(crate) open spec fn dbl(xs: Seq<int>, ys: Seq<int>) -> Ch<int> {
    let e = 2 * ys[0];
    let ln = 3 * fm(xs[0], xs[0]) - 3;
    let e2 = fm(e, e);
    let e3 = fm(e2, e);
    let xn = fm(ln, ln) - fm(2 * xs[0], e2);
    let yn = fm(ln, fm(xs[0], e2) - xn) - fm(ys[0], e3);
    Ch { d2: e2, d3: e3, xn, yn }
}

pub(crate) open spec fn dbl_f() -> Ch<RF> {
    let e = rf_sc(2, rf_y(0));
    let ln = rf_sub(rf_sc(3, rf_mul(rf_x(0), rf_x(0))), rf_k(3));
    let e2 = rf_mul(e, e);
    let e3 = rf_mul(e2, e);
    let xn = rf_sub(rf_mul(ln, ln), rf_mul(rf_sc(2, rf_x(0)), e2));
    let yn = rf_sub(rf_mul(ln, rf_sub(rf_mul(rf_x(0), e2), xn)), rf_mul(rf_y(0), e3));
    Ch { d2: e2, d3: e3, xn, yn }
}

pub(crate) open spec fn dbl_d() -> Ch<RD> {
    let e = rd_sc(rd_y(0));
    let ln = rd_sub(rd_sc(rd_mul(rd_x(0), rd_x(0))), rd_k());
    let e2 = rd_mul(e, e);
    let e3 = rd_mul(e2, e);
    let xn = rd_sub(rd_mul(ln, ln), rd_mul(rd_sc(rd_x(0)), e2));
    let yn = rd_sub(rd_mul(ln, rd_sub(rd_mul(rd_x(0), e2), xn)), rd_mul(rd_y(0), e3));
    Ch { d2: e2, d3: e3, xn, yn }
}

/// f(x) = x^3 - 3x + b.
pub(crate) open spec fn fv(x: int) -> int {
    fm(fm(x, x), x) - 3 * x + B_LIT()
}

pub(crate) open spec fn fv_f(x: RF) -> RF {
    rf_add(rf_sub(rf_mul(rf_mul(x, x), x), rf_sc(3, x)), rf_k(B_LIT()))
}

pub(crate) open spec fn fv_d(x: RD) -> RD {
    rd_add(rd_sub(rd_mul(rd_mul(x, x), x), rd_sc(x)), rd_k())
}

/// D2's W(x1, x2) (planner: Res_e(f(e), q(e)), q(e) = 2e^2 + s e - (t + 3)), in s = x1 + x2, t = x1 x2:
/// -8b^2 + b (s^3 + 6st + 6s) + t^3 - 3ts^2 - 3t^2 - 9s^2 - 9t + 27.
pub(crate) open spec fn w_val(x1: int, x2: int) -> int {
    let s = x1 + x2;
    let t = fm(x1, x2);
    let ss = fm(s, s);
    let bc = fm(ss, s) + 6 * fm(s, t) + 6 * s;
    let c0 = fm(fm(t, t), t) - 3 * fm(t, ss) - 3 * fm(t, t) - 9 * ss - 9 * t;
    fm(B_LIT(), bc) - 8 * fm(B_LIT(), B_LIT()) + c0 + 27
}

pub(crate) open spec fn w_f(x1: RF, x2: RF) -> RF {
    let b = rf_k(B_LIT());
    let s = rf_add(x1, x2);
    let t = rf_mul(x1, x2);
    let ss = rf_mul(s, s);
    let bc = rf_add(rf_add(rf_mul(ss, s), rf_sc(6, rf_mul(s, t))), rf_sc(6, s));
    let c0 = rf_sub(
        rf_sub(
            rf_sub(rf_sub(rf_mul(rf_mul(t, t), t), rf_sc(3, rf_mul(t, ss))), rf_sc(3, rf_mul(t, t))),
            rf_sc(9, ss),
        ),
        rf_sc(9, t),
    );
    rf_add(rf_add(rf_sub(rf_mul(b, bc), rf_sc(8, rf_mul(b, b))), c0), rf_k(27))
}

pub(crate) open spec fn w_d(x1: RD, x2: RD) -> RD {
    let b = rd_k();
    let s = rd_add(x1, x2);
    let t = rd_mul(x1, x2);
    let ss = rd_mul(s, s);
    let bc = rd_add(rd_add(rd_mul(ss, s), rd_sc(rd_mul(s, t))), rd_sc(s));
    let c0 = rd_sub(
        rd_sub(rd_sub(rd_sub(rd_mul(rd_mul(t, t), t), rd_sc(rd_mul(t, ss))), rd_sc(rd_mul(t, t))), rd_sc(ss)),
        rd_sc(t),
    );
    rd_add(rd_add(rd_sub(rd_mul(b, bc), rd_sc(rd_mul(b, b))), c0), rd_k())
}

/// The curve equation for (xn / D, yn / D^(3/2)): yn^2 - (xn^3 - 3 xn D^2 + b D^3).
pub(crate) open spec fn clo(xn: int, yn: int, d: int) -> int {
    fm(yn, yn) - (fm(fm(xn, xn), xn) - 3 * fm(xn, fm(d, d)) + fm(B_LIT(), fm(d, fm(d, d))))
}

pub(crate) open spec fn clo_f(xn: RF, yn: RF, d: RF) -> RF {
    rf_sub(
        rf_mul(yn, yn),
        rf_add(
            rf_sub(rf_mul(rf_mul(xn, xn), xn), rf_sc(3, rf_mul(xn, rf_mul(d, d)))),
            rf_mul(rf_k(B_LIT()), rf_mul(d, rf_mul(d, d))),
        ),
    )
}

pub(crate) open spec fn clo_d(xn: RD, yn: RD, d: RD) -> RD {
    rd_sub(
        rd_mul(yn, yn),
        rd_add(
            rd_sub(rd_mul(rd_mul(xn, xn), xn), rd_sc(rd_mul(xn, rd_mul(d, d)))),
            rd_mul(rd_k(), rd_mul(d, rd_mul(d, d))),
        ),
    )
}

/// -(x0, y0) as (x0 : p - y0 : 1), so that the spec's P + (-P) branch matches it exactly.
pub(crate) open spec fn ptn(xs: Seq<int>, ys: Seq<int>) -> Proj {
    Proj { x: xs[0], y: P_LIT() - ys[0], z: 1 }
}

pub(crate) open spec fn ptn_f() -> PF {
    PF { x: rf_x(0), y: rf_sub(rf_k(P_LIT()), rf_y(0)), z: rf_k(1) }
}

pub(crate) open spec fn ptn_d() -> PD {
    PD { x: rd_x(0), y: rd_sub(rd_k(), rd_y(0)), z: rd_k() }
}

/// (x1 : -y1 : 1), used only inside I4.
pub(crate) open spec fn ptm(xs: Seq<int>, ys: Seq<int>) -> Proj {
    Proj { x: xs[1], y: -1 * ys[1], z: 1 }
}

pub(crate) open spec fn ptm_f() -> PF {
    PF { x: rf_x(1), y: rf_sc(-1, rf_y(1)), z: rf_k(1) }
}

pub(crate) open spec fn ptm_d() -> PD {
    PD { x: rd_x(1), y: rd_sc(rd_y(1)), z: rd_k() }
}

// ---------------------------------------------------------------------------------------------
// The identities (P = (x0, y0), Q = (x1, y1) affine on the curve)
// ---------------------------------------------------------------------------------------------

// I2 chord: X3 d^2 == xn Z3.
pub(crate) open spec fn id_chord_x(xs: Seq<int>, ys: Seq<int>) -> int {
    let o = rcb(pt(xs, ys, 0), pt(xs, ys, 1));
    let c = chord(xs, ys);
    fm(o.x, c.d2) - fm(c.xn, o.z)
}

pub(crate) open spec fn idf_chord_x() -> RF {
    let o = rcb_f(pt_f(0), pt_f(1));
    let c = chord_f();
    rf_sub(rf_mul(o.x, c.d2), rf_mul(c.xn, o.z))
}

pub(crate) open spec fn idd_chord_x() -> RD {
    let o = rcb_d(pt_d(0), pt_d(1));
    let c = chord_d();
    rd_sub(rd_mul(o.x, c.d2), rd_mul(c.xn, o.z))
}

// I3 chord: Y3 d^3 == yn Z3.
pub(crate) open spec fn id_chord_y(xs: Seq<int>, ys: Seq<int>) -> int {
    let o = rcb(pt(xs, ys, 0), pt(xs, ys, 1));
    let c = chord(xs, ys);
    fm(o.y, c.d3) - fm(c.yn, o.z)
}

pub(crate) open spec fn idf_chord_y() -> RF {
    let o = rcb_f(pt_f(0), pt_f(1));
    let c = chord_f();
    rf_sub(rf_mul(o.y, c.d3), rf_mul(c.yn, o.z))
}

pub(crate) open spec fn idd_chord_y() -> RD {
    let o = rcb_d(pt_d(0), pt_d(1));
    let c = chord_d();
    rd_sub(rd_mul(o.y, c.d3), rd_mul(c.yn, o.z))
}

// I4 chord: Z3(P, Q) Z3(P, -Q) == d^3 W(x0, x1).
pub(crate) open spec fn id_chord_z(xs: Seq<int>, ys: Seq<int>) -> int {
    let o = rcb(pt(xs, ys, 0), pt(xs, ys, 1));
    let om = rcb(pt(xs, ys, 0), ptm(xs, ys));
    let c = chord(xs, ys);
    fm(o.z, om.z) - fm(c.d3, w_val(xs[0], xs[1]))
}

pub(crate) open spec fn idf_chord_z() -> RF {
    let o = rcb_f(pt_f(0), pt_f(1));
    let om = rcb_f(pt_f(0), ptm_f());
    let c = chord_f();
    rf_sub(rf_mul(o.z, om.z), rf_mul(c.d3, w_f(rf_x(0), rf_x(1))))
}

pub(crate) open spec fn idd_chord_z() -> RD {
    idd_chord_z_of(rcb_d(pt_d(0), pt_d(1)), rcb_d(pt_d(0), ptm_d()))
}

/// idd_chord_z from its two RCB tables (`grid_small` checks one of them as a literal).
pub(crate) open spec fn idd_chord_z_of(o: PD, om: PD) -> RD {
    let c = chord_d();
    rd_sub(rd_mul(o.z, om.z), rd_mul(c.d3, w_d(rd_x(0), rd_x(1))))
}

// I5 doubling: X3 e^2 == xn Z3.
pub(crate) open spec fn id_dbl_x(xs: Seq<int>, ys: Seq<int>) -> int {
    let o = rcb(pt(xs, ys, 0), pt(xs, ys, 0));
    let c = dbl(xs, ys);
    fm(o.x, c.d2) - fm(c.xn, o.z)
}

pub(crate) open spec fn idf_dbl_x() -> RF {
    let o = rcb_f(pt_f(0), pt_f(0));
    let c = dbl_f();
    rf_sub(rf_mul(o.x, c.d2), rf_mul(c.xn, o.z))
}

pub(crate) open spec fn idd_dbl_x() -> RD {
    let o = rcb_d(pt_d(0), pt_d(0));
    let c = dbl_d();
    rd_sub(rd_mul(o.x, c.d2), rd_mul(c.xn, o.z))
}

// I6 doubling: Y3 e^3 == yn Z3.
pub(crate) open spec fn id_dbl_y(xs: Seq<int>, ys: Seq<int>) -> int {
    let o = rcb(pt(xs, ys, 0), pt(xs, ys, 0));
    let c = dbl(xs, ys);
    fm(o.y, c.d3) - fm(c.yn, o.z)
}

pub(crate) open spec fn idf_dbl_y() -> RF {
    let o = rcb_f(pt_f(0), pt_f(0));
    let c = dbl_f();
    rf_sub(rf_mul(o.y, c.d3), rf_mul(c.yn, o.z))
}

pub(crate) open spec fn idd_dbl_y() -> RD {
    let o = rcb_d(pt_d(0), pt_d(0));
    let c = dbl_d();
    rd_sub(rd_mul(o.y, c.d3), rd_mul(c.yn, o.z))
}

// I7 doubling: Z3 == 8 y0 f(x0).
pub(crate) open spec fn id_dbl_z(xs: Seq<int>, ys: Seq<int>) -> int {
    let o = rcb(pt(xs, ys, 0), pt(xs, ys, 0));
    o.z - fm(8 * ys[0], fv(xs[0]))
}

pub(crate) open spec fn idf_dbl_z() -> RF {
    let o = rcb_f(pt_f(0), pt_f(0));
    rf_sub(o.z, rf_mul(rf_sc(8, rf_y(0)), fv_f(rf_x(0))))
}

pub(crate) open spec fn idd_dbl_z() -> RD {
    let o = rcb_d(pt_d(0), pt_d(0));
    rd_sub(o.z, rd_mul(rd_sc(rd_y(0)), fv_d(rd_x(0))))
}

// I8a P + (-P): X3 == 0.
pub(crate) open spec fn id_inv_x(xs: Seq<int>, ys: Seq<int>) -> int {
    rcb(pt(xs, ys, 0), ptn(xs, ys)).x
}

pub(crate) open spec fn idf_inv_x() -> RF {
    rcb_f(pt_f(0), ptn_f()).x
}

pub(crate) open spec fn idd_inv_x() -> RD {
    rcb_d(pt_d(0), ptn_d()).x
}

// I8b P + (-P): Z3 == 0.
pub(crate) open spec fn id_inv_z(xs: Seq<int>, ys: Seq<int>) -> int {
    rcb(pt(xs, ys, 0), ptn(xs, ys)).z
}

pub(crate) open spec fn idf_inv_z() -> RF {
    rcb_f(pt_f(0), ptn_f()).z
}

pub(crate) open spec fn idd_inv_z() -> RD {
    rcb_d(pt_d(0), ptn_d()).z
}

// I8c P + (-P): Y3 == Y3(P, P).
pub(crate) open spec fn id_inv_y(xs: Seq<int>, ys: Seq<int>) -> int {
    rcb(pt(xs, ys, 0), ptn(xs, ys)).y - rcb(pt(xs, ys, 0), pt(xs, ys, 0)).y
}

pub(crate) open spec fn idf_inv_y() -> RF {
    rf_sub(rcb_f(pt_f(0), ptn_f()).y, rcb_f(pt_f(0), pt_f(0)).y)
}

pub(crate) open spec fn idd_inv_y() -> RD {
    idd_inv_y_of(rcb_d(pt_d(0), ptn_d()), rcb_d(pt_d(0), pt_d(0)))
}

/// idd_inv_y from its two RCB tables (`grid_small` checks one of them as a literal).
pub(crate) open spec fn idd_inv_y_of(o: PD, od: PD) -> RD {
    rd_sub(o.y, od.y)
}

// I10a chord closure: (xn / d^2, yn / d^3) is on the curve.
pub(crate) open spec fn id_closure_chord(xs: Seq<int>, ys: Seq<int>) -> int {
    let c = chord(xs, ys);
    clo(c.xn, c.yn, c.d2)
}

pub(crate) open spec fn idf_closure_chord() -> RF {
    let c = chord_f();
    clo_f(c.xn, c.yn, c.d2)
}

pub(crate) open spec fn idd_closure_chord() -> RD {
    let c = chord_d();
    clo_d(c.xn, c.yn, c.d2)
}

// I10b doubling closure: (xn / e^2, yn / e^3) is on the curve.
pub(crate) open spec fn id_closure_dbl(xs: Seq<int>, ys: Seq<int>) -> int {
    let c = dbl(xs, ys);
    clo(c.xn, c.yn, c.d2)
}

pub(crate) open spec fn idf_closure_dbl() -> RF {
    let c = dbl_f();
    clo_f(c.xn, c.yn, c.d2)
}

pub(crate) open spec fn idd_closure_dbl() -> RD {
    let c = dbl_d();
    clo_d(c.xn, c.yn, c.d2)
}
// ---------------------------------------------------------------------------------------------
// The y-free resultant identities (completeness, D2): plain values, formal MP, degree bounds
// ---------------------------------------------------------------------------------------------

/// r1 = 2 (x1^2 + 4 x1 x2 + x2^2 - 6).
pub(crate) open spec fn r1_val(x1: int, x2: int) -> int {
    let s = x1 + x2;
    2 * (fm(s, s) + 2 * fm(x1, x2) - 6)
}

/// r0 = -2 (-4b + x1^2 x2 + x1 x2^2 + 3 x1 + 3 x2).
pub(crate) open spec fn r0_val(x1: int, x2: int) -> int {
    let s = x1 + x2;
    -2 * (-4 * B_LIT() + fm(fm(x1, x2), s) + 3 * s)
}

/// q(e) = 2e^2 + (x1 + x2) e - (x1 x2 + 3).
pub(crate) open spec fn q_val(x1: int, x2: int, e: int) -> int {
    let s = x1 + x2;
    2 * fm(e, e) + fm(s, e) - (fm(x1, x2) + 3)
}

/// RES1: r1^2 q(-r0 / r1) == -16 W, i.e. 2 r0^2 - s r0 r1 - (t + 3) r1^2 + 16 W == 0.
pub(crate) open spec fn id_res1(x1: int, x2: int) -> int {
    let s = x1 + x2;
    let a = r0_val(x1, x2);
    let b = r1_val(x1, x2);
    2 * fm(a, a) - fm(fm(s, a), b) - fm(fm(x1, x2) + 3, fm(b, b)) + 16 * w_val(x1, x2)
}

/// RES2: 8 f(e) == q(e) (4e - 2 x1 - 2 x2) + r1 e + r0.
pub(crate) open spec fn id_res2(x1: int, x2: int, e: int) -> int {
    8 * fv(e) - fm(q_val(x1, x2, e), 4 * e - 2 * (x1 + x2)) - fm(r1_val(x1, x2), e) - r0_val(x1, x2)
}

pub(crate) open spec fn psub(a: MP, b: MP) -> MP {
    padd(a, pneg(b))
}

pub(crate) open spec fn psc(c: int, a: MP) -> MP {
    pmul(pk(c), a)
}

pub(crate) open spec fn dz() -> Seq<nat> {
    seq![0nat, 0nat, 0nat]
}

pub(crate) open spec fn dsub(a: Seq<nat>, b: Seq<nat>) -> Seq<nat> {
    dmax(a, dsum(dz(), b))
}

pub(crate) open spec fn dsc(a: Seq<nat>) -> Seq<nat> {
    dsum(dz(), a)
}

pub(crate) open spec fn fv_mp(x: MP) -> MP {
    padd(psub(pmul(pmul(x, x), x), psc(3, x)), pk(B_LIT()))
}

pub(crate) open spec fn fv_ds(x: Seq<nat>) -> Seq<nat> {
    dmax(dsub(dsum(dsum(x, x), x), dsc(x)), dz())
}

pub(crate) open spec fn w_mp(x1: MP, x2: MP) -> MP {
    let b = pk(B_LIT());
    let s = padd(x1, x2);
    let t = pmul(x1, x2);
    let ss = pmul(s, s);
    let bc = padd(padd(pmul(ss, s), psc(6, pmul(s, t))), psc(6, s));
    let c0 = psub(psub(psub(psub(pmul(pmul(t, t), t), psc(3, pmul(t, ss))), psc(3, pmul(t, t))), psc(9, ss)), psc(9, t));
    padd(padd(psub(pmul(b, bc), psc(8, pmul(b, b))), c0), pk(27))
}

pub(crate) open spec fn w_ds(x1: Seq<nat>, x2: Seq<nat>) -> Seq<nat> {
    let b = dz();
    let s = dmax(x1, x2);
    let t = dsum(x1, x2);
    let ss = dsum(s, s);
    let bc = dmax(dmax(dsum(ss, s), dsc(dsum(s, t))), dsc(s));
    let c0 = dsub(dsub(dsub(dsub(dsum(dsum(t, t), t), dsc(dsum(t, ss))), dsc(dsum(t, t))), dsc(ss)), dsc(t));
    dmax(dmax(dsub(dsum(b, bc), dsc(dsum(b, b))), c0), dz())
}

pub(crate) open spec fn r1_mp(x1: MP, x2: MP) -> MP {
    let s = padd(x1, x2);
    psc(2, psub(padd(pmul(s, s), psc(2, pmul(x1, x2))), pk(6)))
}

pub(crate) open spec fn r1_ds(x1: Seq<nat>, x2: Seq<nat>) -> Seq<nat> {
    let s = dmax(x1, x2);
    dsc(dsub(dmax(dsum(s, s), dsc(dsum(x1, x2))), dz()))
}

pub(crate) open spec fn r0_mp(x1: MP, x2: MP) -> MP {
    let s = padd(x1, x2);
    psc(-2, padd(padd(pk(-4 * B_LIT()), pmul(pmul(x1, x2), s)), psc(3, s)))
}

pub(crate) open spec fn r0_ds(x1: Seq<nat>, x2: Seq<nat>) -> Seq<nat> {
    let s = dmax(x1, x2);
    dsc(dmax(dmax(dz(), dsum(dsum(x1, x2), s)), dsc(s)))
}

pub(crate) open spec fn q_mp(x1: MP, x2: MP, e: MP) -> MP {
    let s = padd(x1, x2);
    psub(padd(psc(2, pmul(e, e)), pmul(s, e)), padd(pmul(x1, x2), pk(3)))
}

pub(crate) open spec fn q_ds(x1: Seq<nat>, x2: Seq<nat>, e: Seq<nat>) -> Seq<nat> {
    let s = dmax(x1, x2);
    dsub(dmax(dsc(dsum(e, e)), dsum(s, e)), dmax(dsum(x1, x2), dz()))
}

pub(crate) open spec fn res1_mp() -> MP {
    let (x1, x2) = (px(0), px(1));
    let s = padd(x1, x2);
    let a = r0_mp(x1, x2);
    let b = r1_mp(x1, x2);
    padd(
        psub(psub(psc(2, pmul(a, a)), pmul(pmul(s, a), b)), pmul(padd(pmul(x1, x2), pk(3)), pmul(b, b))),
        psc(16, w_mp(x1, x2)),
    )
}

pub(crate) open spec fn res1_ds() -> Seq<nat> {
    let (x1, x2) = (e3(0, 1), e3(1, 1));
    let s = dmax(x1, x2);
    let a = r0_ds(x1, x2);
    let b = r1_ds(x1, x2);
    dmax(
        dsub(dsub(dsc(dsum(a, a)), dsum(dsum(s, a), b)), dsum(dmax(dsum(x1, x2), dz()), dsum(b, b))),
        dsc(w_ds(x1, x2)),
    )
}

pub(crate) open spec fn res2_mp() -> MP {
    let (x1, x2, e) = (px(0), px(1), px(2));
    let lin = psub(psc(4, e), psc(2, padd(x1, x2)));
    psub(psub(psub(psc(8, fv_mp(e)), pmul(q_mp(x1, x2, e), lin)), pmul(r1_mp(x1, x2), e)), r0_mp(x1, x2))
}

pub(crate) open spec fn res2_ds() -> Seq<nat> {
    let (x1, x2, e) = (e3(0, 1), e3(1, 1), e3(2, 1));
    let lin = dsub(dsc(e), dsc(dmax(x1, x2)));
    dsub(dsub(dsub(dsc(fv_ds(e)), dsum(q_ds(x1, x2, e), lin)), dsum(r1_ds(x1, x2), e)), r0_ds(x1, x2))
}

/// A 3-variable degree bound below the grid sizes n.
pub(crate) open spec fn ds_ok(ds: Seq<nat>, n: Seq<int>) -> bool {
    ds.len() == 3 && ds[0] < n[0] && ds[1] < n[1] && ds[2] < n[2]
}

// ---------------------------------------------------------------------------------------------
// Grids
// ---------------------------------------------------------------------------------------------

pub(crate) open spec fn gxs(n: int) -> Seq<int> {
    Seq::new(n as nat, |i: int| gx(i))
}

pub(crate) open spec fn gys(n: int) -> Seq<int> {
    Seq::new(n as nat, |i: int| gy(i))
}

/// The first n0, n1, n2 grid x-values for the three points.
pub(crate) open spec fn grid_x(n0: int, n1: int, n2: int) -> Seq<Seq<int>> {
    seq![gxs(n0), gxs(n1), gxs(n2)]
}

pub(crate) open spec fn grid_y(n0: int, n1: int, n2: int) -> Seq<Seq<int>> {
    seq![gys(n0), gys(n1), gys(n2)]
}

/// {0, 1, ..., n - 1}.
pub(crate) open spec fn iota(n: int) -> Seq<int> {
    Seq::new(n as nat, |i: int| i)
}

/// f vanishes mod p at grid point (gx(i), gx(j), gx(l)) under all 8 y-sign choices.
#[verifier::opaque]
pub(crate) open spec fn sg_cell(f: spec_fn(Seq<int>, Seq<int>) -> int, i: int, j: int, l: int) -> bool {
    let xs = seq![gx(i), gx(j), gx(l)];
    let ys = seq![gy(i), gy(j), gy(l)];
    &&& f(xs, sgn(0, ys)) % P_LIT() == 0
    &&& f(xs, sgn(1, ys)) % P_LIT() == 0
    &&& f(xs, sgn(2, ys)) % P_LIT() == 0
    &&& f(xs, sgn(3, ys)) % P_LIT() == 0
    &&& f(xs, sgn(4, ys)) % P_LIT() == 0
    &&& f(xs, sgn(5, ys)) % P_LIT() == 0
    &&& f(xs, sgn(6, ys)) % P_LIT() == 0
    &&& f(xs, sgn(7, ys)) % P_LIT() == 0
}

// ---------------------------------------------------------------------------------------------
// Arithmetic helpers
// ---------------------------------------------------------------------------------------------

pub(crate) proof fn lemma_md(x: int)
    ensures
        fmod(x % P_LIT()) == fmod(x),
        fmod(x) == x % P_LIT(),
{
    lemma_group_consts();
    lemma_mod_twice(x, P_LIT());
}

pub(crate) proof fn lemma_cg_add(a: int, b: int, c: int, d: int)
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

pub(crate) proof fn lemma_cg_mul(a: int, b: int, c: int, d: int)
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

// ---------------------------------------------------------------------------------------------
// Links: a formal value agrees mod p with a plain one on the curve
// ---------------------------------------------------------------------------------------------

pub(crate) open spec fn lk(a: RF, v: int, xs: Seq<int>, ys: Seq<int>) -> bool {
    fmod(rval(a, xs, ys)) == fmod(v)
}

pub(crate) open spec fn lkp(a: PF, v: Proj, xs: Seq<int>, ys: Seq<int>) -> bool {
    lk(a.x, v.x, xs, ys) && lk(a.y, v.y, xs, ys) && lk(a.z, v.z, xs, ys)
}

pub(crate) proof fn lemma_lk_m(a: RF, b: RF, va: int, vb: int, xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
        lk(a, va, xs, ys),
        lk(b, vb, xs, ys),
    ensures
        lk(rf_mul(a, b), fm(va, vb), xs, ys),
{
    lemma_lk_mul(a, b, xs, ys, va, vb);
    lemma_md(va * vb);
}

proof fn lemma_lk_a(a: RF, b: RF, va: int, vb: int, xs: Seq<int>, ys: Seq<int>)
    requires
        lk(a, va, xs, ys),
        lk(b, vb, xs, ys),
    ensures
        lk(rf_add(a, b), va + vb, xs, ys),
{
    lemma_lk_add(a, b, xs, ys, va, vb);
}

proof fn lemma_lk_c(c: int, a: RF, va: int, xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
        lk(a, va, xs, ys),
    ensures
        lk(rf_sc(c, a), c * va, xs, ys),
{
    lemma_rval_k(c, xs, ys);
    lemma_lk_mul(rf_k(c), a, xs, ys, c, va);
}

pub(crate) proof fn lemma_lk_s(a: RF, b: RF, va: int, vb: int, xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
        lk(a, va, xs, ys),
        lk(b, vb, xs, ys),
    ensures
        lk(rf_sub(a, b), va - vb, xs, ys),
{
    lemma_lk_c(-1, b, vb, xs, ys);
    lemma_lk_add(a, rf_neg(b), xs, ys, va, -1 * vb);
}

proof fn lemma_lk_k(c: int, xs: Seq<int>, ys: Seq<int>)
    ensures
        lk(rf_k(c), c, xs, ys),
{
    lemma_rval_k(c, xs, ys);
}

proof fn lemma_lk_r(a: RF, v: int, xs: Seq<int>, ys: Seq<int>)
    requires
        lk(a, v, xs, ys),
    ensures
        lk(a, v % P_LIT(), xs, ys),
{
    lemma_md(v);
}

pub(crate) proof fn lemma_pt_link(i: nat, xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
        i < 3,
    ensures
        lkp(pt_f(i), pt(xs, ys, i as int), xs, ys),
{
    lemma_rval_x(i, xs, ys);
    lemma_rval_y(i, xs, ys);
    lemma_lk_k(1, xs, ys);
}

/// The plain RCB formula and its formal mirror agree on the curve.
pub(crate) proof fn lemma_rcb_link(a: Proj, b: Proj, fa: PF, fb: PF, xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
        lkp(fa, a, xs, ys),
        lkp(fb, b, xs, ys),
    ensures
        lkp(rcb_f(fa, fb), rcb(a, b), xs, ys),
{
    let b3 = 3 * B_LIT();
    let fb3 = rf_k(b3);
    lemma_lk_k(b3, xs, ys);
    // t0, y12, z12, bz
    lemma_lk_m(fa.x, fb.z, a.x, b.z, xs, ys);
    lemma_lk_m(fb.x, fa.z, b.x, a.z, xs, ys);
    lemma_lk_a(rf_mul(fa.x, fb.z), rf_mul(fb.x, fa.z), fm(a.x, b.z), fm(b.x, a.z), xs, ys);
    let t0 = fm(a.x, b.z) + fm(b.x, a.z);
    let ft0 = rf_add(rf_mul(fa.x, fb.z), rf_mul(fb.x, fa.z));
    lemma_lk_m(fa.y, fb.y, a.y, b.y, xs, ys);
    lemma_lk_m(fa.z, fb.z, a.z, b.z, xs, ys);
    let (y12, fy12) = (fm(a.y, b.y), rf_mul(fa.y, fb.y));
    let (z12, fz12) = (fm(a.z, b.z), rf_mul(fa.z, fb.z));
    lemma_lk_m(fb3, fz12, b3, z12, xs, ys);
    let (bz, fbz) = (fm(b3, z12), rf_mul(fb3, fz12));
    // u, v
    lemma_lk_c(3, ft0, t0, xs, ys);
    lemma_lk_a(fy12, rf_sc(3, ft0), y12, 3 * t0, xs, ys);
    lemma_lk_s(rf_add(fy12, rf_sc(3, ft0)), fbz, y12 + 3 * t0, bz, xs, ys);
    let (u, fu) = (y12 + 3 * t0 - bz, rf_sub(rf_add(fy12, rf_sc(3, ft0)), fbz));
    lemma_lk_s(fy12, rf_sc(3, ft0), y12, 3 * t0, xs, ys);
    lemma_lk_a(rf_sub(fy12, rf_sc(3, ft0)), fbz, y12 - 3 * t0, bz, xs, ys);
    let (v, fv0) = (y12 - 3 * t0 + bz, rf_add(rf_sub(fy12, rf_sc(3, ft0)), fbz));
    // w
    lemma_lk_m(fa.x, fb.x, a.x, b.x, xs, ys);
    let (xx, fxx) = (fm(a.x, b.x), rf_mul(fa.x, fb.x));
    lemma_lk_c(-3, fxx, xx, xs, ys);
    lemma_lk_m(fb3, ft0, b3, t0, xs, ys);
    lemma_lk_a(rf_sc(-3, fxx), rf_mul(fb3, ft0), -3 * xx, fm(b3, t0), xs, ys);
    lemma_lk_c(9, fz12, z12, xs, ys);
    lemma_lk_s(rf_add(rf_sc(-3, fxx), rf_mul(fb3, ft0)), rf_sc(9, fz12), -3 * xx + fm(b3, t0), 9 * z12, xs, ys);
    let w = -3 * xx + fm(b3, t0) - 9 * z12;
    let fw = rf_sub(rf_add(rf_sc(-3, fxx), rf_mul(fb3, ft0)), rf_sc(9, fz12));
    // s, r, q
    lemma_lk_m(fa.x, fb.y, a.x, b.y, xs, ys);
    lemma_lk_m(fb.x, fa.y, b.x, a.y, xs, ys);
    lemma_lk_a(rf_mul(fa.x, fb.y), rf_mul(fb.x, fa.y), fm(a.x, b.y), fm(b.x, a.y), xs, ys);
    let (s, fs) = (fm(a.x, b.y) + fm(b.x, a.y), rf_add(rf_mul(fa.x, fb.y), rf_mul(fb.x, fa.y)));
    lemma_lk_m(fa.y, fb.z, a.y, b.z, xs, ys);
    lemma_lk_m(fb.y, fa.z, b.y, a.z, xs, ys);
    lemma_lk_a(rf_mul(fa.y, fb.z), rf_mul(fb.y, fa.z), fm(a.y, b.z), fm(b.y, a.z), xs, ys);
    let (r, fr) = (fm(a.y, b.z) + fm(b.y, a.z), rf_add(rf_mul(fa.y, fb.z), rf_mul(fb.y, fa.z)));
    lemma_lk_c(3, fxx, xx, xs, ys);
    lemma_lk_c(3, fz12, z12, xs, ys);
    lemma_lk_s(rf_sc(3, fxx), rf_sc(3, fz12), 3 * xx, 3 * z12, xs, ys);
    let (q, fq) = (3 * xx - 3 * z12, rf_sub(rf_sc(3, fxx), rf_sc(3, fz12)));
    // outputs
    lemma_lk_m(fs, fu, s, u, xs, ys);
    lemma_lk_m(fr, fw, r, w, xs, ys);
    lemma_lk_s(rf_mul(fs, fu), rf_mul(fr, fw), fm(s, u), fm(r, w), xs, ys);
    lemma_lk_r(rf_sub(rf_mul(fs, fu), rf_mul(fr, fw)), fm(s, u) - fm(r, w), xs, ys);
    lemma_lk_m(fv0, fu, v, u, xs, ys);
    lemma_lk_m(fq, fw, q, w, xs, ys);
    lemma_lk_a(rf_mul(fv0, fu), rf_mul(fq, fw), fm(v, u), fm(q, w), xs, ys);
    lemma_lk_r(rf_add(rf_mul(fv0, fu), rf_mul(fq, fw)), fm(v, u) + fm(q, w), xs, ys);
    lemma_lk_m(fr, fv0, r, v, xs, ys);
    lemma_lk_m(fs, fq, s, q, xs, ys);
    lemma_lk_a(rf_mul(fr, fv0), rf_mul(fs, fq), fm(r, v), fm(s, q), xs, ys);
    lemma_lk_r(rf_add(rf_mul(fr, fv0), rf_mul(fs, fq)), fm(r, v) + fm(s, q), xs, ys);
}

proof fn lemma_chord_link(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        lk(chord_f().d2, chord(xs, ys).d2, xs, ys),
        lk(chord_f().d3, chord(xs, ys).d3, xs, ys),
        lk(chord_f().xn, chord(xs, ys).xn, xs, ys),
        lk(chord_f().yn, chord(xs, ys).yn, xs, ys),
{
    let (x0, x1, y0, y1) = (rf_x(0), rf_x(1), rf_y(0), rf_y(1));
    lemma_rval_x(0, xs, ys);
    lemma_rval_x(1, xs, ys);
    lemma_rval_y(0, xs, ys);
    lemma_rval_y(1, xs, ys);
    lemma_lk_s(x1, x0, xs[1], xs[0], xs, ys);
    lemma_lk_s(y1, y0, ys[1], ys[0], xs, ys);
    let (d, vd) = (rf_sub(x1, x0), xs[1] - xs[0]);
    let (ln, vl) = (rf_sub(y1, y0), ys[1] - ys[0]);
    lemma_lk_m(d, d, vd, vd, xs, ys);
    let (d2, vd2) = (rf_mul(d, d), fm(vd, vd));
    lemma_lk_m(d2, d, vd2, vd, xs, ys);
    let (d3, vd3) = (rf_mul(d2, d), fm(vd2, vd));
    lemma_lk_m(ln, ln, vl, vl, xs, ys);
    lemma_lk_a(x0, x1, xs[0], xs[1], xs, ys);
    lemma_lk_m(rf_add(x0, x1), d2, xs[0] + xs[1], vd2, xs, ys);
    lemma_lk_s(rf_mul(ln, ln), rf_mul(rf_add(x0, x1), d2), fm(vl, vl), fm(xs[0] + xs[1], vd2), xs, ys);
    let xn = rf_sub(rf_mul(ln, ln), rf_mul(rf_add(x0, x1), d2));
    let vxn = fm(vl, vl) - fm(xs[0] + xs[1], vd2);
    lemma_lk_m(x0, d2, xs[0], vd2, xs, ys);
    lemma_lk_s(rf_mul(x0, d2), xn, fm(xs[0], vd2), vxn, xs, ys);
    lemma_lk_m(ln, rf_sub(rf_mul(x0, d2), xn), vl, fm(xs[0], vd2) - vxn, xs, ys);
    lemma_lk_m(y0, d3, ys[0], vd3, xs, ys);
    lemma_lk_s(
        rf_mul(ln, rf_sub(rf_mul(x0, d2), xn)),
        rf_mul(y0, d3),
        fm(vl, fm(xs[0], vd2) - vxn),
        fm(ys[0], vd3),
        xs,
        ys,
    );
}

proof fn lemma_dbl_link(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        lk(dbl_f().d2, dbl(xs, ys).d2, xs, ys),
        lk(dbl_f().d3, dbl(xs, ys).d3, xs, ys),
        lk(dbl_f().xn, dbl(xs, ys).xn, xs, ys),
        lk(dbl_f().yn, dbl(xs, ys).yn, xs, ys),
{
    let (x0, y0) = (rf_x(0), rf_y(0));
    lemma_rval_x(0, xs, ys);
    lemma_rval_y(0, xs, ys);
    lemma_lk_k(3, xs, ys);
    lemma_lk_c(2, y0, ys[0], xs, ys);
    let (e, ve) = (rf_sc(2, y0), 2 * ys[0]);
    lemma_lk_m(x0, x0, xs[0], xs[0], xs, ys);
    lemma_lk_c(3, rf_mul(x0, x0), fm(xs[0], xs[0]), xs, ys);
    lemma_lk_s(rf_sc(3, rf_mul(x0, x0)), rf_k(3), 3 * fm(xs[0], xs[0]), 3, xs, ys);
    let (ln, vl) = (rf_sub(rf_sc(3, rf_mul(x0, x0)), rf_k(3)), 3 * fm(xs[0], xs[0]) - 3);
    lemma_lk_m(e, e, ve, ve, xs, ys);
    let (e2, ve2) = (rf_mul(e, e), fm(ve, ve));
    lemma_lk_m(e2, e, ve2, ve, xs, ys);
    let (e3, ve3) = (rf_mul(e2, e), fm(ve2, ve));
    lemma_lk_m(ln, ln, vl, vl, xs, ys);
    lemma_lk_c(2, x0, xs[0], xs, ys);
    lemma_lk_m(rf_sc(2, x0), e2, 2 * xs[0], ve2, xs, ys);
    lemma_lk_s(rf_mul(ln, ln), rf_mul(rf_sc(2, x0), e2), fm(vl, vl), fm(2 * xs[0], ve2), xs, ys);
    let xn = rf_sub(rf_mul(ln, ln), rf_mul(rf_sc(2, x0), e2));
    let vxn = fm(vl, vl) - fm(2 * xs[0], ve2);
    lemma_lk_m(x0, e2, xs[0], ve2, xs, ys);
    lemma_lk_s(rf_mul(x0, e2), xn, fm(xs[0], ve2), vxn, xs, ys);
    lemma_lk_m(ln, rf_sub(rf_mul(x0, e2), xn), vl, fm(xs[0], ve2) - vxn, xs, ys);
    lemma_lk_m(y0, e3, ys[0], ve3, xs, ys);
    lemma_lk_s(
        rf_mul(ln, rf_sub(rf_mul(x0, e2), xn)),
        rf_mul(y0, e3),
        fm(vl, fm(xs[0], ve2) - vxn),
        fm(ys[0], ve3),
        xs,
        ys,
    );
}

proof fn lemma_fv_link(x: RF, v: int, xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
        lk(x, v, xs, ys),
    ensures
        lk(fv_f(x), fv(v), xs, ys),
{
    lemma_lk_m(x, x, v, v, xs, ys);
    lemma_lk_m(rf_mul(x, x), x, fm(v, v), v, xs, ys);
    lemma_lk_c(3, x, v, xs, ys);
    lemma_lk_s(rf_mul(rf_mul(x, x), x), rf_sc(3, x), fm(fm(v, v), v), 3 * v, xs, ys);
    lemma_lk_k(B_LIT(), xs, ys);
    lemma_lk_a(rf_sub(rf_mul(rf_mul(x, x), x), rf_sc(3, x)), rf_k(B_LIT()), fm(fm(v, v), v) - 3 * v, B_LIT(), xs, ys);
}

proof fn lemma_w_link(x1: RF, x2: RF, v1: int, v2: int, xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
        lk(x1, v1, xs, ys),
        lk(x2, v2, xs, ys),
    ensures
        lk(w_f(x1, x2), w_val(v1, v2), xs, ys),
{
    let bl = B_LIT();
    let b = rf_k(bl);
    lemma_lk_k(bl, xs, ys);
    lemma_lk_k(27, xs, ys);
    lemma_lk_a(x1, x2, v1, v2, xs, ys);
    let (s, vs) = (rf_add(x1, x2), v1 + v2);
    lemma_lk_m(x1, x2, v1, v2, xs, ys);
    let (t, vt) = (rf_mul(x1, x2), fm(v1, v2));
    lemma_lk_m(s, s, vs, vs, xs, ys);
    let (ss, vss) = (rf_mul(s, s), fm(vs, vs));
    // bc
    lemma_lk_m(ss, s, vss, vs, xs, ys);
    lemma_lk_m(s, t, vs, vt, xs, ys);
    lemma_lk_c(6, rf_mul(s, t), fm(vs, vt), xs, ys);
    lemma_lk_a(rf_mul(ss, s), rf_sc(6, rf_mul(s, t)), fm(vss, vs), 6 * fm(vs, vt), xs, ys);
    lemma_lk_c(6, s, vs, xs, ys);
    let bc0 = rf_add(rf_mul(ss, s), rf_sc(6, rf_mul(s, t)));
    lemma_lk_a(bc0, rf_sc(6, s), fm(vss, vs) + 6 * fm(vs, vt), 6 * vs, xs, ys);
    let bc = rf_add(bc0, rf_sc(6, s));
    let vbc = fm(vss, vs) + 6 * fm(vs, vt) + 6 * vs;
    // c0
    lemma_lk_m(t, t, vt, vt, xs, ys);
    lemma_lk_m(rf_mul(t, t), t, fm(vt, vt), vt, xs, ys);
    lemma_lk_m(t, ss, vt, vss, xs, ys);
    lemma_lk_c(3, rf_mul(t, ss), fm(vt, vss), xs, ys);
    let c1 = rf_sub(rf_mul(rf_mul(t, t), t), rf_sc(3, rf_mul(t, ss)));
    let v1c = fm(fm(vt, vt), vt) - 3 * fm(vt, vss);
    lemma_lk_s(rf_mul(rf_mul(t, t), t), rf_sc(3, rf_mul(t, ss)), fm(fm(vt, vt), vt), 3 * fm(vt, vss), xs, ys);
    lemma_lk_c(3, rf_mul(t, t), fm(vt, vt), xs, ys);
    lemma_lk_s(c1, rf_sc(3, rf_mul(t, t)), v1c, 3 * fm(vt, vt), xs, ys);
    let c2 = rf_sub(c1, rf_sc(3, rf_mul(t, t)));
    let v2c = v1c - 3 * fm(vt, vt);
    lemma_lk_c(9, ss, vss, xs, ys);
    lemma_lk_s(c2, rf_sc(9, ss), v2c, 9 * vss, xs, ys);
    lemma_lk_c(9, t, vt, xs, ys);
    lemma_lk_s(rf_sub(c2, rf_sc(9, ss)), rf_sc(9, t), v2c - 9 * vss, 9 * vt, xs, ys);
    let c0 = rf_sub(rf_sub(c2, rf_sc(9, ss)), rf_sc(9, t));
    let vc0 = v2c - 9 * vss - 9 * vt;
    // total
    lemma_lk_m(b, bc, bl, vbc, xs, ys);
    lemma_lk_m(b, b, bl, bl, xs, ys);
    lemma_lk_c(8, rf_mul(b, b), fm(bl, bl), xs, ys);
    lemma_lk_s(rf_mul(b, bc), rf_sc(8, rf_mul(b, b)), fm(bl, vbc), 8 * fm(bl, bl), xs, ys);
    let t1 = rf_sub(rf_mul(b, bc), rf_sc(8, rf_mul(b, b)));
    let vt1 = fm(bl, vbc) - 8 * fm(bl, bl);
    lemma_lk_a(t1, c0, vt1, vc0, xs, ys);
    lemma_lk_a(rf_add(t1, c0), rf_k(27), vt1 + vc0, 27, xs, ys);
}

proof fn lemma_clo_link(xn: RF, yn: RF, d: RF, vx: int, vy: int, vd: int, xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
        lk(xn, vx, xs, ys),
        lk(yn, vy, xs, ys),
        lk(d, vd, xs, ys),
    ensures
        lk(clo_f(xn, yn, d), clo(vx, vy, vd), xs, ys),
{
    let bl = B_LIT();
    lemma_lk_k(bl, xs, ys);
    lemma_lk_m(yn, yn, vy, vy, xs, ys);
    lemma_lk_m(xn, xn, vx, vx, xs, ys);
    lemma_lk_m(rf_mul(xn, xn), xn, fm(vx, vx), vx, xs, ys);
    lemma_lk_m(d, d, vd, vd, xs, ys);
    lemma_lk_m(xn, rf_mul(d, d), vx, fm(vd, vd), xs, ys);
    lemma_lk_c(3, rf_mul(xn, rf_mul(d, d)), fm(vx, fm(vd, vd)), xs, ys);
    lemma_lk_s(
        rf_mul(rf_mul(xn, xn), xn),
        rf_sc(3, rf_mul(xn, rf_mul(d, d))),
        fm(fm(vx, vx), vx),
        3 * fm(vx, fm(vd, vd)),
        xs,
        ys,
    );
    lemma_lk_m(d, rf_mul(d, d), vd, fm(vd, vd), xs, ys);
    lemma_lk_m(rf_k(bl), rf_mul(d, rf_mul(d, d)), bl, fm(vd, fm(vd, vd)), xs, ys);
    let a = rf_sub(rf_mul(rf_mul(xn, xn), xn), rf_sc(3, rf_mul(xn, rf_mul(d, d))));
    let va = fm(fm(vx, vx), vx) - 3 * fm(vx, fm(vd, vd));
    lemma_lk_a(a, rf_mul(rf_k(bl), rf_mul(d, rf_mul(d, d))), va, fm(bl, fm(vd, fm(vd, vd))), xs, ys);
    lemma_lk_s(
        rf_mul(yn, yn),
        rf_add(a, rf_mul(rf_k(bl), rf_mul(d, rf_mul(d, d)))),
        fm(vy, vy),
        va + fm(bl, fm(vd, fm(vd, vd))),
        xs,
        ys,
    );
}

// ---------------------------------------------------------------------------------------------
// Degrees
// ---------------------------------------------------------------------------------------------

pub(crate) open spec fn pfits(a: PF, d: PD) -> bool {
    rfits(a.x, d.x) && rfits(a.y, d.y) && rfits(a.z, d.z)
}

pub(crate) proof fn lemma_rfits_sub(a: RF, b: RF, da: RD, db: RD)
    requires
        rfits(a, da),
        rfits(b, db),
    ensures
        rfits(rf_sub(a, b), rd_sub(da, db)),
{
    lemma_rfits_k(-1);
    lemma_rfits_mul(rf_k(-1), b, rd_k(), db);
    lemma_rfits_add(a, rf_neg(b), da, rd_neg(db));
}

proof fn lemma_rfits_sc(c: int, a: RF, da: RD)
    requires
        rfits(a, da),
    ensures
        rfits(rf_sc(c, a), rd_sc(da)),
{
    lemma_rfits_k(c);
    lemma_rfits_mul(rf_k(c), a, rd_k(), da);
}

pub(crate) proof fn lemma_pt_fits(i: nat)
    requires
        i < 3,
    ensures
        pfits(pt_f(i), pt_d(i)),
{
    lemma_rfits_x(i);
    lemma_rfits_y(i);
    lemma_rfits_k(1);
}

/// The degree table bounds the formal RCB output.
pub(crate) proof fn lemma_rcb_fits(fa: PF, fb: PF, da: PD, db: PD)
    requires
        pfits(fa, da),
        pfits(fb, db),
    ensures
        pfits(rcb_f(fa, fb), rcb_d(da, db)),
{
    let (fb3, db3) = (rf_k(3 * B_LIT()), rd_k());
    lemma_rfits_k(3 * B_LIT());
    lemma_rfits_mul(fa.x, fb.z, da.x, db.z);
    lemma_rfits_mul(fb.x, fa.z, db.x, da.z);
    lemma_rfits_add(rf_mul(fa.x, fb.z), rf_mul(fb.x, fa.z), rd_mul(da.x, db.z), rd_mul(db.x, da.z));
    let ft0 = rf_add(rf_mul(fa.x, fb.z), rf_mul(fb.x, fa.z));
    let dt0 = rd_add(rd_mul(da.x, db.z), rd_mul(db.x, da.z));
    lemma_rfits_mul(fa.y, fb.y, da.y, db.y);
    lemma_rfits_mul(fa.z, fb.z, da.z, db.z);
    let (fy12, dy12) = (rf_mul(fa.y, fb.y), rd_mul(da.y, db.y));
    let (fz12, dz12) = (rf_mul(fa.z, fb.z), rd_mul(da.z, db.z));
    lemma_rfits_mul(fb3, fz12, db3, dz12);
    let (fbz, dbz) = (rf_mul(fb3, fz12), rd_mul(db3, dz12));
    // u, v
    lemma_rfits_sc(3, ft0, dt0);
    lemma_rfits_add(fy12, rf_sc(3, ft0), dy12, rd_sc(dt0));
    lemma_rfits_sub(rf_add(fy12, rf_sc(3, ft0)), fbz, rd_add(dy12, rd_sc(dt0)), dbz);
    let (fu, du) = (rf_sub(rf_add(fy12, rf_sc(3, ft0)), fbz), rd_sub(rd_add(dy12, rd_sc(dt0)), dbz));
    lemma_rfits_sub(fy12, rf_sc(3, ft0), dy12, rd_sc(dt0));
    lemma_rfits_add(rf_sub(fy12, rf_sc(3, ft0)), fbz, rd_sub(dy12, rd_sc(dt0)), dbz);
    let (fv0, dv) = (rf_add(rf_sub(fy12, rf_sc(3, ft0)), fbz), rd_add(rd_sub(dy12, rd_sc(dt0)), dbz));
    // w
    lemma_rfits_mul(fa.x, fb.x, da.x, db.x);
    let (fxx, dxx) = (rf_mul(fa.x, fb.x), rd_mul(da.x, db.x));
    lemma_rfits_sc(-3, fxx, dxx);
    lemma_rfits_mul(fb3, ft0, db3, dt0);
    lemma_rfits_add(rf_sc(-3, fxx), rf_mul(fb3, ft0), rd_sc(dxx), rd_mul(db3, dt0));
    lemma_rfits_sc(9, fz12, dz12);
    lemma_rfits_sub(
        rf_add(rf_sc(-3, fxx), rf_mul(fb3, ft0)),
        rf_sc(9, fz12),
        rd_add(rd_sc(dxx), rd_mul(db3, dt0)),
        rd_sc(dz12),
    );
    let fw = rf_sub(rf_add(rf_sc(-3, fxx), rf_mul(fb3, ft0)), rf_sc(9, fz12));
    let dw = rd_sub(rd_add(rd_sc(dxx), rd_mul(db3, dt0)), rd_sc(dz12));
    // s, r, q
    lemma_rfits_mul(fa.x, fb.y, da.x, db.y);
    lemma_rfits_mul(fb.x, fa.y, db.x, da.y);
    lemma_rfits_add(rf_mul(fa.x, fb.y), rf_mul(fb.x, fa.y), rd_mul(da.x, db.y), rd_mul(db.x, da.y));
    let fs = rf_add(rf_mul(fa.x, fb.y), rf_mul(fb.x, fa.y));
    let ds = rd_add(rd_mul(da.x, db.y), rd_mul(db.x, da.y));
    lemma_rfits_mul(fa.y, fb.z, da.y, db.z);
    lemma_rfits_mul(fb.y, fa.z, db.y, da.z);
    lemma_rfits_add(rf_mul(fa.y, fb.z), rf_mul(fb.y, fa.z), rd_mul(da.y, db.z), rd_mul(db.y, da.z));
    let fr = rf_add(rf_mul(fa.y, fb.z), rf_mul(fb.y, fa.z));
    let dr = rd_add(rd_mul(da.y, db.z), rd_mul(db.y, da.z));
    lemma_rfits_sc(3, fxx, dxx);
    lemma_rfits_sc(3, fz12, dz12);
    lemma_rfits_sub(rf_sc(3, fxx), rf_sc(3, fz12), rd_sc(dxx), rd_sc(dz12));
    let (fq, dq) = (rf_sub(rf_sc(3, fxx), rf_sc(3, fz12)), rd_sub(rd_sc(dxx), rd_sc(dz12)));
    // outputs
    lemma_rfits_mul(fs, fu, ds, du);
    lemma_rfits_mul(fr, fw, dr, dw);
    lemma_rfits_sub(rf_mul(fs, fu), rf_mul(fr, fw), rd_mul(ds, du), rd_mul(dr, dw));
    lemma_rfits_mul(fv0, fu, dv, du);
    lemma_rfits_mul(fq, fw, dq, dw);
    lemma_rfits_add(rf_mul(fv0, fu), rf_mul(fq, fw), rd_mul(dv, du), rd_mul(dq, dw));
    lemma_rfits_mul(fr, fv0, dr, dv);
    lemma_rfits_mul(fs, fq, ds, dq);
    lemma_rfits_add(rf_mul(fr, fv0), rf_mul(fs, fq), rd_mul(dr, dv), rd_mul(ds, dq));
}

proof fn lemma_chord_fits()
    ensures
        rfits(chord_f().d2, chord_d().d2),
        rfits(chord_f().d3, chord_d().d3),
        rfits(chord_f().xn, chord_d().xn),
        rfits(chord_f().yn, chord_d().yn),
{
    let (x0, x1, y0, y1) = (rf_x(0), rf_x(1), rf_y(0), rf_y(1));
    let (e0, e1, f0, f1) = (rd_x(0), rd_x(1), rd_y(0), rd_y(1));
    lemma_rfits_x(0);
    lemma_rfits_x(1);
    lemma_rfits_y(0);
    lemma_rfits_y(1);
    lemma_rfits_sub(x1, x0, e1, e0);
    lemma_rfits_sub(y1, y0, f1, f0);
    let (d, dd) = (rf_sub(x1, x0), rd_sub(e1, e0));
    let (ln, dl) = (rf_sub(y1, y0), rd_sub(f1, f0));
    lemma_rfits_mul(d, d, dd, dd);
    let (d2, dd2) = (rf_mul(d, d), rd_mul(dd, dd));
    lemma_rfits_mul(d2, d, dd2, dd);
    let (d3, dd3) = (rf_mul(d2, d), rd_mul(dd2, dd));
    lemma_rfits_mul(ln, ln, dl, dl);
    lemma_rfits_add(x0, x1, e0, e1);
    lemma_rfits_mul(rf_add(x0, x1), d2, rd_add(e0, e1), dd2);
    lemma_rfits_sub(rf_mul(ln, ln), rf_mul(rf_add(x0, x1), d2), rd_mul(dl, dl), rd_mul(rd_add(e0, e1), dd2));
    let xn = rf_sub(rf_mul(ln, ln), rf_mul(rf_add(x0, x1), d2));
    let dxn = rd_sub(rd_mul(dl, dl), rd_mul(rd_add(e0, e1), dd2));
    lemma_rfits_mul(x0, d2, e0, dd2);
    lemma_rfits_sub(rf_mul(x0, d2), xn, rd_mul(e0, dd2), dxn);
    lemma_rfits_mul(ln, rf_sub(rf_mul(x0, d2), xn), dl, rd_sub(rd_mul(e0, dd2), dxn));
    lemma_rfits_mul(y0, d3, f0, dd3);
    lemma_rfits_sub(
        rf_mul(ln, rf_sub(rf_mul(x0, d2), xn)),
        rf_mul(y0, d3),
        rd_mul(dl, rd_sub(rd_mul(e0, dd2), dxn)),
        rd_mul(f0, dd3),
    );
}

proof fn lemma_dbl_fits()
    ensures
        rfits(dbl_f().d2, dbl_d().d2),
        rfits(dbl_f().d3, dbl_d().d3),
        rfits(dbl_f().xn, dbl_d().xn),
        rfits(dbl_f().yn, dbl_d().yn),
{
    let (x0, y0, e0, f0) = (rf_x(0), rf_y(0), rd_x(0), rd_y(0));
    lemma_rfits_x(0);
    lemma_rfits_y(0);
    lemma_rfits_k(3);
    lemma_rfits_sc(2, y0, f0);
    let (e, de) = (rf_sc(2, y0), rd_sc(f0));
    lemma_rfits_mul(x0, x0, e0, e0);
    lemma_rfits_sc(3, rf_mul(x0, x0), rd_mul(e0, e0));
    lemma_rfits_sub(rf_sc(3, rf_mul(x0, x0)), rf_k(3), rd_sc(rd_mul(e0, e0)), rd_k());
    let (ln, dl) = (rf_sub(rf_sc(3, rf_mul(x0, x0)), rf_k(3)), rd_sub(rd_sc(rd_mul(e0, e0)), rd_k()));
    lemma_rfits_mul(e, e, de, de);
    let (e2, de2) = (rf_mul(e, e), rd_mul(de, de));
    lemma_rfits_mul(e2, e, de2, de);
    let (e3, de3) = (rf_mul(e2, e), rd_mul(de2, de));
    lemma_rfits_mul(ln, ln, dl, dl);
    lemma_rfits_sc(2, x0, e0);
    lemma_rfits_mul(rf_sc(2, x0), e2, rd_sc(e0), de2);
    lemma_rfits_sub(rf_mul(ln, ln), rf_mul(rf_sc(2, x0), e2), rd_mul(dl, dl), rd_mul(rd_sc(e0), de2));
    let xn = rf_sub(rf_mul(ln, ln), rf_mul(rf_sc(2, x0), e2));
    let dxn = rd_sub(rd_mul(dl, dl), rd_mul(rd_sc(e0), de2));
    lemma_rfits_mul(x0, e2, e0, de2);
    lemma_rfits_sub(rf_mul(x0, e2), xn, rd_mul(e0, de2), dxn);
    lemma_rfits_mul(ln, rf_sub(rf_mul(x0, e2), xn), dl, rd_sub(rd_mul(e0, de2), dxn));
    lemma_rfits_mul(y0, e3, f0, de3);
    lemma_rfits_sub(
        rf_mul(ln, rf_sub(rf_mul(x0, e2), xn)),
        rf_mul(y0, e3),
        rd_mul(dl, rd_sub(rd_mul(e0, de2), dxn)),
        rd_mul(f0, de3),
    );
}

proof fn lemma_fv_fits(x: RF, d: RD)
    requires
        rfits(x, d),
    ensures
        rfits(fv_f(x), fv_d(d)),
{
    lemma_rfits_mul(x, x, d, d);
    lemma_rfits_mul(rf_mul(x, x), x, rd_mul(d, d), d);
    lemma_rfits_sc(3, x, d);
    lemma_rfits_sub(rf_mul(rf_mul(x, x), x), rf_sc(3, x), rd_mul(rd_mul(d, d), d), rd_sc(d));
    lemma_rfits_k(B_LIT());
    lemma_rfits_add(rf_sub(rf_mul(rf_mul(x, x), x), rf_sc(3, x)), rf_k(B_LIT()), rd_sub(rd_mul(rd_mul(d, d), d), rd_sc(d)), rd_k());
}

proof fn lemma_w_fits(x1: RF, x2: RF, d1: RD, d2: RD)
    requires
        rfits(x1, d1),
        rfits(x2, d2),
    ensures
        rfits(w_f(x1, x2), w_d(d1, d2)),
{
    let (b, db) = (rf_k(B_LIT()), rd_k());
    lemma_rfits_k(B_LIT());
    lemma_rfits_k(27);
    lemma_rfits_add(x1, x2, d1, d2);
    let (s, ds) = (rf_add(x1, x2), rd_add(d1, d2));
    lemma_rfits_mul(x1, x2, d1, d2);
    let (t, dt) = (rf_mul(x1, x2), rd_mul(d1, d2));
    lemma_rfits_mul(s, s, ds, ds);
    let (ss, dss) = (rf_mul(s, s), rd_mul(ds, ds));
    lemma_rfits_mul(ss, s, dss, ds);
    lemma_rfits_mul(s, t, ds, dt);
    lemma_rfits_sc(6, rf_mul(s, t), rd_mul(ds, dt));
    lemma_rfits_add(rf_mul(ss, s), rf_sc(6, rf_mul(s, t)), rd_mul(dss, ds), rd_sc(rd_mul(ds, dt)));
    lemma_rfits_sc(6, s, ds);
    let bc0 = rf_add(rf_mul(ss, s), rf_sc(6, rf_mul(s, t)));
    let dbc0 = rd_add(rd_mul(dss, ds), rd_sc(rd_mul(ds, dt)));
    lemma_rfits_add(bc0, rf_sc(6, s), dbc0, rd_sc(ds));
    let (bc, dbc) = (rf_add(bc0, rf_sc(6, s)), rd_add(dbc0, rd_sc(ds)));
    lemma_rfits_mul(t, t, dt, dt);
    lemma_rfits_mul(rf_mul(t, t), t, rd_mul(dt, dt), dt);
    lemma_rfits_mul(t, ss, dt, dss);
    lemma_rfits_sc(3, rf_mul(t, ss), rd_mul(dt, dss));
    lemma_rfits_sub(rf_mul(rf_mul(t, t), t), rf_sc(3, rf_mul(t, ss)), rd_mul(rd_mul(dt, dt), dt), rd_sc(rd_mul(dt, dss)));
    let c1 = rf_sub(rf_mul(rf_mul(t, t), t), rf_sc(3, rf_mul(t, ss)));
    let dc1 = rd_sub(rd_mul(rd_mul(dt, dt), dt), rd_sc(rd_mul(dt, dss)));
    lemma_rfits_sc(3, rf_mul(t, t), rd_mul(dt, dt));
    lemma_rfits_sub(c1, rf_sc(3, rf_mul(t, t)), dc1, rd_sc(rd_mul(dt, dt)));
    let (c2, dc2) = (rf_sub(c1, rf_sc(3, rf_mul(t, t))), rd_sub(dc1, rd_sc(rd_mul(dt, dt))));
    lemma_rfits_sc(9, ss, dss);
    lemma_rfits_sub(c2, rf_sc(9, ss), dc2, rd_sc(dss));
    lemma_rfits_sc(9, t, dt);
    lemma_rfits_sub(rf_sub(c2, rf_sc(9, ss)), rf_sc(9, t), rd_sub(dc2, rd_sc(dss)), rd_sc(dt));
    let c0 = rf_sub(rf_sub(c2, rf_sc(9, ss)), rf_sc(9, t));
    let dc0 = rd_sub(rd_sub(dc2, rd_sc(dss)), rd_sc(dt));
    lemma_rfits_mul(b, bc, db, dbc);
    lemma_rfits_mul(b, b, db, db);
    lemma_rfits_sc(8, rf_mul(b, b), rd_mul(db, db));
    lemma_rfits_sub(rf_mul(b, bc), rf_sc(8, rf_mul(b, b)), rd_mul(db, dbc), rd_sc(rd_mul(db, db)));
    let t1 = rf_sub(rf_mul(b, bc), rf_sc(8, rf_mul(b, b)));
    let dt1 = rd_sub(rd_mul(db, dbc), rd_sc(rd_mul(db, db)));
    lemma_rfits_add(t1, c0, dt1, dc0);
    lemma_rfits_add(rf_add(t1, c0), rf_k(27), rd_add(dt1, dc0), rd_k());
}

proof fn lemma_clo_fits(xn: RF, yn: RF, d: RF, dx: RD, dy: RD, dd: RD)
    requires
        rfits(xn, dx),
        rfits(yn, dy),
        rfits(d, dd),
    ensures
        rfits(clo_f(xn, yn, d), clo_d(dx, dy, dd)),
{
    lemma_rfits_k(B_LIT());
    lemma_rfits_mul(yn, yn, dy, dy);
    lemma_rfits_mul(xn, xn, dx, dx);
    lemma_rfits_mul(rf_mul(xn, xn), xn, rd_mul(dx, dx), dx);
    lemma_rfits_mul(d, d, dd, dd);
    lemma_rfits_mul(xn, rf_mul(d, d), dx, rd_mul(dd, dd));
    lemma_rfits_sc(3, rf_mul(xn, rf_mul(d, d)), rd_mul(dx, rd_mul(dd, dd)));
    lemma_rfits_sub(
        rf_mul(rf_mul(xn, xn), xn),
        rf_sc(3, rf_mul(xn, rf_mul(d, d))),
        rd_mul(rd_mul(dx, dx), dx),
        rd_sc(rd_mul(dx, rd_mul(dd, dd))),
    );
    lemma_rfits_mul(d, rf_mul(d, d), dd, rd_mul(dd, dd));
    lemma_rfits_mul(rf_k(B_LIT()), rf_mul(d, rf_mul(d, d)), rd_k(), rd_mul(dd, rd_mul(dd, dd)));
    let a = rf_sub(rf_mul(rf_mul(xn, xn), xn), rf_sc(3, rf_mul(xn, rf_mul(d, d))));
    let da = rd_sub(rd_mul(rd_mul(dx, dx), dx), rd_sc(rd_mul(dx, rd_mul(dd, dd))));
    lemma_rfits_add(a, rf_mul(rf_k(B_LIT()), rf_mul(d, rf_mul(d, d))), da, rd_mul(rd_k(), rd_mul(dd, rd_mul(dd, dd))));
    lemma_rfits_sub(
        rf_mul(yn, yn),
        rf_add(a, rf_mul(rf_k(B_LIT()), rf_mul(d, rf_mul(d, d)))),
        rd_mul(dy, dy),
        rd_add(da, rd_mul(rd_k(), rd_mul(dd, rd_mul(dd, dd)))),
    );
}

// ---------------------------------------------------------------------------------------------
// The identities' links and degree bounds
// ---------------------------------------------------------------------------------------------

proof fn lemma_ptn_link(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        lkp(ptn_f(), ptn(xs, ys), xs, ys),
{
    lemma_rval_x(0, xs, ys);
    lemma_rval_y(0, xs, ys);
    lemma_lk_k(P_LIT(), xs, ys);
    lemma_lk_s(rf_k(P_LIT()), rf_y(0), P_LIT(), ys[0], xs, ys);
    lemma_lk_k(1, xs, ys);
}

proof fn lemma_ptn_fits()
    ensures
        pfits(ptn_f(), ptn_d()),
{
    lemma_rfits_x(0);
    lemma_rfits_y(0);
    lemma_rfits_k(P_LIT());
    lemma_rfits_sub(rf_k(P_LIT()), rf_y(0), rd_k(), rd_y(0));
    lemma_rfits_k(1);
}

proof fn lemma_ptm_link(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        lkp(ptm_f(), ptm(xs, ys), xs, ys),
{
    lemma_rval_x(1, xs, ys);
    lemma_rval_y(1, xs, ys);
    lemma_lk_c(-1, rf_y(1), ys[1], xs, ys);
    lemma_lk_k(1, xs, ys);
}

proof fn lemma_ptm_fits()
    ensures
        pfits(ptm_f(), ptm_d()),
{
    lemma_rfits_x(1);
    lemma_rfits_y(1);
    lemma_rfits_sc(-1, rf_y(1), rd_y(1));
    lemma_rfits_k(1);
}

proof fn lemma_link_chord_x(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        lk(idf_chord_x(), id_chord_x(xs, ys), xs, ys),
{
    lemma_pt_link(0, xs, ys);
    lemma_pt_link(1, xs, ys);
    lemma_rcb_link(pt(xs, ys, 0), pt(xs, ys, 1), pt_f(0), pt_f(1), xs, ys);
    lemma_chord_link(xs, ys);
    let (o, fo) = (rcb(pt(xs, ys, 0), pt(xs, ys, 1)), rcb_f(pt_f(0), pt_f(1)));
    let (c, fc) = (chord(xs, ys), chord_f());
    lemma_lk_m(fo.x, fc.d2, o.x, c.d2, xs, ys);
    lemma_lk_m(fc.xn, fo.z, c.xn, o.z, xs, ys);
    lemma_lk_s(rf_mul(fo.x, fc.d2), rf_mul(fc.xn, fo.z), fm(o.x, c.d2), fm(c.xn, o.z), xs, ys);
}

proof fn lemma_fits_chord_x()
    ensures
        rfits(idf_chord_x(), idd_chord_x()),
{
    lemma_pt_fits(0);
    lemma_pt_fits(1);
    lemma_rcb_fits(pt_f(0), pt_f(1), pt_d(0), pt_d(1));
    lemma_chord_fits();
    let (fo, d) = (rcb_f(pt_f(0), pt_f(1)), rcb_d(pt_d(0), pt_d(1)));
    let (fc, e) = (chord_f(), chord_d());
    lemma_rfits_mul(fo.x, fc.d2, d.x, e.d2);
    lemma_rfits_mul(fc.xn, fo.z, e.xn, d.z);
    lemma_rfits_sub(rf_mul(fo.x, fc.d2), rf_mul(fc.xn, fo.z), rd_mul(d.x, e.d2), rd_mul(e.xn, d.z));
}

proof fn lemma_link_chord_y(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        lk(idf_chord_y(), id_chord_y(xs, ys), xs, ys),
{
    lemma_pt_link(0, xs, ys);
    lemma_pt_link(1, xs, ys);
    lemma_rcb_link(pt(xs, ys, 0), pt(xs, ys, 1), pt_f(0), pt_f(1), xs, ys);
    lemma_chord_link(xs, ys);
    let (o, fo) = (rcb(pt(xs, ys, 0), pt(xs, ys, 1)), rcb_f(pt_f(0), pt_f(1)));
    let (c, fc) = (chord(xs, ys), chord_f());
    lemma_lk_m(fo.y, fc.d3, o.y, c.d3, xs, ys);
    lemma_lk_m(fc.yn, fo.z, c.yn, o.z, xs, ys);
    lemma_lk_s(rf_mul(fo.y, fc.d3), rf_mul(fc.yn, fo.z), fm(o.y, c.d3), fm(c.yn, o.z), xs, ys);
}

proof fn lemma_fits_chord_y()
    ensures
        rfits(idf_chord_y(), idd_chord_y()),
{
    lemma_pt_fits(0);
    lemma_pt_fits(1);
    lemma_rcb_fits(pt_f(0), pt_f(1), pt_d(0), pt_d(1));
    lemma_chord_fits();
    let (fo, d) = (rcb_f(pt_f(0), pt_f(1)), rcb_d(pt_d(0), pt_d(1)));
    let (fc, e) = (chord_f(), chord_d());
    lemma_rfits_mul(fo.y, fc.d3, d.y, e.d3);
    lemma_rfits_mul(fc.yn, fo.z, e.yn, d.z);
    lemma_rfits_sub(rf_mul(fo.y, fc.d3), rf_mul(fc.yn, fo.z), rd_mul(d.y, e.d3), rd_mul(e.yn, d.z));
}

proof fn lemma_link_dbl_x(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        lk(idf_dbl_x(), id_dbl_x(xs, ys), xs, ys),
{
    lemma_pt_link(0, xs, ys);
    lemma_rcb_link(pt(xs, ys, 0), pt(xs, ys, 0), pt_f(0), pt_f(0), xs, ys);
    lemma_dbl_link(xs, ys);
    let (o, fo) = (rcb(pt(xs, ys, 0), pt(xs, ys, 0)), rcb_f(pt_f(0), pt_f(0)));
    let (c, fc) = (dbl(xs, ys), dbl_f());
    lemma_lk_m(fo.x, fc.d2, o.x, c.d2, xs, ys);
    lemma_lk_m(fc.xn, fo.z, c.xn, o.z, xs, ys);
    lemma_lk_s(rf_mul(fo.x, fc.d2), rf_mul(fc.xn, fo.z), fm(o.x, c.d2), fm(c.xn, o.z), xs, ys);
}

proof fn lemma_fits_dbl_x()
    ensures
        rfits(idf_dbl_x(), idd_dbl_x()),
{
    lemma_pt_fits(0);
    lemma_rcb_fits(pt_f(0), pt_f(0), pt_d(0), pt_d(0));
    lemma_dbl_fits();
    let (fo, d) = (rcb_f(pt_f(0), pt_f(0)), rcb_d(pt_d(0), pt_d(0)));
    let (fc, e) = (dbl_f(), dbl_d());
    lemma_rfits_mul(fo.x, fc.d2, d.x, e.d2);
    lemma_rfits_mul(fc.xn, fo.z, e.xn, d.z);
    lemma_rfits_sub(rf_mul(fo.x, fc.d2), rf_mul(fc.xn, fo.z), rd_mul(d.x, e.d2), rd_mul(e.xn, d.z));
}

proof fn lemma_link_dbl_y(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        lk(idf_dbl_y(), id_dbl_y(xs, ys), xs, ys),
{
    lemma_pt_link(0, xs, ys);
    lemma_rcb_link(pt(xs, ys, 0), pt(xs, ys, 0), pt_f(0), pt_f(0), xs, ys);
    lemma_dbl_link(xs, ys);
    let (o, fo) = (rcb(pt(xs, ys, 0), pt(xs, ys, 0)), rcb_f(pt_f(0), pt_f(0)));
    let (c, fc) = (dbl(xs, ys), dbl_f());
    lemma_lk_m(fo.y, fc.d3, o.y, c.d3, xs, ys);
    lemma_lk_m(fc.yn, fo.z, c.yn, o.z, xs, ys);
    lemma_lk_s(rf_mul(fo.y, fc.d3), rf_mul(fc.yn, fo.z), fm(o.y, c.d3), fm(c.yn, o.z), xs, ys);
}

proof fn lemma_fits_dbl_y()
    ensures
        rfits(idf_dbl_y(), idd_dbl_y()),
{
    lemma_pt_fits(0);
    lemma_rcb_fits(pt_f(0), pt_f(0), pt_d(0), pt_d(0));
    lemma_dbl_fits();
    let (fo, d) = (rcb_f(pt_f(0), pt_f(0)), rcb_d(pt_d(0), pt_d(0)));
    let (fc, e) = (dbl_f(), dbl_d());
    lemma_rfits_mul(fo.y, fc.d3, d.y, e.d3);
    lemma_rfits_mul(fc.yn, fo.z, e.yn, d.z);
    lemma_rfits_sub(rf_mul(fo.y, fc.d3), rf_mul(fc.yn, fo.z), rd_mul(d.y, e.d3), rd_mul(e.yn, d.z));
}

proof fn lemma_link_chord_z(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        lk(idf_chord_z(), id_chord_z(xs, ys), xs, ys),
{
    lemma_pt_link(0, xs, ys);
    lemma_pt_link(1, xs, ys);
    lemma_ptm_link(xs, ys);
    lemma_rcb_link(pt(xs, ys, 0), pt(xs, ys, 1), pt_f(0), pt_f(1), xs, ys);
    lemma_rcb_link(pt(xs, ys, 0), ptm(xs, ys), pt_f(0), ptm_f(), xs, ys);
    lemma_chord_link(xs, ys);
    lemma_w_link(rf_x(0), rf_x(1), xs[0], xs[1], xs, ys);
    let (o, fo) = (rcb(pt(xs, ys, 0), pt(xs, ys, 1)), rcb_f(pt_f(0), pt_f(1)));
    let (om, fom) = (rcb(pt(xs, ys, 0), ptm(xs, ys)), rcb_f(pt_f(0), ptm_f()));
    let (c, fc) = (chord(xs, ys), chord_f());
    let (w, fw) = (w_val(xs[0], xs[1]), w_f(rf_x(0), rf_x(1)));
    lemma_lk_m(fo.z, fom.z, o.z, om.z, xs, ys);
    lemma_lk_m(fc.d3, fw, c.d3, w, xs, ys);
    lemma_lk_s(rf_mul(fo.z, fom.z), rf_mul(fc.d3, fw), fm(o.z, om.z), fm(c.d3, w), xs, ys);
}

proof fn lemma_fits_chord_z()
    ensures
        rfits(idf_chord_z(), idd_chord_z()),
{
    lemma_pt_fits(0);
    lemma_pt_fits(1);
    lemma_ptm_fits();
    lemma_rcb_fits(pt_f(0), pt_f(1), pt_d(0), pt_d(1));
    lemma_rcb_fits(pt_f(0), ptm_f(), pt_d(0), ptm_d());
    lemma_chord_fits();
    lemma_w_fits(rf_x(0), rf_x(1), rd_x(0), rd_x(1));
    let (fo, d) = (rcb_f(pt_f(0), pt_f(1)), rcb_d(pt_d(0), pt_d(1)));
    let (fom, dm) = (rcb_f(pt_f(0), ptm_f()), rcb_d(pt_d(0), ptm_d()));
    let (fc, e) = (chord_f(), chord_d());
    let (fw, dw) = (w_f(rf_x(0), rf_x(1)), w_d(rd_x(0), rd_x(1)));
    lemma_rfits_mul(fo.z, fom.z, d.z, dm.z);
    lemma_rfits_mul(fc.d3, fw, e.d3, dw);
    lemma_rfits_sub(rf_mul(fo.z, fom.z), rf_mul(fc.d3, fw), rd_mul(d.z, dm.z), rd_mul(e.d3, dw));
}

proof fn lemma_link_dbl_z(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        lk(idf_dbl_z(), id_dbl_z(xs, ys), xs, ys),
{
    lemma_pt_link(0, xs, ys);
    lemma_rcb_link(pt(xs, ys, 0), pt(xs, ys, 0), pt_f(0), pt_f(0), xs, ys);
    let (o, fo) = (rcb(pt(xs, ys, 0), pt(xs, ys, 0)), rcb_f(pt_f(0), pt_f(0)));
    lemma_rval_x(0, xs, ys);
    lemma_rval_y(0, xs, ys);
    lemma_lk_c(8, rf_y(0), ys[0], xs, ys);
    lemma_fv_link(rf_x(0), xs[0], xs, ys);
    lemma_lk_m(rf_sc(8, rf_y(0)), fv_f(rf_x(0)), 8 * ys[0], fv(xs[0]), xs, ys);
    lemma_lk_s(fo.z, rf_mul(rf_sc(8, rf_y(0)), fv_f(rf_x(0))), o.z, fm(8 * ys[0], fv(xs[0])), xs, ys);
}

proof fn lemma_fits_dbl_z()
    ensures
        rfits(idf_dbl_z(), idd_dbl_z()),
{
    lemma_pt_fits(0);
    lemma_rcb_fits(pt_f(0), pt_f(0), pt_d(0), pt_d(0));
    let (fo, d) = (rcb_f(pt_f(0), pt_f(0)), rcb_d(pt_d(0), pt_d(0)));
    lemma_rfits_x(0);
    lemma_rfits_y(0);
    lemma_rfits_sc(8, rf_y(0), rd_y(0));
    lemma_fv_fits(rf_x(0), rd_x(0));
    lemma_rfits_mul(rf_sc(8, rf_y(0)), fv_f(rf_x(0)), rd_sc(rd_y(0)), fv_d(rd_x(0)));
    lemma_rfits_sub(fo.z, rf_mul(rf_sc(8, rf_y(0)), fv_f(rf_x(0))), d.z, rd_mul(rd_sc(rd_y(0)), fv_d(rd_x(0))));
}

proof fn lemma_link_inv_x(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        lk(idf_inv_x(), id_inv_x(xs, ys), xs, ys),
{
    lemma_pt_link(0, xs, ys);
    lemma_ptn_link(xs, ys);
    lemma_rcb_link(pt(xs, ys, 0), ptn(xs, ys), pt_f(0), ptn_f(), xs, ys);
}

proof fn lemma_fits_inv_x()
    ensures
        rfits(idf_inv_x(), idd_inv_x()),
{
    lemma_pt_fits(0);
    lemma_ptn_fits();
    lemma_rcb_fits(pt_f(0), ptn_f(), pt_d(0), ptn_d());
}

proof fn lemma_link_inv_z(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        lk(idf_inv_z(), id_inv_z(xs, ys), xs, ys),
{
    lemma_pt_link(0, xs, ys);
    lemma_ptn_link(xs, ys);
    lemma_rcb_link(pt(xs, ys, 0), ptn(xs, ys), pt_f(0), ptn_f(), xs, ys);
}

proof fn lemma_fits_inv_z()
    ensures
        rfits(idf_inv_z(), idd_inv_z()),
{
    lemma_pt_fits(0);
    lemma_ptn_fits();
    lemma_rcb_fits(pt_f(0), ptn_f(), pt_d(0), ptn_d());
}

proof fn lemma_link_inv_y(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        lk(idf_inv_y(), id_inv_y(xs, ys), xs, ys),
{
    lemma_pt_link(0, xs, ys);
    lemma_ptn_link(xs, ys);
    lemma_rcb_link(pt(xs, ys, 0), ptn(xs, ys), pt_f(0), ptn_f(), xs, ys);
    lemma_rcb_link(pt(xs, ys, 0), pt(xs, ys, 0), pt_f(0), pt_f(0), xs, ys);
    lemma_lk_s(
        rcb_f(pt_f(0), ptn_f()).y,
        rcb_f(pt_f(0), pt_f(0)).y,
        rcb(pt(xs, ys, 0), ptn(xs, ys)).y,
        rcb(pt(xs, ys, 0), pt(xs, ys, 0)).y,
        xs,
        ys,
    );
}

proof fn lemma_fits_inv_y()
    ensures
        rfits(idf_inv_y(), idd_inv_y()),
{
    lemma_pt_fits(0);
    lemma_ptn_fits();
    lemma_rcb_fits(pt_f(0), ptn_f(), pt_d(0), ptn_d());
    lemma_rcb_fits(pt_f(0), pt_f(0), pt_d(0), pt_d(0));
    lemma_rfits_sub(
        rcb_f(pt_f(0), ptn_f()).y,
        rcb_f(pt_f(0), pt_f(0)).y,
        rcb_d(pt_d(0), ptn_d()).y,
        rcb_d(pt_d(0), pt_d(0)).y,
    );
}

proof fn lemma_link_closure_chord(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        lk(idf_closure_chord(), id_closure_chord(xs, ys), xs, ys),
{
    lemma_chord_link(xs, ys);
    let (c, fc) = (chord(xs, ys), chord_f());
    lemma_clo_link(fc.xn, fc.yn, fc.d2, c.xn, c.yn, c.d2, xs, ys);
}

proof fn lemma_fits_closure_chord()
    ensures
        rfits(idf_closure_chord(), idd_closure_chord()),
{
    lemma_chord_fits();
    let (fc, e) = (chord_f(), chord_d());
    lemma_clo_fits(fc.xn, fc.yn, fc.d2, e.xn, e.yn, e.d2);
}

proof fn lemma_link_closure_dbl(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        lk(idf_closure_dbl(), id_closure_dbl(xs, ys), xs, ys),
{
    lemma_dbl_link(xs, ys);
    let (c, fc) = (dbl(xs, ys), dbl_f());
    lemma_clo_link(fc.xn, fc.yn, fc.d2, c.xn, c.yn, c.d2, xs, ys);
}

proof fn lemma_fits_closure_dbl()
    ensures
        rfits(idf_closure_dbl(), idd_closure_dbl()),
{
    lemma_dbl_fits();
    let (fc, e) = (dbl_f(), dbl_d());
    lemma_clo_fits(fc.xn, fc.yn, fc.d2, e.xn, e.yn, e.d2);
}

// ---------------------------------------------------------------------------------------------
// The grid driver
// ---------------------------------------------------------------------------------------------

proof fn lemma_deg_fits(d: RD, n0: int, n1: int, n2: int)
    requires
        deg_ok(d, seq![n0, n1, n2]),
        0 <= n0 && 0 <= n1 && 0 <= n2,
    ensures
        deg_fits(d, grid_x(n0, n1, n2)),
{
    let g = grid_x(n0, n1, n2);
    let n = seq![n0, n1, n2];
    assert(g[0].len() == n0 && g[1].len() == n1 && g[2].len() == n2);
    assert forall|s: int, k: int| 0 <= s < 8 && 0 <= k < 3 && !rz(d[s]) implies #[trigger] d[s][k]
        < g[k].len() by {
        assert(row_ok(d[s], n)) by {
            assert(s == 0 || s == 1 || s == 2 || s == 3 || s == 4 || s == 5 || s == 6 || s == 7);
        }
        assert(k == 0 || k == 1 || k == 2);
    }
}

/// `lemma_identity`'s grid premises for the first n0, n1, n2 grid points.
pub(crate) proof fn lemma_grid_ok(n0: int, n1: int, n2: int)
    requires
        1 <= n0 <= 13,
        1 <= n1 <= 13,
        1 <= n2 <= 13,
    ensures
        grid_ok(grid_x(n0, n1, n2), grid_y(n0, n1, n2)),
{
    lemma_grid_pts_ok();
    let (g, h) = (grid_x(n0, n1, n2), grid_y(n0, n1, n2));
    assert forall|k: int| 0 <= k < 3 implies #[trigger] gk_ok(g, h, k) by {
        let n = if k == 0 {
            n0
        } else if k == 1 {
            n1
        } else {
            n2
        };
        assert(g[k] == gxs(n) && h[k] == gys(n));
        assert forall|i: int, j: int|
            #![trigger gxs(n)[i], gxs(n)[j]]
            0 <= i < gxs(n).len() && 0 <= j < gxs(n).len() && i != j implies fmod(gxs(n)[i]) != fmod(
            gxs(n)[j],
        ) by {
            assert(gxs(n)[i] == gx(i) && gxs(n)[j] == gx(j));
        }
    }
    assert forall|k: int, t: int| 0 <= k < 3 && 0 <= t < g[k].len() implies #[trigger] gpt_ok(
        g[k][t],
        h[k][t],
    ) by {
        let n = if k == 0 {
            n0
        } else if k == 1 {
            n1
        } else {
            n2
        };
        assert(g[k] == gxs(n) && h[k] == gys(n));
        assert(g[k][t] == gx(t) && h[k][t] == gy(t));
        assert(gpt_ok(gx(t), gy(t)));
    }
}

/// A curve identity f, linked on the curve to a formal g whose degrees are below the grid sizes,
/// holds on the curve if it holds at every grid cell under every y-sign choice.
pub(crate) proof fn lemma_id_grid(
    f: spec_fn(Seq<int>, Seq<int>) -> int,
    g: RF,
    d: RD,
    n0: int,
    n1: int,
    n2: int,
)
    requires
        rfits(g, d),
        1 <= n0 <= 13,
        1 <= n1 <= 13,
        1 <= n2 <= 13,
        deg_ok(d, seq![n0, n1, n2]),
        forall|i: int, j: int, l: int|
            0 <= i < n0 && 0 <= j < n1 && 0 <= l < n2 ==> #[trigger] sg_cell(f, i, j, l),
        forall|xs: Seq<int>, ys: Seq<int>| on3(xs, ys) ==> #[trigger] lk(g, f(xs, ys), xs, ys),
    ensures
        forall|xs: Seq<int>, ys: Seq<int>| #[trigger] on3(xs, ys) ==> fmod(f(xs, ys)) == 0,
{
    lemma_group_consts();
    let (gx3, gy3) = (grid_x(n0, n1, n2), grid_y(n0, n1, n2));
    lemma_grid_ok(n0, n1, n2);
    lemma_deg_fits(d, n0, n1, n2);
    assert forall|i: int, j: int, l: int, sig: u8| in_box(gx3, i, j, l) && sig < 8 implies fmod(
        #[trigger] rval(g, gpt(gx3, i, j, l), sgn(sig, gpt(gy3, i, j, l))),
    ) == 0 by {
        lemma_grid_seq(n0, n1, n2, i, j, l);
        let xs = gpt(gx3, i, j, l);
        let ys = sgn(sig, gpt(gy3, i, j, l));
        lemma_grid_on3(gx3, gy3, i, j, l, sig);
        assert(lk(g, f(xs, ys), xs, ys));
        assert(sg_cell(f, i, j, l));
        reveal(sg_cell);
        assert(f(xs, ys) % P_LIT() == 0) by {
            assert(sig == 0 || sig == 1 || sig == 2 || sig == 3 || sig == 4 || sig == 5 || sig == 6
                || sig == 7);
        }
    }
    lemma_identity(g, d, gx3, gy3);
    assert forall|xs: Seq<int>, ys: Seq<int>| #[trigger] on3(xs, ys) implies fmod(f(xs, ys)) == 0 by {
        assert(lk(g, f(xs, ys), xs, ys));
        assert(fmod(rval(g, xs, ys)) == 0);
    }
}

// ---------------------------------------------------------------------------------------------
// The exported identities: each holds at all curve points (on3), proved on its grid
// ---------------------------------------------------------------------------------------------

pub(crate) open spec fn fn_chord_x() -> spec_fn(Seq<int>, Seq<int>) -> int {
    |xs: Seq<int>, ys: Seq<int>| id_chord_x(xs, ys)
}

// I2 chord: X3 d^2 == xn Z3.
pub(crate) proof fn lemma_id_chord_x(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        fmod(id_chord_x(xs, ys)) == 0,
{
    lemma_fits_chord_x();
    lemma_deg_chord_x();
    lemma_cells_chord_x();
    assert forall|us: Seq<int>, vs: Seq<int>| on3(us, vs) implies #[trigger] lk(idf_chord_x(), fn_chord_x()(us, vs), us, vs) by {
        lemma_link_chord_x(us, vs);
    }
    lemma_id_grid(fn_chord_x(), idf_chord_x(), idd_chord_x(), 7, 7, 1);
    assert(fmod(fn_chord_x()(xs, ys)) == 0);
}

pub(crate) open spec fn fn_chord_y() -> spec_fn(Seq<int>, Seq<int>) -> int {
    |xs: Seq<int>, ys: Seq<int>| id_chord_y(xs, ys)
}

// I3 chord: Y3 d^3 == yn Z3.
pub(crate) proof fn lemma_id_chord_y(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        fmod(id_chord_y(xs, ys)) == 0,
{
    lemma_fits_chord_y();
    lemma_deg_chord_y();
    lemma_cells_chord_y();
    assert forall|us: Seq<int>, vs: Seq<int>| on3(us, vs) implies #[trigger] lk(idf_chord_y(), fn_chord_y()(us, vs), us, vs) by {
        lemma_link_chord_y(us, vs);
    }
    lemma_id_grid(fn_chord_y(), idf_chord_y(), idd_chord_y(), 8, 8, 1);
    assert(fmod(fn_chord_y()(xs, ys)) == 0);
}

pub(crate) open spec fn fn_chord_z() -> spec_fn(Seq<int>, Seq<int>) -> int {
    |xs: Seq<int>, ys: Seq<int>| id_chord_z(xs, ys)
}

// I4 chord: Z3(P, Q) Z3(P, -Q) == d^3 W(x0, x1).
pub(crate) proof fn lemma_id_chord_z(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        fmod(id_chord_z(xs, ys)) == 0,
{
    lemma_fits_chord_z();
    lemma_deg_chord_z();
    lemma_cells_chord_z();
    assert forall|us: Seq<int>, vs: Seq<int>| on3(us, vs) implies #[trigger] lk(idf_chord_z(), fn_chord_z()(us, vs), us, vs) by {
        lemma_link_chord_z(us, vs);
    }
    lemma_id_grid(fn_chord_z(), idf_chord_z(), idd_chord_z(), 7, 7, 1);
    assert(fmod(fn_chord_z()(xs, ys)) == 0);
}

pub(crate) open spec fn fn_dbl_x() -> spec_fn(Seq<int>, Seq<int>) -> int {
    |xs: Seq<int>, ys: Seq<int>| id_dbl_x(xs, ys)
}

// I5 doubling: X3 e^2 == xn Z3.
pub(crate) proof fn lemma_id_dbl_x(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        fmod(id_dbl_x(xs, ys)) == 0,
{
    lemma_fits_dbl_x();
    lemma_deg_dbl_x();
    lemma_cells_dbl_x();
    assert forall|us: Seq<int>, vs: Seq<int>| on3(us, vs) implies #[trigger] lk(idf_dbl_x(), fn_dbl_x()(us, vs), us, vs) by {
        lemma_link_dbl_x(us, vs);
    }
    lemma_id_grid(fn_dbl_x(), idf_dbl_x(), idd_dbl_x(), 8, 1, 1);
    assert(fmod(fn_dbl_x()(xs, ys)) == 0);
}

pub(crate) open spec fn fn_dbl_y() -> spec_fn(Seq<int>, Seq<int>) -> int {
    |xs: Seq<int>, ys: Seq<int>| id_dbl_y(xs, ys)
}

// I6 doubling: Y3 e^3 == yn Z3.
pub(crate) proof fn lemma_id_dbl_y(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        fmod(id_dbl_y(xs, ys)) == 0,
{
    lemma_fits_dbl_y();
    lemma_deg_dbl_y();
    lemma_cells_dbl_y();
    assert forall|us: Seq<int>, vs: Seq<int>| on3(us, vs) implies #[trigger] lk(idf_dbl_y(), fn_dbl_y()(us, vs), us, vs) by {
        lemma_link_dbl_y(us, vs);
    }
    lemma_id_grid(fn_dbl_y(), idf_dbl_y(), idd_dbl_y(), 10, 1, 1);
    assert(fmod(fn_dbl_y()(xs, ys)) == 0);
}

pub(crate) open spec fn fn_dbl_z() -> spec_fn(Seq<int>, Seq<int>) -> int {
    |xs: Seq<int>, ys: Seq<int>| id_dbl_z(xs, ys)
}

// I7 doubling: Z3 == 8 y0 f(x0).
pub(crate) proof fn lemma_id_dbl_z(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        fmod(id_dbl_z(xs, ys)) == 0,
{
    lemma_fits_dbl_z();
    lemma_deg_dbl_z();
    lemma_cells_dbl_z();
    assert forall|us: Seq<int>, vs: Seq<int>| on3(us, vs) implies #[trigger] lk(idf_dbl_z(), fn_dbl_z()(us, vs), us, vs) by {
        lemma_link_dbl_z(us, vs);
    }
    lemma_id_grid(fn_dbl_z(), idf_dbl_z(), idd_dbl_z(), 4, 1, 1);
    assert(fmod(fn_dbl_z()(xs, ys)) == 0);
}

pub(crate) open spec fn fn_inv_x() -> spec_fn(Seq<int>, Seq<int>) -> int {
    |xs: Seq<int>, ys: Seq<int>| id_inv_x(xs, ys)
}

// I8a P + (-P): X3 == 0.
pub(crate) proof fn lemma_id_inv_x(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        fmod(id_inv_x(xs, ys)) == 0,
{
    lemma_fits_inv_x();
    lemma_deg_inv_x();
    lemma_cells_inv_x();
    assert forall|us: Seq<int>, vs: Seq<int>| on3(us, vs) implies #[trigger] lk(idf_inv_x(), fn_inv_x()(us, vs), us, vs) by {
        lemma_link_inv_x(us, vs);
    }
    lemma_id_grid(fn_inv_x(), idf_inv_x(), idd_inv_x(), 5, 1, 1);
    assert(fmod(fn_inv_x()(xs, ys)) == 0);
}

pub(crate) open spec fn fn_inv_z() -> spec_fn(Seq<int>, Seq<int>) -> int {
    |xs: Seq<int>, ys: Seq<int>| id_inv_z(xs, ys)
}

// I8b P + (-P): Z3 == 0.
pub(crate) proof fn lemma_id_inv_z(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        fmod(id_inv_z(xs, ys)) == 0,
{
    lemma_fits_inv_z();
    lemma_deg_inv_z();
    lemma_cells_inv_z();
    assert forall|us: Seq<int>, vs: Seq<int>| on3(us, vs) implies #[trigger] lk(idf_inv_z(), fn_inv_z()(us, vs), us, vs) by {
        lemma_link_inv_z(us, vs);
    }
    lemma_id_grid(fn_inv_z(), idf_inv_z(), idd_inv_z(), 4, 1, 1);
    assert(fmod(fn_inv_z()(xs, ys)) == 0);
}

pub(crate) open spec fn fn_inv_y() -> spec_fn(Seq<int>, Seq<int>) -> int {
    |xs: Seq<int>, ys: Seq<int>| id_inv_y(xs, ys)
}

// I8c P + (-P): Y3 == Y3(P, P).
pub(crate) proof fn lemma_id_inv_y(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        fmod(id_inv_y(xs, ys)) == 0,
{
    lemma_fits_inv_y();
    lemma_deg_inv_y();
    lemma_cells_inv_y();
    assert forall|us: Seq<int>, vs: Seq<int>| on3(us, vs) implies #[trigger] lk(idf_inv_y(), fn_inv_y()(us, vs), us, vs) by {
        lemma_link_inv_y(us, vs);
    }
    lemma_id_grid(fn_inv_y(), idf_inv_y(), idd_inv_y(), 7, 1, 1);
    assert(fmod(fn_inv_y()(xs, ys)) == 0);
}

pub(crate) open spec fn fn_closure_chord() -> spec_fn(Seq<int>, Seq<int>) -> int {
    |xs: Seq<int>, ys: Seq<int>| id_closure_chord(xs, ys)
}

// I10a chord closure.
pub(crate) proof fn lemma_id_closure_chord(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        fmod(id_closure_chord(xs, ys)) == 0,
{
    lemma_fits_closure_chord();
    lemma_deg_closure_chord();
    lemma_cells_closure_chord();
    assert forall|us: Seq<int>, vs: Seq<int>| on3(us, vs) implies #[trigger] lk(idf_closure_chord(), fn_closure_chord()(us, vs), us, vs) by {
        lemma_link_closure_chord(us, vs);
    }
    lemma_id_grid(fn_closure_chord(), idf_closure_chord(), idd_closure_chord(), 10, 10, 1);
    assert(fmod(fn_closure_chord()(xs, ys)) == 0);
}

pub(crate) open spec fn fn_closure_dbl() -> spec_fn(Seq<int>, Seq<int>) -> int {
    |xs: Seq<int>, ys: Seq<int>| id_closure_dbl(xs, ys)
}

// I10b doubling closure.
pub(crate) proof fn lemma_id_closure_dbl(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        fmod(id_closure_dbl(xs, ys)) == 0,
{
    lemma_fits_closure_dbl();
    lemma_deg_closure_dbl();
    lemma_cells_closure_dbl();
    assert forall|us: Seq<int>, vs: Seq<int>| on3(us, vs) implies #[trigger] lk(idf_closure_dbl(), fn_closure_dbl()(us, vs), us, vs) by {
        lemma_link_closure_dbl(us, vs);
    }
    lemma_id_grid(fn_closure_dbl(), idf_closure_dbl(), idd_closure_dbl(), 13, 1, 1);
    assert(fmod(fn_closure_dbl()(xs, ys)) == 0);
}

// ---------------------------------------------------------------------------------------------
// The resultant identities (y-free, all x): links, degrees, and the grid over {0, 1, ...}
// ---------------------------------------------------------------------------------------------

pub(crate) open spec fn ek(a: MP, v: int, xs: Seq<int>) -> bool {
    fmod(ev(a, xs)) == fmod(v)
}

proof fn lemma_ek_m(a: MP, b: MP, va: int, vb: int, xs: Seq<int>)
    requires
        ek(a, va, xs),
        ek(b, vb, xs),
    ensures
        ek(pmul(a, b), fm(va, vb), xs),
{
    lemma_ev_mul(a, b, xs);
    lemma_cg_mul(ev(a, xs), ev(b, xs), va, vb);
    lemma_md(va * vb);
}

proof fn lemma_ek_a(a: MP, b: MP, va: int, vb: int, xs: Seq<int>)
    requires
        ek(a, va, xs),
        ek(b, vb, xs),
    ensures
        ek(padd(a, b), va + vb, xs),
{
    lemma_ev_add(a, b, xs);
    lemma_cg_add(ev(a, xs), ev(b, xs), va, vb);
}

proof fn lemma_ek_c(c: int, a: MP, va: int, xs: Seq<int>)
    requires
        ek(a, va, xs),
    ensures
        ek(psc(c, a), c * va, xs),
{
    lemma_ev_mul(pk(c), a, xs);
    lemma_ev_k(c, xs);
    lemma_cg_mul(c, ev(a, xs), c, va);
}

proof fn lemma_ek_s(a: MP, b: MP, va: int, vb: int, xs: Seq<int>)
    requires
        ek(a, va, xs),
        ek(b, vb, xs),
    ensures
        ek(psub(a, b), va - vb, xs),
{
    lemma_ek_c(-1, b, vb, xs);
    lemma_ek_a(a, pneg(b), va, -1 * vb, xs);
}

proof fn lemma_ek_k(c: int, xs: Seq<int>)
    ensures
        ek(pk(c), c, xs),
{
    lemma_ev_k(c, xs);
}

proof fn lemma_fv_ek(x: MP, v: int, xs: Seq<int>)
    requires
        ek(x, v, xs),
    ensures
        ek(fv_mp(x), fv(v), xs),
{
    lemma_ek_m(x, x, v, v, xs);
    lemma_ek_m(pmul(x, x), x, fm(v, v), v, xs);
    lemma_ek_c(3, x, v, xs);
    lemma_ek_s(pmul(pmul(x, x), x), psc(3, x), fm(fm(v, v), v), 3 * v, xs);
    lemma_ek_k(B_LIT(), xs);
    lemma_ek_a(psub(pmul(pmul(x, x), x), psc(3, x)), pk(B_LIT()), fm(fm(v, v), v) - 3 * v, B_LIT(), xs);
}

proof fn lemma_w_ek(x1: MP, x2: MP, v1: int, v2: int, xs: Seq<int>)
    requires
        ek(x1, v1, xs),
        ek(x2, v2, xs),
    ensures
        ek(w_mp(x1, x2), w_val(v1, v2), xs),
{
    let bl = B_LIT();
    let b = pk(bl);
    lemma_ek_k(bl, xs);
    lemma_ek_k(27, xs);
    lemma_ek_a(x1, x2, v1, v2, xs);
    let (s, vs) = (padd(x1, x2), v1 + v2);
    lemma_ek_m(x1, x2, v1, v2, xs);
    let (t, vt) = (pmul(x1, x2), fm(v1, v2));
    lemma_ek_m(s, s, vs, vs, xs);
    let (ss, vss) = (pmul(s, s), fm(vs, vs));
    lemma_ek_m(ss, s, vss, vs, xs);
    lemma_ek_m(s, t, vs, vt, xs);
    lemma_ek_c(6, pmul(s, t), fm(vs, vt), xs);
    lemma_ek_a(pmul(ss, s), psc(6, pmul(s, t)), fm(vss, vs), 6 * fm(vs, vt), xs);
    lemma_ek_c(6, s, vs, xs);
    let bc0 = padd(pmul(ss, s), psc(6, pmul(s, t)));
    lemma_ek_a(bc0, psc(6, s), fm(vss, vs) + 6 * fm(vs, vt), 6 * vs, xs);
    let bc = padd(bc0, psc(6, s));
    let vbc = fm(vss, vs) + 6 * fm(vs, vt) + 6 * vs;
    lemma_ek_m(t, t, vt, vt, xs);
    lemma_ek_m(pmul(t, t), t, fm(vt, vt), vt, xs);
    lemma_ek_m(t, ss, vt, vss, xs);
    lemma_ek_c(3, pmul(t, ss), fm(vt, vss), xs);
    lemma_ek_s(pmul(pmul(t, t), t), psc(3, pmul(t, ss)), fm(fm(vt, vt), vt), 3 * fm(vt, vss), xs);
    let c1 = psub(pmul(pmul(t, t), t), psc(3, pmul(t, ss)));
    let v1c = fm(fm(vt, vt), vt) - 3 * fm(vt, vss);
    lemma_ek_c(3, pmul(t, t), fm(vt, vt), xs);
    lemma_ek_s(c1, psc(3, pmul(t, t)), v1c, 3 * fm(vt, vt), xs);
    let c2 = psub(c1, psc(3, pmul(t, t)));
    let v2c = v1c - 3 * fm(vt, vt);
    lemma_ek_c(9, ss, vss, xs);
    lemma_ek_s(c2, psc(9, ss), v2c, 9 * vss, xs);
    lemma_ek_c(9, t, vt, xs);
    lemma_ek_s(psub(c2, psc(9, ss)), psc(9, t), v2c - 9 * vss, 9 * vt, xs);
    let c0 = psub(psub(c2, psc(9, ss)), psc(9, t));
    let vc0 = v2c - 9 * vss - 9 * vt;
    lemma_ek_m(b, bc, bl, vbc, xs);
    lemma_ek_m(b, b, bl, bl, xs);
    lemma_ek_c(8, pmul(b, b), fm(bl, bl), xs);
    lemma_ek_s(pmul(b, bc), psc(8, pmul(b, b)), fm(bl, vbc), 8 * fm(bl, bl), xs);
    let t1 = psub(pmul(b, bc), psc(8, pmul(b, b)));
    let vt1 = fm(bl, vbc) - 8 * fm(bl, bl);
    lemma_ek_a(t1, c0, vt1, vc0, xs);
    lemma_ek_a(padd(t1, c0), pk(27), vt1 + vc0, 27, xs);
}

proof fn lemma_r1_ek(x1: MP, x2: MP, v1: int, v2: int, xs: Seq<int>)
    requires
        ek(x1, v1, xs),
        ek(x2, v2, xs),
    ensures
        ek(r1_mp(x1, x2), r1_val(v1, v2), xs),
{
    let (s, vs) = (padd(x1, x2), v1 + v2);
    lemma_ek_a(x1, x2, v1, v2, xs);
    lemma_ek_m(s, s, vs, vs, xs);
    lemma_ek_m(x1, x2, v1, v2, xs);
    lemma_ek_c(2, pmul(x1, x2), fm(v1, v2), xs);
    lemma_ek_a(pmul(s, s), psc(2, pmul(x1, x2)), fm(vs, vs), 2 * fm(v1, v2), xs);
    lemma_ek_k(6, xs);
    lemma_ek_s(padd(pmul(s, s), psc(2, pmul(x1, x2))), pk(6), fm(vs, vs) + 2 * fm(v1, v2), 6, xs);
    lemma_ek_c(2, psub(padd(pmul(s, s), psc(2, pmul(x1, x2))), pk(6)), fm(vs, vs) + 2 * fm(v1, v2) - 6, xs);
}

proof fn lemma_r0_ek(x1: MP, x2: MP, v1: int, v2: int, xs: Seq<int>)
    requires
        ek(x1, v1, xs),
        ek(x2, v2, xs),
    ensures
        ek(r0_mp(x1, x2), r0_val(v1, v2), xs),
{
    let (s, vs) = (padd(x1, x2), v1 + v2);
    let c = -4 * B_LIT();
    lemma_ek_a(x1, x2, v1, v2, xs);
    lemma_ek_k(c, xs);
    lemma_ek_m(x1, x2, v1, v2, xs);
    lemma_ek_m(pmul(x1, x2), s, fm(v1, v2), vs, xs);
    lemma_ek_a(pk(c), pmul(pmul(x1, x2), s), c, fm(fm(v1, v2), vs), xs);
    lemma_ek_c(3, s, vs, xs);
    lemma_ek_a(padd(pk(c), pmul(pmul(x1, x2), s)), psc(3, s), c + fm(fm(v1, v2), vs), 3 * vs, xs);
    lemma_ek_c(-2, padd(padd(pk(c), pmul(pmul(x1, x2), s)), psc(3, s)), c + fm(fm(v1, v2), vs) + 3 * vs, xs);
}

proof fn lemma_q_ek(x1: MP, x2: MP, e: MP, v1: int, v2: int, ve: int, xs: Seq<int>)
    requires
        ek(x1, v1, xs),
        ek(x2, v2, xs),
        ek(e, ve, xs),
    ensures
        ek(q_mp(x1, x2, e), q_val(v1, v2, ve), xs),
{
    let (s, vs) = (padd(x1, x2), v1 + v2);
    lemma_ek_a(x1, x2, v1, v2, xs);
    lemma_ek_m(e, e, ve, ve, xs);
    lemma_ek_c(2, pmul(e, e), fm(ve, ve), xs);
    lemma_ek_m(s, e, vs, ve, xs);
    lemma_ek_a(psc(2, pmul(e, e)), pmul(s, e), 2 * fm(ve, ve), fm(vs, ve), xs);
    lemma_ek_m(x1, x2, v1, v2, xs);
    lemma_ek_k(3, xs);
    lemma_ek_a(pmul(x1, x2), pk(3), fm(v1, v2), 3, xs);
    lemma_ek_s(
        padd(psc(2, pmul(e, e)), pmul(s, e)),
        padd(pmul(x1, x2), pk(3)),
        2 * fm(ve, ve) + fm(vs, ve),
        fm(v1, v2) + 3,
        xs,
    );
}

proof fn lemma_res1_link(xs: Seq<int>)
    requires
        xs.len() == 3,
    ensures
        ek(res1_mp(), id_res1(xs[0], xs[1]), xs),
{
    let (x1, x2, v1, v2) = (px(0), px(1), xs[0], xs[1]);
    lemma_ev_x(0, xs);
    lemma_ev_x(1, xs);
    let (s, vs) = (padd(x1, x2), v1 + v2);
    lemma_ek_a(x1, x2, v1, v2, xs);
    lemma_r0_ek(x1, x2, v1, v2, xs);
    lemma_r1_ek(x1, x2, v1, v2, xs);
    lemma_w_ek(x1, x2, v1, v2, xs);
    let (a, va) = (r0_mp(x1, x2), r0_val(v1, v2));
    let (b, vb) = (r1_mp(x1, x2), r1_val(v1, v2));
    lemma_ek_m(a, a, va, va, xs);
    lemma_ek_c(2, pmul(a, a), fm(va, va), xs);
    lemma_ek_m(s, a, vs, va, xs);
    lemma_ek_m(pmul(s, a), b, fm(vs, va), vb, xs);
    lemma_ek_s(psc(2, pmul(a, a)), pmul(pmul(s, a), b), 2 * fm(va, va), fm(fm(vs, va), vb), xs);
    lemma_ek_m(x1, x2, v1, v2, xs);
    lemma_ek_k(3, xs);
    lemma_ek_a(pmul(x1, x2), pk(3), fm(v1, v2), 3, xs);
    lemma_ek_m(b, b, vb, vb, xs);
    lemma_ek_m(padd(pmul(x1, x2), pk(3)), pmul(b, b), fm(v1, v2) + 3, fm(vb, vb), xs);
    let t1 = psub(psc(2, pmul(a, a)), pmul(pmul(s, a), b));
    let vt1 = 2 * fm(va, va) - fm(fm(vs, va), vb);
    lemma_ek_s(t1, pmul(padd(pmul(x1, x2), pk(3)), pmul(b, b)), vt1, fm(fm(v1, v2) + 3, fm(vb, vb)), xs);
    lemma_ek_c(16, w_mp(x1, x2), w_val(v1, v2), xs);
    lemma_ek_a(
        psub(t1, pmul(padd(pmul(x1, x2), pk(3)), pmul(b, b))),
        psc(16, w_mp(x1, x2)),
        vt1 - fm(fm(v1, v2) + 3, fm(vb, vb)),
        16 * w_val(v1, v2),
        xs,
    );
}

proof fn lemma_res2_link(xs: Seq<int>)
    requires
        xs.len() == 3,
    ensures
        ek(res2_mp(), id_res2(xs[0], xs[1], xs[2]), xs),
{
    let (x1, x2, e, v1, v2, ve) = (px(0), px(1), px(2), xs[0], xs[1], xs[2]);
    lemma_ev_x(0, xs);
    lemma_ev_x(1, xs);
    lemma_ev_x(2, xs);
    lemma_ek_c(4, e, ve, xs);
    lemma_ek_a(x1, x2, v1, v2, xs);
    lemma_ek_c(2, padd(x1, x2), v1 + v2, xs);
    lemma_ek_s(psc(4, e), psc(2, padd(x1, x2)), 4 * ve, 2 * (v1 + v2), xs);
    let (lin, vlin) = (psub(psc(4, e), psc(2, padd(x1, x2))), 4 * ve - 2 * (v1 + v2));
    lemma_fv_ek(e, ve, xs);
    lemma_ek_c(8, fv_mp(e), fv(ve), xs);
    lemma_q_ek(x1, x2, e, v1, v2, ve, xs);
    lemma_ek_m(q_mp(x1, x2, e), lin, q_val(v1, v2, ve), vlin, xs);
    lemma_ek_s(psc(8, fv_mp(e)), pmul(q_mp(x1, x2, e), lin), 8 * fv(ve), fm(q_val(v1, v2, ve), vlin), xs);
    let t1 = psub(psc(8, fv_mp(e)), pmul(q_mp(x1, x2, e), lin));
    let vt1 = 8 * fv(ve) - fm(q_val(v1, v2, ve), vlin);
    lemma_r1_ek(x1, x2, v1, v2, xs);
    lemma_ek_m(r1_mp(x1, x2), e, r1_val(v1, v2), ve, xs);
    lemma_ek_s(t1, pmul(r1_mp(x1, x2), e), vt1, fm(r1_val(v1, v2), ve), xs);
    lemma_r0_ek(x1, x2, v1, v2, xs);
    lemma_ek_s(psub(t1, pmul(r1_mp(x1, x2), e)), r0_mp(x1, x2), vt1 - fm(r1_val(v1, v2), ve), r0_val(v1, v2), xs);
}

/// fits with a 3-variable degree bound.
pub(crate) open spec fn f3(a: MP, d: Seq<nat>) -> bool {
    fits(a, d) && d.len() == 3
}

proof fn lemma_f3_add(a: MP, b: MP, da: Seq<nat>, db: Seq<nat>)
    requires
        f3(a, da),
        f3(b, db),
    ensures
        f3(padd(a, b), dmax(da, db)),
{
    lemma_fits_add(a, b, da, db);
}

proof fn lemma_f3_mul(a: MP, b: MP, da: Seq<nat>, db: Seq<nat>)
    requires
        f3(a, da),
        f3(b, db),
    ensures
        f3(pmul(a, b), dsum(da, db)),
{
    lemma_fits_mul(a, b, da, db);
}

proof fn lemma_f3_sc(c: int, a: MP, da: Seq<nat>)
    requires
        f3(a, da),
    ensures
        f3(psc(c, a), dsc(da)),
{
    lemma_fits_mul(pk(c), a, dz(), da);
}

proof fn lemma_f3_sub(a: MP, b: MP, da: Seq<nat>, db: Seq<nat>)
    requires
        f3(a, da),
        f3(b, db),
    ensures
        f3(psub(a, b), dsub(da, db)),
{
    lemma_f3_sc(-1, b, db);
    lemma_f3_add(a, pneg(b), da, dsc(db));
}

proof fn lemma_f3_k(c: int)
    ensures
        f3(pk(c), dz()),
{
}

proof fn lemma_f3_x(i: nat)
    requires
        i < 3,
    ensures
        f3(px(i), e3(i, 1)),
{
    lemma_fits_x(i, e3(i, 1));
}

proof fn lemma_fv_f3(x: MP, d: Seq<nat>)
    requires
        f3(x, d),
    ensures
        f3(fv_mp(x), fv_ds(d)),
{
    lemma_f3_mul(x, x, d, d);
    lemma_f3_mul(pmul(x, x), x, dsum(d, d), d);
    lemma_f3_sc(3, x, d);
    lemma_f3_sub(pmul(pmul(x, x), x), psc(3, x), dsum(dsum(d, d), d), dsc(d));
    lemma_f3_k(B_LIT());
    lemma_f3_add(psub(pmul(pmul(x, x), x), psc(3, x)), pk(B_LIT()), dsub(dsum(dsum(d, d), d), dsc(d)), dz());
}

proof fn lemma_w_f3(x1: MP, x2: MP, d1: Seq<nat>, d2: Seq<nat>)
    requires
        f3(x1, d1),
        f3(x2, d2),
    ensures
        f3(w_mp(x1, x2), w_ds(d1, d2)),
{
    let (b, db) = (pk(B_LIT()), dz());
    lemma_f3_k(B_LIT());
    lemma_f3_k(27);
    lemma_f3_add(x1, x2, d1, d2);
    let (s, ds) = (padd(x1, x2), dmax(d1, d2));
    lemma_f3_mul(x1, x2, d1, d2);
    let (t, dt) = (pmul(x1, x2), dsum(d1, d2));
    lemma_f3_mul(s, s, ds, ds);
    let (ss, dss) = (pmul(s, s), dsum(ds, ds));
    lemma_f3_mul(ss, s, dss, ds);
    lemma_f3_mul(s, t, ds, dt);
    lemma_f3_sc(6, pmul(s, t), dsum(ds, dt));
    lemma_f3_add(pmul(ss, s), psc(6, pmul(s, t)), dsum(dss, ds), dsc(dsum(ds, dt)));
    lemma_f3_sc(6, s, ds);
    let bc0 = padd(pmul(ss, s), psc(6, pmul(s, t)));
    let dbc0 = dmax(dsum(dss, ds), dsc(dsum(ds, dt)));
    lemma_f3_add(bc0, psc(6, s), dbc0, dsc(ds));
    let (bc, dbc) = (padd(bc0, psc(6, s)), dmax(dbc0, dsc(ds)));
    lemma_f3_mul(t, t, dt, dt);
    lemma_f3_mul(pmul(t, t), t, dsum(dt, dt), dt);
    lemma_f3_mul(t, ss, dt, dss);
    lemma_f3_sc(3, pmul(t, ss), dsum(dt, dss));
    lemma_f3_sub(pmul(pmul(t, t), t), psc(3, pmul(t, ss)), dsum(dsum(dt, dt), dt), dsc(dsum(dt, dss)));
    let c1 = psub(pmul(pmul(t, t), t), psc(3, pmul(t, ss)));
    let dc1 = dsub(dsum(dsum(dt, dt), dt), dsc(dsum(dt, dss)));
    lemma_f3_sc(3, pmul(t, t), dsum(dt, dt));
    lemma_f3_sub(c1, psc(3, pmul(t, t)), dc1, dsc(dsum(dt, dt)));
    let (c2, dc2) = (psub(c1, psc(3, pmul(t, t))), dsub(dc1, dsc(dsum(dt, dt))));
    lemma_f3_sc(9, ss, dss);
    lemma_f3_sub(c2, psc(9, ss), dc2, dsc(dss));
    lemma_f3_sc(9, t, dt);
    lemma_f3_sub(psub(c2, psc(9, ss)), psc(9, t), dsub(dc2, dsc(dss)), dsc(dt));
    let c0 = psub(psub(c2, psc(9, ss)), psc(9, t));
    let dc0 = dsub(dsub(dc2, dsc(dss)), dsc(dt));
    lemma_f3_mul(b, bc, db, dbc);
    lemma_f3_mul(b, b, db, db);
    lemma_f3_sc(8, pmul(b, b), dsum(db, db));
    lemma_f3_sub(pmul(b, bc), psc(8, pmul(b, b)), dsum(db, dbc), dsc(dsum(db, db)));
    let t1 = psub(pmul(b, bc), psc(8, pmul(b, b)));
    let dt1 = dsub(dsum(db, dbc), dsc(dsum(db, db)));
    lemma_f3_add(t1, c0, dt1, dc0);
    lemma_f3_add(padd(t1, c0), pk(27), dmax(dt1, dc0), dz());
}

proof fn lemma_r1_f3(x1: MP, x2: MP, d1: Seq<nat>, d2: Seq<nat>)
    requires
        f3(x1, d1),
        f3(x2, d2),
    ensures
        f3(r1_mp(x1, x2), r1_ds(d1, d2)),
{
    let (s, ds) = (padd(x1, x2), dmax(d1, d2));
    lemma_f3_add(x1, x2, d1, d2);
    lemma_f3_mul(s, s, ds, ds);
    lemma_f3_mul(x1, x2, d1, d2);
    lemma_f3_sc(2, pmul(x1, x2), dsum(d1, d2));
    lemma_f3_add(pmul(s, s), psc(2, pmul(x1, x2)), dsum(ds, ds), dsc(dsum(d1, d2)));
    lemma_f3_k(6);
    lemma_f3_sub(padd(pmul(s, s), psc(2, pmul(x1, x2))), pk(6), dmax(dsum(ds, ds), dsc(dsum(d1, d2))), dz());
    lemma_f3_sc(
        2,
        psub(padd(pmul(s, s), psc(2, pmul(x1, x2))), pk(6)),
        dsub(dmax(dsum(ds, ds), dsc(dsum(d1, d2))), dz()),
    );
}

proof fn lemma_r0_f3(x1: MP, x2: MP, d1: Seq<nat>, d2: Seq<nat>)
    requires
        f3(x1, d1),
        f3(x2, d2),
    ensures
        f3(r0_mp(x1, x2), r0_ds(d1, d2)),
{
    let (s, ds) = (padd(x1, x2), dmax(d1, d2));
    let c = -4 * B_LIT();
    lemma_f3_add(x1, x2, d1, d2);
    lemma_f3_k(c);
    lemma_f3_mul(x1, x2, d1, d2);
    lemma_f3_mul(pmul(x1, x2), s, dsum(d1, d2), ds);
    lemma_f3_add(pk(c), pmul(pmul(x1, x2), s), dz(), dsum(dsum(d1, d2), ds));
    lemma_f3_sc(3, s, ds);
    lemma_f3_add(padd(pk(c), pmul(pmul(x1, x2), s)), psc(3, s), dmax(dz(), dsum(dsum(d1, d2), ds)), dsc(ds));
    lemma_f3_sc(
        -2,
        padd(padd(pk(c), pmul(pmul(x1, x2), s)), psc(3, s)),
        dmax(dmax(dz(), dsum(dsum(d1, d2), ds)), dsc(ds)),
    );
}

proof fn lemma_q_f3(x1: MP, x2: MP, e: MP, d1: Seq<nat>, d2: Seq<nat>, de: Seq<nat>)
    requires
        f3(x1, d1),
        f3(x2, d2),
        f3(e, de),
    ensures
        f3(q_mp(x1, x2, e), q_ds(d1, d2, de)),
{
    let (s, ds) = (padd(x1, x2), dmax(d1, d2));
    lemma_f3_add(x1, x2, d1, d2);
    lemma_f3_mul(e, e, de, de);
    lemma_f3_sc(2, pmul(e, e), dsum(de, de));
    lemma_f3_mul(s, e, ds, de);
    lemma_f3_add(psc(2, pmul(e, e)), pmul(s, e), dsc(dsum(de, de)), dsum(ds, de));
    lemma_f3_mul(x1, x2, d1, d2);
    lemma_f3_k(3);
    lemma_f3_add(pmul(x1, x2), pk(3), dsum(d1, d2), dz());
    lemma_f3_sub(
        padd(psc(2, pmul(e, e)), pmul(s, e)),
        padd(pmul(x1, x2), pk(3)),
        dmax(dsc(dsum(de, de)), dsum(ds, de)),
        dmax(dsum(d1, d2), dz()),
    );
}

proof fn lemma_res1_f3()
    ensures
        f3(res1_mp(), res1_ds()),
{
    let (x1, x2, d1, d2) = (px(0), px(1), e3(0, 1), e3(1, 1));
    lemma_f3_x(0);
    lemma_f3_x(1);
    let (s, ds) = (padd(x1, x2), dmax(d1, d2));
    lemma_f3_add(x1, x2, d1, d2);
    lemma_r0_f3(x1, x2, d1, d2);
    lemma_r1_f3(x1, x2, d1, d2);
    lemma_w_f3(x1, x2, d1, d2);
    let (a, da) = (r0_mp(x1, x2), r0_ds(d1, d2));
    let (b, db) = (r1_mp(x1, x2), r1_ds(d1, d2));
    lemma_f3_mul(a, a, da, da);
    lemma_f3_sc(2, pmul(a, a), dsum(da, da));
    lemma_f3_mul(s, a, ds, da);
    lemma_f3_mul(pmul(s, a), b, dsum(ds, da), db);
    lemma_f3_sub(psc(2, pmul(a, a)), pmul(pmul(s, a), b), dsc(dsum(da, da)), dsum(dsum(ds, da), db));
    lemma_f3_mul(x1, x2, d1, d2);
    lemma_f3_k(3);
    lemma_f3_add(pmul(x1, x2), pk(3), dsum(d1, d2), dz());
    lemma_f3_mul(b, b, db, db);
    lemma_f3_mul(padd(pmul(x1, x2), pk(3)), pmul(b, b), dmax(dsum(d1, d2), dz()), dsum(db, db));
    let t1 = psub(psc(2, pmul(a, a)), pmul(pmul(s, a), b));
    let dt1 = dsub(dsc(dsum(da, da)), dsum(dsum(ds, da), db));
    let t2 = pmul(padd(pmul(x1, x2), pk(3)), pmul(b, b));
    let dt2 = dsum(dmax(dsum(d1, d2), dz()), dsum(db, db));
    lemma_f3_sub(t1, t2, dt1, dt2);
    lemma_f3_sc(16, w_mp(x1, x2), w_ds(d1, d2));
    lemma_f3_add(psub(t1, t2), psc(16, w_mp(x1, x2)), dsub(dt1, dt2), dsc(w_ds(d1, d2)));
}

proof fn lemma_res2_f3()
    ensures
        f3(res2_mp(), res2_ds()),
{
    let (x1, x2, e, d1, d2, de) = (px(0), px(1), px(2), e3(0, 1), e3(1, 1), e3(2, 1));
    lemma_f3_x(0);
    lemma_f3_x(1);
    lemma_f3_x(2);
    lemma_f3_sc(4, e, de);
    lemma_f3_add(x1, x2, d1, d2);
    lemma_f3_sc(2, padd(x1, x2), dmax(d1, d2));
    lemma_f3_sub(psc(4, e), psc(2, padd(x1, x2)), dsc(de), dsc(dmax(d1, d2)));
    let (lin, dlin) = (psub(psc(4, e), psc(2, padd(x1, x2))), dsub(dsc(de), dsc(dmax(d1, d2))));
    lemma_fv_f3(e, de);
    lemma_f3_sc(8, fv_mp(e), fv_ds(de));
    lemma_q_f3(x1, x2, e, d1, d2, de);
    lemma_f3_mul(q_mp(x1, x2, e), lin, q_ds(d1, d2, de), dlin);
    lemma_f3_sub(psc(8, fv_mp(e)), pmul(q_mp(x1, x2, e), lin), dsc(fv_ds(de)), dsum(q_ds(d1, d2, de), dlin));
    let t1 = psub(psc(8, fv_mp(e)), pmul(q_mp(x1, x2, e), lin));
    let dt1 = dsub(dsc(fv_ds(de)), dsum(q_ds(d1, d2, de), dlin));
    lemma_r1_f3(x1, x2, d1, d2);
    lemma_f3_mul(r1_mp(x1, x2), e, r1_ds(d1, d2), de);
    lemma_f3_sub(t1, pmul(r1_mp(x1, x2), e), dt1, dsum(r1_ds(d1, d2), de));
    lemma_r0_f3(x1, x2, d1, d2);
    lemma_f3_sub(psub(t1, pmul(r1_mp(x1, x2), e)), r0_mp(x1, x2), dsub(dt1, dsum(r1_ds(d1, d2), de)), r0_ds(d1, d2));
}

proof fn lemma_iota(n: int)
    requires
        1 <= n <= 13,
    ensures
        iota(n).len() == n,
        distinct_mod_p(iota(n)),
        forall|v: int| #[trigger] iota(n).contains(v) ==> 0 <= v < n,
{
    lemma_group_consts();
    assert forall|i: int, j: int|
        #![trigger iota(n)[i], iota(n)[j]]
        0 <= i < iota(n).len() && 0 <= j < iota(n).len() && i != j implies fmod(iota(n)[i]) != fmod(
        iota(n)[j],
    ) by {
        lemma_small_mod(i as nat, P_LIT() as nat);
        lemma_small_mod(j as nat, P_LIT() as nat);
    }
    assert forall|v: int| #[trigger] iota(n).contains(v) implies 0 <= v < n by {
        let i = choose|i: int| 0 <= i < iota(n).len() && iota(n)[i] == v;
    }
}

/// RES1 for all x1, x2 (y-free; `poly::lemma_grid` on {0..5} x {0..5} x {0}).
pub(crate) proof fn lemma_res1(x1: int, x2: int)
    ensures
        fmod(id_res1(x1, x2)) == 0,
{
    hide(id_res1);
    hide(res1_mp);
    hide(res1_ds);
    lemma_group_consts();
    lemma_res1_f3();
    lemma_deg_res1();
    lemma_cells_res1();
    let (a, ds) = (res1_mp(), res1_ds());
    let g = seq![iota(6), iota(6), iota(1)];
    lemma_iota(6);
    lemma_iota(1);
    assert forall|k: int| 0 <= k < g.len() implies #[trigger] g[k].len() > ds[k] && distinct_mod_p(g[k]) by {
        assert(k == 0 || k == 1 || k == 2);
    }
    assert forall|xs: Seq<int>| in_grid(xs, g) implies fmod(#[trigger] ev(a, xs)) == 0 by {
        assert(g[0].contains(xs[0]) && g[1].contains(xs[1]));
        lemma_res1_link(xs);
        lemma_md(id_res1(xs[0], xs[1]));
    }
    lemma_grid(a, ds, g);
    let xs = seq![x1, x2, 0int];
    lemma_res1_link(xs);
    assert(fmod(ev(a, xs)) == 0);
}

/// RES2 for all x1, x2, e (y-free; `poly::lemma_grid` on {0..2} x {0..2} x {0..3}).
pub(crate) proof fn lemma_res2(x1: int, x2: int, e: int)
    ensures
        fmod(id_res2(x1, x2, e)) == 0,
{
    hide(id_res2);
    hide(res2_mp);
    hide(res2_ds);
    lemma_group_consts();
    lemma_res2_f3();
    lemma_deg_res2();
    lemma_cells_res2();
    let (a, ds) = (res2_mp(), res2_ds());
    let g = seq![iota(3), iota(3), iota(4)];
    lemma_iota(3);
    lemma_iota(4);
    assert forall|k: int| 0 <= k < g.len() implies #[trigger] g[k].len() > ds[k] && distinct_mod_p(g[k]) by {
        assert(k == 0 || k == 1 || k == 2);
    }
    assert forall|xs: Seq<int>| in_grid(xs, g) implies fmod(#[trigger] ev(a, xs)) == 0 by {
        assert(g[0].contains(xs[0]) && g[1].contains(xs[1]) && g[2].contains(xs[2]));
        lemma_res2_link(xs);
        lemma_md(id_res2(xs[0], xs[1], xs[2]));
    }
    lemma_grid(a, ds, g);
    let xs = seq![x1, x2, e];
    lemma_res2_link(xs);
    assert(fmod(ev(a, xs)) == 0);
}

// ---------------------------------------------------------------------------------------------
// Structural lemmas
// ---------------------------------------------------------------------------------------------

pub(crate) proof fn lemma_rcb_symm(a: Proj, b: Proj)
    ensures
        rcb(a, b) == rcb(b, a),
{
}

/// x2 == k x (mod p).
pub(crate) open spec fn kc(x2: int, k: int, x: int) -> bool {
    fmod(x2) == fmod(k * x)
}

proof fn lemma_kc_ml(a2: int, k: int, a: int, b: int)
    requires
        kc(a2, k, a),
    ensures
        kc(fm(a2, b), k, fm(a, b)),
{
    lemma_group_consts();
    let p = P_LIT();
    lemma_md(a2 * b);
    lemma_md(k * fm(a, b));
    lemma_mul_mod_noop_left(a2, b, p);
    lemma_mul_mod_noop_left(k * a, b, p);
    lemma_mul_is_associative(k, a, b);
    lemma_mul_mod_noop_right(k, a * b, p);
}

proof fn lemma_kc_mr(a: int, b2: int, k: int, b: int)
    requires
        kc(b2, k, b),
    ensures
        kc(fm(a, b2), k, fm(a, b)),
{
    lemma_kc_ml(b2, k, b, a);
    lemma_mul_is_commutative(a, b2);
    lemma_mul_is_commutative(a, b);
}

proof fn lemma_kc_mm(a2: int, b2: int, k: int, a: int, b: int)
    requires
        kc(a2, k, a),
        kc(b2, k, b),
    ensures
        kc(fm(a2, b2), k * k, fm(a, b)),
{
    lemma_kc_ml(a2, k, a, b2);
    lemma_kc_mr(a, b2, k, b);
    lemma_md(k);
    lemma_cg_mul(k, fm(a, b2), k, k * fm(a, b));
    lemma_mul_is_associative(k, k, fm(a, b));
}

proof fn lemma_kc_add(a2: int, b2: int, k: int, a: int, b: int)
    requires
        kc(a2, k, a),
        kc(b2, k, b),
    ensures
        kc(a2 + b2, k, a + b),
{
    lemma_cg_add(a2, b2, k * a, k * b);
    lemma_mul_is_distributive_add(k, a, b);
}

proof fn lemma_kc_sub(a2: int, b2: int, k: int, a: int, b: int)
    requires
        kc(a2, k, a),
        kc(b2, k, b),
    ensures
        kc(a2 - b2, k, a - b),
{
    lemma_group_consts();
    lemma_sub_mod_noop(a2, b2, p256_p());
    lemma_sub_mod_noop(k * a, k * b, p256_p());
    lemma_mul_is_distributive_sub(k, a, b);
}

proof fn lemma_kc_c(c: int, a2: int, k: int, a: int)
    requires
        kc(a2, k, a),
    ensures
        kc(c * a2, k, c * a),
{
    lemma_md(c);
    lemma_cg_mul(c, a2, c, k * a);
    lemma_mul_is_associative(c, k, a);
    lemma_mul_is_commutative(c, k);
    lemma_mul_is_associative(k, c, a);
}

/// The output step: (e2 mod p) == fmod(kk * (e mod p)) when e2 == kk e (mod p).
proof fn lemma_kc_out(e2: int, kk: int, e: int)
    requires
        kc(e2, kk, e),
    ensures
        e2 % P_LIT() == fmod(kk * (e % P_LIT())),
{
    lemma_group_consts();
    lemma_md(e2);
    lemma_mul_mod_noop_right(kk, e, P_LIT());
}

/// RCB is bihomogeneous of degree 2: scaling the first input by k scales the output by k^2.
pub(crate) proof fn lemma_rcb_scale_l(k: int, a: Proj, b: Proj)
    ensures
        rcb(sc(k, a), b) == sc(k * k, rcb(a, b)),
{
    lemma_group_consts();
    let c = sc(k, a);
    let b3 = 3 * B_LIT();
    lemma_md(k * a.x);
    lemma_md(k * a.y);
    lemma_md(k * a.z);
    assert(kc(c.x, k, a.x) && kc(c.y, k, a.y) && kc(c.z, k, a.z));
    // t0, y12, z12, bz
    lemma_kc_ml(c.x, k, a.x, b.z);
    lemma_kc_mr(b.x, c.z, k, a.z);
    lemma_kc_add(fm(c.x, b.z), fm(b.x, c.z), k, fm(a.x, b.z), fm(b.x, a.z));
    let (t0, t0c) = (fm(a.x, b.z) + fm(b.x, a.z), fm(c.x, b.z) + fm(b.x, c.z));
    lemma_kc_ml(c.y, k, a.y, b.y);
    lemma_kc_ml(c.z, k, a.z, b.z);
    let (y12, y12c) = (fm(a.y, b.y), fm(c.y, b.y));
    let (z12, z12c) = (fm(a.z, b.z), fm(c.z, b.z));
    lemma_kc_mr(b3, z12c, k, z12);
    let (bz, bzc) = (fm(b3, z12), fm(b3, z12c));
    // u, v
    lemma_kc_c(3, t0c, k, t0);
    lemma_kc_add(y12c, 3 * t0c, k, y12, 3 * t0);
    lemma_kc_sub(y12c + 3 * t0c, bzc, k, y12 + 3 * t0, bz);
    let (u, uc) = (y12 + 3 * t0 - bz, y12c + 3 * t0c - bzc);
    lemma_kc_sub(y12c, 3 * t0c, k, y12, 3 * t0);
    lemma_kc_add(y12c - 3 * t0c, bzc, k, y12 - 3 * t0, bz);
    let (v, vc) = (y12 - 3 * t0 + bz, y12c - 3 * t0c + bzc);
    // w
    lemma_kc_ml(c.x, k, a.x, b.x);
    let (xx, xxc) = (fm(a.x, b.x), fm(c.x, b.x));
    lemma_kc_c(-3, xxc, k, xx);
    lemma_kc_mr(b3, t0c, k, t0);
    lemma_kc_add(-3 * xxc, fm(b3, t0c), k, -3 * xx, fm(b3, t0));
    lemma_kc_c(9, z12c, k, z12);
    lemma_kc_sub(-3 * xxc + fm(b3, t0c), 9 * z12c, k, -3 * xx + fm(b3, t0), 9 * z12);
    let (w, wc) = (-3 * xx + fm(b3, t0) - 9 * z12, -3 * xxc + fm(b3, t0c) - 9 * z12c);
    // s, r, q
    lemma_kc_ml(c.x, k, a.x, b.y);
    lemma_kc_mr(b.x, c.y, k, a.y);
    lemma_kc_add(fm(c.x, b.y), fm(b.x, c.y), k, fm(a.x, b.y), fm(b.x, a.y));
    let (s, sc_) = (fm(a.x, b.y) + fm(b.x, a.y), fm(c.x, b.y) + fm(b.x, c.y));
    lemma_kc_ml(c.y, k, a.y, b.z);
    lemma_kc_mr(b.y, c.z, k, a.z);
    lemma_kc_add(fm(c.y, b.z), fm(b.y, c.z), k, fm(a.y, b.z), fm(b.y, a.z));
    let (r, rc) = (fm(a.y, b.z) + fm(b.y, a.z), fm(c.y, b.z) + fm(b.y, c.z));
    lemma_kc_c(3, xxc, k, xx);
    lemma_kc_c(3, z12c, k, z12);
    lemma_kc_sub(3 * xxc, 3 * z12c, k, 3 * xx, 3 * z12);
    let (q, qc) = (3 * xx - 3 * z12, 3 * xxc - 3 * z12c);
    // outputs
    lemma_kc_mm(sc_, uc, k, s, u);
    lemma_kc_mm(rc, wc, k, r, w);
    lemma_kc_sub(fm(sc_, uc), fm(rc, wc), k * k, fm(s, u), fm(r, w));
    lemma_kc_out(fm(sc_, uc) - fm(rc, wc), k * k, fm(s, u) - fm(r, w));
    lemma_kc_mm(vc, uc, k, v, u);
    lemma_kc_mm(qc, wc, k, q, w);
    lemma_kc_add(fm(vc, uc), fm(qc, wc), k * k, fm(v, u), fm(q, w));
    lemma_kc_out(fm(vc, uc) + fm(qc, wc), k * k, fm(v, u) + fm(q, w));
    lemma_kc_mm(rc, vc, k, r, v);
    lemma_kc_mm(sc_, qc, k, s, q);
    lemma_kc_add(fm(rc, vc), fm(sc_, qc), k * k, fm(r, v), fm(s, q));
    lemma_kc_out(fm(rc, vc) + fm(sc_, qc), k * k, fm(r, v) + fm(s, q));
}

pub(crate) proof fn lemma_rcb_scale_r(k: int, a: Proj, b: Proj)
    ensures
        rcb(a, sc(k, b)) == sc(k * k, rcb(a, b)),
{
    lemma_rcb_symm(a, sc(k, b));
    lemma_rcb_scale_l(k, b, a);
    lemma_rcb_symm(b, a);
}

/// fm(fm(a, b), fm(c, d)) == (a b)(c d) mod p.
proof fn lemma_fm4(a: int, b: int, c: int, d: int)
    ensures
        fm(fm(a, b), fm(c, d)) == ((a * b) * (c * d)) % P_LIT(),
{
    lemma_mul_mod_noop_general(a * b, c * d, P_LIT());
}

/// O + B: (0 : yv : 0) + B == yv^2 B.y * B.
pub(crate) proof fn lemma_rcb_inf_l(yv: int, b: Proj)
    ensures
        rcb(Proj { x: 0, y: yv, z: 0 }, b) == sc(yv * yv * b.y, b),
{
    lemma_group_consts();
    let p = P_LIT();
    let k = yv * yv * b.y;
    let y12 = fm(yv, b.y);
    lemma_fm4(b.x, yv, yv, b.y);
    lemma_fm4(yv, b.y, yv, b.y);
    lemma_fm4(yv, b.z, yv, b.y);
    assert((b.x * yv) * (yv * b.y) == (yv * yv * b.y) * b.x) by (nonlinear_arith);
    assert((yv * b.y) * (yv * b.y) == (yv * yv * b.y) * b.y) by (nonlinear_arith);
    assert((yv * b.z) * (yv * b.y) == (yv * yv * b.y) * b.z) by (nonlinear_arith);
    lemma_mod_twice(fm(b.x, yv) * y12, p);
    lemma_mod_twice(y12 * y12, p);
    lemma_mod_twice(fm(yv, b.z) * y12, p);
    let a = Proj { x: 0, y: yv, z: 0 };
    assert(fm(a.x, b.z) == 0 && fm(b.x, a.z) == 0 && fm(a.z, b.z) == 0 && fm(a.x, b.x) == 0);
    assert(fm(a.x, b.y) == 0 && fm(b.y, a.z) == 0 && fm(3 * B_LIT(), 0) == 0);
    assert(fm(fm(yv, b.z), 0) == 0 && fm(fm(b.x, yv), 0) == 0);
    let o = rcb(a, b);
    assert(o.x == fm(fm(b.x, yv), y12) % p);
    assert(o.y == fm(y12, y12) % p);
    assert(o.z == fm(fm(yv, b.z), y12) % p);
}

} // verus!
