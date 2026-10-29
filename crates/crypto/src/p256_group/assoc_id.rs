//! Associativity of the complete addition law as a curve identity: the three 2x2 minors of
//! rcb(rcb(A0, A1), A2) against rcb(A0, rcb(A1, A2)), for affine Ai = (xs[i] : ys[i] : 1), vanish
//! mod p at every curve triple. Proved by grid evaluation (`grid_assoc_{a,b,c,d}`) through
//! `rcb::lemma_id_grid` on the 10 x 13 x 10 grid.
#[allow(unused_imports)]
use super::field::*;
#[allow(unused_imports)]
use super::grid_assoc_a::*;
#[allow(unused_imports)]
use super::grid_assoc_b::*;
#[allow(unused_imports)]
use super::grid_assoc_c::*;
#[allow(unused_imports)]
use super::grid_assoc_d::*;
#[allow(unused_imports)]
use super::grid_small::*;
#[allow(unused_imports)]
use super::rcb::*;
#[allow(unused_imports)]
use super::red::*;
#[allow(unused_imports)]
use crate::p256::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// The plain identity, and its formal and degree mirrors
// ---------------------------------------------------------------------------------------------

/// (rcb(rcb(A0, A1), A2), rcb(A0, rcb(A1, A2))).
pub(crate) open spec fn assoc_lr(xs: Seq<int>, ys: Seq<int>) -> (Proj, Proj) {
    let (a0, a1, a2) = (pt(xs, ys, 0), pt(xs, ys, 1), pt(xs, ys, 2));
    (rcb(rcb(a0, a1), a2), rcb(a0, rcb(a1, a2)))
}

/// The m-th 2x2 minor of (l, r): (x, y), (x, z), (y, z).
pub(crate) open spec fn minor(m: nat, l: Proj, r: Proj) -> int {
    if m == 0 {
        fm(l.x, r.y) - fm(r.x, l.y)
    } else if m == 1 {
        fm(l.x, r.z) - fm(r.x, l.z)
    } else {
        fm(l.y, r.z) - fm(r.y, l.z)
    }
}

pub(crate) open spec fn assoc_minor(m: nat, xs: Seq<int>, ys: Seq<int>) -> int {
    minor(m, assoc_lr(xs, ys).0, assoc_lr(xs, ys).1)
}

/// All three minors vanish mod p (one evaluation of the four RCB calls).
pub(crate) open spec fn minors0(lr: (Proj, Proj)) -> bool {
    &&& minor(0, lr.0, lr.1) % P_LIT() == 0
    &&& minor(1, lr.0, lr.1) % P_LIT() == 0
    &&& minor(2, lr.0, lr.1) % P_LIT() == 0
}

pub(crate) open spec fn minor_f(m: nat, l: PF, r: PF) -> RF {
    if m == 0 {
        rf_sub(rf_mul(l.x, r.y), rf_mul(r.x, l.y))
    } else if m == 1 {
        rf_sub(rf_mul(l.x, r.z), rf_mul(r.x, l.z))
    } else {
        rf_sub(rf_mul(l.y, r.z), rf_mul(r.y, l.z))
    }
}

pub(crate) open spec fn minor_d(m: nat, l: PD, r: PD) -> RD {
    if m == 0 {
        rd_sub(rd_mul(l.x, r.y), rd_mul(r.x, l.y))
    } else if m == 1 {
        rd_sub(rd_mul(l.x, r.z), rd_mul(r.x, l.z))
    } else {
        rd_sub(rd_mul(l.y, r.z), rd_mul(r.y, l.z))
    }
}

pub(crate) open spec fn assoc_l_f() -> PF {
    rcb_f(rcb_f(pt_f(0), pt_f(1)), pt_f(2))
}

pub(crate) open spec fn assoc_r_f() -> PF {
    rcb_f(pt_f(0), rcb_f(pt_f(1), pt_f(2)))
}

pub(crate) open spec fn assoc_f(m: nat) -> RF {
    minor_f(m, assoc_l_f(), assoc_r_f())
}

pub(crate) open spec fn assoc_l_d() -> PD {
    rcb_d(rcb_d(pt_d(0), pt_d(1)), pt_d(2))
}

pub(crate) open spec fn assoc_r_d() -> PD {
    rcb_d(pt_d(0), rcb_d(pt_d(1), pt_d(2)))
}

pub(crate) open spec fn assoc_d(m: nat) -> RD {
    minor_d(m, assoc_l_d(), assoc_r_d())
}

// ---------------------------------------------------------------------------------------------
// Grid cells (evaluated by the generated chunks)
// ---------------------------------------------------------------------------------------------

/// All three minors vanish mod p at grid point (gx(i), gx(j), gx(l)) under all 8 y-sign choices.
#[verifier::opaque]
pub(crate) open spec fn assoc_cell(i: int, j: int, l: int) -> bool {
    let xs = seq![gx(i), gx(j), gx(l)];
    let ys = seq![gy(i), gy(j), gy(l)];
    &&& minors0(assoc_lr(xs, sgn(0, ys)))
    &&& minors0(assoc_lr(xs, sgn(1, ys)))
    &&& minors0(assoc_lr(xs, sgn(2, ys)))
    &&& minors0(assoc_lr(xs, sgn(3, ys)))
    &&& minors0(assoc_lr(xs, sgn(4, ys)))
    &&& minors0(assoc_lr(xs, sgn(5, ys)))
    &&& minors0(assoc_lr(xs, sgn(6, ys)))
    &&& minors0(assoc_lr(xs, sgn(7, ys)))
}

pub(crate) open spec fn c_assoc() -> spec_fn(int, int, int) -> bool {
    |i: int, j: int, l: int| assoc_cell(i, j, l)
}

pub(crate) open spec fn fn_assoc(m: nat) -> spec_fn(Seq<int>, Seq<int>) -> int {
    |xs: Seq<int>, ys: Seq<int>| assoc_minor(m, xs, ys)
}

// ---------------------------------------------------------------------------------------------
// Degrees (literal per-level tables, checked in grid_assoc_a), fits and link
// ---------------------------------------------------------------------------------------------

pub(crate) proof fn lemma_assoc_degrees()
    ensures
        deg_ok(assoc_d(0), seq![10int, 13, 10]),
        deg_ok(assoc_d(1), seq![10int, 13, 10]),
        deg_ok(assoc_d(2), seq![10int, 13, 10]),
{
    hide(rcb_d);
    hide(minor_d);
    hide(deg_ok);
    hide(pdl_assoc_01);
    hide(pdl_assoc_12);
    hide(pdl_assoc_l);
    hide(pdl_assoc_r);
    lemma_assoc_deg_01();
    lemma_assoc_deg_12();
    lemma_assoc_deg_l();
    lemma_assoc_deg_r();
    lemma_assoc_deg_m0();
    lemma_assoc_deg_m1();
    lemma_assoc_deg_m2();
    assert(assoc_l_d() == pdl_assoc_l());
    assert(assoc_r_d() == pdl_assoc_r());
}

proof fn lemma_fits_lr()
    ensures
        pfits(assoc_l_f(), assoc_l_d()),
        pfits(assoc_r_f(), assoc_r_d()),
{
    lemma_pt_fits(0);
    lemma_pt_fits(1);
    lemma_pt_fits(2);
    lemma_rcb_fits(pt_f(0), pt_f(1), pt_d(0), pt_d(1));
    lemma_rcb_fits(pt_f(1), pt_f(2), pt_d(1), pt_d(2));
    lemma_rcb_fits(rcb_f(pt_f(0), pt_f(1)), pt_f(2), rcb_d(pt_d(0), pt_d(1)), pt_d(2));
    lemma_rcb_fits(pt_f(0), rcb_f(pt_f(1), pt_f(2)), pt_d(0), rcb_d(pt_d(1), pt_d(2)));
}

proof fn lemma_assoc_fits(m: nat)
    ensures
        rfits(assoc_f(m), assoc_d(m)),
{
    hide(rcb_f);
    hide(rcb_d);
    lemma_fits_lr();
    let (l, r, dl, dr) = (assoc_l_f(), assoc_r_f(), assoc_l_d(), assoc_r_d());
    if m == 0 {
        lemma_rfits_mul(l.x, r.y, dl.x, dr.y);
        lemma_rfits_mul(r.x, l.y, dr.x, dl.y);
        lemma_rfits_sub(rf_mul(l.x, r.y), rf_mul(r.x, l.y), rd_mul(dl.x, dr.y), rd_mul(dr.x, dl.y));
    } else if m == 1 {
        lemma_rfits_mul(l.x, r.z, dl.x, dr.z);
        lemma_rfits_mul(r.x, l.z, dr.x, dl.z);
        lemma_rfits_sub(rf_mul(l.x, r.z), rf_mul(r.x, l.z), rd_mul(dl.x, dr.z), rd_mul(dr.x, dl.z));
    } else {
        lemma_rfits_mul(l.y, r.z, dl.y, dr.z);
        lemma_rfits_mul(r.y, l.z, dr.y, dl.z);
        lemma_rfits_sub(rf_mul(l.y, r.z), rf_mul(r.y, l.z), rd_mul(dl.y, dr.z), rd_mul(dr.y, dl.z));
    }
}

proof fn lemma_link_lr(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        lkp(assoc_l_f(), assoc_lr(xs, ys).0, xs, ys),
        lkp(assoc_r_f(), assoc_lr(xs, ys).1, xs, ys),
{
    let (a0, a1, a2) = (pt(xs, ys, 0), pt(xs, ys, 1), pt(xs, ys, 2));
    lemma_pt_link(0, xs, ys);
    lemma_pt_link(1, xs, ys);
    lemma_pt_link(2, xs, ys);
    lemma_rcb_link(a0, a1, pt_f(0), pt_f(1), xs, ys);
    lemma_rcb_link(a1, a2, pt_f(1), pt_f(2), xs, ys);
    lemma_rcb_link(rcb(a0, a1), a2, rcb_f(pt_f(0), pt_f(1)), pt_f(2), xs, ys);
    lemma_rcb_link(a0, rcb(a1, a2), pt_f(0), rcb_f(pt_f(1), pt_f(2)), xs, ys);
}

proof fn lemma_assoc_link(m: nat, xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        lk(assoc_f(m), assoc_minor(m, xs, ys), xs, ys),
{
    hide(rcb);
    hide(rcb_f);
    lemma_link_lr(xs, ys);
    let (l, r, fl, fr) = (assoc_lr(xs, ys).0, assoc_lr(xs, ys).1, assoc_l_f(), assoc_r_f());
    if m == 0 {
        lemma_lk_m(fl.x, fr.y, l.x, r.y, xs, ys);
        lemma_lk_m(fr.x, fl.y, r.x, l.y, xs, ys);
        lemma_lk_s(rf_mul(fl.x, fr.y), rf_mul(fr.x, fl.y), fm(l.x, r.y), fm(r.x, l.y), xs, ys);
    } else if m == 1 {
        lemma_lk_m(fl.x, fr.z, l.x, r.z, xs, ys);
        lemma_lk_m(fr.x, fl.z, r.x, l.z, xs, ys);
        lemma_lk_s(rf_mul(fl.x, fr.z), rf_mul(fr.x, fl.z), fm(l.x, r.z), fm(r.x, l.z), xs, ys);
    } else {
        lemma_lk_m(fl.y, fr.z, l.y, r.z, xs, ys);
        lemma_lk_m(fr.y, fl.z, r.y, l.z, xs, ys);
        lemma_lk_s(rf_mul(fl.y, fr.z), rf_mul(fr.y, fl.z), fm(l.y, r.z), fm(r.y, l.z), xs, ys);
    }
}

// ---------------------------------------------------------------------------------------------
// Grid glue and the export
// ---------------------------------------------------------------------------------------------

proof fn lemma_assoc_cells()
    ensures
        forall|i: int, j: int, l: int|
            0 <= i < 10 && 0 <= j < 13 && 0 <= l < 10 ==> #[trigger] assoc_cell(i, j, l),
{
    lemma_assoc_cells_a();
    lemma_assoc_cells_b();
    lemma_assoc_cells_c();
    lemma_assoc_cells_d();
    assert forall|i: int, j: int, l: int| 0 <= i < 10 && 0 <= j < 13 && 0 <= l < 10 implies #[trigger] assoc_cell(
        i,
        j,
        l,
    ) by {
        if i < 3 {
        } else if i < 6 {
        } else if i < 8 {
        } else {
        }
    }
}

proof fn lemma_assoc_sg(m: nat)
    requires
        m < 3,
    ensures
        forall|i: int, j: int, l: int|
            0 <= i < 10 && 0 <= j < 13 && 0 <= l < 10 ==> #[trigger] sg_cell(fn_assoc(m), i, j, l),
{
    hide(assoc_lr);
    hide(minor);
    lemma_assoc_cells();
    assert forall|i: int, j: int, l: int| 0 <= i < 10 && 0 <= j < 13 && 0 <= l < 10 implies #[trigger] sg_cell(
        fn_assoc(m),
        i,
        j,
        l,
    ) by {
        assert(assoc_cell(i, j, l));
        reveal(assoc_cell);
        reveal(sg_cell);
        assert(m == 0 || m == 1 || m == 2);
    }
}

proof fn lemma_assoc_minor(m: nat)
    requires
        m < 3,
    ensures
        forall|xs: Seq<int>, ys: Seq<int>| #[trigger] on3(xs, ys) ==> fmod(assoc_minor(m, xs, ys)) == 0,
{
    lemma_assoc_degrees();
    lemma_assoc_fits(m);
    lemma_assoc_sg(m);
    assert forall|us: Seq<int>, vs: Seq<int>| on3(us, vs) implies #[trigger] lk(assoc_f(m), fn_assoc(m)(us, vs), us, vs) by {
        lemma_assoc_link(m, us, vs);
    }
    assert(deg_ok(assoc_d(m), seq![10int, 13, 10]));
    lemma_id_grid(fn_assoc(m), assoc_f(m), assoc_d(m), 10, 13, 10);
    assert forall|xs: Seq<int>, ys: Seq<int>| #[trigger] on3(xs, ys) implies fmod(assoc_minor(m, xs, ys)) == 0 by {
        assert(fmod(fn_assoc(m)(xs, ys)) == 0);
    }
}

/// RCB associativity up to projective scaling: the three 2x2 minors of rcb(rcb(A0, A1), A2)
/// against rcb(A0, rcb(A1, A2)) vanish mod p at every curve triple.
pub(crate) proof fn lemma_rcb_assoc_minors(xs: Seq<int>, ys: Seq<int>)
    requires
        on3(xs, ys),
    ensures
        fmod(assoc_minor(0, xs, ys)) == 0,
        fmod(assoc_minor(1, xs, ys)) == 0,
        fmod(assoc_minor(2, xs, ys)) == 0,
{
    lemma_assoc_minor(0);
    lemma_assoc_minor(1);
    lemma_assoc_minor(2);
}

} // verus!
