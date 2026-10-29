//! Formal multivariate polynomials over the integers (read mod p) and the grid vanishing theorem:
//! a polynomial whose degree in each variable is below that variable's grid size, and which
//! vanishes mod p on the grid, vanishes mod p everywhere (Alon 1999, Combinatorial
//! Nullstellensatz, Lemma 2.1). Univariate step: a nonzero polynomial over a field has at most
//! deg roots (synthetic division by x - r plus "GF(p) has no zero divisors").
#[allow(unused_imports)]
use super::field::*;
#[allow(unused_imports)]
use crate::p256::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Formal polynomials
// ---------------------------------------------------------------------------------------------

/// A constant, or the coefficients (constant term first) in the leading variable, each a
/// polynomial in the remaining variables.
pub(crate) enum MP {
    K(int),
    L(Seq<MP>),
}

/// c0 + x (c1 + x (c2 + ...)).
pub(crate) open spec fn horner(cs: Seq<int>, x: int) -> int
    decreases cs.len(),
{
    if cs.len() == 0 {
        0
    } else {
        cs[0] + x * horner(cs.drop_first(), x)
    }
}

/// Horner from coefficient i: for a = L(cs), cs[i] + x0 (cs[i+1] + x0 (...)), each cs[j] evaluated
/// at xs.drop_first(). (Index recursion, not a closure, so that callers can unfold it.)
pub(crate) open spec fn eva(a: MP, i: nat, xs: Seq<int>) -> int
    decreases a, pm_m(a, i),
{
    match a {
        MP::K(c) => c,
        MP::L(cs) => if i < cs.len() {
            eva(cs[i as int], 0, xs.drop_first()) + xs[0] * eva(a, i + 1, xs)
        } else {
            0
        },
    }
}

/// Evaluation: Horner in xs[0] over ev(cs[j], xs.drop_first()).
pub(crate) open spec fn ev(a: MP, xs: Seq<int>) -> int {
    eva(a, 0, xs)
}

/// Degree in variable k at most ds[k], and at most ds.len() variables.
pub(crate) open spec fn fits(a: MP, ds: Seq<nat>) -> bool
    decreases a,
{
    match a {
        MP::K(_) => true,
        MP::L(cs) => ds.len() > 0 && cs.len() <= ds[0] + 1 && forall|j: int|
            0 <= j < cs.len() ==> fits(#[trigger] cs[j], ds.drop_first()),
    }
}

/// Coefficients in the leading variable (a constant is its own constant term).
pub(crate) open spec fn coeffs(a: MP) -> Seq<MP> {
    match a {
        MP::K(c) => seq![MP::K(c)],
        MP::L(cs) => cs,
    }
}

pub(crate) open spec fn padd(a: MP, b: MP) -> MP
    decreases a, b,
{
    match (a, b) {
        (MP::K(c), MP::K(d)) => MP::K(c + d),
        _ => {
            let ca = coeffs(a);
            let cb = coeffs(b);
            MP::L(
                Seq::new(
                    if ca.len() >= cb.len() {
                        ca.len()
                    } else {
                        cb.len()
                    },
                    |j: int|
                        if 0 <= j < ca.len() && j < cb.len() {
                            padd(ca[j], cb[j])
                        } else if 0 <= j < ca.len() {
                            ca[j]
                        } else if 0 <= j < cb.len() {
                            cb[j]
                        } else {
                            MP::K(0)
                        },
                ),
            )
        },
    }
}

/// x0 * a.
pub(crate) open spec fn shift(a: MP) -> MP {
    MP::L(seq![MP::K(0)] + coeffs(a))
}

pub(crate) open spec fn pm_m(a: MP, i: nat) -> int {
    match a {
        MP::K(_) => 0,
        MP::L(cs) => if i < cs.len() {
            cs.len() - i
        } else {
            0
        },
    }
}

/// co: a is a coefficient (a polynomial in x1, x2, ...), and the result is a·b.
/// Otherwise, for a = L(cs): (cs[i] + x0 cs[i+1] + ...)·b, as cs[i]·b + x0·((cs[i+1] + ...)·b);
/// for a = K(c): c·b.
pub(crate) open spec fn pm(a: MP, i: nat, b: MP, co: bool) -> MP
    decreases a, pm_c(a, i, co), b,
{
    if co {
        let cb = coeffs(b);
        MP::L(
            Seq::new(
                cb.len(),
                |j: int|
                    if 0 <= j < cb.len() {
                        pm(a, 0, cb[j], false)
                    } else {
                        MP::K(0)
                    },
            ),
        )
    } else {
        match a {
            MP::K(c) => match b {
                MP::K(d) => MP::K(c * d),
                MP::L(bs) => MP::L(
                    Seq::new(
                        bs.len(),
                        |j: int|
                            if 0 <= j < bs.len() {
                                pm(a, 0, bs[j], false)
                            } else {
                                MP::K(0)
                            },
                    ),
                ),
            },
            MP::L(cs) => if i < cs.len() {
                let p0 = pm(cs[i as int], 0, b, true);
                if i + 1 < cs.len() {
                    padd(p0, shift(pm(a, i + 1, b, false)))
                } else {
                    p0
                }
            } else {
                MP::K(0)
            },
        }
    }
}

pub(crate) open spec fn pm_c(a: MP, i: nat, co: bool) -> int {
    if co {
        pm_m(a, 0) + 1
    } else {
        pm_m(a, i)
    }
}

pub(crate) open spec fn pmul(a: MP, b: MP) -> MP {
    pm(a, 0, b, false)
}

pub(crate) open spec fn pk(c: int) -> MP {
    MP::K(c)
}

/// The variable x_i.
pub(crate) open spec fn px(i: nat) -> MP
    decreases i,
{
    if i == 0 {
        MP::L(seq![MP::K(0), MP::K(1)])
    } else {
        MP::L(seq![px((i - 1) as nat)])
    }
}

// Degree bookkeeping.
pub(crate) open spec fn dmax(da: Seq<nat>, db: Seq<nat>) -> Seq<nat> {
    Seq::new(
        da.len(),
        |k: int|
            if da[k] >= db[k] {
                da[k]
            } else {
                db[k]
            },
    )
}

pub(crate) open spec fn dsum(da: Seq<nat>, db: Seq<nat>) -> Seq<nat> {
    Seq::new(da.len(), |k: int| (da[k] + db[k]) as nat)
}

// Grids.
pub(crate) open spec fn distinct_mod_p(s: Seq<int>) -> bool {
    forall|i: int, j: int|
        #![trigger s[i], s[j]]
        0 <= i < s.len() && 0 <= j < s.len() && i != j ==> fmod(s[i]) != fmod(s[j])
}

pub(crate) open spec fn in_grid(xs: Seq<int>, g: Seq<Seq<int>>) -> bool {
    xs.len() == g.len() && forall|k: int| 0 <= k < g.len() ==> #[trigger] g[k].contains(xs[k])
}

// ---------------------------------------------------------------------------------------------
// Horner over int sequences
// ---------------------------------------------------------------------------------------------

pub(crate) open spec fn gz(u: Seq<int>, j: int) -> int {
    if 0 <= j < u.len() {
        u[j]
    } else {
        0
    }
}

pub(crate) open spec fn tl(u: Seq<int>) -> Seq<int> {
    if u.len() > 0 {
        u.drop_first()
    } else {
        u
    }
}

pub(crate) open spec fn vadd(u: Seq<int>, v: Seq<int>) -> Seq<int> {
    Seq::new(
        if u.len() >= v.len() {
            u.len()
        } else {
            v.len()
        },
        |j: int| gz(u, j) + gz(v, j),
    )
}

pub(crate) open spec fn vscale(c: int, u: Seq<int>) -> Seq<int> {
    Seq::new(u.len(), |j: int| c * u[j])
}

proof fn lemma_horner_tl(u: Seq<int>, x: int)
    ensures
        horner(u, x) == gz(u, 0) + x * horner(tl(u), x),
{
    if u.len() == 0 {
        lemma_mul_basics(x);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_horner_add(u: Seq<int>, v: Seq<int>, x: int)
    ensures
        horner(vadd(u, v), x) == horner(u, x) + horner(v, x),
    decreases u.len() + v.len(),
{
    let s = vadd(u, v);
    if u.len() > 0 || v.len() > 0 {
        assert(s.drop_first() =~= vadd(tl(u), tl(v)));
        lemma_horner_add(tl(u), tl(v), x);
        lemma_horner_tl(u, x);
        lemma_horner_tl(v, x);
        lemma_mul_is_distributive_add(x, horner(tl(u), x), horner(tl(v), x));
    }
}

#[verifier::spinoff_prover]
proof fn lemma_horner_scale(c: int, u: Seq<int>, x: int)
    ensures
        horner(vscale(c, u), x) == c * horner(u, x),
    decreases u.len(),
{
    if u.len() == 0 {
        lemma_mul_basics(c);
    } else {
        let h = horner(u.drop_first(), x);
        assert(vscale(c, u).drop_first() =~= vscale(c, u.drop_first()));
        lemma_horner_scale(c, u.drop_first(), x);
        lemma_mul_is_distributive_add(c, u[0], x * h);
        lemma_mul_is_associative(c, x, h);
        lemma_mul_is_associative(x, c, h);
        lemma_mul_is_commutative(c, x);
    }
}

proof fn lemma_horner_shift(u: Seq<int>, x: int)
    ensures
        horner(seq![0int] + u, x) == x * horner(u, x),
{
    assert((seq![0int] + u).drop_first() =~= u);
}

/// All coefficients 0 mod p ⇒ the value is 0 mod p.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_horner_zero(u: Seq<int>, x: int)
    requires
        forall|j: int| 0 <= j < u.len() ==> fmod(#[trigger] u[j]) == 0,
    ensures
        fmod(horner(u, x)) == 0,
    decreases u.len(),
{
    lemma_group_consts();
    let p = p256_p();
    if u.len() > 0 {
        let h = horner(u.drop_first(), x);
        lemma_horner_zero(u.drop_first(), x);
        lemma_add_mod_noop(u[0], x * h, p);
        lemma_mul_mod_noop_right(x, h, p);
        lemma_mul_basics(x);
    }
}

// ---------------------------------------------------------------------------------------------
// Evaluation lemmas (exact over int)
// ---------------------------------------------------------------------------------------------

pub(crate) open spec fn evs(cs: Seq<MP>, ys: Seq<int>) -> Seq<int> {
    Seq::new(cs.len(), |j: int| ev(cs[j], ys))
}

#[verifier::spinoff_prover]
proof fn lemma_eva_shift(cs: Seq<MP>, i: nat, xs: Seq<int>)
    requires
        cs.len() > 0,
    ensures
        eva(MP::L(cs), i + 1, xs) == eva(MP::L(cs.drop_first()), i, xs),
    decreases cs.len() - i,
{
    if i + 1 < cs.len() {
        lemma_eva_shift(cs, i + 1, xs);
        assert(cs.drop_first()[i as int] == cs[i + 1 as int]);
    }
}

pub(crate) proof fn lemma_ev_cons(cs: Seq<MP>, xs: Seq<int>)
    requires
        cs.len() > 0,
    ensures
        ev(MP::L(cs), xs) == ev(cs[0], xs.drop_first()) + xs[0] * ev(MP::L(cs.drop_first()), xs),
{
    lemma_eva_shift(cs, 0, xs);
}

pub(crate) proof fn lemma_ev_nil(xs: Seq<int>)
    ensures
        ev(MP::L(Seq::<MP>::empty()), xs) == 0,
{
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_ev_evs(cs: Seq<MP>, xs: Seq<int>)
    ensures
        ev(MP::L(cs), xs) == horner(evs(cs, xs.drop_first()), xs[0]),
    decreases cs.len(),
{
    if cs.len() > 0 {
        let t = xs.drop_first();
        lemma_ev_cons(cs, xs);
        lemma_ev_evs(cs.drop_first(), xs);
        assert(evs(cs, t).drop_first() =~= evs(cs.drop_first(), t));
    }
}

pub(crate) proof fn lemma_ev_coeffs(a: MP, xs: Seq<int>)
    ensures
        ev(a, xs) == ev(MP::L(coeffs(a)), xs),
{
    if let MP::K(c) = a {
        lemma_ev_cons(coeffs(a), xs);
        assert(coeffs(a).drop_first() =~= Seq::<MP>::empty());
        lemma_ev_nil(xs);
        lemma_mul_basics(xs[0]);
    }
}

pub(crate) proof fn lemma_ev_k(c: int, xs: Seq<int>)
    ensures
        ev(pk(c), xs) == c,
{
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_ev_x(i: nat, xs: Seq<int>)
    requires
        i < xs.len(),
    ensures
        ev(px(i), xs) == xs[i as int],
    decreases i,
{
    let cs = coeffs(px(i));
    lemma_ev_cons(cs, xs);
    lemma_ev_nil(xs);
    lemma_mul_basics(xs[0]);
    if i == 0 {
        assert(cs.drop_first() =~= seq![MP::K(1)]);
        lemma_ev_cons(cs.drop_first(), xs);
        assert(cs.drop_first().drop_first() =~= Seq::<MP>::empty());
    } else {
        assert(cs.drop_first() =~= Seq::<MP>::empty());
        lemma_ev_x((i - 1) as nat, xs.drop_first());
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_ev_add(a: MP, b: MP, xs: Seq<int>)
    ensures
        ev(padd(a, b), xs) == ev(a, xs) + ev(b, xs),
    decreases a, b,
{
    if let MP::L(s) = padd(a, b) {
        let ca = coeffs(a);
        let cb = coeffs(b);
        let t = xs.drop_first();
        lemma_ev_coeffs(a, xs);
        lemma_ev_coeffs(b, xs);
        lemma_ev_evs(ca, xs);
        lemma_ev_evs(cb, xs);
        lemma_ev_evs(s, xs);
        assert forall|j: int| 0 <= j < s.len() implies #[trigger] evs(s, t)[j] == vadd(
            evs(ca, t),
            evs(cb, t),
        )[j] by {
            if j < ca.len() && j < cb.len() {
                lemma_ev_add(ca[j], cb[j], t);
            }
        }
        assert(evs(s, t) =~= vadd(evs(ca, t), evs(cb, t)));
        lemma_horner_add(evs(ca, t), evs(cb, t), xs[0]);
    }
}

pub(crate) proof fn lemma_ev_shift(a: MP, xs: Seq<int>)
    ensures
        ev(shift(a), xs) == xs[0] * ev(a, xs),
{
    let t = xs.drop_first();
    let ca = coeffs(a);
    lemma_ev_coeffs(a, xs);
    lemma_ev_evs(ca, xs);
    lemma_ev_evs(seq![MP::K(0)] + ca, xs);
    assert(evs(seq![MP::K(0)] + ca, t) =~= seq![0int] + evs(ca, t));
    lemma_horner_shift(evs(ca, t), xs[0]);
}

/// The suffix polynomial cs[i] + x0 cs[i+1] + ... that pm(a, i, b) multiplies by b.
pub(crate) open spec fn suffix(a: MP, i: nat) -> MP {
    match a {
        MP::K(_) => a,
        MP::L(cs) => MP::L(cs.subrange(i as int, cs.len() as int)),
    }
}

#[verifier::spinoff_prover]
proof fn lemma_ev_pm(a: MP, i: nat, b: MP, co: bool, xs: Seq<int>)
    requires
        !co && a is L ==> i <= a->L_0.len(),
    ensures
        co ==> ev(pm(a, i, b, co), xs) == ev(a, xs.drop_first()) * ev(b, xs),
        !co ==> ev(pm(a, i, b, co), xs) == ev(suffix(a, i), xs) * ev(b, xs),
    decreases a, pm_c(a, i, co), b,
{
    let t = xs.drop_first();
    if co {
        let cb = coeffs(b);
        if let MP::L(s) = pm(a, i, b, co) {
            lemma_ev_evs(s, xs);
            lemma_ev_evs(cb, xs);
            lemma_ev_coeffs(b, xs);
            assert forall|j: int| 0 <= j < s.len() implies #[trigger] evs(s, t)[j] == vscale(
                ev(a, t),
                evs(cb, t),
            )[j] by {
                lemma_ev_pm(a, 0, cb[j], false, t);
                lemma_suffix0(a);
            }
            assert(evs(s, t) =~= vscale(ev(a, t), evs(cb, t)));
            lemma_horner_scale(ev(a, t), evs(cb, t), xs[0]);
        }
    } else {
        match a {
            MP::K(c) => {
                if let MP::L(bs) = b {
                    if let MP::L(s) = pm(a, i, b, co) {
                        lemma_ev_evs(s, xs);
                        lemma_ev_evs(bs, xs);
                        assert forall|j: int| 0 <= j < s.len() implies #[trigger] evs(s, t)[j]
                            == vscale(c, evs(bs, t))[j] by {
                            lemma_ev_pm(a, 0, bs[j], false, t);
                        }
                        assert(evs(s, t) =~= vscale(c, evs(bs, t)));
                        lemma_horner_scale(c, evs(bs, t), xs[0]);
                    }
                }
            },
            MP::L(cs) => {
                if i < cs.len() {
                    let ai = cs[i as int];
                    let p0 = pm(ai, 0, b, true);
                    lemma_ev_pm(ai, 0, b, true, xs);
                    // ev(suffix(a, i)) == ev(ai) + x0 * ev(suffix(a, i + 1))
                    let sf = cs.subrange(i as int, cs.len() as int);
                    lemma_ev_cons(sf, xs);
                    assert(sf.drop_first() =~= cs.subrange(i + 1 as int, cs.len() as int));
                    let x0 = xs[0];
                    let A = ev(ai, t);
                    let E = ev(suffix(a, (i + 1) as nat), xs);
                    let B = ev(b, xs);
                    if i + 1 < cs.len() {
                        let q = pm(a, (i + 1) as nat, b, false);
                        lemma_ev_pm(a, (i + 1) as nat, b, false, xs);
                        lemma_ev_shift(q, xs);
                        lemma_ev_add(p0, shift(q), xs);
                        lemma_mul_is_distributive_add_other_way(B, A, x0 * E);
                        lemma_mul_is_associative(x0, E, B);
                    } else {
                        assert(cs.subrange(i + 1 as int, cs.len() as int) =~= Seq::<MP>::empty());
                        lemma_ev_nil(xs);
                        lemma_mul_basics(x0);
                    }
                } else {
                    assert(cs.subrange(i as int, cs.len() as int) =~= Seq::<MP>::empty());
                    lemma_ev_nil(xs);
                    lemma_mul_basics(ev(b, xs));
                }
            },
        }
    }
}

proof fn lemma_suffix0(a: MP)
    ensures
        suffix(a, 0) == a,
{
    if let MP::L(cs) = a {
        assert(cs.subrange(0, cs.len() as int) =~= cs);
    }
}

pub(crate) proof fn lemma_ev_mul(a: MP, b: MP, xs: Seq<int>)
    ensures
        ev(pmul(a, b), xs) == ev(a, xs) * ev(b, xs),
{
    lemma_ev_pm(a, 0, b, false, xs);
    lemma_suffix0(a);
}

// ---------------------------------------------------------------------------------------------
// Degree lemmas
// ---------------------------------------------------------------------------------------------

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fits_mono(a: MP, d: Seq<nat>, e: Seq<nat>)
    requires
        fits(a, d),
        d.len() == e.len(),
        forall|k: int| 0 <= k < d.len() ==> d[k] <= e[k],
    ensures
        fits(a, e),
    decreases a,
{
    if let MP::L(cs) = a {
        assert forall|j: int| 0 <= j < cs.len() implies fits(#[trigger] cs[j], e.drop_first()) by {
            lemma_fits_mono(cs[j], d.drop_first(), e.drop_first());
        }
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fits_add(a: MP, b: MP, da: Seq<nat>, db: Seq<nat>)
    requires
        fits(a, da),
        fits(b, db),
        da.len() == db.len(),
    ensures
        fits(padd(a, b), dmax(da, db)),
    decreases a, b,
{
    if let MP::L(s) = padd(a, b) {
        let ca = coeffs(a);
        let cb = coeffs(b);
        let dm = dmax(da, db);
        assert(da.len() > 0);
        assert(dm.drop_first() =~= dmax(da.drop_first(), db.drop_first()));
        assert forall|j: int| 0 <= j < s.len() implies fits(#[trigger] s[j], dm.drop_first()) by {
            if j < ca.len() && j < cb.len() {
                lemma_fits_add(ca[j], cb[j], da.drop_first(), db.drop_first());
            } else if j < ca.len() {
                lemma_fits_mono(ca[j], da.drop_first(), dm.drop_first());
            } else {
                lemma_fits_mono(cb[j], db.drop_first(), dm.drop_first());
            }
        }
    }
}

proof fn lemma_fits_shift(a: MP, ds: Seq<nat>)
    requires
        ds.len() > 0,
        ds[0] >= 1,
        fits(a, ds.update(0, (ds[0] - 1) as nat)),
    ensures
        fits(shift(a), ds),
{
    let s = seq![MP::K(0)] + coeffs(a);
    assert(ds.update(0, (ds[0] - 1) as nat).drop_first() =~= ds.drop_first());
    assert forall|j: int| 0 <= j < s.len() implies fits(#[trigger] s[j], ds.drop_first()) by {
        if j > 0 {
            assert(s[j] == coeffs(a)[j - 1]);
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_fits_pm(a: MP, i: nat, b: MP, co: bool, da: Seq<nat>, db: Seq<nat>)
    requires
        co ==> da.len() > 0 && fits(a, da.drop_first()),
        !co ==> fits(a, da),
        fits(b, db),
        da.len() == db.len(),
    ensures
        co ==> fits(pm(a, i, b, co), dsum(da, db).update(0, db[0])),
        !co && i == 0 ==> fits(pm(a, i, b, co), dsum(da, db)),
        !co && a is L && i < a->L_0.len() ==> fits(
            pm(a, i, b, co),
            dsum(da, db).update(0, (da[0] + db[0] - i) as nat),
        ),
    decreases a, pm_c(a, i, co), b,
{
    let ds = dsum(da, db);
    let dt = dsum(da.drop_first(), db.drop_first());
    if co {
        let cb = coeffs(b);
        if let MP::L(s) = pm(a, i, b, co) {
            assert(ds.update(0, db[0]).drop_first() =~= dt);
            assert forall|j: int| 0 <= j < s.len() implies fits(#[trigger] s[j], dt) by {
                lemma_fits_pm(a, 0, cb[j], false, da.drop_first(), db.drop_first());
            }
        }
    } else {
        match a {
            MP::K(c) => {
                if let MP::L(bs) = b {
                    if let MP::L(s) = pm(a, i, b, co) {
                        assert(ds.drop_first() =~= dt);
                        assert forall|j: int| 0 <= j < s.len() implies fits(
                            #[trigger] s[j],
                            dt,
                        ) by {
                            lemma_fits_pm(a, 0, bs[j], false, da.drop_first(), db.drop_first());
                        }
                    }
                }
            },
            MP::L(cs) => {
                if i < cs.len() {
                    let D = ds.update(0, (da[0] + db[0] - i) as nat);
                    let p0 = pm(cs[i as int], 0, b, true);
                    lemma_fits_pm(cs[i as int], 0, b, true, da, db);
                    lemma_fits_mono(p0, ds.update(0, db[0]), D);
                    if i + 1 < cs.len() {
                        let q = pm(a, (i + 1) as nat, b, false);
                        lemma_fits_pm(a, (i + 1) as nat, b, false, da, db);
                        assert(D.update(0, (D[0] - 1) as nat) =~= ds.update(
                            0,
                            (da[0] + db[0] - (i + 1)) as nat,
                        ));
                        lemma_fits_shift(q, D);
                        lemma_fits_add(p0, shift(q), D, D);
                        assert(dmax(D, D) =~= D);
                    }
                    if i == 0 {
                        assert(D =~= ds);
                    }
                }
            },
        }
    }
}

pub(crate) proof fn lemma_fits_mul(a: MP, b: MP, da: Seq<nat>, db: Seq<nat>)
    requires
        fits(a, da),
        fits(b, db),
        da.len() == db.len(),
    ensures
        fits(pmul(a, b), dsum(da, db)),
{
    lemma_fits_pm(a, 0, b, false, da, db);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fits_x(i: nat, ds: Seq<nat>)
    requires
        i < ds.len(),
        ds[i as int] >= 1,
    ensures
        fits(px(i), ds),
    decreases i,
{
    let cs = coeffs(px(i));
    if i > 0 {
        lemma_fits_x((i - 1) as nat, ds.drop_first());
        assert(cs[0] == px((i - 1) as nat));
    }
    assert forall|j: int| 0 <= j < cs.len() implies fits(#[trigger] cs[j], ds.drop_first()) by {
        if i == 0 {
            assert(cs[j] == MP::K(0) || cs[j] == MP::K(1));
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Univariate roots
// ---------------------------------------------------------------------------------------------

/// Quotient of synthetic division of horner(cs, .) by (x - r).
pub(crate) open spec fn quo(cs: Seq<int>, r: int) -> Seq<int>
    decreases cs.len(),
{
    if cs.len() <= 1 {
        Seq::empty()
    } else {
        seq![horner(cs.drop_first(), r)] + quo(cs.drop_first(), r)
    }
}

/// horner(cs, x) == horner(cs, r) + (x - r) horner(quo(cs, r), x).
#[verifier::spinoff_prover]
proof fn lemma_quo(cs: Seq<int>, r: int, x: int)
    ensures
        quo(cs, r).len() == if cs.len() == 0 {
            0
        } else {
            cs.len() - 1
        },
        horner(cs, x) == horner(cs, r) + (x - r) * horner(quo(cs, r), x),
    decreases cs.len(),
{
    let q = quo(cs, r);
    if cs.len() <= 1 {
        lemma_mul_basics(x - r);
        lemma_mul_basics(x);
        lemma_mul_basics(r);
        assert(horner(q, x) == 0);
        if cs.len() == 1 {
            assert(horner(cs.drop_first(), x) == 0);
            assert(horner(cs.drop_first(), r) == 0);
        }
    } else {
        let tt = cs.drop_first();
        lemma_quo(tt, r, x);
        let A = horner(tt, r);
        let Q = horner(quo(tt, r), x);
        assert(q.drop_first() =~= quo(tt, r));
        assert(horner(q, x) == A + x * Q);
        assert(horner(cs, x) == cs[0] + x * horner(tt, x));
        assert(horner(cs, r) == cs[0] + r * A);
        assert(x * horner(tt, x) == x * (A + (x - r) * Q));
        assert((x - r) * horner(q, x) == (x - r) * (A + x * Q));
        lemma_mul_is_distributive_add(x, A, (x - r) * Q);
        lemma_mul_is_distributive_add(x - r, A, x * Q);
        lemma_mul_is_distributive_add_other_way(A, r, x - r);
        lemma_mul_is_associative(x, x - r, Q);
        lemma_mul_is_associative(x - r, x, Q);
        lemma_mul_is_commutative(x, x - r);
    }
}

/// P(r) ≡ 0 and every quotient coefficient ≡ 0 ⇒ every coefficient of P ≡ 0.
#[verifier::spinoff_prover]
proof fn lemma_quo_zero(cs: Seq<int>, r: int)
    requires
        fmod(horner(cs, r)) == 0,
        forall|k: int| 0 <= k < quo(cs, r).len() ==> fmod(#[trigger] quo(cs, r)[k]) == 0,
    ensures
        forall|j: int| 0 <= j < cs.len() ==> fmod(#[trigger] cs[j]) == 0,
    decreases cs.len(),
{
    lemma_group_consts();
    let p = p256_p();
    if cs.len() == 1 {
        lemma_mul_basics(r);
    } else if cs.len() >= 2 {
        let tt = cs.drop_first();
        let q = quo(cs, r);
        let A = horner(tt, r);
        assert(q.drop_first() =~= quo(tt, r));
        assert(fmod(A) == 0) by {
            assert(q[0] == A);
        }
        assert forall|k: int| 0 <= k < quo(tt, r).len() implies fmod(#[trigger] quo(tt, r)[k])
            == 0 by {
            assert(quo(tt, r)[k] == q[k + 1]);
        }
        lemma_quo_zero(tt, r);
        // c0 == horner(cs, r) - r A, both ≡ 0
        lemma_add_mod_noop(cs[0], r * A, p);
        lemma_mul_mod_noop_right(r, A, p);
        lemma_mul_basics(r);
        lemma_mod_twice(cs[0], p);
        assert forall|j: int| 0 <= j < cs.len() implies fmod(#[trigger] cs[j]) == 0 by {
            if j > 0 {
                assert(cs[j] == tt[j - 1]);
            }
        }
    }
}

/// A polynomial with fewer coefficients than it has roots (distinct mod p) is 0 mod p.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_roots(cs: Seq<int>, pts: Seq<int>)
    requires
        pts.len() >= cs.len(),
        distinct_mod_p(pts),
        forall|t: int| 0 <= t < pts.len() ==> fmod(#[trigger] horner(cs, pts[t])) == 0,
    ensures
        forall|j: int| 0 <= j < cs.len() ==> fmod(#[trigger] cs[j]) == 0,
    decreases cs.len(),
{
    lemma_group_consts();
    let p = p256_p();
    if cs.len() > 0 {
        let r = pts[0];
        let rest = pts.drop_first();
        let q = quo(cs, r);
        lemma_quo(cs, r, r);
        assert(fmod(horner(cs, r)) == 0);
        assert forall|t: int| 0 <= t < rest.len() implies fmod(#[trigger] horner(q, rest[t]))
            == 0 by {
            let x = rest[t];
            assert(x == pts[t + 1]);
            assert(fmod(horner(cs, x)) == 0);
            lemma_quo(cs, r, x);
            // (x - r) h ≡ horner(cs, x) - horner(cs, r) ≡ 0
            lemma_sub_mod_noop(horner(cs, x), horner(cs, r), p);
            assert(fmod((x - r) * horner(q, x)) == 0);
            lemma_no_zero_div(x - r, horner(q, x));
            lemma_mod_equivalence(x, r, p);
            assert(fmod(pts[t + 1]) != fmod(pts[0]));
        }
        assert(distinct_mod_p(rest)) by {
            assert forall|i: int, j: int|
                #![trigger rest[i], rest[j]]
                0 <= i < rest.len() && 0 <= j < rest.len() && i != j implies fmod(rest[i])
                != fmod(rest[j]) by {
                assert(rest[i] == pts[i + 1] && rest[j] == pts[j + 1]);
            }
        }
        lemma_roots(q, rest);
        lemma_quo_zero(cs, r);
    }
}

// ---------------------------------------------------------------------------------------------
// The grid theorem
// ---------------------------------------------------------------------------------------------

/// Combinatorial Nullstellensatz, Lemma 2.1 (Alon 1999), over GF(p).
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_grid(a: MP, ds: Seq<nat>, g: Seq<Seq<int>>)
    requires
        fits(a, ds),
        g.len() == ds.len(),
        forall|k: int| 0 <= k < g.len() ==> #[trigger] g[k].len() > ds[k] && distinct_mod_p(g[k]),
        forall|xs: Seq<int>| in_grid(xs, g) ==> fmod(#[trigger] ev(a, xs)) == 0,
    ensures
        forall|xs: Seq<int>| xs.len() == ds.len() ==> fmod(#[trigger] ev(a, xs)) == 0,
    decreases ds.len(),
{
    match a {
        MP::K(c) => {
            let w = Seq::new(g.len(), |k: int| g[k][0]);
            assert forall|k: int| 0 <= k < g.len() implies #[trigger] g[k].contains(w[k]) by {
                assert(g[k].len() > ds[k]);
                assert(g[k][0] == w[k]);
            }
            assert(in_grid(w, g));
            assert(fmod(ev(a, w)) == 0);
        },
        MP::L(cs) => {
            let n = ds.len();
            let dt = ds.drop_first();
            let gt = g.drop_first();
            let g0 = g[0];
            assert(g0.len() > ds[0]);
            assert(distinct_mod_p(g0));
            assert forall|k: int| 0 <= k < gt.len() implies #[trigger] gt[k].len() > dt[k]
                && distinct_mod_p(gt[k]) by {
                assert(gt[k] == g[k + 1] && dt[k] == ds[k + 1]);
            }
            assert forall|j: int| 0 <= j < cs.len() implies forall|ys: Seq<int>|
                ys.len() == dt.len() ==> fmod(#[trigger] ev(#[trigger] cs[j], ys)) == 0 by {
                assert forall|ys: Seq<int>| in_grid(ys, gt) implies fmod(
                    #[trigger] ev(cs[j], ys),
                ) == 0 by {
                    let vs = evs(cs, ys);
                    assert forall|t: int| 0 <= t < g0.len() implies fmod(
                        #[trigger] horner(vs, g0[t]),
                    ) == 0 by {
                        let xs = seq![g0[t]] + ys;
                        assert(xs.drop_first() =~= ys);
                        assert forall|k: int| 0 <= k < g.len() implies #[trigger] g[k].contains(
                            xs[k],
                        ) by {
                            if k == 0 {
                                assert(g0[t] == xs[0]);
                            } else {
                                assert(gt[k - 1] == g[k] && xs[k] == ys[k - 1]);
                                assert(gt[k - 1].contains(ys[k - 1]));
                            }
                        }
                        assert(in_grid(xs, g));
                        lemma_ev_evs(cs, xs);
                    }
                    lemma_roots(vs, g0);
                    assert(vs[j] == ev(cs[j], ys));
                }
                assert(fits(cs[j], dt));
                lemma_grid(cs[j], dt, gt);
            }
            assert forall|xs: Seq<int>| xs.len() == ds.len() implies fmod(#[trigger] ev(a, xs))
                == 0 by {
                let t = xs.drop_first();
                lemma_ev_evs(cs, xs);
                assert forall|j: int| 0 <= j < evs(cs, t).len() implies fmod(
                    #[trigger] evs(cs, t)[j],
                ) == 0 by {
                    assert(fmod(ev(cs[j], t)) == 0);
                }
                lemma_horner_zero(evs(cs, t), xs[0]);
            }
        },
    }
}

// ---------------------------------------------------------------------------------------------
// Smoke: (x0 + x1)^2 - x0^2 - 2 x0 x1 - x1^2 on the grid {0, 1, 2}^2
// ---------------------------------------------------------------------------------------------

pub(crate) open spec fn pneg(a: MP) -> MP {
    pmul(pk(-1), a)
}

pub(crate) open spec fn smoke_poly() -> MP {
    let x0 = px(0);
    let x1 = px(1);
    let s = padd(x0, x1);
    padd(
        padd(padd(pmul(s, s), pneg(pmul(x0, x0))), pneg(pmul(pk(2), pmul(x0, x1)))),
        pneg(pmul(x1, x1)),
    )
}

pub(crate) open spec fn smoke_val(u: int, v: int) -> int {
    (u + v) * (u + v) + -1 * (u * u) + -1 * (2 * (u * v)) + -1 * (v * v)
}

pub(crate) open spec fn smoke_grid() -> Seq<Seq<int>> {
    seq![seq![0int, 1, 2], seq![0int, 1, 2]]
}

pub(crate) proof fn lemma_grid_smoke()
    ensures
        forall|xs: Seq<int>| xs.len() == 2 ==> fmod(#[trigger] ev(smoke_poly(), xs)) == 0,
{
    lemma_group_consts();
    let x0 = px(0);
    let x1 = px(1);
    let s = padd(x0, x1);
    let d1 = seq![1nat, 1nat];
    let d0 = seq![0nat, 0nat];
    let d2 = seq![2nat, 2nat];
    // degrees
    lemma_fits_x(0, d1);
    lemma_fits_x(1, d1);
    lemma_fits_add(x0, x1, d1, d1);
    assert(dmax(d1, d1) =~= d1);
    assert(dsum(d1, d1) =~= d2);
    assert(dsum(d0, d2) =~= d2);
    assert(dsum(d0, d1) =~= d1);
    assert(dmax(d2, d2) =~= d2);
    lemma_fits_mul(s, s, d1, d1);
    lemma_fits_mul(x0, x0, d1, d1);
    lemma_fits_mul(x0, x1, d1, d1);
    lemma_fits_mul(x1, x1, d1, d1);
    lemma_fits_mul(pk(-1), pmul(x0, x0), d0, d2);
    lemma_fits_mul(pk(2), pmul(x0, x1), d0, d2);
    lemma_fits_mul(pk(-1), pmul(pk(2), pmul(x0, x1)), d0, d2);
    lemma_fits_mul(pk(-1), pmul(x1, x1), d0, d2);
    let t1 = padd(pmul(s, s), pneg(pmul(x0, x0)));
    let t2 = padd(t1, pneg(pmul(pk(2), pmul(x0, x1))));
    lemma_fits_add(pmul(s, s), pneg(pmul(x0, x0)), d2, d2);
    lemma_fits_add(t1, pneg(pmul(pk(2), pmul(x0, x1))), d2, d2);
    lemma_fits_add(t2, pneg(pmul(x1, x1)), d2, d2);
    assert(fits(smoke_poly(), d2));
    // the grid
    let g = smoke_grid();
    assert(distinct_mod_p(g[0]) && distinct_mod_p(g[1]));
    // the lengths g[k].len() > d2[k] are left to lemma_grid's precondition
    assert forall|xs: Seq<int>| in_grid(xs, g) implies fmod(#[trigger] ev(smoke_poly(), xs))
        == 0 by {
        let u = xs[0];
        let v = xs[1];
        lemma_ev_x(0, xs);
        lemma_ev_x(1, xs);
        lemma_ev_add(x0, x1, xs);
        lemma_ev_mul(s, s, xs);
        lemma_ev_mul(x0, x0, xs);
        lemma_ev_mul(x0, x1, xs);
        lemma_ev_mul(x1, x1, xs);
        lemma_ev_mul(pk(-1), pmul(x0, x0), xs);
        lemma_ev_mul(pk(2), pmul(x0, x1), xs);
        lemma_ev_mul(pk(-1), pmul(pk(2), pmul(x0, x1)), xs);
        lemma_ev_mul(pk(-1), pmul(x1, x1), xs);
        lemma_ev_add(pmul(s, s), pneg(pmul(x0, x0)), xs);
        lemma_ev_add(t1, pneg(pmul(pk(2), pmul(x0, x1))), xs);
        lemma_ev_add(t2, pneg(pmul(x1, x1)), xs);
        assert(ev(smoke_poly(), xs) == smoke_val(u, v));
        assert(g[0].contains(u) && g[1].contains(v));
        assert(u == 0 || u == 1 || u == 2);
        assert(v == 0 || v == 1 || v == 2);
        // the nine literal points
        assert(smoke_val(0, 0) == 0 && smoke_val(0, 1) == 0 && smoke_val(0, 2) == 0) by (nonlinear_arith);
        assert(smoke_val(1, 0) == 0 && smoke_val(1, 1) == 0 && smoke_val(1, 2) == 0) by (nonlinear_arith);
        assert(smoke_val(2, 0) == 0 && smoke_val(2, 1) == 0 && smoke_val(2, 2) == 0) by (nonlinear_arith);
        assert(smoke_val(u, v) == 0);
    }
    lemma_grid(smoke_poly(), d2, g);
}


} // verus!
