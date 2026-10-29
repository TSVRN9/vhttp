//! The order of G: nG = O by a double-and-add chain checked chunk by chunk (chain.rs), and
//! kG != O for 1 <= k < n by Fermat's little theorem mod n.
//! The chain's point additions take each field inverse as a witness w, checked under
//! `compute_only` as (den * w) % p == 1 and lifted to `finv(den) == fmod(w)` by
//! `lemma_finv_unique`; a computed inverse (a 256-bit `powmod`) exceeds the evaluator's
//! recursion depth at the required `--rlimit 0.6`.
#[allow(unused_imports)]
use super::field::*;
#[allow(unused_imports)]
use super::group::*;
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
// Definitions (evaluable by `compute_only`: literal constants only)
// ---------------------------------------------------------------------------------------------

/// w is the inverse of `point_add(a, b)`'s denominator (when that branch divides at all).
pub(crate) open spec fn inv_ok(a: SpecPoint, b: SpecPoint, w: int) -> bool {
    match (a, b) {
        (SpecPoint::Affine(x1, y1), SpecPoint::Affine(x2, y2)) => (x1 == x2 && (y1 + y2) % P_LIT()
            == 0) || ((if x1 == x2 {
            2 * y1
        } else {
            x2 - x1
        }) * w) % P_LIT() == 1,
        _ => true,
    }
}

/// `point_add` with `fmod` as `% P_LIT()` and `finv(den)` as the witness w: the same case
/// structure and association order.
pub(crate) open spec fn padd_fast(a: SpecPoint, b: SpecPoint, w: int) -> SpecPoint {
    match (a, b) {
        (SpecPoint::Infinity, _) => b,
        (_, SpecPoint::Infinity) => a,
        (SpecPoint::Affine(x1, y1), SpecPoint::Affine(x2, y2)) => {
            if x1 == x2 && (y1 + y2) % P_LIT() == 0 {
                SpecPoint::Infinity
            } else {
                let lambda = if x1 == x2 {
                    ((3 * x1 * x1 - 3) * w) % P_LIT()
                } else {
                    ((y2 - y1) * w) % P_LIT()
                };
                let x3 = (lambda * lambda - x1 - x2) % P_LIT();
                let y3 = (lambda * (x1 - x3) - y1) % P_LIT();
                SpecPoint::Affine(x3, y3)
            }
        },
    }
}

/// Double-and-add from acc over bits (most significant first): per bit, acc = 2 acc, then
/// acc = G + acc if the bit is set. ws holds two inverse witnesses per bit (the second unused
/// for a clear bit); None if a needed witness fails `inv_ok`.
pub(crate) open spec fn chain(acc: SpecPoint, bits: Seq<bool>, ws: Seq<int>) -> Option<SpecPoint>
    decreases bits.len(),
{
    if bits.len() == 0 {
        Some(acc)
    } else {
        let d = padd_fast(acc, acc, ws[0]);
        let r = if bits[0] {
            padd_fast(G_LIT(), d, ws[1])
        } else {
            d
        };
        if inv_ok(acc, acc, ws[0]) && (!bits[0] || inv_ok(G_LIT(), d, ws[1])) {
            chain(r, bits.drop_first(), ws.subrange(2, ws.len() as int))
        } else {
            None
        }
    }
}

/// e extended by bits (most significant first): e * 2^|bits| + (bits as a big-endian number).
pub(crate) open spec fn bext(e: nat, bits: Seq<bool>) -> nat
    decreases bits.len(),
{
    if bits.len() == 0 {
        e
    } else {
        bext(2 * e + if bits[0] {
            1nat
        } else {
            0nat
        }, bits.drop_first())
    }
}

// ---------------------------------------------------------------------------------------------
// The chain computes scalar multiples of G
// ---------------------------------------------------------------------------------------------

/// SP 800-186 §3.2.1.3: G is on the curve.
pub(crate) proof fn lemma_g_curve_pt()
    ensures
        curve_pt(p256_g()),
{
    lemma_group_consts();
    assert(0 <= GX_LIT() < P_LIT() && 0 <= GY_LIT() < P_LIT() && (GY_LIT() * GY_LIT()) % P_LIT()
        == (GX_LIT() * GX_LIT() * GX_LIT() - 3 * GX_LIT() + B_LIT()) % P_LIT()) by (compute_only);
}

pub(crate) proof fn lemma_padd_fast(a: SpecPoint, b: SpecPoint, w: int)
    requires
        inv_ok(a, b, w),
    ensures
        padd_fast(a, b, w) == point_add(a, b),
{
    lemma_group_consts();
    match (a, b) {
        (SpecPoint::Affine(x1, y1), SpecPoint::Affine(x2, y2)) => {
            if !(x1 == x2 && (y1 + y2) % P_LIT() == 0) {
                let num = if x1 == x2 {
                    3 * x1 * x1 - 3
                } else {
                    y2 - y1
                };
                let den = if x1 == x2 {
                    2 * y1
                } else {
                    x2 - x1
                };
                // finv(den) == w % p, so (num * finv(den)) % p == (num * w) % p
                lemma_finv_unique(den, w);
                lemma_mul_mod_noop_right(num, w, P_LIT());
            }
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_chain(e: nat, bits: Seq<bool>, ws: Seq<int>)
    requires
        chain(scalar_mult(e, p256_g()), bits, ws) is Some,
    ensures
        chain(scalar_mult(e, p256_g()), bits, ws) == Some(scalar_mult(bext(e, bits), p256_g())),
    decreases bits.len(),
{
    if bits.len() > 0 {
        let g = p256_g();
        lemma_group_consts();
        lemma_g_curve_pt();
        let acc = scalar_mult(e, g);
        let d = padd_fast(acc, acc, ws[0]);
        lemma_padd_fast(acc, acc, ws[0]);
        super::lemma_scalar_mult_double(e, g);
        assert(d == scalar_mult(2 * e, g));
        let e2 = 2 * e + if bits[0] {
            1nat
        } else {
            0nat
        };
        if bits[0] {
            lemma_padd_fast(G_LIT(), d, ws[1]);
            assert(((2 * e + 1) - 1) as nat == 2 * e);
        }
        assert(chain(acc, bits, ws) == chain(
            scalar_mult(e2, g),
            bits.drop_first(),
            ws.subrange(2, ws.len() as int),
        ));
        lemma_chain(e2, bits.drop_first(), ws.subrange(2, ws.len() as int));
    }
}

// ---------------------------------------------------------------------------------------------
// ord(G) = n
// ---------------------------------------------------------------------------------------------

/// nG = O (the chain of chain.rs, whose exponents end at n).
pub(crate) proof fn lemma_n_g_inf()
    ensures
        scalar_mult(p256_n() as nat, p256_g()) is Infinity,
{
    lemma_group_consts();
    super::chain::lemma_chain_all();
}

/// kP = O implies (kj)P = O.
proof fn lemma_mult_of_zero(k: nat, j: nat, pt: SpecPoint)
    requires
        curve_pt(pt),
        scalar_mult(k, pt) is Infinity,
    ensures
        scalar_mult(k * j, pt) is Infinity,
    decreases j,
{
    if j > 0 {
        let j1 = (j - 1) as nat;
        lemma_mult_of_zero(k, j1, pt);
        super::lemma_scalar_mult_add(k, k * j1, pt);
        lemma_mul_is_distributive_add(k as int, 1, j1 as int);
        assert(k * j == k + k * j1);
        assert(scalar_mult(k * j, pt) == point_add(scalar_mult(k, pt), scalar_mult(k * j1, pt)));
    } else {
        lemma_mul_basics(k as int);
    }
}

/// kG != O for 1 <= k < n. If kG = O, take m = k^(n - 2): FLT mod n gives k m = 1 + t n, so
/// G = (1 + t n)G = (k m)G = O, but G is affine.
pub(crate) proof fn lemma_g_order(k: nat)
    requires
        1 <= k < p256_n(),
    ensures
        !(scalar_mult(k, p256_g()) is Infinity),
{
    let g = p256_g();
    if scalar_mult(k, g) is Infinity {
        lemma_group_consts();
        lemma_g_curve_pt();
        let n = p256_n() as nat;
        let e = (n - 2) as nat;
        lemma_small_mod(k, n);
        lemma_flt_n(k as int);
        // k * k^(n - 2) == k^(n - 1)
        lemma_pow_positive(k as int, e);
        lemma_pow_adds(k as int, 1, e);
        lemma_pow1(k as int);
        assert((1 + e) as nat == (n - 1) as nat);
        let m = pow(k as int, e) as nat;
        let km = k * m;
        assert(km % n == 1);
        let t = km / n;
        lemma_fundamental_div_mod(km as int, n as int);
        assert(km == 1 + n * t);
        lemma_mult_of_zero(k, m, g);
        lemma_n_g_inf();
        lemma_mult_of_zero(n, t, g);
        // (1 + t n)G = G + O = G
        assert(((1 + n * t) - 1) as nat == (n * t) as nat);
        assert(scalar_mult(km, g) == g);
    }
}

} // verus!
