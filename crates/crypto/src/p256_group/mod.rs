#![allow(dead_code)]
//! P-256 group law (Phase 5d): proofs of `lemma_scalar_mult_double` and
//! `lemma_scalar_mult_g_nonzero` over the frozen `crate::p256` spec, with no new trusted base.
//! Exported lemmas are `mod.rs` wrappers: proof fns are erased, so `use` re-exports fail to build.

mod nt;
mod field;
mod pratt;
mod torsion;
mod torsion_cert;
mod poly;
mod red;
mod rcb;
mod grid_small;
mod assoc_id;
mod grid_assoc_a;
mod grid_assoc_b;
mod grid_assoc_c;
mod grid_assoc_d;
mod group;
mod order;
mod chain;

#[allow(unused_imports)]
use crate::p256::*;
#[allow(unused_imports)]
use group::*;
use vstd::prelude::*;

verus! {

/// kP stays on the curve (or O): induction on k through `point_add`'s closure.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_scalar_mult_closed(k: nat, pt: SpecPoint)
    requires
        curve_pt(pt),
    ensures
        curve_pt(scalar_mult(k, pt)),
    decreases k,
{
    if k > 0 {
        lemma_scalar_mult_closed((k - 1) as nat, pt);
        lemma_point_add_closed(pt, scalar_mult((k - 1) as nat, pt));
    }
}

/// (a + b)P = aP + bP: induction on a; the step is P + (a'P + bP) = (P + a'P) + bP by
/// associativity. No commutativity is needed.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_scalar_mult_add(a: nat, b: nat, pt: SpecPoint)
    requires
        curve_pt(pt),
    ensures
        scalar_mult(a + b, pt) == point_add(scalar_mult(a, pt), scalar_mult(b, pt)),
    decreases a,
{
    if a > 0 {
        let a1 = (a - 1) as nat;
        lemma_scalar_mult_add(a1, b, pt);
        lemma_scalar_mult_closed(a1, pt);
        lemma_scalar_mult_closed(b, pt);
        lemma_point_add_assoc(pt, scalar_mult(a1, pt), scalar_mult(b, pt));
        assert(((a + b) - 1) as nat == a1 + b);
    }
}

/// (2j)P = jP + jP, the doubling law consumed by 5c's `scalar_mult_ct` (statement frozen by 5c
/// Task 6).
pub(crate) proof fn lemma_scalar_mult_double(j: nat, pt: SpecPoint)
    requires
        pt is Infinity || (pt is Affine && on_curve(pt->0, pt->1)),
    ensures
        scalar_mult((2 * j) as nat, pt) == point_add(scalar_mult(j, pt), scalar_mult(j, pt)),
{
    lemma_scalar_mult_add(j, j, pt);
    assert((2 * j) as nat == j + j);
}

/// 5c Task 6's double-and-add step, reached the way 5c calls the export (Review Focus 3).
proof fn lemma_5c_interface_smoke(ev: nat, pt: SpecPoint)
    requires
        pt is Infinity || (pt is Affine && on_curve(pt->0, pt->1)),
    ensures
        scalar_mult((2 * ev + 1) as nat, pt) == point_add(
            pt,
            point_add(scalar_mult(ev, pt), scalar_mult(ev, pt)),
        ),
{
    crate::p256_group::lemma_scalar_mult_double(ev, pt);
    assert(((2 * ev + 1) as nat - 1) as nat == (2 * ev) as nat);
}

/// kG != O for 1 <= k < n, i.e. ord(G) = n (statement frozen by 5c Task 7).
pub(crate) proof fn lemma_scalar_mult_g_nonzero(k: nat)
    requires
        1 <= k < p256_n(),
    ensures
        !(scalar_mult(k, p256_g()) is Infinity),
{
    order::lemma_g_order(k);
}

/// 5c Task 7's call: a valid private key's scalar never maps G to O.
proof fn lemma_5c_order_smoke(d: Seq<u8>)
    requires
        scalar_valid(d),
    ensures
        !(scalar_mult(crate::bytes::os2ip(d), p256_g()) is Infinity),
{
    crate::p256_group::lemma_scalar_mult_g_nonzero(crate::bytes::os2ip(d));
}

} // verus!
