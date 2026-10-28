//! Literal P-256 constants (for `compute_only` evaluation) bridged to the frozen `crate::p256`
//! spec, Fermat's little theorem mod p and n, and the GF(p) facts the group-law proof uses.
#![allow(non_snake_case)]
#[allow(unused_imports)]
use super::nt::*;
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

/// SP 800-186 §3.2.1.3 p.
pub(crate) open spec fn P_LIT() -> int {
    115792089210356248762697446949407573530086143415290314195533631308867097853951int
}

/// SP 800-186 §3.2.1.3 n.
pub(crate) open spec fn N_LIT() -> int {
    115792089210356248762697446949407573529996955224135760342422259061068512044369int
}

/// SP 800-186 §3.2.1.3 b.
pub(crate) open spec fn B_LIT() -> int {
    41058363725152142129326129780047268409114441015993725554835256314039467401291int
}

/// SP 800-186 §3.2.1.3 Gx.
pub(crate) open spec fn GX_LIT() -> int {
    48439561293906451759052585252797914202762949526041747995844080717082404635286int
}

/// SP 800-186 §3.2.1.3 Gy.
pub(crate) open spec fn GY_LIT() -> int {
    36134250956749795798585127919587881956611106672985015071877198253568414405109int
}

pub(crate) open spec fn G_LIT() -> SpecPoint {
    SpecPoint::Affine(GX_LIT(), GY_LIT())
}

/// The literals equal the frozen spec's big-endian constants.
pub(crate) proof fn lemma_group_consts()
    ensures
        p256_p() == P_LIT(),
        p256_n() == N_LIT(),
        p256_b() == B_LIT(),
        p256_g() == G_LIT(),
{
    assert(p256_p() == P_LIT() && p256_n() == N_LIT() && p256_b() == B_LIT() && p256_g()
        == G_LIT()) by (compute_only);
}

/// Fermat's little theorem mod p (from the Pratt certificate of p).
pub(crate) proof fn lemma_flt_p(x: int)
    requires
        fmod(x) != 0,
    ensures
        fmod(pow(x, (p256_p() - 1) as nat)) == 1,
{
    lemma_group_consts();
    super::pratt::lemma_prime_P();
    assert(x % (super::pratt::Q_P() as int) != 0);
    assert(pow(x, (super::pratt::Q_P() - 1) as nat) % (super::pratt::Q_P() as int) == 1);
}

/// Fermat's little theorem mod n (from the Pratt certificate of n).
pub(crate) proof fn lemma_flt_n(x: int)
    requires
        x % p256_n() != 0,
    ensures
        pow(x, (p256_n() - 1) as nat) % p256_n() == 1,
{
    lemma_group_consts();
    super::pratt::lemma_prime_N();
    assert(x % (super::pratt::Q_N() as int) != 0);
    assert(pow(x, (super::pratt::Q_N() - 1) as nat) % (super::pratt::Q_N() as int) == 1);
}

pub(crate) proof fn lemma_finv_mul(x: int)
    requires
        fmod(x) != 0,
    ensures
        fmod(x * finv(x)) == 1,
{
    lemma_group_consts();
    let p = p256_p();
    let e = (p - 2) as nat;
    lemma_flt_p(x);
    // x * x^(p - 2) == x^(p - 1)
    lemma_pow_adds(x, 1, e);
    lemma_pow1(x);
    assert((1 + e) as nat == (p - 1) as nat);
    lemma_mul_mod_noop_right(x, pow(x, e), p);
}

pub(crate) proof fn lemma_finv_unique(x: int, w: int)
    requires
        fmod(x * w) == 1,
    ensures
        finv(x) == fmod(w),
{
    lemma_group_consts();
    let p = p256_p();
    if fmod(x) == 0 {
        // (x * w) % p == ((x % p) * w) % p == 0
        lemma_mul_mod_noop_left(x, w, p);
        lemma_mul_basics(w);
        assert(false);
    }
    lemma_finv_mul(x);
    let v = finv(x);
    lemma_mod_bound(pow(x, (p - 2) as nat), p);
    // v == (v * (x w)) % p == ((x v) w) % p == ((x v % p) w) % p == w % p
    lemma_mul_mod_noop_right(v, x * w, p);
    lemma_small_mod(v as nat, p as nat);
    lemma_mul_is_associative(v, x, w);
    lemma_mul_is_commutative(v, x);
    lemma_mul_mod_noop_left(x * v, w, p);
}

/// GF(p) has no zero divisors (Euclid's lemma, p prime).
pub(crate) proof fn lemma_no_zero_div(a: int, b: int)
    requires
        fmod(a * b) == 0,
    ensures
        fmod(a) == 0 || fmod(b) == 0,
{
    lemma_group_consts();
    let p = p256_p();
    super::pratt::lemma_p_prime();
    lemma_mod_bound(a, p);
    lemma_mod_bound(b, p);
    let a1 = (a % p) as nat;
    let b1 = (b % p) as nat;
    lemma_mul_mod_noop_general(a, b, p);
    lemma_euclid_prime(p as nat, a1, b1);
    lemma_small_mod(a1, p as nat);
    lemma_small_mod(b1, p as nat);
}

pub(crate) proof fn lemma_finv_powmod(x: int)
    ensures
        finv(x) == powmod(x % p256_p(), (p256_p() - 2) as nat, p256_p()),
{
    lemma_group_consts();
    let p = p256_p();
    let e = (p - 2) as nat;
    lemma_powmod(x % p, e, p);
    lemma_pow_mod_noop(x, e, p);
}

pub(crate) proof fn lemma_finv_one()
    ensures
        finv(1) == 1,
{
    lemma_group_consts();
    lemma1_pow((p256_p() - 2) as nat);
    lemma_small_mod(1, p256_p() as nat);
}

pub(crate) proof fn lemma_b_range()
    ensures
        0 < p256_b() < p256_p(),
{
    lemma_group_consts();
}

} // verus!
