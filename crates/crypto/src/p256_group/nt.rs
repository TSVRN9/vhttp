//! Elementary number theory for 5d: modular exponentiation, gcd and Bezout, Euclid's lemma, and
//! the Lucas primality theorem with Fermat's little theorem for certified moduli.
// Lucas 1876 / Pratt 1975
#[allow(unused_imports)]
use crate::rsa::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power::*;
#[allow(unused_imports)]
use vstd::set_lib::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Definitions (evaluable by `compute_only`: no vstd `pow`, recursion by index, no quantifiers)
// ---------------------------------------------------------------------------------------------

/// a^e mod q by square-and-multiply on e / 2, reducing mod q at every step.
pub(crate) open spec fn powmod(a: int, e: nat, q: int) -> int
    decreases e,
{
    if e == 0 {
        1int % q
    } else {
        let h = powmod(a, e / 2, q);
        let s = (h * h) % q;
        if e % 2 == 0 {
            s
        } else {
            (s * (a % q)) % q
        }
    }
}

/// r^e over nat (a local power, so that `compute_only` never touches vstd `pow`).
pub(crate) open spec fn npow(r: nat, e: nat) -> nat
    decreases e,
{
    if e == 0 {
        1
    } else {
        r * npow(r, (e - 1) as nat)
    }
}

/// Product of fs[j].0 ^ fs[j].1 for j in [i, |fs|).
pub(crate) open spec fn prod_from(fs: Seq<(nat, nat)>, i: nat) -> nat
    decreases fs.len() - i,
{
    if i >= fs.len() {
        1
    } else {
        npow(fs[i as int].0, fs[i as int].1) * prod_from(fs, i + 1)
    }
}

/// Product of r_i ^ e_i over the factor list fs.
pub(crate) open spec fn prod_pow(fs: Seq<(nat, nat)>) -> nat {
    prod_from(fs, 0)
}

/// For every j in [i, |fs|), with r = fs[j].0: r > 1, r | q - 1 and a^((q - 1) / r) != 1 mod q.
pub(crate) open spec fn lucas_fs_ok(q: nat, a: int, fs: Seq<(nat, nat)>, i: nat) -> bool
    decreases fs.len() - i,
{
    if i >= fs.len() {
        true
    } else {
        let r = fs[i as int].0;
        r > 1 && (q - 1) % (r as int) == 0 && powmod(a, ((q - 1) / (r as int)) as nat, q as int)
            != 1 && lucas_fs_ok(q, a, fs, i + 1)
    }
}

/// Lucas certificate for q with witness a and the factorization fs of q - 1.
pub(crate) open spec fn lucas_ok(q: nat, a: int, fs: Seq<(nat, nat)>) -> bool {
    q > 2 && prod_pow(fs) == q - 1 && powmod(a, (q - 1) as nat, q as int) == 1 && lucas_fs_ok(
        q,
        a,
        fs,
        0,
    )
}

/// No k in [d, floor(sqrt(r))] divides r.
pub(crate) open spec fn trial_from(r: nat, d: nat) -> bool
    decreases r - d,
{
    if d >= r || d * d > r {
        true
    } else {
        r % d != 0 && trial_from(r, d + 1)
    }
}

/// Trial division: no divisor of r in [2, floor(sqrt(r))].
pub(crate) open spec fn trial_ok(r: nat) -> bool {
    trial_from(r, 2)
}

/// No k in [lo, hi) divides r (one chunk of `trial_from`).
pub(crate) open spec fn trial_seg(r: nat, lo: nat, hi: nat) -> bool
    decreases hi - lo,
{
    if lo >= hi {
        true
    } else {
        r % lo != 0 && trial_seg(r, lo + 1, hi)
    }
}

/// e >> k.
pub(crate) open spec fn shr(e: nat, k: nat) -> nat
    decreases k,
{
    if k == 0 {
        e
    } else {
        shr(e / 2, (k - 1) as nat)
    }
}

/// `powmod` resumed from s == a^(e >> k) mod q through the low k bits of e (one chunk).
pub(crate) open spec fn powmod_ext(s: int, a: int, e: nat, k: nat, q: int) -> int
    decreases k,
{
    if k == 0 {
        s
    } else {
        let h = powmod_ext(s, a, e / 2, (k - 1) as nat, q);
        let s2 = (h * h) % q;
        if e % 2 == 0 {
            s2
        } else {
            (s2 * (a % q)) % q
        }
    }
}

/// Euclid's gcd.
pub(crate) open spec fn gcd(a: nat, b: nat) -> nat
    decreases b,
{
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

// ---------------------------------------------------------------------------------------------
// powmod
// ---------------------------------------------------------------------------------------------

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_powmod(a: int, e: nat, q: int)
    requires
        q > 1,
    ensures
        powmod(a, e, q) == pow(a, e) % q,
    decreases e,
{
    if e == 0 {
        lemma_pow0(a);
    } else {
        let k = e / 2;
        lemma_powmod(a, k, q);
        let pk = pow(a, k);
        lemma_pow_adds(a, k, k);
        lemma_mul_mod_noop_general(pk, pk, q);
        // (h * h) % q == pow(a, k + k) % q
        if e % 2 == 0 {
            assert(e == k + k);
        } else {
            assert(e == (k + k) + 1);
            lemma_pow_adds(a, k + k, 1);
            lemma_pow1(a);
            lemma_mul_mod_noop_general(pow(a, k + k), a, q);
        }
    }
}

pub(crate) proof fn lemma_shr_pos(e: nat, k: nat)
    requires
        shr(e, k) > 0,
    ensures
        e > 0,
    decreases k,
{
    if k > 0 {
        lemma_shr_pos(e / 2, (k - 1) as nat);
    }
}

/// Exponent-prefix split of `powmod`.
pub(crate) proof fn lemma_powmod_ext(a: int, e: nat, k: nat, q: int)
    requires
        shr(e, k) > 0,
    ensures
        powmod(a, e, q) == powmod_ext(powmod(a, shr(e, k), q), a, e, k, q),
    decreases k,
{
    if k > 0 {
        lemma_shr_pos(e, k);
        lemma_powmod_ext(a, e / 2, (k - 1) as nat, q);
    }
}

// ---------------------------------------------------------------------------------------------
// Divisibility helpers
// ---------------------------------------------------------------------------------------------

/// d | x and d | y imply d | s x + t y.
proof fn lemma_dvd_lin(d: int, x: int, y: int, s: int, t: int)
    requires
        d > 0,
        x % d == 0,
        y % d == 0,
    ensures
        (s * x + t * y) % d == 0,
{
    let cx = x / d;
    let cy = y / d;
    lemma_fundamental_div_mod(x, d);
    lemma_fundamental_div_mod(y, d);
    let c = s * cx + t * cy;
    assert(s * x == (s * cx) * d) by {
        lemma_mul_is_associative(s, cx, d);
        lemma_mul_is_commutative(cx, d);
    }
    assert(t * y == (t * cy) * d) by {
        lemma_mul_is_associative(t, cy, d);
        lemma_mul_is_commutative(cy, d);
    }
    lemma_mul_is_distributive_add_other_way(d, s * cx, t * cy);
    lemma_mod_multiples_basic(c, d);
}

/// d | k and k | x imply d | x.
proof fn lemma_dvd_trans(d: int, k: int, x: int)
    requires
        d > 0,
        k > 0,
        k % d == 0,
        x % k == 0,
    ensures
        x % d == 0,
{
    lemma_fundamental_div_mod(x, k);
    lemma_mul_is_commutative(k, x / k);
    lemma_dvd_lin(d, k, 0, x / k, 0);
}

/// A positive multiple of d is at least d.
proof fn lemma_dvd_le(d: int, x: int)
    requires
        d > 0,
        x > 0,
        x % d == 0,
    ensures
        d <= x,
{
    lemma_fundamental_div_mod(x, d);
    if x / d <= 0 {
        lemma_mul_nonpositive_left(d, x / d);
    } else {
        lemma_mul_increases(x / d, d);
        lemma_mul_is_commutative(x / d, d);
    }
}

proof fn lemma_mul_nonpositive_left(d: int, c: int)
    requires
        d > 0,
        c <= 0,
    ensures
        d * c <= 0,
{
    assert(d * c <= 0) by (nonlinear_arith)
        requires
            d > 0,
            c <= 0,
    ;
}

/// x % q == 1 implies x^k % q == 1.
proof fn lemma_pow_of_one(x: int, k: nat, q: int)
    requires
        q > 1,
        x % q == 1,
    ensures
        pow(x, k) % q == 1,
{
    lemma_pow_mod_noop(x, k, q);
    lemma1_pow(k);
    lemma_small_mod(1, q as nat);
}

/// a^m % q == 1 implies a^(m k) % q == 1.
proof fn lemma_pow_mul_one(a: int, m: nat, k: nat, q: int)
    requires
        q > 1,
        pow(a, m) % q == 1,
    ensures
        pow(a, m * k) % q == 1,
{
    lemma_pow_multiplies(a, m, k);
    lemma_pow_of_one(pow(a, m), k, q);
}

// ---------------------------------------------------------------------------------------------
// gcd and Bezout
// ---------------------------------------------------------------------------------------------

/// gcd(a, b) is positive when a or b is, and divides both.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_gcd_divides(a: nat, b: nat)
    requires
        a > 0 || b > 0,
    ensures
        gcd(a, b) > 0,
        a % gcd(a, b) == 0,
        b % gcd(a, b) == 0,
    decreases b,
{
    if b == 0 {
        lemma_mod_self_0(a as int);
    } else {
        let r = a % b;
        lemma_gcd_divides(b, r);
        let g = gcd(b, r);
        // a == (a / b) * b + r
        lemma_fundamental_div_mod(a as int, b as int);
        lemma_mul_is_commutative(b as int, (a / b) as int);
        lemma_dvd_lin(g as int, b as int, r as int, (a / b) as int, 1);
    }
}

/// Bezout: x a + y b == gcd(a, b), with the coefficients returned.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_bezout(a: nat, b: nat) -> (xy: (int, int))
    ensures
        xy.0 * a + xy.1 * b == gcd(a, b),
    decreases b,
{
    if b == 0 {
        (1, 0)
    } else {
        let r = a % b;
        let k = a / b;
        let (x, y) = lemma_bezout(b, r);
        // x b + y r == g and a == b k + r
        lemma_fundamental_div_mod(a as int, b as int);
        assert(y * a + (x - y * k) * b == x * b + y * r) by (nonlinear_arith)
            requires
                a == b * k + r,
        ;
        (y, x - y * k)
    }
}

/// a^d == 1 and a^m == 1 (mod q) imply a^gcd(d, m) == 1, by Euclid on the exponents.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_pow_gcd(a: int, d: nat, m: nat, q: int)
    requires
        q > 1,
        pow(a, d) % q == 1,
        pow(a, m) % q == 1,
    ensures
        pow(a, gcd(d, m)) % q == 1,
    decreases m,
{
    if m > 0 {
        let k = d / m;
        let r = d % m;
        lemma_fundamental_div_mod(d as int, m as int);
        assert(d == m * k + r);
        lemma_pow_adds(a, m * k, r);
        lemma_pow_mul_one(a, m, k, q);
        // 1 == (a^(m k) * a^r) % q == ((a^(m k) % q) * a^r) % q == a^r % q
        lemma_mul_mod_noop_general(pow(a, m * k), pow(a, r), q);
        lemma_pow_gcd(a, m, r, q);
    }
}

// ---------------------------------------------------------------------------------------------
// Primes: Euclid's lemma, least divisors, trial division
// ---------------------------------------------------------------------------------------------

/// A positive divisor of a prime s is 1 or s.
proof fn lemma_prime_divisor_cases(s: nat, g: nat)
    requires
        is_prime(s),
        g > 0,
        s % g == 0,
    ensures
        g == 1 || g == s,
{
    lemma_dvd_le(g as int, s as int);
    if 1 < g && g < s {
        assert(s % g != 0);
    }
}

/// Euclid's lemma: a prime s dividing a b divides a or b.
pub(crate) proof fn lemma_euclid_prime(s: nat, a: nat, b: nat)
    requires
        is_prime(s),
        (a * b) % s == 0,
    ensures
        a % s == 0 || b % s == 0,
{
    if a % s != 0 {
        lemma_gcd_divides(s, a);
        let g = gcd(s, a);
        lemma_prime_divisor_cases(s, g);
        if g == s {
            assert(a % s == 0);
        }
        assert(g == 1);
        let (x, y) = lemma_bezout(s, a);
        // b == (x b) s + y (a b)
        assert(b == (x * b) * s + y * (a * b)) by (nonlinear_arith)
            requires
                x * s + y * a == 1,
        ;
        lemma_mod_self_0(s as int);
        lemma_dvd_lin(s as int, s as int, (a * b) as int, x * b, y);
    }
}

/// The least divisor k >= 2 of D is prime.
pub(crate) proof fn lemma_least_divisor_prime(D: nat, k: nat)
    requires
        2 <= k <= D,
        D % k == 0,
        forall|j: nat| 2 <= j < k ==> #[trigger] (D % j) != 0,
    ensures
        is_prime(k),
{
    assert forall|j: nat| 1 < j < k implies #[trigger] (k % j) != 0 by {
        if k % j == 0 {
            lemma_dvd_trans(j as int, k as int, D as int);
            assert(D % j == 0);
        }
    }
}

/// Search from k upward for the least divisor of D.
#[verifier::spinoff_prover]
proof fn lemma_least_divisor_from(D: nat, k: nat) -> (s: nat)
    requires
        2 <= k <= D,
        forall|j: nat| 2 <= j < k ==> #[trigger] (D % j) != 0,
    ensures
        is_prime(s),
        D % s == 0,
    decreases D - k,
{
    if D % k == 0 {
        lemma_least_divisor_prime(D, k);
        k
    } else {
        if k == D {
            lemma_mod_self_0(D as int);
        }
        assert forall|j: nat| 2 <= j < k + 1 implies #[trigger] (D % j) != 0 by {
            if j < k {
                assert(D % j != 0);
            }
        }
        lemma_least_divisor_from(D, k + 1)
    }
}

/// Every D >= 2 has a prime divisor.
pub(crate) proof fn lemma_prime_divisor(D: nat) -> (s: nat)
    requires
        D >= 2,
    ensures
        is_prime(s),
        D % s == 0,
{
    lemma_least_divisor_from(D, 2)
}

/// A prime s dividing r^e divides r.
#[verifier::spinoff_prover]
proof fn lemma_prime_dvd_npow(s: nat, r: nat, e: nat)
    requires
        is_prime(s),
        npow(r, e) % s == 0,
    ensures
        r % s == 0,
    decreases e,
{
    if e == 0 {
        lemma_small_mod(1, s);
    } else {
        lemma_euclid_prime(s, r, npow(r, (e - 1) as nat));
        if r % s != 0 {
            lemma_prime_dvd_npow(s, r, (e - 1) as nat);
        }
    }
}

/// A prime s dividing prod_from(fs, i), with every fs[j].0 prime, is some fs[j].0 with j >= i.
#[verifier::spinoff_prover]
proof fn lemma_prime_dvd_prod(s: nat, fs: Seq<(nat, nat)>, i: nat) -> (j: int)
    requires
        is_prime(s),
        prod_from(fs, i) % s == 0,
        forall|k: int| 0 <= k < fs.len() ==> is_prime(#[trigger] fs[k].0),
    ensures
        i <= j < fs.len(),
        fs[j].0 == s,
    decreases fs.len() - i,
{
    if i >= fs.len() {
        lemma_small_mod(1, s);
        assert(false);
        0
    } else {
        let r = fs[i as int].0;
        lemma_euclid_prime(s, npow(r, fs[i as int].1), prod_from(fs, i + 1));
        if npow(r, fs[i as int].1) % s == 0 {
            lemma_prime_dvd_npow(s, r, fs[i as int].1);
            assert(is_prime(r));
            lemma_prime_divisor_cases(r, s);
            i as int
        } else {
            lemma_prime_dvd_prod(s, fs, i + 1)
        }
    }
}

/// 1 < D | prod_pow(fs), every r_i prime, imply some r_i | D.
pub(crate) proof fn lemma_divisor_hits_factor(D: nat, fs: Seq<(nat, nat)>) -> (i: int)
    requires
        D > 1,
        prod_pow(fs) % D == 0,
        forall|k: int| 0 <= k < fs.len() ==> is_prime(#[trigger] fs[k].0),
    ensures
        0 <= i < fs.len(),
        D % fs[i].0 == 0,
{
    let s = lemma_prime_divisor(D);
    lemma_dvd_trans(s as int, D as int, prod_pow(fs) as int);
    lemma_prime_dvd_prod(s, fs, 0)
}

/// trial_from(r, d) rules out every m in [d, r) with m^2 <= r.
#[verifier::spinoff_prover]
proof fn lemma_trial_from(r: nat, d: nat, m: nat)
    requires
        trial_from(r, d),
        2 <= d <= m,
        m < r,
        m * m <= r,
    ensures
        r % m != 0,
    decreases m - d,
{
    assert(d * d <= m * m) by (nonlinear_arith)
        requires
            0 <= d <= m,
    ;
    if d < m {
        lemma_trial_from(r, d + 1, m);
    }
}

/// Chunked trial division: [lo, hi) clear and trial_from(r, hi) give trial_from(r, lo).
pub(crate) proof fn lemma_trial_seg(r: nat, lo: nat, hi: nat)
    requires
        lo <= hi,
        trial_seg(r, lo, hi),
        trial_from(r, hi),
    ensures
        trial_from(r, lo),
    decreases hi - lo,
{
    if lo < hi {
        lemma_trial_seg(r, lo + 1, hi);
    }
}

pub(crate) proof fn lemma_trial_prime(r: nat)
    requires
        r >= 2,
        trial_ok(r),
    ensures
        is_prime(r),
{
    assert forall|j: nat| 1 < j < r implies #[trigger] (r % j) != 0 by {
        if r % j == 0 {
            let c = r / j;
            lemma_fundamental_div_mod(r as int, j as int);
            assert(r == j * c);
            assert(c >= 2) by (nonlinear_arith)
                requires
                    r == j * c,
                    1 < j < r,
            ;
            lemma_mul_is_commutative(j as int, c as int);
            lemma_mod_multiples_basic(j as int, c as int);
            let m = if j <= c { j } else { c };
            assert(m * m <= j * c) by (nonlinear_arith)
                requires
                    0 <= m <= j,
                    m <= c,
            ;
            assert(r % m == 0);
            lemma_trial_from(r, 2, m);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Lucas
// ---------------------------------------------------------------------------------------------

/// The per-factor facts of lucas_fs_ok, at index j.
#[verifier::spinoff_prover]
proof fn lemma_lucas_fs_at(q: nat, a: int, fs: Seq<(nat, nat)>, i: nat, j: int)
    requires
        lucas_fs_ok(q, a, fs, i),
        i <= j < fs.len(),
    ensures
        fs[j].0 > 1,
        (q - 1) % (fs[j].0 as int) == 0,
        powmod(a, ((q - 1) / (fs[j].0 as int)) as nat, q as int) != 1,
    decreases fs.len() - i,
{
    if j > i {
        lemma_lucas_fs_at(q, a, fs, i + 1, j);
    }
}

/// No exponent 0 < d < q - 1 has a^d == 1 mod q.
proof fn lemma_lucas_order(q: nat, a: int, fs: Seq<(nat, nat)>, d: nat)
    requires
        lucas_ok(q, a, fs),
        forall|k: int| 0 <= k < fs.len() ==> is_prime(#[trigger] fs[k].0),
        0 < d < q - 1,
    ensures
        pow(a, d) % (q as int) != 1,
{
    let n = (q - 1) as nat;
    let qi = q as int;
    if pow(a, d) % qi == 1 {
        lemma_powmod(a, n, qi);
        lemma_gcd_divides(d, n);
        lemma_pow_gcd(a, d, n, qi);
        let g = gcd(d, n);
        lemma_dvd_le(g as int, d as int);
        let big_d = n / g;
        lemma_fundamental_div_mod(n as int, g as int);
        // n == g * big_d, and big_d > 1 since g < n
        assert(big_d > 1) by (nonlinear_arith)
            requires
                n == g * big_d,
                0 < g < n,
        ;
        lemma_mod_multiples_basic(g as int, big_d as int);
        lemma_mul_is_commutative(g as int, big_d as int);
        let i = lemma_divisor_hits_factor(big_d, fs);
        let r = fs[i].0;
        lemma_lucas_fs_at(q, a, fs, 0, i);
        let c = big_d / r;
        lemma_fundamental_div_mod(big_d as int, r as int);
        // n == r * (g * c), so n / r == g * c
        assert(n == r * (g * c)) by (nonlinear_arith)
            requires
                n == g * big_d,
                big_d == r * c,
        ;
        lemma_div_multiples_vanish((g * c) as int, r as int);
        lemma_pow_mul_one(a, g, c, qi);
        lemma_powmod(a, (n / r) as nat, qi);
    }
}

/// a^i mod q is nonzero, and i |-> a^i mod q is injective on [0, q - 1).
proof fn lemma_lucas_inj(q: nat, a: int, fs: Seq<(nat, nat)>, i: nat, j: nat)
    requires
        lucas_ok(q, a, fs),
        forall|k: int| 0 <= k < fs.len() ==> is_prime(#[trigger] fs[k].0),
        i <= j < q - 1,
    ensures
        pow(a, i) % (q as int) != 0,
        pow(a, i) % (q as int) == pow(a, j) % (q as int) ==> i == j,
{
    let n = (q - 1) as nat;
    let qi = q as int;
    lemma_powmod(a, n, qi);
    let u = pow(a, (n - j) as nat);
    // u a^j == a^n and u a^i == a^(n - (j - i))
    lemma_pow_adds(a, (n - j) as nat, j);
    lemma_pow_adds(a, (n - j) as nat, i);
    let e = (n - j + i) as nat;
    lemma_mul_mod_noop_general(u, pow(a, i), qi);
    lemma_mul_mod_noop_general(u, pow(a, j), qi);
    if pow(a, i) % qi == 0 {
        // a^e == u a^i == 0 mod q, so a^n == a^e a^(j - i) == 0 mod q
        lemma_pow_adds(a, e, (j - i) as nat);
        lemma_mul_mod_noop_general(pow(a, e), pow(a, (j - i) as nat), qi);
        lemma_mul_basics(u);
        lemma_mul_basics(pow(a, (j - i) as nat));
        lemma_small_mod(0, qi as nat);
    }
    if pow(a, i) % qi == pow(a, j) % qi && i < j {
        // a^e == a^n == 1 mod q with 0 < e < n
        lemma_small_mod(1, qi as nat);
        lemma_lucas_order(q, a, fs, e);
    }
}

/// Every x in [1, q) is a^i mod q for some i in [0, q - 1).
proof fn lemma_lucas_onto(q: nat, a: int, fs: Seq<(nat, nat)>, x: int) -> (i: nat)
    requires
        lucas_ok(q, a, fs),
        forall|k: int| 0 <= k < fs.len() ==> is_prime(#[trigger] fs[k].0),
        1 <= x < q,
    ensures
        i < q - 1,
        pow(a, i) % (q as int) == x,
{
    broadcast use Set::lemma_map_contains;

    let qi = q as int;
    let f = |i: int| pow(a, i as nat) % qi;
    let dom = set_int_range(0, qi - 1);
    let img = dom.map(f);
    let tgt = set_int_range(1, qi);
    lemma_int_range(0, qi - 1);
    lemma_int_range(1, qi);
    assert(dom.injective_on(f)) by {
        assert forall|i1: int, i2: int|
            dom.contains(i1) && dom.contains(i2) && #[trigger] f(i1) == #[trigger] f(i2) implies i1
            == i2 by {
            if i1 <= i2 {
                lemma_lucas_inj(q, a, fs, i1 as nat, i2 as nat);
            } else {
                lemma_lucas_inj(q, a, fs, i2 as nat, i1 as nat);
            }
        }
    }
    lemma_map_size(dom, img, f);
    assert(img.subset_of(tgt)) by {
        assert forall|y: int| img.contains(y) implies tgt.contains(y) by {
            let i = choose|i: int| dom.contains(i) && y == f(i);
            lemma_mod_bound(pow(a, i as nat), qi);
            lemma_lucas_inj(q, a, fs, i as nat, i as nat);
        }
    }
    lemma_subset_equality(img, tgt);
    assert(img.contains(x));
    let i = choose|i: int| dom.contains(i) && x == f(i);
    i as nat
}

/// Lucas: a certificate with prime factors proves q prime and Fermat's little theorem mod q.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_lucas(q: nat, a: int, fs: Seq<(nat, nat)>)
    requires
        lucas_ok(q, a, fs),
        forall|i: int| 0 <= i < fs.len() ==> is_prime(#[trigger] fs[i].0),
    ensures
        is_prime(q),
        forall|x: int| x % (q as int) != 0 ==> #[trigger] (pow(x, (q - 1) as nat) % (q as int)) == 1,
{
    assert forall|k: nat| 1 < k < q implies #[trigger] (q % k) != 0 by {
        lemma_lucas_no_divisor(q, a, fs, k);
    }
    assert forall|x: int| x % (q as int) != 0 implies #[trigger] (pow(x, (q - 1) as nat) % (
    q as int)) == 1 by {
        lemma_lucas_flt(q, a, fs, x);
    }
}

proof fn lemma_lucas_no_divisor(q: nat, a: int, fs: Seq<(nat, nat)>, k: nat)
    requires
        lucas_ok(q, a, fs),
        forall|i: int| 0 <= i < fs.len() ==> is_prime(#[trigger] fs[i].0),
        1 < k < q,
    ensures
        q % k != 0,
{
    let n = (q - 1) as nat;
    let qi = q as int;
    if q % k == 0 {
        let i = lemma_lucas_onto(q, a, fs, k as int);
        let w = pow(a, (n - i) as nat);
        lemma_pow_adds(a, i, (n - i) as nat);
        lemma_powmod(a, n, qi);
        // (k w) % q == (a^i w) % q == a^n % q == 1
        lemma_mul_mod_noop_general(pow(a, i), w, qi);
        let c = q / k;
        lemma_fundamental_div_mod(q as int, k as int);
        assert(c > 0) by (nonlinear_arith)
            requires
                q == k * c,
                q > 0,
                k > 0,
        ;
        // ((k w) % (k c)) % k == (k w) % k == 0, but the left side is 1 % k == 1
        lemma_mod_mod(k * w, k as int, c as int);
        lemma_mul_is_commutative(k as int, w);
        lemma_mod_multiples_basic(w, k as int);
        lemma_small_mod(1, k);
    }
}

proof fn lemma_lucas_flt(q: nat, a: int, fs: Seq<(nat, nat)>, x: int)
    requires
        lucas_ok(q, a, fs),
        forall|i: int| 0 <= i < fs.len() ==> is_prime(#[trigger] fs[i].0),
        x % (q as int) != 0,
    ensures
        pow(x, (q - 1) as nat) % (q as int) == 1,
{
    let n = (q - 1) as nat;
    let qi = q as int;
    lemma_mod_bound(x, qi);
    let i = lemma_lucas_onto(q, a, fs, x % qi);
    lemma_powmod(a, n, qi);
    // x^n == (x % q)^n == (a^i % q)^n == (a^i)^n == (a^n)^i == 1 mod q
    lemma_pow_mod_noop(x, n, qi);
    lemma_pow_mod_noop(pow(a, i), n, qi);
    lemma_pow_multiplies(a, i, n);
    lemma_mul_is_commutative(i as int, n as int);
    lemma_pow_mul_one(a, n, i, qi);
}

/// Lucas on q = 7, a = 3, 7 - 1 = 2 * 3.
proof fn lemma_lucas_smoke() {
    assert(lucas_ok(7, 3, seq![(2nat, 1nat), (3nat, 1nat)])) by (compute_only);
    lemma_trial_prime(2);
    lemma_trial_prime(3);
    let fs = seq![(2nat, 1nat), (3nat, 1nat)];
    lemma_lucas(7, 3, fs);
    assert(is_prime(7));
    assert(5int % (7nat as int) != 0);
    assert(pow(5, (7nat - 1) as nat) % (7nat as int) == 1);
}

} // verus!
