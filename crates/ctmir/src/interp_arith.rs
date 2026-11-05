//! Exec integer arithmetic proved equal to `ctcore::sem`'s opaque `binop`, `unop` and `cast`, for
//! the verified interpreter (`interp`). Every op works on the unsigned readings `uval` of its
//! operands modulo `md(t) = 2^bits(t)`; a signed reading `ival` is `uval` or `uval - md(t)`, so
//! each spec formula reduces to one on the unsigned readings.
#[cfg(verus_keep_ghost)]
use ctcore::sem::{abs, b2i, binop, bits, cast, ival, signed, tdiv, trem, trunc, unop, uval};
use ctcore::syntax::{BinOp, IntTy, UnOp};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::mul::lemma_mul_upper_bound;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

pub spec const M128: int = u128::MAX as int + 1;

/// `2^bits(t)` as a literal.
pub open spec fn md(t: IntTy) -> int {
    match t {
        IntTy::U8 | IntTy::I8 => 0x100,
        IntTy::U16 | IntTy::I16 => 0x1_0000,
        IntTy::U32 | IntTy::I32 => 0x1_0000_0000,
        IntTy::U64 | IntTy::I64 | IntTy::Usize | IntTy::Isize => 0x1_0000_0000_0000_0000,
        IntTy::U128 | IntTy::I128 => M128,
        IntTy::Bool => 2,
    }
}

pub open spec fn wide(t: IntTy) -> bool { t is U128 || t is I128 }

pub proof fn lemma_md(t: IntTy)
    ensures pow2(bits(t)) == md(t), pow2((bits(t) - 1) as nat) * 2 == md(t), bits(t) >= 1, wide(t) <==> md(t) == M128,
        !wide(t) ==> md(t) <= 0x1_0000_0000_0000_0000,
{
    lemma2_to64();
    lemma2_to64_rest();
    lemma_pow2_adds(64, 64);
    lemma_pow2_adds(63, 64);
}

/// The readings of `a` at `t`: `u = uval`, `x = ival`, with `x` congruent to `u`.
pub proof fn lemma_read(t: IntTy, a: u128)
    ensures ({
        let (m, u, x) = (md(t), uval(t, a), ival(t, a));
        &&& 0 <= u < m && m >= 2 && m % 2 == 0
        &&& u == (a as int) % m
        &&& signed(t) ==> (if u >= m / 2 { x == u - m } else { x == u })
        &&& !signed(t) ==> x == u
        &&& x % m == u
        &&& -(m / 2) <= x < m
    }),
{
    lemma_md(t);
    let (m, u) = (md(t), uval(t, a));
    lemma_mod_bound(a as int, m);
    if ival(t, a) != u {
        lemma_mod_sub_multiples_vanish(u, m);
    }
    lemma_small_mod(u as nat, m as nat);
}

/// `x % m` for `x` congruent to `u` (both readings).
proof fn lemma_cong_add(m: int, u: int, v: int, x: int, y: int)
    requires m > 0, x % m == u % m, y % m == v % m,
    ensures (x + y) % m == (u + v) % m, (x - y) % m == (u - v) % m, (x * y) % m == (u * v) % m, (-x) % m == (-u) % m,
{
    lemma_add_mod_noop(x, y, m);
    lemma_add_mod_noop(u, v, m);
    lemma_sub_mod_noop(x, y, m);
    lemma_sub_mod_noop(u, v, m);
    lemma_mul_mod_noop(x, y, m);
    lemma_mul_mod_noop(u, v, m);
    lemma_sub_mod_noop(0, x, m);
    lemma_sub_mod_noop(0, u, m);
}

// ------------------------------------------------------------------ exec readings

pub fn bits_exec(t: &IntTy) -> (r: u32)
    ensures r as nat == bits(*t),
{
    match t {
        IntTy::U8 | IntTy::I8 => 8,
        IntTy::U16 | IntTy::I16 => 16,
        IntTy::U32 | IntTy::I32 => 32,
        IntTy::U64 | IntTy::I64 | IntTy::Usize | IntTy::Isize => 64,
        IntTy::U128 | IntTy::I128 => 128,
        IntTy::Bool => 1,
    }
}

pub fn is_wide(t: &IntTy) -> (r: bool)
    ensures r == wide(*t),
{
    match t { IntTy::U128 | IntTy::I128 => true, _ => false }
}

pub fn is_signed(t: &IntTy) -> (r: bool)
    ensures r == signed(*t),
{
    match t { IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize => true, _ => false }
}

/// `md(t)` for a type narrower than 128 bits.
pub fn md_exec(t: &IntTy) -> (r: u128)
    requires !wide(*t),
    ensures r == md(*t),
{
    match t {
        IntTy::U8 | IntTy::I8 => 0x100,
        IntTy::U16 | IntTy::I16 => 0x1_0000,
        IntTy::U32 | IntTy::I32 => 0x1_0000_0000,
        IntTy::U64 | IntTy::I64 | IntTy::Usize | IntTy::Isize => 0x1_0000_0000_0000_0000,
        IntTy::Bool => 2,
        _ => 0,
    }
}

/// Half of `md(t)`: the sign bit.
pub fn half_exec(t: &IntTy) -> (r: u128)
    ensures r * 2 == md(*t),
{
    match t {
        IntTy::U8 | IntTy::I8 => 0x80,
        IntTy::U16 | IntTy::I16 => 0x8000,
        IntTy::U32 | IntTy::I32 => 0x8000_0000,
        IntTy::U64 | IntTy::I64 | IntTy::Usize | IntTy::Isize => 0x8000_0000_0000_0000,
        IntTy::U128 | IntTy::I128 => 0x8000_0000_0000_0000_0000_0000_0000_0000,
        IntTy::Bool => 1,
    }
}

pub fn uval_exec(t: &IntTy, a: u128) -> (r: u128)
    ensures r == uval(*t, a),
{
    proof { lemma_read(*t, a); lemma_md(*t); lemma_small_mod(a as nat, M128 as nat); }
    if is_wide(t) { a } else { a % md_exec(t) }
}

/// `(-q) % md(t)` for `0 <= q <= md(t)`, as `u128`.
fn neg_mod(t: &IntTy, q: u128) -> (r: u128)
    requires q <= md(*t),
    ensures r as int == (-(q as int)) % md(*t),
{
    proof { lemma_md(*t); }
    if q == 0 {
        0
    } else {
        proof { lemma_fundamental_div_mod_converse(-(q as int), md(*t), -1, md(*t) - q); }
        if is_wide(t) { 0u128.wrapping_sub(q) } else { md_exec(t) - q }
    }
}

/// `|ival(t, a)|` as `u128`, and whether `ival(t, a) < 0`.
fn abs_exec(t: &IntTy, a: u128) -> (r: (u128, bool))
    ensures r.0 as int == abs(ival(*t, a)), r.1 == (ival(*t, a) < 0), r.0 as int <= md(*t),
{
    proof { lemma_read(*t, a); lemma_md(*t); }
    let u = uval_exec(t, a);
    if is_signed(t) && u >= half_exec(t) {
        (if is_wide(t) { 0u128.wrapping_sub(u) } else { md_exec(t) - u }, true)
    } else {
        (u, false)
    }
}

/// The order key of `a` at `t`: `ival(t, a) + md(t) / 2` for signed `t`, `uval` otherwise.
fn key_exec(t: &IntTy, a: u128) -> (r: u128)
    ensures r as int == (if signed(*t) { ival(*t, a) + md(*t) / 2 } else { ival(*t, a) }),
{
    proof { lemma_read(*t, a); lemma_md(*t); }
    let u = uval_exec(t, a);
    if is_signed(t) {
        let h = half_exec(t);
        if u >= h { u - h } else { u + h }
    } else {
        u
    }
}

/// `pow2(s)` for `s < 128`.
fn pow2_exec(s: u32) -> (r: u128)
    requires s < 128,
    ensures r as int == pow2(s as nat), r >= 1,
{
    let mut p: u128 = 1;
    let mut i: u32 = 0;
    proof { lemma2_to64(); }
    while i < s
        invariant i <= s < 128, p as int == pow2(i as nat), p >= 1,
        decreases s - i,
    {
        proof {
            lemma_pow2_unfold((i + 1) as nat);
            lemma_pow2_strictly_increases((i + 1) as nat, 128);
            lemma2_to64_rest();
            lemma_pow2_adds(64, 64);
        }
        p = p * 2;
        i = i + 1;
    }
    p
}

// ------------------------------------------------------------------ binop

proof fn lemma_add_sub_mul(op: BinOp, t: IntTy, a: u128, b: u128)
    requires op is Add || op is Sub || op is Mul,
    ensures binop(op, t, a, b) as int == (match op {
        BinOp::Add => (uval(t, a) + uval(t, b)) % md(t),
        BinOp::Sub => (uval(t, a) - uval(t, b)) % md(t),
        _ => (uval(t, a) * uval(t, b)) % md(t),
    }),
{
    reveal(binop);
    lemma_read(t, a);
    lemma_read(t, b);
    lemma_md(t);
    let m = md(t);
    lemma_small_mod(uval(t, a) as nat, m as nat);
    lemma_small_mod(uval(t, b) as nat, m as nat);
    lemma_cong_add(m, uval(t, a), uval(t, b), ival(t, a), ival(t, b));
    lemma_mod_bound(uval(t, a) + uval(t, b), m);
    lemma_mod_bound(uval(t, a) - uval(t, b), m);
    lemma_mod_bound(uval(t, a) * uval(t, b), m);
}

proof fn lemma_bitwise(op: BinOp, t: IntTy, a: u128, b: u128)
    requires op is BitXor || op is BitAnd || op is BitOr,
    ensures binop(op, t, a, b) as int == (match op {
        BinOp::BitXor => (a ^ b) as int % md(t),
        BinOp::BitAnd => (a & b) as int % md(t),
        _ => (a | b) as int % md(t),
    }),
{
    reveal(binop);
    lemma_md(t);
    lemma_mod_bound((a ^ b) as int, md(t));
    lemma_mod_bound((a & b) as int, md(t));
    lemma_mod_bound((a | b) as int, md(t));
}

/// `Div`/`Rem` on the absolute values and signs.
proof fn lemma_div_rem(op: BinOp, t: IntTy, a: u128, b: u128)
    requires op is Div || op is Rem, uval(t, b) != 0,
    ensures ({
        let (x, y) = (ival(t, a), ival(t, b));
        let q = abs(x) / abs(y);
        let r = abs(x) % abs(y);
        &&& y != 0 && abs(y) > 0
        &&& 0 <= q <= md(t) && 0 <= r < md(t) && (q < md(t) || ((x < 0) != (y < 0)))
        &&& op is Div ==> binop(op, t, a, b) as int == (if (x < 0) != (y < 0) { (-q) % md(t) } else { q % md(t) })
        &&& op is Rem ==> binop(op, t, a, b) as int == (if x < 0 { (-r) % md(t) } else { r % md(t) })
    }),
{
    reveal(binop);
    lemma_read(t, a);
    lemma_read(t, b);
    lemma_md(t);
    let (x, y) = (ival(t, a), ival(t, b));
    let m = md(t);
    assert(abs(x) <= m / 2 || (!signed(t) && abs(x) < m));
    assert(abs(y) >= 1);
    lemma_div_is_ordered_by_denominator(abs(x), 1, abs(y));
    lemma_div_basics(abs(x));
    lemma_mod_bound(abs(x), abs(y));
    let q = abs(x) / abs(y);
    let r = abs(x) % abs(y);
    lemma_mod_bound(-q, m);
    lemma_mod_bound(q, m);
    lemma_mod_bound(-r, m);
    lemma_mod_bound(r, m);
    assert(tdiv(x, y) == (if (x < 0) != (y < 0) { -q } else { q }));
    assert(trem(x, y) == (if x < 0 { -r } else { r }));
    assert(trunc(t, tdiv(x, y)) as int == tdiv(x, y) % m);
    assert(trunc(t, trem(x, y)) as int == trem(x, y) % m);
}

/// `Shl`: `(uval(a) * 2^s) % md(t)`, `s` the masked amount.
proof fn lemma_shl(t: IntTy, a: u128, b: u128)
    ensures ({
        let s = (uval(t, b) % (bits(t) as int)) as nat;
        &&& s < bits(t)
        &&& binop(BinOp::Shl, t, a, b) as int == (uval(t, a) * pow2(s)) % md(t)
    }),
{
    reveal(binop);
    lemma_read(t, a);
    lemma_read(t, b);
    lemma_md(t);
    let m = md(t);
    let s = (uval(t, b) % (bits(t) as int)) as nat;
    lemma_mod_bound(uval(t, b), bits(t) as int);
    lemma_small_mod(uval(t, a) as nat, m as nat);
    lemma_mul_mod_noop(ival(t, a), pow2(s) as int, m);
    lemma_mul_mod_noop(uval(t, a), pow2(s) as int, m);
    lemma_mod_bound(uval(t, a) * pow2(s), m);
}

/// `Shr`: the floor of `ival(a) / 2^s`, read back modulo `md(t)`.
proof fn lemma_shr(t: IntTy, a: u128, b: u128)
    ensures ({
        let s = (uval(t, b) % (bits(t) as int)) as nat;
        let (u, p, m) = (uval(t, a), pow2(s) as int, md(t));
        &&& s < bits(t) && p >= 1
        &&& binop(BinOp::Shr, t, a, b) as int == (if ival(t, a) < 0 { m - 1 - (m - u - 1) / p } else { u / p })
        &&& 0 <= (m - u - 1) / p <= m - u - 1 && u / p <= u
    }),
{
    reveal(binop);
    lemma_read(t, a);
    lemma_read(t, b);
    lemma_md(t);
    let s = (uval(t, b) % (bits(t) as int)) as nat;
    lemma_mod_bound(uval(t, b), bits(t) as int);
    lemma_pow2_pos(s);
    let (u, x, p, m) = (uval(t, a), ival(t, a), pow2(s) as int, md(t));
    lemma_div_is_ordered_by_denominator(u, 1, p);
    lemma_div_basics(u);
    lemma_div_pos_is_pos(u, p);
    if x < 0 {
        let d = m - u - 1;
        lemma_div_is_ordered_by_denominator(d, 1, p);
        lemma_div_basics(d);
        lemma_div_pos_is_pos(d, p);
        let k = d / p;
        lemma_fundamental_div_mod(d, p);
        lemma_mod_bound(d, p);
        assert(x == (-k - 1) * p + (p - 1 - d % p)) by (nonlinear_arith)
            requires x == u - m, d == m - u - 1, d == p * k + d % p;
        lemma_fundamental_div_mod_converse(x, p, -k - 1, p - 1 - d % p);
        lemma_fundamental_div_mod_converse(x / p, m, -1, m - 1 - k);
    } else {
        lemma_small_mod((u / p) as nat, m as nat);
    }
}

proof fn lemma_cmp(op: BinOp, t: IntTy, a: u128, b: u128)
    requires op is Eq || op is Ne || op is Lt || op is Le || op is Gt || op is Ge,
    ensures ({
        let (ka, kb) = (if signed(t) { ival(t, a) + md(t) / 2 } else { ival(t, a) }, if signed(t) { ival(t, b) + md(t) / 2 } else { ival(t, b) });
        binop(op, t, a, b) == match op {
            BinOp::Eq => b2i(uval(t, a) == uval(t, b)),
            BinOp::Ne => b2i(uval(t, a) != uval(t, b)),
            BinOp::Lt => b2i(ka < kb),
            BinOp::Le => b2i(ka <= kb),
            BinOp::Gt => b2i(ka > kb),
            _ => b2i(ka >= kb),
        }
    }),
{
    reveal(binop);
    lemma_read(t, a);
    lemma_read(t, b);
}

fn arith_exec(op: &BinOp, t: &IntTy, a: u128, b: u128) -> (r: u128)
    requires *op is Add || *op is Sub || *op is Mul,
    ensures r == binop(*op, *t, a, b),
{
    proof { lemma_read(*t, a); lemma_read(*t, b); lemma_md(*t); lemma_add_sub_mul(*op, *t, a, b); }
    let ua = uval_exec(t, a);
    let ub = uval_exec(t, b);
    if is_wide(t) {
        match op {
            BinOp::Add => {
                proof { if ua + ub >= M128 { lemma_fundamental_div_mod_converse(ua + ub, M128, 1, ua + ub - M128); } else { lemma_small_mod((ua + ub) as nat, M128 as nat); } }
                ua.wrapping_add(ub)
            },
            BinOp::Sub => {
                proof { if ua < ub { lemma_fundamental_div_mod_converse(ua - ub, M128, -1, M128 + ua - ub); } else { lemma_small_mod((ua - ub) as nat, M128 as nat); } }
                ua.wrapping_sub(ub)
            },
            _ => ua.wrapping_mul(ub),
        }
    } else {
        let m = md_exec(t);
        match op {
            BinOp::Add => (ua + ub) % m,
            BinOp::Sub => {
                proof { lemma_mod_add_multiples_vanish(ua - ub, m as int); }
                (ua + (m - ub)) % m
            },
            _ => {
                proof { lemma_mul_upper_bound(ua as int, (m - 1) as int, ub as int, (m - 1) as int); }
                assert((m - 1) * (m - 1) <= u128::MAX) by (nonlinear_arith) requires m <= 0x1_0000_0000_0000_0000;
                (ua * ub) % m
            },
        }
    }
}

fn bitwise_exec(op: &BinOp, t: &IntTy, a: u128, b: u128) -> (r: u128)
    requires *op is BitXor || *op is BitAnd || *op is BitOr,
    ensures r == binop(*op, *t, a, b),
{
    proof { lemma_md(*t); lemma_bitwise(*op, *t, a, b); }
    let v = match op { BinOp::BitXor => a ^ b, BinOp::BitAnd => a & b, _ => a | b };
    if is_wide(t) {
        proof { lemma_small_mod(v as nat, M128 as nat); }
        v
    } else {
        v % md_exec(t)
    }
}

fn divrem_exec(op: &BinOp, t: &IntTy, a: u128, b: u128) -> (r: u128)
    requires *op is Div || *op is Rem,
    ensures r == binop(*op, *t, a, b),
{
    proof { lemma_read(*t, a); lemma_read(*t, b); lemma_md(*t); }
    if uval_exec(t, b) == 0 {
        proof { reveal(binop); }
        return 0;
    }
    proof { lemma_div_rem(*op, *t, a, b); }
    let (xa, na) = abs_exec(t, a);
    let (yb, nb) = abs_exec(t, b);
    let (v, neg) = match op { BinOp::Div => (xa / yb, na != nb), _ => (xa % yb, na) };
    if neg {
        neg_mod(t, v)
    } else {
        proof { lemma_small_mod(v as nat, md(*t) as nat); }
        v
    }
}

fn shl_exec(t: &IntTy, a: u128, b: u128) -> (r: u128)
    ensures r == binop(BinOp::Shl, *t, a, b),
{
    proof { lemma_read(*t, a); lemma_read(*t, b); lemma_md(*t); lemma_shl(*t, a, b); }
    let ua = uval_exec(t, a);
    let s = (uval_exec(t, b) % (bits_exec(t) as u128)) as u32;
    let p = pow2_exec(s);
    if is_wide(t) {
        ua.wrapping_mul(p)
    } else {
        let m = md_exec(t);
        proof {
            lemma_pow2_strictly_increases(s as nat, 64);
            lemma2_to64();
            lemma_mul_upper_bound(ua as int, (m - 1) as int, p as int, 0x1_0000_0000_0000_0000);
        }
        assert((m - 1) * 0x1_0000_0000_0000_0000 <= u128::MAX) by (nonlinear_arith) requires m <= 0x1_0000_0000_0000_0000;
        (ua * p) % m
    }
}

fn shr_exec(t: &IntTy, a: u128, b: u128) -> (r: u128)
    ensures r == binop(BinOp::Shr, *t, a, b),
{
    proof { lemma_read(*t, a); lemma_read(*t, b); lemma_md(*t); lemma_shr(*t, a, b); }
    let ua = uval_exec(t, a);
    let s = (uval_exec(t, b) % (bits_exec(t) as u128)) as u32;
    let p = pow2_exec(s);
    let (_, neg) = abs_exec(t, a);
    if neg {
        if is_wide(t) { u128::MAX - (u128::MAX - ua) / p } else { md_exec(t) - 1 - (md_exec(t) - ua - 1) / p }
    } else {
        ua / p
    }
}

fn cmp_exec(op: &BinOp, t: &IntTy, a: u128, b: u128) -> (r: u128)
    requires *op is Eq || *op is Ne || *op is Lt || *op is Le || *op is Gt || *op is Ge,
    ensures r == binop(*op, *t, a, b),
{
    proof { lemma_cmp(*op, *t, a, b); }
    let (ua, ub) = (uval_exec(t, a), uval_exec(t, b));
    let (ka, kb) = (key_exec(t, a), key_exec(t, b));
    let c = match op {
        BinOp::Eq => ua == ub,
        BinOp::Ne => ua != ub,
        BinOp::Lt => ka < kb,
        BinOp::Le => ka <= kb,
        BinOp::Gt => ka > kb,
        _ => ka >= kb,
    };
    if c { 1 } else { 0 }
}

pub fn binop_exec(op: &BinOp, t: &IntTy, a: u128, b: u128) -> (r: u128)
    ensures r == binop(*op, *t, a, b),
{
    match op {
        BinOp::Add | BinOp::Sub | BinOp::Mul => arith_exec(op, t, a, b),
        BinOp::BitXor | BinOp::BitAnd | BinOp::BitOr => bitwise_exec(op, t, a, b),
        BinOp::Div | BinOp::Rem => divrem_exec(op, t, a, b),
        BinOp::Shl => shl_exec(t, a, b),
        BinOp::Shr => shr_exec(t, a, b),
        _ => cmp_exec(op, t, a, b),
    }
}

// ------------------------------------------------------------------ unop, cast

pub fn unop_exec(op: &UnOp, t: &IntTy, a: u128) -> (r: u128)
    ensures r == unop(*op, *t, a),
{
    proof { reveal(unop); lemma_read(*t, a); lemma_md(*t); }
    let ua = uval_exec(t, a);
    match op {
        UnOp::Not => {
            proof { lemma_small_mod((md(*t) - 1 - ua) as nat, md(*t) as nat); }
            if is_wide(t) { u128::MAX - ua } else { md_exec(t) - 1 - ua }
        },
        UnOp::Neg => {
            proof { lemma_small_mod(ua as nat, md(*t) as nat); lemma_cong_add(md(*t), ua as int, 0, ival(*t, a), 0); }
            neg_mod(t, ua)
        },
    }
}

pub fn cast_exec(from: &IntTy, to: &IntTy, a: u128) -> (r: u128)
    ensures r == cast(*from, *to, a),
{
    proof { reveal(cast); lemma_read(*from, a); lemma_md(*from); lemma_md(*to); }
    let ua = uval_exec(from, a);
    let (d, neg) = abs_exec(from, a);
    let (bf, bt) = (bits_exec(from), bits_exec(to));
    let ghost (mf, mt) = (md(*from), md(*to));
    if !neg {
        if is_wide(to) {
            proof { lemma_small_mod(ua as nat, M128 as nat); }
            ua
        } else {
            ua % md_exec(to)
        }
    } else if bt >= bf {
        // -mt < x < 0: x % mt == mt - |x|
        proof {
            if bt > bf { lemma_pow2_strictly_increases(bf as nat, bt as nat); }
            lemma_fundamental_div_mod_converse(ua - mf, mt, -1, mt - d);
        }
        if is_wide(to) { 0u128.wrapping_sub(d) } else { md_exec(to) - d }
    } else {
        // mt divides mf: x % mt == ua % mt
        proof {
            lemma_pow2_adds(bt as nat, (bf - bt) as nat);
            let c = pow2((bf - bt) as nat) as int;
            assert(mf == mt * c);
            lemma_mod_multiples_vanish(-c, ua as int, mt);
            assert(mt * (-c) + ua == ua - mf) by (nonlinear_arith) requires mf == mt * c;
        }
        ua % md_exec(to)
    }
}

} // verus!
