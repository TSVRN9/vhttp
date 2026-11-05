//! `print` (serde_json's compact writer, `json::print`) is injective: two values that print the
//! same bytes are equal up to views (`jeq`). So the value `parse` returns is the only one the dump
//! is the printing of. The proof reads `print`'s output left to right: every value is
//! self-delimiting given what may follow it (`delim`: nothing, `,`, `]` or `}`), a number because
//! that follower is not a digit.
#[allow(unused_imports)]
use crate::json::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ equality up to views

/// `a` and `b` are the same JSON value, comparing strings and keys by their bytes.
pub open spec fn jeq(a: Json, b: Json) -> bool
    decreases a,
{
    match a {
        Json::Str(x) => b is Str && x@ == b->Str_0@,
        Json::Arr(x) => b is Arr && jeqs(x@, b->Arr_0@),
        Json::Obj(x) => b is Obj && jeqf(x@, b->Obj_0@),
        _ => a == b,
    }
}

pub open spec fn jeqs(s: Seq<Json>, t: Seq<Json>) -> bool
    decreases s,
{
    s.len() == t.len() && (s.len() == 0 || (jeq(s[0], t[0]) && jeqs(s.drop_first(), t.drop_first())))
}

pub open spec fn jeqf(s: Seq<(Vec<u8>, Json)>, t: Seq<(Vec<u8>, Json)>) -> bool
    decreases s,
{
    s.len() == t.len() && (s.len() == 0 || (s[0].0@ == t[0].0@ && jeq(s[0].1, t[0].1) && jeqf(s.drop_first(), t.drop_first())))
}

// ------------------------------------------------------------------ forward forms of the printer

/// Array elements, comma-separated, read from the front.
pub open spec fn fe(s: Seq<Json>) -> Seq<u8> { if s.len() == 0 { seq![] } else { print(s[0]) + ft(s.drop_first()) } }

pub open spec fn ft(t: Seq<Json>) -> Seq<u8>
    decreases t.len(),
{
    if t.len() == 0 { seq![] } else { seq![44u8] + print(t[0]) + ft(t.drop_first()) }
}

pub open spec fn fitem(e: (Vec<u8>, Json)) -> Seq<u8> { print_str(e.0@) + seq![58u8] + print(e.1) }

pub open spec fn ffe(s: Seq<(Vec<u8>, Json)>) -> Seq<u8> { if s.len() == 0 { seq![] } else { fitem(s[0]) + fft(s.drop_first()) } }

pub open spec fn fft(t: Seq<(Vec<u8>, Json)>) -> Seq<u8>
    decreases t.len(),
{
    if t.len() == 0 { seq![] } else { seq![44u8] + fitem(t[0]) + fft(t.drop_first()) }
}

proof fn lemma_ft_push(t: Seq<Json>, x: Json)
    ensures ft(t.push(x)) == ft(t) + seq![44u8] + print(x),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(t.push(x).drop_first() =~= Seq::<Json>::empty());
        assert(ft(t.push(x)) =~= seq![44u8] + print(x) + ft(Seq::<Json>::empty()));
        assert(ft(t.push(x)) =~= ft(t) + seq![44u8] + print(x));
    } else {
        assert(t.push(x).drop_first() =~= t.drop_first().push(x));
        lemma_ft_push(t.drop_first(), x);
        assert(ft(t.push(x)) =~= ft(t) + seq![44u8] + print(x));
    }
}

proof fn lemma_fft_push(t: Seq<(Vec<u8>, Json)>, x: (Vec<u8>, Json))
    ensures fft(t.push(x)) == fft(t) + seq![44u8] + fitem(x),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(t.push(x).drop_first() =~= Seq::<(Vec<u8>, Json)>::empty());
        assert(fft(t.push(x)) =~= seq![44u8] + fitem(x) + fft(Seq::<(Vec<u8>, Json)>::empty()));
        assert(fft(t.push(x)) =~= fft(t) + seq![44u8] + fitem(x));
    } else {
        assert(t.push(x).drop_first() =~= t.drop_first().push(x));
        lemma_fft_push(t.drop_first(), x);
        assert(fft(t.push(x)) =~= fft(t) + seq![44u8] + fitem(x));
    }
}

/// `print_elems` (built from the back) is `fe`.
proof fn lemma_pe_fwd(s: Seq<Json>)
    ensures print_elems(s) == fe(s),
    decreases s.len(),
{
    if s.len() > 0 {
        let n = s.len() - 1;
        let s0 = s.subrange(0, n);
        lemma_pe_fwd(s0);
        if n == 0 {
            assert(s.drop_first() =~= Seq::<Json>::empty());
            assert(print_elems(s) =~= fe(s));
        } else {
            assert(s.drop_first() =~= s0.drop_first().push(s[n]));
            assert(s0[0] == s[0]);
            lemma_ft_push(s0.drop_first(), s[n]);
            assert(print_elems(s) =~= fe(s));
        }
    }
}

proof fn lemma_pf_fwd(s: Seq<(Vec<u8>, Json)>)
    ensures print_fields(s) == ffe(s),
    decreases s.len(),
{
    if s.len() > 0 {
        let n = s.len() - 1;
        let s0 = s.subrange(0, n);
        lemma_pf_fwd(s0);
        if n == 0 {
            assert(s.drop_first() =~= Seq::<(Vec<u8>, Json)>::empty());
            assert(print_fields(s) =~= ffe(s));
        } else {
            assert(s.drop_first() =~= s0.drop_first().push(s[n]));
            assert(s0[0] == s[0]);
            lemma_fft_push(s0.drop_first(), s[n]);
            assert(print_fields(s) =~= ffe(s));
        }
    }
}

proof fn lemma_esc_cat(a: Seq<u8>, b: Seq<u8>)
    ensures esc_all(a + b) == esc_all(a) + esc_all(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(esc_all(a) + esc_all(b) =~= esc_all(a));
    } else {
        let b0 = b.subrange(0, b.len() - 1);
        assert((a + b).subrange(0, (a + b).len() - 1) =~= a + b0);
        assert((a + b).last() == b.last());
        lemma_esc_cat(a, b0);
        assert(esc_all(a + b) =~= esc_all(a) + esc_all(b));
    }
}

proof fn lemma_esc_fwd(s: Seq<u8>)
    requires s.len() > 0,
    ensures esc_all(s) == esc(s[0]) + esc_all(s.drop_first()),
{
    assert(s =~= seq![s[0]] + s.drop_first());
    lemma_esc_cat(seq![s[0]], s.drop_first());
    assert(seq![s[0]].subrange(0, 0) =~= Seq::<u8>::empty());
    assert(esc_all(Seq::<u8>::empty()) =~= Seq::<u8>::empty());
    assert(seq![s[0]].last() == s[0]);
    assert(esc_all(seq![s[0]]) =~= esc_all(Seq::<u8>::empty()) + esc(s[0]));
    assert(esc_all(seq![s[0]]) =~= esc(s[0]));
}

// ------------------------------------------------------------------ bytes

proof fn lemma_cancel(a: Seq<u8>, x: Seq<u8>, b: Seq<u8>, y: Seq<u8>)
    requires a + x == b + y, a.len() == b.len(),
    ensures a == b, x == y,
{
    assert(a =~= (a + x).subrange(0, a.len() as int));
    assert(b =~= (b + y).subrange(0, b.len() as int));
    assert(x =~= (a + x).subrange(a.len() as int, (a + x).len() as int));
    assert(y =~= (b + y).subrange(b.len() as int, (b + y).len() as int));
}

pub open spec fn is_digit(c: u8) -> bool { 48 <= c && c <= 57 }

proof fn lemma_digits(n: nat)
    ensures digits(n).len() >= 1, forall|i: int| 0 <= i < digits(n).len() ==> is_digit(#[trigger] digits(n)[i]),
        (digits(n).len() == 1) == (n < 10),
    decreases n,
{
    if n >= 10 { lemma_digits(n / 10); }
}

proof fn lemma_digits_inj(a: nat, b: nat)
    requires digits(a) == digits(b),
    ensures a == b,
    decreases a,
{
    lemma_digits(a);
    lemma_digits(b);
    if a >= 10 && b >= 10 {
        let (da, db) = (digits(a / 10), digits(b / 10));
        let (la, lb) = (seq![(48 + a % 10) as u8], seq![(48 + b % 10) as u8]);
        assert(digits(a) == da + la);
        assert(digits(b) == db + lb);
        assert(da.len() == db.len());
        lemma_cancel(da, la, db, lb);
        assert(la[0] == lb[0]);
        assert(a % 10 == b % 10);
        lemma_digits_inj(a / 10, b / 10);
        assert(a == b) by (nonlinear_arith) requires a / 10 == b / 10, a % 10 == b % 10;
        assert(a == b);
    } else if a < 10 && b < 10 {
        assert(digits(a) == seq![(48 + a) as u8]);
        assert(digits(b) == seq![(48 + b) as u8]);
        let (ca, cb) = ((48 + a) as u8, (48 + b) as u8);
        assert(seq![ca][0] == ca && seq![cb][0] == cb);
        assert(ca == cb);
        assert(ca as int == 48 + a && cb as int == 48 + b);
        assert(a == b);
    } else {
        assert(digits(a).len() != digits(b).len());
        assert(false);
    }
}

/// What may follow a value: nothing, or `,`, `]`, `}`.
pub open spec fn delim(r: Seq<u8>) -> bool { r.len() == 0 || r[0] == 44u8 || r[0] == 93u8 || r[0] == 125u8 }

proof fn lemma_num(a: nat, b: nat, r1: Seq<u8>, r2: Seq<u8>)
    requires digits(a) + r1 == digits(b) + r2, delim(r1), delim(r2),
    ensures a == b, r1 == r2,
{
    lemma_digits(a);
    lemma_digits(b);
    let (x, y) = (digits(a), digits(b));
    if x.len() < y.len() {
        assert((x + r1).len() == (y + r2).len());
        assert((x + r1)[x.len() as int] == r1[0]);
        assert((y + r2)[x.len() as int] == y[x.len() as int]);
    } else if y.len() < x.len() {
        assert((x + r1).len() == (y + r2).len());
        assert((y + r2)[y.len() as int] == r2[0]);
        assert((x + r1)[y.len() as int] == x[y.len() as int]);
    }
    lemma_cancel(x, r1, y, r2);
    lemma_digits_inj(a, b);
}

/// An escaped byte is self-delimiting: `esc(c1) + x1 == esc(c2) + x2` gives `c1 == c2`.
proof fn lemma_esc(c1: u8, c2: u8, x1: Seq<u8>, x2: Seq<u8>)
    requires esc(c1) + x1 == esc(c2) + x2,
    ensures c1 == c2, x1 == x2,
{
    let (e1, e2) = (esc(c1), esc(c2));
    assert((e1 + x1)[0] == e1[0] && (e2 + x2)[0] == e2[0]);
    if e1.len() > 1 && e2.len() > 1 {
        assert((e1 + x1)[1] == e1[1] && (e2 + x2)[1] == e2[1]);
        if c1 < 0x20 && c1 != 0x08 && c1 != 0x0c && c1 != 0x0a && c1 != 0x0d && c1 != 0x09
            && c2 < 0x20 && c2 != 0x08 && c2 != 0x0c && c2 != 0x0a && c2 != 0x0d && c2 != 0x09 {
            assert((e1 + x1)[4] == e1[4] && (e2 + x2)[4] == e2[4]);
            assert((e1 + x1)[5] == e1[5] && (e2 + x2)[5] == e2[5]);
            assert(hex(c1 / 16) == hex(c2 / 16) && hex(c1 % 16) == hex(c2 % 16));
            assert(c1 / 16 == c2 / 16 && c1 % 16 == c2 % 16);
        }
    }
    assert(c1 == c2);
    lemma_cancel(e1, x1, e2, x2);
}

/// A nonempty string's escaped contents do not start with `"`.
proof fn lemma_str_head(s: Seq<u8>, r: Seq<u8>)
    requires s.len() > 0,
    ensures (esc_all(s) + r)[0] != 34u8,
{
    lemma_esc_fwd(s);
    assert((esc_all(s) + r)[0] == esc(s[0])[0]);
}

/// One escaped byte off the front of both sides.
proof fn lemma_str_step(s1: Seq<u8>, s2: Seq<u8>, r1: Seq<u8>, r2: Seq<u8>)
    requires s1.len() > 0, s2.len() > 0, esc_all(s1) + r1 == esc_all(s2) + r2,
    ensures s1[0] == s2[0], esc_all(s1.drop_first()) + r1 == esc_all(s2.drop_first()) + r2,
{
    lemma_esc_fwd(s1);
    lemma_esc_fwd(s2);
    let (t1, t2) = (s1.drop_first(), s2.drop_first());
    assert(esc_all(s1) + r1 =~= esc(s1[0]) + (esc_all(t1) + r1));
    assert(esc_all(s2) + r2 =~= esc(s2[0]) + (esc_all(t2) + r2));
    lemma_esc(s1[0], s2[0], esc_all(t1) + r1, esc_all(t2) + r2);
}

/// A string's escaped contents end at the first unescaped `"`.
proof fn lemma_str(s1: Seq<u8>, s2: Seq<u8>, r1: Seq<u8>, r2: Seq<u8>)
    requires esc_all(s1) + seq![34u8] + r1 == esc_all(s2) + seq![34u8] + r2,
    ensures s1 == s2, r1 == r2,
    decreases s1.len(),
{
    hide(esc);
    let q = seq![34u8];
    let (x1, x2) = (q + r1, q + r2);
    assert(esc_all(s1) + q + r1 =~= esc_all(s1) + x1);
    assert(esc_all(s2) + q + r2 =~= esc_all(s2) + x2);
    if s1.len() == 0 || s2.len() == 0 {
        if s1.len() > 0 { lemma_str_head(s1, x1); }
        if s2.len() > 0 { lemma_str_head(s2, x2); }
        assert(s1.len() == 0 ==> esc_all(s1) =~= Seq::<u8>::empty());
        assert(s2.len() == 0 ==> esc_all(s2) =~= Seq::<u8>::empty());
        assert(x1[0] == 34u8 && x2[0] == 34u8);
        assert(s1.len() == 0 && s2.len() == 0);
        assert(esc_all(s1) + x1 =~= x1 && esc_all(s2) + x2 =~= x2);
        lemma_cancel(q, r1, q, r2);
        assert(s1 =~= s2);
    } else {
        lemma_str_step(s1, s2, x1, x2);
        let (t1, t2) = (s1.drop_first(), s2.drop_first());
        assert(esc_all(t1) + q + r1 =~= esc_all(t1) + x1);
        assert(esc_all(t2) + q + r2 =~= esc_all(t2) + x2);
        lemma_str(t1, t2, r1, r2);
        assert(s1 =~= seq![s1[0]] + t1);
        assert(s2 =~= seq![s2[0]] + t2);
    }
}

// ------------------------------------------------------------------ values

/// A value's first byte: `n`, `t`, `f`, `-`, a digit, `"`, `[` or `{`; never a `delim`.
proof fn lemma_first(j: Json)
    ensures print(j).len() > 0, !delim(print(j)), print(j)[0] != 93u8, print(j)[0] != 125u8, print(j)[0] != 44u8,
{
    match j {
        Json::Num(neg, m) => {
            lemma_digits(m as nat);
            if !neg { assert(print(j) == digits(m as nat)); assert(is_digit(digits(m as nat)[0])); }
        },
        _ => {},
    }
}

/// Equal bytes start values of the same kind (and numbers of the same sign).
proof fn lemma_kind(j1: Json, j2: Json, r1: Seq<u8>, r2: Seq<u8>)
    requires print(j1) + r1 == print(j2) + r2,
    ensures
        j1 is Null == j2 is Null, j1 is Bool == j2 is Bool, j1 is Str == j2 is Str, j1 is Arr == j2 is Arr, j1 is Obj == j2 is Obj,
        j1 is Num == j2 is Num, (j1 is Num && j2 is Num) ==> j1->Num_0 == j2->Num_0,
        (j1 is Bool && j2 is Bool) ==> j1 == j2,
{
    let (p1, p2) = (print(j1), print(j2));
    lemma_first(j1);
    lemma_first(j2);
    assert((p1 + r1)[0] == p1[0] && (p2 + r2)[0] == p2[0]);
    if let Json::Num(n, m) = j1 { lemma_digits(m as nat); if !n { assert(p1 == digits(m as nat)); assert(is_digit(p1[0])); } }
    if let Json::Num(n, m) = j2 { lemma_digits(m as nat); if !n { assert(p2 == digits(m as nat)); assert(is_digit(p2[0])); } }
}

/// **`print` is self-delimiting**: equal bytes, each value followed by a `delim`, give equal
/// values and equal followers.
pub proof fn lemma_val(j1: Json, j2: Json, r1: Seq<u8>, r2: Seq<u8>)
    requires print(j1) + r1 == print(j2) + r2, delim(r1), delim(r2),
    ensures jeq(j1, j2), r1 == r2,
    decreases j1, 2nat,
{
    lemma_kind(j1, j2, r1, r2);
    match j1 {
        Json::Null | Json::Bool(_) => { lemma_cancel(print(j1), r1, print(j2), r2); },
        Json::Num(_, _) => lemma_val_num(j1, j2, r1, r2),
        Json::Str(_) => lemma_val_str(j1, j2, r1, r2),
        Json::Arr(_) => lemma_val_arr(j1, j2, r1, r2),
        Json::Obj(_) => lemma_val_obj(j1, j2, r1, r2),
    }
}

proof fn lemma_val_num(j1: Json, j2: Json, r1: Seq<u8>, r2: Seq<u8>)
    requires print(j1) + r1 == print(j2) + r2, delim(r1), delim(r2), j1 is Num, j2 is Num, j1->Num_0 == j2->Num_0,
    ensures jeq(j1, j2), r1 == r2,
{
    let (n, m1) = (j1->Num_0, j1->Num_1);
    let m2 = j2->Num_1;
    let s0 = if n { seq![45u8] } else { Seq::<u8>::empty() };
    assert(print(j1) + r1 =~= s0 + (digits(m1 as nat) + r1));
    assert(print(j2) + r2 =~= s0 + (digits(m2 as nat) + r2));
    lemma_cancel(s0, digits(m1 as nat) + r1, s0, digits(m2 as nat) + r2);
    lemma_num(m1 as nat, m2 as nat, r1, r2);
}

proof fn lemma_val_str(j1: Json, j2: Json, r1: Seq<u8>, r2: Seq<u8>)
    requires print(j1) + r1 == print(j2) + r2, j1 is Str, j2 is Str,
    ensures jeq(j1, j2), r1 == r2,
{
    let (x1, x2) = (j1->Str_0, j2->Str_0);
    let q = seq![34u8];
    assert(print(j1) + r1 =~= q + (esc_all(x1@) + q + r1));
    assert(print(j2) + r2 =~= q + (esc_all(x2@) + q + r2));
    lemma_cancel(q, esc_all(x1@) + q + r1, q, esc_all(x2@) + q + r2);
    lemma_str(x1@, x2@, r1, r2);
}

proof fn lemma_arr_print(j: Json, r: Seq<u8>)
    requires j is Arr,
    ensures print(j) + r == seq![91u8] + (fe(j->Arr_0@) + (seq![93u8] + r)),
{
    lemma_pe_fwd(j->Arr_0@);
    assert(print(j) + r =~= seq![91u8] + (fe(j->Arr_0@) + (seq![93u8] + r)));
}

proof fn lemma_obj_print(j: Json, r: Seq<u8>)
    requires j is Obj,
    ensures print(j) + r == seq![123u8] + (ffe(j->Obj_0@) + (seq![125u8] + r)),
{
    lemma_pf_fwd(j->Obj_0@);
    assert(print(j) + r =~= seq![123u8] + (ffe(j->Obj_0@) + (seq![125u8] + r)));
}

proof fn lemma_val_arr(j1: Json, j2: Json, r1: Seq<u8>, r2: Seq<u8>)
    requires print(j1) + r1 == print(j2) + r2, j1 is Arr, j2 is Arr,
    ensures jeq(j1, j2), r1 == r2,
    decreases j1, 1nat,
{
    let (v1, v2) = (j1->Arr_0, j2->Arr_0);
    let o = seq![91u8];
    let c1 = seq![93u8] + r1;
    let c2 = seq![93u8] + r2;
    lemma_arr_print(j1, r1);
    lemma_arr_print(j2, r2);
    lemma_cancel(o, fe(v1@) + c1, o, fe(v2@) + c2);
    lemma_elems(v1@, v2@, c1, c2);
    lemma_cancel(seq![93u8], r1, seq![93u8], r2);
}

proof fn lemma_val_obj(j1: Json, j2: Json, r1: Seq<u8>, r2: Seq<u8>)
    requires print(j1) + r1 == print(j2) + r2, j1 is Obj, j2 is Obj,
    ensures jeq(j1, j2), r1 == r2,
    decreases j1, 1nat,
{
    let (v1, v2) = (j1->Obj_0, j2->Obj_0);
    let o = seq![123u8];
    let c1 = seq![125u8] + r1;
    let c2 = seq![125u8] + r2;
    lemma_obj_print(j1, r1);
    lemma_obj_print(j2, r2);
    lemma_cancel(o, ffe(v1@) + c1, o, ffe(v2@) + c2);
    lemma_fields(v1@, v2@, c1, c2);
    lemma_cancel(seq![125u8], r1, seq![125u8], r2);
}

/// The elements of an array, then its `]`.
proof fn lemma_elems(s1: Seq<Json>, s2: Seq<Json>, x1: Seq<u8>, x2: Seq<u8>)
    requires fe(s1) + x1 == fe(s2) + x2, x1.len() > 0, x1[0] == 93u8, x2.len() > 0, x2[0] == 93u8,
    ensures jeqs(s1, s2), x1 == x2,
    decreases s1, 0nat,
{
    if s1.len() == 0 && s2.len() == 0 {
        assert(fe(s1) + x1 =~= x1 && fe(s2) + x2 =~= x2);
    } else if s1.len() == 0 {
        lemma_first(s2[0]);
        assert(fe(s1) + x1 =~= x1);
        assert((fe(s2) + x2)[0] == print(s2[0])[0]);
    } else if s2.len() == 0 {
        lemma_first(s1[0]);
        assert(fe(s2) + x2 =~= x2);
        assert((fe(s1) + x1)[0] == print(s1[0])[0]);
    } else {
        let (t1, t2) = (s1.drop_first(), s2.drop_first());
        let (y1, y2) = (ft(t1) + x1, ft(t2) + x2);
        assert(fe(s1) + x1 =~= print(s1[0]) + y1);
        assert(fe(s2) + x2 =~= print(s2[0]) + y2);
        assert(delim(y1)) by { if t1.len() > 0 { assert(y1[0] == 44u8); } else { assert(y1 =~= x1); } }
        assert(delim(y2)) by { if t2.len() > 0 { assert(y2[0] == 44u8); } else { assert(y2 =~= x2); } }
        lemma_val(s1[0], s2[0], y1, y2);
        lemma_tail(t1, t2, x1, x2);
    }
}

proof fn lemma_tail(t1: Seq<Json>, t2: Seq<Json>, x1: Seq<u8>, x2: Seq<u8>)
    requires ft(t1) + x1 == ft(t2) + x2, x1.len() > 0, x1[0] == 93u8, x2.len() > 0, x2[0] == 93u8,
    ensures jeqs(t1, t2), x1 == x2,
    decreases t1, 0nat,
{
    if t1.len() == 0 && t2.len() == 0 {
        assert(ft(t1) + x1 =~= x1 && ft(t2) + x2 =~= x2);
    } else if t1.len() == 0 {
        assert(ft(t1) + x1 =~= x1);
        assert((ft(t2) + x2)[0] == 44u8);
    } else if t2.len() == 0 {
        assert(ft(t2) + x2 =~= x2);
        assert((ft(t1) + x1)[0] == 44u8);
    } else {
        let (u1, u2) = (t1.drop_first(), t2.drop_first());
        let (y1, y2) = (ft(u1) + x1, ft(u2) + x2);
        let cm = seq![44u8];
        assert(ft(t1) + x1 =~= cm + (print(t1[0]) + y1));
        assert(ft(t2) + x2 =~= cm + (print(t2[0]) + y2));
        lemma_cancel(cm, print(t1[0]) + y1, cm, print(t2[0]) + y2);
        assert(delim(y1)) by { if u1.len() > 0 { assert(y1[0] == 44u8); } else { assert(y1 =~= x1); } }
        assert(delim(y2)) by { if u2.len() > 0 { assert(y2[0] == 44u8); } else { assert(y2 =~= x2); } }
        lemma_val(t1[0], t2[0], y1, y2);
        lemma_tail(u1, u2, x1, x2);
    }
}

/// One member `"key":value`, then what follows it.
proof fn lemma_item(e1: (Vec<u8>, Json), e2: (Vec<u8>, Json), y1: Seq<u8>, y2: Seq<u8>)
    requires fitem(e1) + y1 == fitem(e2) + y2, delim(y1), delim(y2),
    ensures e1.0@ == e2.0@, jeq(e1.1, e2.1), y1 == y2,
    decreases e1.1, 3nat,
{
    let q = seq![34u8];
    let co = seq![58u8];
    let (z1, z2) = (co + print(e1.1) + y1, co + print(e2.1) + y2);
    assert(fitem(e1) + y1 =~= q + (esc_all(e1.0@) + q + z1));
    assert(fitem(e2) + y2 =~= q + (esc_all(e2.0@) + q + z2));
    lemma_cancel(q, esc_all(e1.0@) + q + z1, q, esc_all(e2.0@) + q + z2);
    lemma_str(e1.0@, e2.0@, z1, z2);
    assert(z1 =~= co + (print(e1.1) + y1));
    assert(z2 =~= co + (print(e2.1) + y2));
    lemma_cancel(co, print(e1.1) + y1, co, print(e2.1) + y2);
    lemma_val(e1.1, e2.1, y1, y2);
}

proof fn lemma_fields(s1: Seq<(Vec<u8>, Json)>, s2: Seq<(Vec<u8>, Json)>, x1: Seq<u8>, x2: Seq<u8>)
    requires ffe(s1) + x1 == ffe(s2) + x2, x1.len() > 0, x1[0] == 125u8, x2.len() > 0, x2[0] == 125u8,
    ensures jeqf(s1, s2), x1 == x2,
    decreases s1, 0nat,
{
    if s1.len() == 0 && s2.len() == 0 {
        assert(ffe(s1) + x1 =~= x1 && ffe(s2) + x2 =~= x2);
    } else if s1.len() == 0 {
        assert(ffe(s1) + x1 =~= x1);
        assert((ffe(s2) + x2)[0] == 34u8);
    } else if s2.len() == 0 {
        assert(ffe(s2) + x2 =~= x2);
        assert((ffe(s1) + x1)[0] == 34u8);
    } else {
        let (t1, t2) = (s1.drop_first(), s2.drop_first());
        let (y1, y2) = (fft(t1) + x1, fft(t2) + x2);
        assert(ffe(s1) + x1 =~= fitem(s1[0]) + y1);
        assert(ffe(s2) + x2 =~= fitem(s2[0]) + y2);
        assert(delim(y1)) by { if t1.len() > 0 { assert(y1[0] == 44u8); } else { assert(y1 =~= x1); } }
        assert(delim(y2)) by { if t2.len() > 0 { assert(y2[0] == 44u8); } else { assert(y2 =~= x2); } }
        lemma_item(s1[0], s2[0], y1, y2);
        lemma_ftail(t1, t2, x1, x2);
    }
}

proof fn lemma_ftail(t1: Seq<(Vec<u8>, Json)>, t2: Seq<(Vec<u8>, Json)>, x1: Seq<u8>, x2: Seq<u8>)
    requires fft(t1) + x1 == fft(t2) + x2, x1.len() > 0, x1[0] == 125u8, x2.len() > 0, x2[0] == 125u8,
    ensures jeqf(t1, t2), x1 == x2,
    decreases t1, 0nat,
{
    if t1.len() == 0 && t2.len() == 0 {
        assert(fft(t1) + x1 =~= x1 && fft(t2) + x2 =~= x2);
    } else if t1.len() == 0 {
        assert(fft(t1) + x1 =~= x1);
        assert((fft(t2) + x2)[0] == 44u8);
    } else if t2.len() == 0 {
        assert(fft(t2) + x2 =~= x2);
        assert((fft(t1) + x1)[0] == 44u8);
    } else {
        let (u1, u2) = (t1.drop_first(), t2.drop_first());
        let (y1, y2) = (fft(u1) + x1, fft(u2) + x2);
        let cm = seq![44u8];
        assert(fft(t1) + x1 =~= cm + (fitem(t1[0]) + y1));
        assert(fft(t2) + x2 =~= cm + (fitem(t2[0]) + y2));
        lemma_cancel(cm, fitem(t1[0]) + y1, cm, fitem(t2[0]) + y2);
        assert(delim(y1)) by { if u1.len() > 0 { assert(y1[0] == 44u8); } else { assert(y1 =~= x1); } }
        assert(delim(y2)) by { if u2.len() > 0 { assert(y2[0] == 44u8); } else { assert(y2 =~= x2); } }
        lemma_item(t1[0], t2[0], y1, y2);
        lemma_ftail(u1, u2, x1, x2);
    }
}

/// **`print` is injective** (up to views): the bytes determine the value.
pub proof fn theorem_print_injective(j1: Json, j2: Json)
    requires print(j1) == print(j2),
    ensures jeq(j1, j2),
{
    let e = Seq::<u8>::empty();
    assert(print(j1) + e =~= print(j2) + e);
    lemma_val(j1, j2, e, e);
}

} // verus!
