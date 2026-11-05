//! Semantics conformance fixtures (spec §Verified interpreter and conformance tests): one small fn
//! per construct the front end supports. `tests/vectors.rs` runs each natively and writes
//! `semconf-vectors.txt` in `tools/ct-driver/selftest.txt`'s format; the selftest runs the same fns
//! through the dump and `ctmir::sem`, run by the verified evaluator (`ctmir::eval_run`), and every
//! vector must match. Built without overflow checks (Cargo.toml), as the dumped MIR is.

/// Per int type `T`: each binary operator, the shifts by a `u32` and by a `T` amount, `!`.
macro_rules! int_ops {
    ($($t:ident),*) => { $(
        pub mod $t {
            pub fn add(a: $t, b: $t) -> $t { a + b }
            pub fn sub(a: $t, b: $t) -> $t { a - b }
            pub fn mul(a: $t, b: $t) -> $t { a * b }
            pub fn div(a: $t, b: $t) -> $t { a / b }
            pub fn rem(a: $t, b: $t) -> $t { a % b }
            pub fn xor(a: $t, b: $t) -> $t { a ^ b }
            pub fn and(a: $t, b: $t) -> $t { a & b }
            pub fn or(a: $t, b: $t) -> $t { a | b }
            pub fn shl(a: $t, b: u32) -> $t { a << b }
            pub fn shr(a: $t, b: u32) -> $t { a >> b }
            pub fn shl_same(a: $t, b: $t) -> $t { a << b }
            pub fn shr_same(a: $t, b: $t) -> $t { a >> b }
            pub fn eq(a: $t, b: $t) -> bool { a == b }
            pub fn ne(a: $t, b: $t) -> bool { a != b }
            pub fn lt(a: $t, b: $t) -> bool { a < b }
            pub fn le(a: $t, b: $t) -> bool { a <= b }
            pub fn gt(a: $t, b: $t) -> bool { a > b }
            pub fn ge(a: $t, b: $t) -> bool { a >= b }
            pub fn not(a: $t) -> $t { !a }
        }
    )* };
}

int_ops!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

/// `-a` on the signed types.
pub mod neg {
    pub fn i8(a: i8) -> i8 { -a }
    pub fn i16(a: i16) -> i16 { -a }
    pub fn i32(a: i32) -> i32 { -a }
    pub fn i64(a: i64) -> i64 { -a }
    pub fn i128(a: i128) -> i128 { -a }
    pub fn isize(a: isize) -> isize { -a }
}

/// `bool`'s operators.
pub mod boolean {
    pub fn and(a: bool, b: bool) -> bool { a & b }
    pub fn or(a: bool, b: bool) -> bool { a | b }
    pub fn xor(a: bool, b: bool) -> bool { a ^ b }
    pub fn eq(a: bool, b: bool) -> bool { a == b }
    pub fn lt(a: bool, b: bool) -> bool { a < b }
    pub fn not(a: bool) -> bool { !a }
    pub fn lazy_and(a: bool, b: bool) -> bool { a && b }
}

/// `a as <to>` from each int type and `bool` to each int type: `cast::<from>::<to>`.
macro_rules! casts {
    ($($f:ident),*) => { $(
        pub mod $f {
            pub fn u8(a: $f) -> u8 { a as u8 }
            pub fn u16(a: $f) -> u16 { a as u16 }
            pub fn u32(a: $f) -> u32 { a as u32 }
            pub fn u64(a: $f) -> u64 { a as u64 }
            pub fn u128(a: $f) -> u128 { a as u128 }
            pub fn usize(a: $f) -> usize { a as usize }
            pub fn i8(a: $f) -> i8 { a as i8 }
            pub fn i16(a: $f) -> i16 { a as i16 }
            pub fn i32(a: $f) -> i32 { a as i32 }
            pub fn i64(a: $f) -> i64 { a as i64 }
            pub fn i128(a: $f) -> i128 { a as i128 }
            pub fn isize(a: $f) -> isize { a as isize }
        }
    )* };
}

pub mod cast {
    casts!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, bool);
}

/// Slices, `ConstantIndex`, `Repeat`, array and ADT constants, a niche constant.
pub mod data {
    pub fn slice_len(x: &[u8]) -> usize {
        x.len()
    }

    pub fn slice_get(x: &[u8], i: usize) -> u8 {
        x[i]
    }

    pub fn slice_sum(x: &[u8]) -> u32 {
        let mut s = 0u32;
        let mut i = 0;
        while i < x.len() {
            s = s * 31 + x[i] as u32;
            i += 1;
        }
        s
    }

    pub fn arr_get(x: &[u16; 8], i: usize) -> u16 {
        x[i]
    }

    /// `ConstantIndex` (an array pattern; slice patterns are outside the subset: `Assume`, and
    /// `ConstantIndex` from the end).
    pub fn arr_pat(x: &[u8; 4]) -> u8 {
        let [a, _, _, d] = *x;
        a ^ d
    }

    pub fn pairs_get(x: &[(u64, u64)], i: usize) -> u64 {
        x[i].0 ^ x[i].1
    }

    pub fn repeat(x: u8, i: usize) -> u8 {
        let a = [x; 16];
        a[i % 16]
    }

    pub fn repeat_pairs(x: u32, n: usize) -> [(u32, bool); 3] {
        let mut a = [(x, false); 3];
        a[n % 3].1 = true;
        a
    }

    const TBL: [u16; 8] = [1, 2, 3, 0x8000, 0xffff, 7, 0, 42];

    pub fn tbl(i: usize) -> u16 {
        TBL[i % 8]
    }

    pub fn tbl_whole() -> [u16; 8] {
        TBL
    }

    const BYTES: [u8; 7] = *b"semconf";

    pub fn bytes_const(i: usize) -> u8 {
        BYTES[i % BYTES.len()]
    }

    pub struct Pair {
        pub a: i32,
        pub b: u8,
    }

    const PT: Pair = Pair { a: -4, b: 9 };

    pub fn adt_const(x: i32) -> i32 {
        PT.a * x + PT.b as i32
    }

    pub fn adt_const_whole() -> Pair {
        PT
    }

    pub enum Code {
        Conn(u64),
        Stream(u64),
    }

    /// An `Option<Code>` constant: `None` is niche-encoded in `Code`'s tag.
    pub fn niche(x: u8) -> Option<Code> {
        if x == 0 {
            Some(Code::Stream(7))
        } else if x == 1 {
            None
        } else {
            Some(Code::Conn(x as u64))
        }
    }

    pub fn niche_bool(x: u8) -> Option<bool> {
        if x < 85 {
            None
        } else {
            Some(x > 170)
        }
    }

    pub fn code_val(c: &Code) -> u64 {
        match c {
            Code::Conn(v) => *v,
            Code::Stream(v) => *v ^ 0xff,
        }
    }

    pub fn tuple(a: u16, b: i64) -> (i64, u16, ()) {
        (b, a, ())
    }
}

/// `&mut` call write-back.
pub mod muts {
    use super::data::Pair;

    fn bump(x: &mut u32, d: u32) {
        *x += d;
    }

    pub fn set_root(x: &mut u32, d: u32) {
        bump(x, d);
        *x ^= 1;
    }

    pub fn call_chain(a: u32) -> u32 {
        let mut v = a;
        bump(&mut v, 3);
        bump(&mut v, a);
        v
    }

    fn put(x: &mut [u8; 4], i: usize, v: u8) {
        x[i % 4] = v;
    }

    pub fn arr_root(x: &mut [u8; 4], i: usize, v: u8) {
        put(x, i, v);
        put(x, i + 1, v ^ 0xff);
    }

    pub fn field_root(p: &mut Pair, x: i32) {
        let b = &mut p.b;
        *b ^= 3;
        p.a = x;
    }

    fn two(a: &mut u8, b: &mut u8) {
        let t = *a;
        *a = *b;
        *b = t ^ 1;
    }

    pub fn two_locals(a: u8, b: u8) -> (u8, u8) {
        let (mut x, mut y) = (a, b);
        two(&mut x, &mut y);
        two(&mut y, &mut x);
        (x, y)
    }
}

/// Vecs and drops: a struct with `Vec` fields and an `Option<Vec<u8>>`.
pub mod drops {
    pub struct TwoVecs {
        pub a: Vec<u8>,
        pub b: Vec<u8>,
    }

    pub fn two_vecs(a: u8, b: u8) -> usize {
        let mut t = TwoVecs { a: Vec::new(), b: Vec::new() };
        t.a.push(a);
        t.b.push(b);
        t.b.push(a);
        t.a.len() * 10 + t.b.len()
    }

    pub fn opt_vec(a: u8) -> usize {
        let o = if a > 100 {
            let mut v = Vec::new();
            v.push(a);
            Some(v)
        } else {
            None
        };
        match &o {
            Some(v) => v.len(),
            None => 0,
        }
    }

    pub fn by_value(o: Option<Vec<u8>>, t: TwoVecs) -> usize {
        let n = match &o {
            Some(v) => v.len(),
            None => 100,
        };
        n + t.a.len() * 1000 + t.b.len()
    }

    pub fn extend(x: &[u8], y: u8) -> Vec<u8> {
        let mut v = Vec::with_capacity(4);
        v.extend_from_slice(x);
        v.push(y);
        let w = v.as_slice().len();
        v.push(w as u8);
        v
    }

    pub fn wrapping(a: u32, b: u32, c: u64, d: u64) -> (u32, u64) {
        (a.wrapping_add(b), c.wrapping_sub(d))
    }
}

/// The two 8b front-end bugs (spec: regression vectors).
pub mod regress {
    /// A non-int `Vec`, built and returned.
    pub fn pairs_vec(a: u64, b: u64) -> Vec<(u64, u64)> {
        let mut v = Vec::new();
        v.push((a, b));
        v.push((b, a));
        v
    }

    /// Drop of a non-int `Vec`: its glue is not translated (`<Vec<(u64, u64)> as Drop>::drop` is
    /// Unresolved), so it has no vector; `tests/vectors.rs` lists it as rejected.
    pub fn drop_pairs(a: u64, b: u64) -> usize {
        let mut v = Vec::new();
        v.push((a, b));
        v.push((b, a));
        v.len()
    }

    fn inner_len(y: &&[u8]) -> usize {
        y.len()
    }

    /// The length of a slice behind two references.
    pub fn nested_len(x: &[u8]) -> usize {
        inner_len(&x)
    }

    pub fn nested_elem_len(x: &[[u8; 3]]) -> usize {
        if x.len() == 0 {
            0
        } else {
            x.len() * 10 + x[0].len()
        }
    }
}
