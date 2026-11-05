//! Runs every `semconf` fn natively and writes `<target>/semconf-vectors.txt` in
//! `tools/ct-driver/selftest.txt`'s format: per fn, its edge inputs (each argument's `0`, `1`,
//! `MAX`, `MIN`, `-1`, crossed) and 64 pseudo-random ones (splitmix64, seed `0x8c8c8c8c`). A native
//! panic is written `=> panic`. `scripts/ct-check.sh` diffs the file against the committed
//! `vectors.txt`.
use semconf::*;
use std::fmt::Write as _;
use std::panic::{catch_unwind, AssertUnwindSafe};

const SEED: u64 = 0x8c8c8c8c;
const RANDOM: usize = 64;

/// splitmix64.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    fn u128(&mut self) -> u128 {
        (self.next() as u128) << 64 | self.next() as u128
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// A value in the vector syntax.
trait Show {
    fn show(&self) -> String;
}

/// An argument type: its edge values and a random one.
trait Arg: Show + Clone {
    fn edges() -> Vec<Self>;
    fn random(r: &mut Rng) -> Self;
}

macro_rules! ints {
    ($($t:ident $u:ident),*) => { $(
        impl Show for $t {
            fn show(&self) -> String { format!("{:#x}{}", *self as $u, stringify!($t)) }
        }
        impl Arg for $t {
            fn edges() -> Vec<Self> {
                let mut v: Vec<$t> = Vec::new();
                for x in [0, 1, $t::MAX, $t::MIN, (0 as $t).wrapping_sub(1)] {
                    if !v.contains(&x) { v.push(x); }
                }
                v
            }
            fn random(r: &mut Rng) -> Self { r.u128() as $t }
        }
    )* };
}

ints!(u8 u8, u16 u16, u32 u32, u64 u64, u128 u128, usize usize, i8 u8, i16 u16, i32 u32, i64 u64, i128 u128, isize usize);

impl Show for bool {
    fn show(&self) -> String { self.to_string() }
}

impl Arg for bool {
    fn edges() -> Vec<Self> { vec![false, true] }
    fn random(r: &mut Rng) -> Self { r.next() & 1 == 1 }
}

impl Show for () {
    fn show(&self) -> String { "()".into() }
}

/// A byte slice or `Vec<u8>`: hex, `-` when empty.
#[derive(Clone)]
struct Bytes(Vec<u8>);

impl Show for Bytes {
    fn show(&self) -> String {
        if self.0.is_empty() { "-".into() } else { self.0.iter().map(|b| format!("{b:02x}")).collect() }
    }
}

impl Arg for Bytes {
    fn edges() -> Vec<Self> { vec![Bytes(vec![]), Bytes(vec![0xff])] }
    fn random(r: &mut Rng) -> Self {
        let n = r.below(40) as usize;
        Bytes((0..n).map(|_| r.next() as u8).collect())
    }
}

impl<T: Show> Show for [T] {
    fn show(&self) -> String { format!("[{}]", self.iter().map(Show::show).collect::<Vec<_>>().join(",")) }
}

impl<T: Show, const N: usize> Show for [T; N] {
    fn show(&self) -> String { self[..].show() }
}

impl<T: Show> Show for Vec<T> {
    fn show(&self) -> String { self[..].show() }
}

impl<A: Show, B: Show> Show for (A, B) {
    fn show(&self) -> String { format!("({},{})", self.0.show(), self.1.show()) }
}

impl<A: Show, B: Show, C: Show> Show for (A, B, C) {
    fn show(&self) -> String { format!("({},{},{})", self.0.show(), self.1.show(), self.2.show()) }
}

impl<T: Show> Show for Option<T> {
    fn show(&self) -> String {
        match self {
            None => "None".into(),
            Some(x) => format!("Some({})", x.show()),
        }
    }
}

impl Show for data::Pair {
    fn show(&self) -> String { format!("#0({},{})", self.a.show(), self.b.show()) }
}

impl Show for data::Code {
    fn show(&self) -> String {
        match self {
            data::Code::Conn(v) => format!("#0({})", v.show()),
            data::Code::Stream(v) => format!("#1({})", v.show()),
        }
    }
}

/// The vector file being written.
struct Out {
    text: String,
    rng: Rng,
}

impl Out {
    /// One vector: `<path> <args> => <outs>`, or `=> panic` when `run` panics.
    fn line(&mut self, path: &str, args: &[String], run: impl FnOnce() -> Vec<String>) {
        let outs = catch_unwind(AssertUnwindSafe(run)).unwrap_or_else(|_| vec!["panic".into()]);
        writeln!(self.text, "semconf::{path} {} => {}", args.join(" "), outs.join(" ")).unwrap();
    }

    fn f1<A: Arg, R: Show>(&mut self, path: &str, f: impl Fn(A) -> R) {
        let mut ins = A::edges();
        ins.extend((0..RANDOM).map(|_| A::random(&mut self.rng)));
        for a in ins {
            self.line(path, &[a.show()], || vec![f(a.clone()).show()]);
        }
    }

    fn f2<A: Arg, B: Arg, R: Show>(&mut self, path: &str, f: impl Fn(A, B) -> R) {
        let mut ins: Vec<(A, B)> = Vec::new();
        for a in A::edges() {
            for b in B::edges() {
                ins.push((a.clone(), b));
            }
        }
        ins.extend((0..RANDOM).map(|_| (A::random(&mut self.rng), B::random(&mut self.rng))));
        for (a, b) in ins {
            self.line(path, &[a.show(), b.show()], || vec![f(a.clone(), b.clone()).show()]);
        }
    }
}

macro_rules! int_vectors {
    ($o:ident; $($t:ident),*) => { $(
        $o.f2(concat!(stringify!($t), "::add"), $t::add);
        $o.f2(concat!(stringify!($t), "::sub"), $t::sub);
        $o.f2(concat!(stringify!($t), "::mul"), $t::mul);
        $o.f2(concat!(stringify!($t), "::div"), $t::div);
        $o.f2(concat!(stringify!($t), "::rem"), $t::rem);
        $o.f2(concat!(stringify!($t), "::xor"), $t::xor);
        $o.f2(concat!(stringify!($t), "::and"), $t::and);
        $o.f2(concat!(stringify!($t), "::or"), $t::or);
        $o.f2(concat!(stringify!($t), "::shl"), $t::shl);
        $o.f2(concat!(stringify!($t), "::shr"), $t::shr);
        $o.f2(concat!(stringify!($t), "::shl_same"), $t::shl_same);
        $o.f2(concat!(stringify!($t), "::shr_same"), $t::shr_same);
        $o.f2(concat!(stringify!($t), "::eq"), $t::eq);
        $o.f2(concat!(stringify!($t), "::ne"), $t::ne);
        $o.f2(concat!(stringify!($t), "::lt"), $t::lt);
        $o.f2(concat!(stringify!($t), "::le"), $t::le);
        $o.f2(concat!(stringify!($t), "::gt"), $t::gt);
        $o.f2(concat!(stringify!($t), "::ge"), $t::ge);
        $o.f1(concat!(stringify!($t), "::not"), $t::not);
    )* };
}

macro_rules! cast_vectors {
    ($o:ident; $($f:ident),*) => { $(
        $o.f1(concat!("cast::", stringify!($f), "::u8"), cast::$f::u8);
        $o.f1(concat!("cast::", stringify!($f), "::u16"), cast::$f::u16);
        $o.f1(concat!("cast::", stringify!($f), "::u32"), cast::$f::u32);
        $o.f1(concat!("cast::", stringify!($f), "::u64"), cast::$f::u64);
        $o.f1(concat!("cast::", stringify!($f), "::u128"), cast::$f::u128);
        $o.f1(concat!("cast::", stringify!($f), "::usize"), cast::$f::usize);
        $o.f1(concat!("cast::", stringify!($f), "::i8"), cast::$f::i8);
        $o.f1(concat!("cast::", stringify!($f), "::i16"), cast::$f::i16);
        $o.f1(concat!("cast::", stringify!($f), "::i32"), cast::$f::i32);
        $o.f1(concat!("cast::", stringify!($f), "::i64"), cast::$f::i64);
        $o.f1(concat!("cast::", stringify!($f), "::i128"), cast::$f::i128);
        $o.f1(concat!("cast::", stringify!($f), "::isize"), cast::$f::isize);
    )* };
}

#[test]
fn write_vectors() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut o = Out {
        text: String::from(
            "# Generated by tools/ct-fixtures/semconf/tests/vectors.rs from native runs; do not edit. Format:\n\
             # tools/ct-driver/selftest.txt's, plus `=> panic` (the native run panics: the core run must stop).\n",
        ),
        rng: Rng(SEED),
    };
    int_vectors!(o; u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);
    o.f1("neg::i8", neg::i8);
    o.f1("neg::i16", neg::i16);
    o.f1("neg::i32", neg::i32);
    o.f1("neg::i64", neg::i64);
    o.f1("neg::i128", neg::i128);
    o.f1("neg::isize", neg::isize);
    o.f2("boolean::and", boolean::and);
    o.f2("boolean::or", boolean::or);
    o.f2("boolean::xor", boolean::xor);
    o.f2("boolean::eq", boolean::eq);
    o.f2("boolean::lt", boolean::lt);
    o.f1("boolean::not", boolean::not);
    o.f2("boolean::lazy_and", boolean::lazy_and);
    cast_vectors!(o; u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, bool);
    data_vectors(&mut o);
    mut_vectors(&mut o);
    drop_vectors(&mut o);
    let file = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("../semconf-vectors.txt");
    std::fs::write(&file, &o.text).unwrap();
}

fn data_vectors(o: &mut Out) {
    use data::*;
    o.f1("data::slice_len", |x: Bytes| slice_len(&x.0));
    let mut ins: Vec<(Bytes, usize)> = Vec::new();
    for x in Bytes::edges() {
        for i in [0, 1, usize::MAX] {
            ins.push((x.clone(), i));
        }
    }
    ins.extend((0..RANDOM).map(|_| (Bytes::random(&mut o.rng), o.rng.below(48) as usize)));
    for (x, i) in ins {
        o.line("data::slice_get", &[x.show(), i.show()], || vec![slice_get(&x.0, i).show()]);
    }
    o.f1("data::slice_sum", |x: Bytes| slice_sum(&x.0));
    for _ in 0..RANDOM {
        let a: [u16; 8] = std::array::from_fn(|_| o.rng.next() as u16);
        let i = o.rng.below(10) as usize;
        o.line("data::arr_get", &[a.show(), i.show()], || vec![arr_get(&a, i).show()]);
    }
    for _ in 0..RANDOM {
        let a: [u8; 4] = std::array::from_fn(|_| o.rng.next() as u8);
        o.line("data::arr_pat", &[Bytes(a.to_vec()).show()], || vec![arr_pat(&a).show()]);
    }
    for _ in 0..RANDOM {
        let n = o.rng.below(5) as usize;
        let x: Vec<(u64, u64)> = (0..n).map(|_| (o.rng.next(), o.rng.next())).collect();
        let i = o.rng.below(6) as usize;
        o.line("data::pairs_get", &[x.show(), i.show()], || vec![pairs_get(&x, i).show()]);
    }
    o.f2("data::repeat", repeat);
    o.f2("data::repeat_pairs", repeat_pairs);
    o.f1("data::tbl", tbl);
    o.line("data::tbl_whole", &[], || vec![tbl_whole().show()]);
    o.f1("data::bytes_const", bytes_const);
    o.f1("data::adt_const", adt_const);
    o.line("data::adt_const_whole", &[], || vec![adt_const_whole().show()]);
    o.f1("data::niche", niche);
    o.f1("data::niche_bool", niche_bool);
    for _ in 0..RANDOM {
        let c = if o.rng.next() & 1 == 0 { Code::Conn(o.rng.next()) } else { Code::Stream(o.rng.next()) };
        o.line("data::code_val", &[c.show()], || vec![code_val(&c).show()]);
    }
    o.f2("data::tuple", tuple);
}

fn mut_vectors(o: &mut Out) {
    use muts::*;
    let mut ins: Vec<(u32, u32)> = Vec::new();
    for a in u32::edges() {
        for b in u32::edges() {
            ins.push((a, b));
        }
    }
    ins.extend((0..RANDOM).map(|_| (o.rng.next() as u32, o.rng.next() as u32)));
    for (x, d) in ins {
        o.line("muts::set_root", &[format!("mut:{}", x.show()), d.show()], || {
            let mut y = x;
            let r = set_root(&mut y, d);
            vec![r.show(), y.show()]
        });
    }
    o.f1("muts::call_chain", call_chain);
    for _ in 0..RANDOM {
        let a: [u8; 4] = std::array::from_fn(|_| o.rng.next() as u8);
        let (i, v) = (o.rng.next() as usize, o.rng.next() as u8);
        o.line("muts::arr_root", &[format!("mut:{}", Bytes(a.to_vec()).show()), i.show(), v.show()], || {
            let mut b = a;
            let r = arr_root(&mut b, i % 1000, v);
            vec![r.show(), Bytes(b.to_vec()).show()]
        });
    }
    for _ in 0..RANDOM {
        let p = data::Pair { a: o.rng.next() as i32, b: o.rng.next() as u8 };
        let x = o.rng.next() as i32;
        o.line("muts::field_root", &[format!("mut:{}", p.show()), x.show()], || {
            let mut q = data::Pair { a: p.a, b: p.b };
            let r = field_root(&mut q, x);
            vec![r.show(), q.show()]
        });
    }
    o.f2("muts::two_locals", two_locals);
}

fn drop_vectors(o: &mut Out) {
    use drops::*;
    o.f2("drops::two_vecs", two_vecs);
    o.f1("drops::opt_vec", opt_vec);
    for _ in 0..RANDOM {
        let ov = if o.rng.next() & 1 == 0 { None } else { Some(Bytes::random(&mut o.rng).0) };
        let (a, b) = (Bytes::random(&mut o.rng).0, Bytes::random(&mut o.rng).0);
        let args = [ov.clone().map(Bytes).show(), format!("#0({},{})", Bytes(a.clone()).show(), Bytes(b.clone()).show())];
        o.line("drops::by_value", &args, || vec![by_value(ov, TwoVecs { a, b }).show()]);
    }
    o.f2("drops::extend", |x: Bytes, y: u8| Bytes(extend(&x.0, y)));
    for _ in 0..RANDOM {
        let (a, b, c, d) = (o.rng.next() as u32, o.rng.next() as u32, o.rng.next(), o.rng.next());
        o.line("drops::wrapping", &[a.show(), b.show(), c.show(), d.show()], || vec![wrapping(a, b, c, d).show()]);
    }
    // the two 8b regressions; `regress::drop_pairs` is rejected by the translator (Unresolved)
    o.f2("regress::pairs_vec", regress::pairs_vec);
    o.f1("regress::nested_len", |x: Bytes| regress::nested_len(&x.0));
    for _ in 0..RANDOM {
        let n = o.rng.below(6) as usize;
        let x: Vec<[u8; 3]> = (0..n).map(|_| std::array::from_fn(|_| o.rng.next() as u8)).collect();
        let s = format!("[{}]", x.iter().map(|e| Bytes(e.to_vec()).show()).collect::<Vec<_>>().join(","));
        o.line("regress::nested_elem_len", &[s], || vec![regress::nested_elem_len(&x).show()]);
    }
}
