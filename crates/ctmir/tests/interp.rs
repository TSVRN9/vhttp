//! The selftest over `tiny.json` (its vectors now run `ctmir::sem` through the verified evaluator),
//! the integer arithmetic the evaluator shares with core (`interp_arith`), and the vector syntax.
use ctcore::syntax::{BinOp as B, IntTy as T, UnOp};
use ctmir::interp_arith::{binop_exec, cast_exec, unop_exec};
use ctmir::interp_val::CVal;
use ctmir::pipeline::{pipeline, Mode};
use ctmir::vectors::{parse_vector, Vector};

const TINY: &[u8] = include_bytes!("data/tiny.json");

fn arr(xs: &[u128]) -> CVal { CVal::Arr(xs.iter().map(|&x| CVal::Int(x)).collect()) }
fn shr(v: CVal) -> CVal { CVal::Shr(Box::new(v)) }

/// A test rendering of a value.
fn d(v: &CVal) -> String {
    let l = |vs: &Vec<CVal>| vs.iter().map(d).collect::<Vec<_>>().join(",");
    match v {
        CVal::Int(n) => format!("{n:#x}"),
        CVal::Unit => "()".into(),
        CVal::Tup(vs) => format!("({})", l(vs)),
        CVal::Adt(k, vs) => format!("#{k}({})", l(vs)),
        CVal::Arr(vs) => format!("[{}]", l(vs)),
        CVal::Shr(b) => format!("&{}", d(b)),
        CVal::Mut(_) => "mut".into(),
    }
}

fn is(v: &CVal, w: &CVal) -> bool { d(v) == d(w) }

/// Rust's wrapping semantics per `IntTy`, at the edges `sem::binop`/`cast` define (the old
/// interpreter's `arithmetic_edges`), plus every op against native Rust on a grid of edge values.
#[test]
fn arithmetic_edges() {
    assert_eq!(binop_exec(&B::Sub, &T::U8, 0, 1), 0xff);
    assert_eq!(binop_exec(&B::Div, &T::I8, 0x80, 0xff), 0x80);
    assert_eq!(binop_exec(&B::Rem, &T::I8, 0x80, 0xff), 0);
    assert_eq!(binop_exec(&B::Div, &T::U32, 7, 0), 0);
    assert_eq!(binop_exec(&B::Rem, &T::I32, 7, 0), 0);
    assert_eq!(binop_exec(&B::Shl, &T::U32, 1, 33), 2);
    assert_eq!(binop_exec(&B::Shr, &T::I8, 0x80, 1), 0xc0);
    assert_eq!(binop_exec(&B::Lt, &T::I8, 0xff, 0), 1);
    assert_eq!(binop_exec(&B::Lt, &T::U8, 0xff, 0), 0);
    assert_eq!(binop_exec(&B::Add, &T::Bool, 1, 1), 0);
    assert_eq!(binop_exec(&B::Shl, &T::U128, 1, 127), 1 << 127);
    assert_eq!(unop_exec(&UnOp::Not, &T::U8, 0x0f), 0xf0);
    assert_eq!(unop_exec(&UnOp::Not, &T::Bool, 1), 0);
    assert_eq!(unop_exec(&UnOp::Neg, &T::I8, 1), 0xff);
    assert_eq!(cast_exec(&T::I8, &T::U32, 0xff), 0xffff_ffff);
    assert_eq!(cast_exec(&T::U8, &T::U32, 0xff), 0xff);
    assert_eq!(cast_exec(&T::U64, &T::U8, 0x1234), 0x34);
    assert_eq!(cast_exec(&T::I64, &T::U128, u64::MAX as u128), u128::MAX);
    assert_eq!(cast_exec(&T::Bool, &T::U8, 1), 1);
    let xs: [i128; 9] = [0, 1, 2, 3, -1, -2, i128::MIN, i128::MAX, 0x5a5a_5a5a_5a5a_5a5a_5a5a_5a5a_5a5a_5a5a];
    for &a in &xs {
        for &b in &xs {
            let (ua, ub) = (a as u128, b as u128);
            assert_eq!(binop_exec(&B::Mul, &T::I128, ua, ub), a.wrapping_mul(b) as u128);
            assert_eq!(binop_exec(&B::Shr, &T::I128, ua, ub), a.wrapping_shr(b as u32) as u128);
            assert_eq!(binop_exec(&B::Shr, &T::I16, ua & 0xffff, ub), (a as i16).wrapping_shr(b as u32) as u16 as u128);
            if b as i64 != 0 {
                assert_eq!(binop_exec(&B::Div, &T::I64, ua & u64::MAX as u128, ub & u64::MAX as u128), (a as i64).wrapping_div(b as i64) as u64 as u128);
            }
            if b as i32 != 0 {
                assert_eq!(binop_exec(&B::Rem, &T::I32, ua & 0xffff_ffff, ub & 0xffff_ffff), (a as i32).wrapping_rem(b as i32) as u32 as u128);
            }
            assert_eq!(binop_exec(&B::Ge, &T::Isize, ua, ub), ((a as i64) >= (b as i64)) as u128);
            assert_eq!(cast_exec(&T::I16, &T::I64, ua), (a as i16) as i64 as u64 as u128);
        }
    }
}

fn toks(s: &str) -> Vec<Vec<u8>> { s.split_whitespace().map(|t| t.as_bytes().to_vec()).collect() }

fn vector(s: &str) -> Result<Vector, String> { parse_vector(&toks(s)).map_err(|e| String::from_utf8_lossy(&e).into_owned()) }

#[test]
fn vector_syntax() {
    let v = vector("00ff - 0x2au128 mut:[0x1u64,0x2u64] => () [0x1u64]").unwrap();
    assert!(is(&v.args[0].1, &shr(arr(&[0, 0xff]))) && !v.args[0].0);
    assert!(is(&v.args[1].1, &shr(arr(&[]))));
    assert!(is(&v.args[2].1, &CVal::Int(0x2a)));
    assert!(v.args[3].0 && is(&v.args[3].1, &arr(&[1, 2])));
    assert!(is(&v.want[0], &CVal::Unit) && is(&v.want[1], &arr(&[1])));
    assert_eq!(v.bits, vec![None, None, Some(128), None]);
    let v = vector("=> None Some(0a)").unwrap();
    assert!(is(&v.want[0], &CVal::Adt(0, vec![])) && is(&v.want[1], &CVal::Adt(1, vec![arr(&[10])])));
    let v = vector("[(0x1u64,0x2u64),(0x3u64,0x4u64)] => Some((0x5u64,0x6usize))").unwrap();
    let pair = |a, b| CVal::Tup(vec![CVal::Int(a), CVal::Int(b)]);
    assert!(is(&v.args[0].1, &shr(CVal::Arr(vec![pair(1, 2), pair(3, 4)]))));
    assert!(is(&v.want[0], &CVal::Adt(1, vec![pair(5, 6)])));
    let v = vector("#0() true => #1(#0(0x105u64)) #2(0x7u8,[(0x1u64,0x2u64)]) false").unwrap();
    assert!(is(&v.args[0].1, &CVal::Adt(0, vec![])) && is(&v.args[1].1, &CVal::Int(1)) && is(&v.want[2], &CVal::Int(0)));
    assert!(is(&v.want[0], &CVal::Adt(1, vec![CVal::Adt(0, vec![CVal::Int(0x105)])])));
    assert!(vector("0x1u8 => panic").unwrap().panic);
    assert!(!vector("0x1u8 => panic 0x1u8").is_ok());
    for bad in ["0x1 => ()", "0x100u8 => ()", "abc => ()", "00", "=> True", "=> (0x1u8,0x2)", "=> #x(0x1u8)", "=> #1(0x1u8", "=> #1", "=> 0xu8"] {
        assert!(vector(bad).is_err(), "{bad}");
    }
}

fn selftest(vectors: &str) -> Result<String, String> {
    pipeline(TINY, &vec![vec![]], &Mode::Selftest(vectors.as_bytes().to_vec()))
        .map(|r| String::from_utf8(r).unwrap())
        .map_err(|e| String::from_utf8_lossy(&e).into_owned())
}

/// The pipeline's selftest: one line per vector of the crate, in file order, duplicates kept.
#[test]
fn selftest_report() {
    let r = selftest("# a comment\ntiny::tiny 0a0b0c0d 0x5usize => 0x9u8 # the bounds check passes\n\
        other::f 00 => ()\ntiny::opt true => Some(0x3u8)\ntiny::opt false => None\ntiny::opt false => None\n\
        tiny::call 0a0b0c0d => 0xeu8\ntiny::opt true => None\ntiny::nope => ()\n").unwrap();
    let ls: Vec<&str> = r.lines().collect();
    assert_eq!(ls.len(), 7, "{r}");
    assert!(ls[0].starts_with("pass tiny::tiny steps="), "{r}");
    assert!(ls[1].starts_with("pass tiny::opt steps=") && ls[2] == ls[3] && ls[2].starts_with("pass tiny::opt"), "{r}");
    assert!(ls[4].starts_with("pass tiny::call steps="), "{r}");
    assert!(ls[5].starts_with("fail tiny::opt got #1(0x3) want #0()"), "{r}");
    assert!(ls[6].starts_with("fail tiny::nope translation failed: 1 error(s), first: Root"), "{r}");
    assert!(selftest("tiny::opt true Some(0x3u8)\n").unwrap_err().starts_with("vectors:1: no `=>`"));
    assert!(selftest("other::f 00 => ()\n").unwrap_err().contains("no selftest vector for analysed crate tiny"));
}

fn selftest_on(dump: &[u8], vectors: &str) -> String {
    let r = pipeline(dump, &vec![vec![]], &Mode::Selftest(vectors.as_bytes().to_vec())).unwrap();
    String::from_utf8(r).unwrap()
}

/// `b` with its only occurrence of `from` replaced by `to` (as in tests/lower.rs).
fn edit(b: &[u8], from: &str, to: &str) -> Vec<u8> {
    let s = std::str::from_utf8(b).unwrap();
    assert_eq!(s.matches(from).count(), 1, "{from}");
    s.replacen(from, to, 1).into_bytes()
}

/// Three bytes for a `&[u8; 4]` parameter: the shape and width checks pass it, `x_wt_args` does not.
#[test]
fn selftest_ill_typed_args_fail() {
    assert_eq!(selftest("tiny::tiny 0a0b0c 0x5usize => 0x0u8\n").unwrap(), "fail tiny::tiny args not well-typed\n");
}

/// The arity, width and `mut:` errors (the old `vector_checks`), as selftest lines.
#[test]
fn selftest_vector_shape_errors() {
    let r = selftest("tiny::tiny 0a0b0c0d => 0x9u8\ntiny::tiny 0a0b0c0d 0x5u8 => 0x9u8\ntiny::tiny 0a0b0c0d 0x5usize => 0x9u16\n\
        tiny::tiny mut:0a0b0c0d 0x5usize => 0x9u8\ntiny::tiny 0a0b0c0d 0x5usize => 0x9u8 ()\n").unwrap();
    assert_eq!(r.lines().collect::<Vec<_>>(), [
        "fail tiny::tiny 1 args for 2 params",
        "fail tiny::tiny param #2: a 8-bit int arg for a 64-bit param",
        "fail tiny::tiny want #1: a 16-bit value for a 8-bit result",
        "fail tiny::tiny param #1: `mut:` must mark exactly the &mut params",
        "fail tiny::tiny 2 expected values for 1 return value and 0 &mut params",
    ]);
}

/// The I1 scenario: with the index unguarded (mask 7, no bounds `Assert`), MIR panics on the
/// out-of-bounds index where core read `Unit`.
#[test]
fn selftest_mir_panics_where_core_completes() {
    let assert_term = r#"{"Assert":{"cond":{"Move":{"local":6,"projection":[]}},"expected":true,"msg":{"BoundsCheck":{"len":{"Constant":{"span":0,"user_ty":null,"const_":{"kind":{"Allocated":{"bytes":[4,0,0,0,0,0,0,0],"provenance":{"ptrs":[]},"align":8,"mutability":"Mut"}},"ty":1,"id":4}}},"index":{"Copy":{"local":5,"projection":[]}}}},"target":1,"unwind":"Continue"}}"#;
    let dump = edit(TINY, assert_term, r#"{"Goto":{"target":1}}"#);
    let dump = edit(&dump, r#"{"bytes":[3,0,0,0,0,0,0,0],"provenance":{"ptrs":[]},"align":8,"mutability":"Mut"}},"ty":1,"id":8}"#,
        r#"{"bytes":[7,0,0,0,0,0,0,0],"provenance":{"ptrs":[]},"align":8,"mutability":"Mut"}},"ty":1,"id":8}"#);
    let r = selftest_on(&dump, "tiny::tiny 0a0b0c0d 0x5usize => 0x9u8\ntiny::tiny 0a0b0c0d 0x2usize => 0xeu8\n");
    let ls: Vec<&str> = r.lines().collect();
    assert!(ls[0].starts_with("fail tiny::tiny mir: panic"), "{r}");
    assert!(ls[1].starts_with("pass tiny::tiny steps="), "{r}");
}

/// A `=> panic` vector passes only on a MIR `Panic`.
#[test]
fn selftest_panic_vector_needs_panic() {
    let r = selftest("tiny::opt true => panic\n").unwrap();
    assert_eq!(r, "fail tiny::opt the run completed (want panic)\n");
}
