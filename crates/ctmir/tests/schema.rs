use ctmir::json::{parse, Json};
use ctmir::mir::*;
use ctmir::schema::decode;
use std::time::Instant;

const TINY: &[u8] = include_bytes!("data/tiny.json");

fn dec(b: &[u8]) -> Option<MirCrate> { decode(parse(b).expect("parse")) }

/// `b` with its only occurrence of `from` replaced by `to`.
fn edit(b: &[u8], from: &str, to: &str) -> Vec<u8> {
    let s = std::str::from_utf8(b).unwrap();
    assert_eq!(s.matches(from).count(), 1, "{from}");
    s.replacen(from, to, 1).into_bytes()
}

fn body<'a>(m: &'a MirCrate, name: &str) -> &'a Body {
    m.insts.iter().find(|i| i.name == name.as_bytes()).unwrap().body.as_ref().unwrap()
}

fn assigned(s: &Statement) -> &Rvalue {
    match &s.kind { StatementKind::Assign(_, rv) => rv, k => panic!("{k:?}") }
}

#[test]
fn tiny() {
    let m = dec(TINY).expect("tiny.json decodes");
    assert_eq!(m.crate_name, b"tiny");
    assert!(!format!("{m:?}").contains("Unknown("));
    // `a[i & 3] ^ x[1]`: `_0 = BitXor(move _4, const 2_u8)`.
    let b = body(&m, "tiny::tiny");
    match assigned(&b.blocks[1].statements[1]) {
        Rvalue::BinaryOp(BinOp::BitXor, Operand::Move(p), Operand::Constant(c)) => {
            assert_eq!((p.local, p.projection.len()), (4, 0));
            let ConstantKind::Allocated(a) = &c.const_.kind else { panic!() };
            assert_eq!(a.bytes, vec![Some(2)]);
        },
        rv => panic!("{rv:?}"),
    }
    // `None::<u8>`: the tag byte, then an uninitialized payload byte (`null`).
    let b = body(&m, "tiny::opt");
    match assigned(&b.blocks[2].statements[0]) {
        Rvalue::Use(Operand::Constant(c), _) => {
            let ConstantKind::Allocated(a) = &c.const_.kind else { panic!() };
            assert_eq!(a.bytes, vec![Some(0), None]);
        },
        rv => panic!("{rv:?}"),
    }
    // `tiny(a, 2)` resolves to `tiny::tiny`'s instance.
    let tiny_id = m.insts.iter().find(|i| i.name == b"tiny::tiny").unwrap().id;
    assert_eq!((m.calls.len(), m.calls[0].def_name.as_slice(), m.calls[0].resolved), (1, &b"tiny::tiny"[..], Some(tiny_id)));
}

#[test]
fn renamed_variant_is_unknown() {
    let m = dec(&edit(TINY, "\"BitXor\"", "\"BitXorX\"")).expect("still decodes");
    match assigned(&body(&m, "tiny::tiny").blocks[1].statements[1]) {
        Rvalue::BinaryOp(BinOp::Unknown(j), _, _) => assert_eq!(*j, Json::Str(b"BitXorX".to_vec())),
        rv => panic!("{rv:?}"),
    }
    // A renamed data variant keeps its payload whole.
    let m = dec(&edit(TINY, "{\"StorageLive\":3}", "{\"StorageLife\":3}")).expect("still decodes");
    let k = &body(&m, "tiny::tiny").blocks[0].statements[0].kind;
    assert_eq!(*k, StatementKind::Unknown(Json::Obj(vec![(b"StorageLife".to_vec(), Json::Num(false, 3))])));
}

#[test]
fn not_serde_shape_is_none() {
    for (from, to) in [
        // struct fields out of order, one missing, one extra
        ("{\"id\":0,\"usize\":3}", "{\"usize\":3,\"id\":0}"),
        ("\"arg_count\":2,\"var_debug_info\"", "\"var_debug_info\""),
        ("\"spread_arg\":null,\"span\":5}", "\"spread_arg\":null,\"span\":5,\"x\":1}"),
        // a known data variant without its payload, a known unit variant with one
        ("{\"StorageLive\":3}", "\"StorageLive\""),
        ("\"Deref\"", "{\"Deref\":null}"),
        // an enum envelope with two keys
        ("{\"StorageLive\":3}", "{\"StorageLive\":3,\"Nop\":3}"),
        // integers that are negative or outside their rustc width (u64, u8)
        ("\"spread_arg\":null,\"span\":5}", "\"spread_arg\":null,\"span\":-5}"),
        ("{\"id\":0,\"usize\":3}", "{\"id\":0,\"usize\":18446744073709551616}"),
        ("\"bytes\":[0,null]", "\"bytes\":[256,null]"),
    ] {
        assert!(dec(&edit(TINY, from, to)).is_none(), "{to}");
    }
}

/// Every `mir-*.json` under `$CT_DUMP_DIR`, recursively: decodes each and lists the bodies that hold
/// an `Unknown`, by variant name. `CT_DUMP_DIR=$CT_OUT cargo test -p ctmir --release --test schema
/// -- --ignored --nocapture`.
#[test]
#[ignore]
fn dumps() {
    let dir = std::path::PathBuf::from(std::env::var("CT_DUMP_DIR").expect("CT_DUMP_DIR"));
    let (mut todo, mut paths) = (vec![dir.clone()], Vec::new());
    while let Some(d) = todo.pop() {
        for e in std::fs::read_dir(&d).unwrap() {
            let p = e.unwrap().path();
            if p.is_dir() { todo.push(p); } else { paths.push(p); }
        }
    }
    paths.sort();
    let mut n = 0;
    for p in paths {
        let file = p.file_name().unwrap().to_string_lossy().into_owned();
        if !(file.starts_with("mir-") && file.ends_with(".json")) { continue; }
        let name = p.strip_prefix(&dir).unwrap().display().to_string();
        let t = Instant::now();
        let m = dec(&std::fs::read(&p).unwrap()).unwrap_or_else(|| panic!("{name}: not serde's shape"));
        let bodies: Vec<_> = m.insts.iter().filter_map(|i| i.body.as_ref().map(|b| (&i.name, format!("{b:?}")))).collect();
        let unk: Vec<_> = bodies.iter().filter(|(_, d)| d.contains("Unknown(")).collect();
        eprintln!("{name}: {:?}, {} insts, {} bodies, {} with Unknown", t.elapsed(), m.insts.len(), bodies.len(), unk.len());
        for (i, d) in unk { eprintln!("  {}: {:?}", String::from_utf8_lossy(i), unknown_names(d)); }
        let d = format!("{m:?}");
        if d.contains("Unknown(") { eprintln!("  whole crate (bodies and tables): {:?}", unknown_names(&d)); }
        n += 1;
    }
    assert!(n > 0, "no mir-*.json under {}", dir.display());
}

/// The variant names held by the `Unknown(Str(..))`/`Unknown(Obj([(..` values in a Debug string.
fn unknown_names(d: &str) -> std::collections::BTreeSet<String> {
    d.match_indices("Unknown(").map(|(i, _)| {
        let rest = &d[i + 8..];
        let start = rest.find('[').unwrap() + 1;
        let rest = rest[start..].trim_start_matches(['(', '[']);
        let end = rest.find(']').unwrap();
        let bytes: Vec<u8> = rest[..end].split(", ").map(|x| x.parse().unwrap()).collect();
        String::from_utf8(bytes).unwrap()
    }).collect()
}
