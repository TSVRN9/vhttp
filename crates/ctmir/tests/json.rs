use ctmir::json::{obj_get, parse, Json};
use std::time::Instant;

fn s(b: &[u8]) -> Json { Json::Str(b.to_vec()) }

#[test]
fn accepts() {
    assert_eq!(parse(b"null"), Some(Json::Null));
    assert_eq!(parse(b"true"), Some(Json::Bool(true)));
    assert_eq!(parse(b"false"), Some(Json::Bool(false)));
    assert_eq!(parse(b"0"), Some(Json::Num(false, 0)));
    assert_eq!(parse(b"[]"), Some(Json::Arr(vec![])));
    assert_eq!(parse(b"{}"), Some(Json::Obj(vec![])));
    assert_eq!(parse(b"\"\x7f\""), Some(s(b"\x7f")));
    assert_eq!(parse(b"\"\\u001f\\u0000\\u000b\""), Some(s(b"\x1f\x00\x0b")));
    assert_eq!(
        parse("[1,-2,{\"a\":\"x\\\"\\\\\\n\\u0001é\"}]".as_bytes()),
        Some(Json::Arr(vec![
            Json::Num(false, 1),
            Json::Num(true, 2),
            Json::Obj(vec![(b"a".to_vec(), s("x\"\\\n\u{1}é".as_bytes()))]),
        ]))
    );
    assert_eq!(parse(b"340282366920938463463374607431768211455"), Some(Json::Num(false, u128::MAX)));
    assert_eq!(parse(b"-340282366920938463463374607431768211455"), Some(Json::Num(true, u128::MAX)));
    let deep = |n: usize| [vec![b'['; n], vec![b']'; n]].concat();
    assert!(parse(&deep(256)).is_some());
    assert!(parse(&deep(257)).is_none());
}

#[test]
fn rejects() {
    for b in [
        &b"[1, 2]"[..], b" 1", b"1 ", b"01", b"-0", b"-", b"1.5", b"1e3", b"{\"a\":1,\"a\":2}",
        b"\"\\u0041\"", // serde writes `A` raw
        b"\"\\u000a\"", // serde writes `\n`
        b"\"\\u001F\"", // serde's hex is lowercase
        b"\"\\/\"", b"\"\x01\"", b"\"abc", b"[1,]", b"[,1]", b"{\"a\"}", b"{1:2}", b"nul", b"",
        b"340282366920938463463374607431768211456", b"[1]]",
    ] {
        assert_eq!(parse(b), None, "{:?}", String::from_utf8_lossy(b));
    }
    assert_eq!(parse(&vec![b'['; 300]), None);
    let mut nested = vec![b'['; 300];
    nested.extend(vec![b']'; 300]);
    assert_eq!(parse(&nested), None);
}

#[test]
fn get() {
    let Some(Json::Obj(f)) = parse(b"{\"a\":1,\"bc\":[],\"b\":null}") else { panic!() };
    assert_eq!(obj_get(&f, b"b"), Some(&Json::Null));
    assert_eq!(obj_get(&f, b"bc"), Some(&Json::Arr(vec![])));
    assert_eq!(obj_get(&f, b"c"), None);
}

/// Appends a serde_json-style compact document of nested records and long escaped strings.
fn synth(out: &mut Vec<u8>, depth: u32, seed: &mut u64) {
    *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    out.extend_from_slice(b"{\"id\":");
    out.extend_from_slice((*seed >> 20).to_string().as_bytes());
    out.extend_from_slice(b",\"name\":\"");
    for k in 0..200u64 {
        match (*seed >> (k % 50)) % 23 {
            0 => out.extend_from_slice(b"\\\""),
            1 => out.extend_from_slice(b"\\n"),
            2 => out.extend_from_slice(b"\\u0001"),
            3 => out.extend_from_slice("é".as_bytes()),
            _ => out.push(b'a' + (k % 26) as u8),
        }
    }
    out.extend_from_slice(b"\",\"neg\":-42,\"kids\":[");
    if depth > 0 {
        for i in 0..6 {
            if i > 0 { out.push(b','); }
            synth(out, depth - 1, seed);
        }
    }
    out.extend_from_slice(b"],\"x\":null}");
}

#[test]
fn synthetic_perf() {
    let mut doc = Vec::new();
    synth(&mut doc, 5, &mut 1);
    let t = Instant::now();
    let j = parse(&doc);
    eprintln!("synthetic: {} bytes parsed in {:?}", doc.len(), t.elapsed());
    assert!(j.is_some());
}

/// Run by the controller after Task 1: `CT_DUMP_DIR=<dir> cargo test -p ctmir --release -- --ignored`.
#[test]
#[ignore]
fn dumps() {
    let dir = std::env::var("CT_DUMP_DIR").expect("CT_DUMP_DIR");
    let mut paths: Vec<_> = std::fs::read_dir(&dir).unwrap().map(|e| e.unwrap().path()).collect();
    paths.sort();
    let mut n = 0;
    for p in paths {
        let name = p.file_name().unwrap().to_string_lossy().into_owned();
        if !(name.starts_with("mir-") && name.ends_with(".json")) { continue; }
        let b = std::fs::read(&p).unwrap();
        let t = Instant::now();
        let ok = parse(&b).is_some();
        eprintln!("{name}: {} bytes, {:?}, {}", b.len(), t.elapsed(), if ok { "ok" } else { "REJECTED" });
        assert!(ok, "{name} rejected");
        n += 1;
    }
    assert!(n > 0, "no mir-*.json in {dir}");
}
