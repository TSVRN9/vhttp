//! The generated tables are trusted spec, so they are re-checked here against the committed RFC
//! text with a parser independent of scripts/gen_tables.py.
use h3::qpack::huffman_table::huff_code;
use h3::qpack::static_table::*;

const A: &str = include_str!("../rfc/rfc9204-appendix-a.txt");
const B: &str = include_str!("../rfc/rfc7541-appendix-b.txt");

/// RFC line wrapping splits after '-' or '/' without a space, elsewhere at a space.
fn join(parts: &[&str]) -> String {
    let mut s = String::new();
    for p in parts {
        if !s.is_empty() && !s.ends_with('-') && !s.ends_with('/') {
            s.push(' ');
        }
        s.push_str(p);
    }
    s
}

fn parse_a() -> Vec<(String, String)> {
    // Each table row ends at the next "+---" border; collect its text lines first.
    let mut rows: Vec<(usize, Vec<&str>, Vec<&str>)> = vec![];
    for line in A.lines().map(str::trim) {
        if !line.starts_with('|') {
            continue;
        }
        let cells: Vec<&str> = line.trim_matches('|').split('|').map(str::trim).collect();
        assert_eq!(cells.len(), 3, "{line}");
        if cells[0] == "Index" {
            continue;
        }
        if let Ok(i) = cells[0].parse() {
            rows.push((i, vec![cells[1]], vec![cells[2]]));
        } else {
            assert!(cells[0].is_empty(), "{line}");
            let last = rows.last_mut().unwrap();
            if !cells[1].is_empty() {
                last.1.push(cells[1]);
            }
            if !cells[2].is_empty() {
                last.2.push(cells[2]);
            }
        }
    }
    for (k, r) in rows.iter().enumerate() {
        assert_eq!(r.0, k);
    }
    rows.iter().map(|r| (join(&r.1), join(&r.2))).collect()
}

#[test]
fn static_table_matches_rfc_text() {
    let rows = parse_a();
    assert_eq!(rows.len(), 99);
    assert_eq!(STATIC_TABLE_LEN, 99);
    for (i, (n, v)) in rows.iter().enumerate() {
        let (en, ev) = static_entry(i as u64).unwrap();
        assert_eq!((en, ev), (n.as_bytes(), v.as_bytes()), "index {i}");
    }
    assert_eq!(static_entry(99), None);
    assert_eq!(static_entry(u64::MAX), None);
}

#[test]
fn static_table_wrapped_rows() {
    // Hand-checked against the RFC: the rows whose cells wrap across lines.
    for (i, v) in [
        (30, "application/dns-message"),
        (41, "public, max-age=31536000"),
        (44, "application/dns-message"),
        (45, "application/javascript"),
        (47, "application/x-www-form-urlencoded"),
        (52, "text/html; charset=utf-8"),
        (54, "text/plain;charset=utf-8"),
        (57, "max-age=31536000; includesubdomains"),
        (58, "max-age=31536000; includesubdomains; preload"),
        (85, "script-src 'none'; object-src 'none'; base-uri 'none'"),
    ] {
        assert_eq!(static_entry(i).unwrap().1, v.as_bytes(), "index {i}");
    }
    assert_eq!(static_entry(0).unwrap(), (&b":authority"[..], &b""[..]));
}

#[test]
fn find_static_cases() {
    assert_eq!(find_static(b":method", b"GET"), StaticMatch::Exact(17));
    assert_eq!(find_static(b":method", b"PATCH"), StaticMatch::Name(15));
    assert_eq!(find_static(b":status", b"200"), StaticMatch::Exact(25));
    assert_eq!(find_static(b":authority", b""), StaticMatch::Exact(0));
    assert_eq!(find_static(b":authority", b"x"), StaticMatch::Name(0));
    assert_eq!(find_static(b"x-custom", b""), StaticMatch::None);
    assert_eq!(find_static(b"", b""), StaticMatch::None);
    for i in 0..99 {
        let (n, v) = static_entry(i).unwrap();
        let first = (0..99).find(|&j| static_entry(j).unwrap() == (n, v)).unwrap();
        assert_eq!(find_static(n, v), StaticMatch::Exact(first));
        let firstn = (0..99).find(|&j| static_entry(j).unwrap().0 == n).unwrap();
        assert_eq!(find_static(n, b"\x00no-such"), StaticMatch::Name(firstn));
    }
}

#[test]
fn huffman_table_matches_rfc_text() {
    let mut seen = vec![false; 257];
    for line in B.lines() {
        // Row tail: `<bits>  <hex>  [<len>]`; the len cell may be space-padded ("[ 6]").
        let Some(lb) = line.trim_end().strip_suffix(']').and_then(|l| l.rfind('[')) else { continue };
        let len = line.trim_end()[lb + 1..line.trim_end().len() - 1].trim();
        let [.., bits, hex] = line[..lb].split_whitespace().collect::<Vec<_>>()[..] else { continue };
        if !bits.starts_with('|') {
            continue;
        }
        let before = line[..line.find(bits).unwrap()].trim_end().strip_suffix(')').unwrap();
        let sym: usize = before[before.rfind('(').unwrap() + 1..].trim().parse().unwrap();
        let code = u32::from_str_radix(hex, 16).unwrap();
        let n: u8 = len.parse().unwrap();
        let bit_str: String = bits.chars().filter(|&c| c != '|').collect();
        assert_eq!(bit_str.len(), n as usize, "sym {sym}");
        assert_eq!(u32::from_str_radix(&bit_str, 2).unwrap(), code, "sym {sym}");
        assert!(!seen[sym], "dup {sym}");
        seen[sym] = true;
        assert_eq!(huff_code(sym as u16), (code, n), "sym {sym}");
    }
    let missing: Vec<_> = (0..257).filter(|&i| !seen[i]).collect();
    assert!(missing.is_empty(), "{missing:?}");
    assert_eq!(huff_code(256), (0x3fffffff, 30));
    assert_eq!(huff_code(257), (0, 0));
    assert_eq!(huff_code(u16::MAX), (0, 0));
}
