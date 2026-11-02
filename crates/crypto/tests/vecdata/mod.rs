#![allow(dead_code)]
// Minimal readers for the CAVP .rsp and Wycheproof .json files under tests/data.
use std::collections::BTreeMap;

pub fn hex(s: &str) -> Vec<u8> {
    assert!(s.len() % 2 == 0, "odd hex length");
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

pub fn data(rel: &str) -> String {
    std::fs::read_to_string(format!("{}/tests/data/{}", env!("CARGO_MANIFEST_DIR"), rel)).unwrap()
}

/// Records separated by blank lines. `[K = v]` / `[K=v]` headers carry into later records,
/// `[X]` is key `section`, a bare `FAIL` is key `FAIL`.
pub fn rsp_records(text: &str) -> Vec<BTreeMap<String, String>> {
    let mut out = Vec::new();
    let mut hdr: BTreeMap<String, String> = BTreeMap::new();
    let mut cur: BTreeMap<String, String> = BTreeMap::new();
    fn flush(out: &mut Vec<BTreeMap<String, String>>, hdr: &BTreeMap<String, String>, cur: &mut BTreeMap<String, String>) {
        if !cur.is_empty() {
            let mut r = hdr.clone();
            r.append(cur);
            out.push(r);
        }
    }
    for line in text.lines() {
        let line = line.trim_end_matches('\r').trim();
        if line.is_empty() {
            flush(&mut out, &hdr, &mut cur);
        } else if line.starts_with('#') {
        } else if line.starts_with('[') && line.ends_with(']') {
            flush(&mut out, &hdr, &mut cur);
            let inner = &line[1..line.len() - 1];
            match inner.split_once('=') {
                Some((k, v)) => hdr.insert(k.trim().to_string(), v.trim().to_string()),
                None => hdr.insert("section".to_string(), inner.trim().to_string()),
            };
        } else if line == "FAIL" {
            cur.insert("FAIL".to_string(), String::new());
        } else {
            let (k, v) = line.split_once('=').unwrap_or_else(|| panic!("bad rsp line {line:?}"));
            cur.insert(k.trim().to_string(), v.trim().to_string());
        }
    }
    flush(&mut out, &hdr, &mut cur);
    out
}

#[derive(Debug, Clone, PartialEq)]
pub enum J {
    Null,
    Bool(bool),
    Num(i64),
    Str(String),
    Arr(Vec<J>),
    Obj(BTreeMap<String, J>),
}

impl J {
    pub fn get(&self, k: &str) -> &J {
        match self {
            J::Obj(m) => m.get(k).unwrap_or_else(|| panic!("no key {k}")),
            _ => panic!("not an object"),
        }
    }
    pub fn has(&self, k: &str) -> bool {
        matches!(self, J::Obj(m) if m.contains_key(k))
    }
    pub fn str(&self) -> &str {
        match self { J::Str(s) => s, _ => panic!("not a string: {self:?}") }
    }
    pub fn num(&self) -> i64 {
        match self { J::Num(n) => *n, _ => panic!("not a number: {self:?}") }
    }
    pub fn arr(&self) -> &[J] {
        match self { J::Arr(a) => a, _ => panic!("not an array") }
    }
}

pub fn parse_json(s: &str) -> J {
    let b = s.as_bytes();
    let mut i = 0;
    let v = value(b, &mut i);
    ws(b, &mut i);
    assert_eq!(i, b.len(), "trailing input");
    v
}

fn ws(b: &[u8], i: &mut usize) {
    while *i < b.len() && matches!(b[*i], b' ' | b'\n' | b'\r' | b'\t') {
        *i += 1;
    }
}

fn lit(b: &[u8], i: &mut usize, w: &str) {
    assert!(b[*i..].starts_with(w.as_bytes()), "bad literal at {}", *i);
    *i += w.len();
}

fn value(b: &[u8], i: &mut usize) -> J {
    ws(b, i);
    match b[*i] {
        b'n' => { lit(b, i, "null"); J::Null }
        b't' => { lit(b, i, "true"); J::Bool(true) }
        b'f' => { lit(b, i, "false"); J::Bool(false) }
        b'"' => J::Str(string(b, i)),
        b'[' => {
            *i += 1;
            let mut v = Vec::new();
            ws(b, i);
            if b[*i] == b']' { *i += 1; return J::Arr(v); }
            loop {
                v.push(value(b, i));
                ws(b, i);
                match b[*i] { b',' => *i += 1, b']' => { *i += 1; return J::Arr(v); } c => panic!("bad array byte {c}") }
            }
        }
        b'{' => {
            *i += 1;
            let mut m = BTreeMap::new();
            ws(b, i);
            if b[*i] == b'}' { *i += 1; return J::Obj(m); }
            loop {
                ws(b, i);
                assert_eq!(b[*i], b'"', "object key");
                let k = string(b, i);
                ws(b, i);
                assert_eq!(b[*i], b':');
                *i += 1;
                let v = value(b, i);
                assert!(m.insert(k, v).is_none(), "duplicate key");
                ws(b, i);
                match b[*i] { b',' => *i += 1, b'}' => { *i += 1; return J::Obj(m); } c => panic!("bad object byte {c}") }
            }
        }
        b'-' | b'0'..=b'9' => {
            let st = *i;
            *i += 1;
            while *i < b.len() && b[*i].is_ascii_digit() { *i += 1; }
            assert!(!matches!(b.get(*i), Some(b'.' | b'e' | b'E')), "float");
            J::Num(std::str::from_utf8(&b[st..*i]).unwrap().parse().unwrap())
        }
        c => panic!("bad json byte {c} at {}", *i),
    }
}

fn string(b: &[u8], i: &mut usize) -> String {
    *i += 1;
    let mut out = Vec::new();
    loop {
        match b[*i] {
            b'"' => { *i += 1; return String::from_utf8(out).unwrap(); }
            b'\\' => {
                *i += 1;
                match b[*i] {
                    b'"' => out.push(b'"'),
                    b'\\' => out.push(b'\\'),
                    b'/' => out.push(b'/'),
                    b'n' => out.push(b'\n'),
                    b'r' => out.push(b'\r'),
                    b't' => out.push(b'\t'),
                    b'u' => {
                        let c = u32::from_str_radix(std::str::from_utf8(&b[*i + 1..*i + 5]).unwrap(), 16).unwrap();
                        let mut buf = [0u8; 4];
                        out.extend_from_slice(char::from_u32(c).expect("surrogate").encode_utf8(&mut buf).as_bytes());
                        *i += 4;
                    }
                    c => panic!("bad escape {c}"),
                }
                *i += 1;
            }
            c => { out.push(c); *i += 1; }
        }
    }
}
