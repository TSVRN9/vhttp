mod vecdata;
use crypto::ecdsa::serialize_ecdsa_der;
use crypto::gcm::{aes128_gcm_open, aes128_gcm_seal};
use crypto::hkdf::{hkdf_expand, hkdf_extract};
use crypto::hmac::hmac_sha256;
use crypto::p256::{p256_ecdh, p256_public_key};
use crypto::sha256::sha256;
use vecdata::*;

fn cat(parts: &[&[u8]]) -> Vec<u8> {
    parts.concat()
}

fn hx(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn msg_by_len(r: &std::collections::BTreeMap<String, String>) -> Vec<u8> {
    let len: usize = r["Len"].parse().unwrap();
    let m = hex(&r["Msg"]);
    assert!(len % 8 == 0);
    m[..len / 8].to_vec()
}

/// (group, test) pairs of a Wycheproof file.
fn wp(rel: &str) -> Vec<(J, J)> {
    let j = parse_json(&data(rel));
    let mut out = Vec::new();
    for g in j.get("testGroups").arr() {
        for t in g.get("tests").arr() {
            out.push((g.clone(), t.clone()));
        }
    }
    assert_eq!(out.len() as i64, j.get("numberOfTests").num());
    out
}

#[test]
fn sources_match() {
    let text = data("SOURCES.txt");
    let mut n = 0;
    for line in text.lines().filter(|l| !l.starts_with('#') && !l.is_empty()) {
        let f: Vec<&str> = line.split_whitespace().collect();
        assert_eq!(f.len(), 4, "{line}");
        let bytes = std::fs::read(format!("{}/tests/data/{}", env!("CARGO_MANIFEST_DIR"), f[1])).unwrap();
        assert_eq!(hx(&sha256(&bytes)), f[0], "{}", f[1]);
        n += 1;
    }
    assert_eq!(n, 18);
}

fn sha_file(rel: &str, want: usize) {
    let mut n = 0;
    for r in rsp_records(&data(rel)).iter().filter(|r| r.contains_key("Len")) {
        assert_eq!(hx(&sha256(&msg_by_len(r))), r["MD"], "{rel} Len {}", r["Len"]);
        n += 1;
    }
    assert_eq!(n, want);
}

#[test]
fn cavp_sha256_short() {
    sha_file("nist/SHA256ShortMsg.rsp", 65);
}

#[test]
fn cavp_sha256_long() {
    sha_file("nist/SHA256LongMsg.rsp", 64);
}

#[test]
fn cavp_sha256_monte() {
    let recs = rsp_records(&data("nist/SHA256Monte.rsp"));
    let mut seed = hex(&recs.iter().find_map(|r| r.get("Seed")).unwrap());
    let mut n = 0;
    for r in recs.iter().filter(|r| r.contains_key("MD")) {
        let mut md = [seed.clone(), seed.clone(), seed.clone()];
        for _ in 3..1003 {
            let next = sha256(&cat(&[&md[0], &md[1], &md[2]])).to_vec();
            md = [md[1].clone(), md[2].clone(), next];
        }
        seed = md[2].clone();
        assert_eq!(hx(&seed), r["MD"], "COUNT {}", r["COUNT"]);
        n += 1;
    }
    assert_eq!(n, 100);
}

#[test]
fn cavp_hmac() {
    let mut n = 0;
    for r in rsp_records(&data("nist/HMAC.rsp")).iter().filter(|r| r.get("L").map(|l| l == "32").unwrap_or(false) && r.contains_key("Mac")) {
        let t: usize = r["Tlen"].parse().unwrap();
        let k = hex(&r["Key"]);
        assert_eq!(k.len(), r["Klen"].parse::<usize>().unwrap());
        assert_eq!(hx(&hmac_sha256(&k, &hex(&r["Msg"]))[..t]), r["Mac"], "Count {}", r["Count"]);
        n += 1;
    }
    assert_eq!(n, 225);
}

#[test]
fn wycheproof_hmac() {
    let (mut v, mut i) = (0, 0);
    for (g, t) in wp("wycheproof/hmac_sha256_test.json") {
        let tag = hex(t.get("tag").str());
        assert_eq!(tag.len() as i64, g.get("tagSize").num() / 8);
        let got = hmac_sha256(&hex(t.get("key").str()), &hex(t.get("msg").str()));
        let eq = got[..tag.len()] == tag[..];
        match t.get("result").str() {
            "valid" => { assert!(eq, "tcId {}", t.get("tcId").num()); v += 1 }
            "invalid" => { assert!(!eq, "tcId {}", t.get("tcId").num()); i += 1 }
            r => panic!("result {r}"),
        }
    }
    assert_eq!((v + i, v, i), (174, 66, 108));
}

#[test]
fn wycheproof_hkdf() {
    let (mut run, mut skipped) = (0, 0);
    for (_, t) in wp("wycheproof/hkdf_sha256_test.json") {
        let size = t.get("size").num() as usize;
        if size > 8160 {
            assert_eq!(t.get("result").str(), "invalid");
            skipped += 1;
            continue;
        }
        assert_eq!(t.get("result").str(), "valid", "tcId {}", t.get("tcId").num());
        let prk = hkdf_extract(&hex(t.get("salt").str()), &hex(t.get("ikm").str()));
        assert_eq!(hx(&hkdf_expand(&prk, &hex(t.get("info").str()), size)), t.get("okm").str(), "tcId {}", t.get("tcId").num());
        run += 1;
    }
    assert_eq!((run, skipped), (83, 3));
}

fn gcm_filter(r: &std::collections::BTreeMap<String, String>) -> bool {
    r.get("Keylen").map(|s| s == "128").unwrap_or(false)
        && r.get("IVlen").map(|s| s == "96").unwrap_or(false)
        && r.get("Taglen").map(|s| s == "128").unwrap_or(false)
        && r.contains_key("Key")
}

#[test]
fn cavp_gcm_encrypt() {
    let mut n = 0;
    for r in rsp_records(&data("nist/gcmEncryptExtIV128.rsp")).iter().filter(|r| gcm_filter(r)) {
        let want = cat(&[&hex(&r["CT"]), &hex(&r["Tag"])]);
        let got = aes128_gcm_seal(&hex(&r["Key"]), &hex(&r["IV"]), &hex(&r["AAD"]), &hex(&r["PT"]));
        assert_eq!(got, want, "Count {}", r["Count"]);
        n += 1;
    }
    assert_eq!(n, 375);
}

#[test]
fn cavp_gcm_decrypt() {
    let (mut n, mut fail) = (0, 0);
    for r in rsp_records(&data("nist/gcmDecrypt128.rsp")).iter().filter(|r| gcm_filter(r)) {
        let ct = cat(&[&hex(&r["CT"]), &hex(&r["Tag"])]);
        let got = aes128_gcm_open(&hex(&r["Key"]), &hex(&r["IV"]), &hex(&r["AAD"]), &ct);
        if r.contains_key("FAIL") {
            assert_eq!(got, None, "Count {}", r["Count"]);
            fail += 1;
        } else {
            assert_eq!(got, Some(hex(&r["PT"])), "Count {}", r["Count"]);
        }
        n += 1;
    }
    assert_eq!((n, fail), (375, 196));
}

#[test]
fn wycheproof_gcm() {
    let (mut v, mut i) = (0, 0);
    for (g, t) in wp("wycheproof/aes_gcm_test.json") {
        if g.get("keySize").num() != 128 || g.get("ivSize").num() != 96 {
            continue;
        }
        let (key, iv, aad) = (hex(t.get("key").str()), hex(t.get("iv").str()), hex(t.get("aad").str()));
        let ct = cat(&[&hex(t.get("ct").str()), &hex(t.get("tag").str())]);
        let id = t.get("tcId").num();
        match t.get("result").str() {
            "valid" => {
                let pt = hex(t.get("msg").str());
                assert_eq!(aes128_gcm_seal(&key, &iv, &aad, &pt), ct, "tcId {id}");
                assert_eq!(aes128_gcm_open(&key, &iv, &aad, &ct), Some(pt), "tcId {id}");
                v += 1;
            }
            "invalid" => {
                assert_eq!(aes128_gcm_open(&key, &iv, &aad, &ct), None, "tcId {id}");
                i += 1;
            }
            r => panic!("result {r}"),
        }
    }
    assert_eq!((v + i, v, i), (67, 40, 27));
}

fn pt65(x: &str, y: &str) -> Vec<u8> {
    cat(&[&[4], &hex(x), &hex(y)])
}

#[test]
fn cavp_ecdh() {
    let mut n = 0;
    for r in rsp_records(&data("nist/KAS_ECC_CDH_PrimitiveTest.txt")).iter().filter(|r| r.get("section").map(|s| s == "P-256").unwrap_or(false) && r.contains_key("COUNT")) {
        let d = hex(&r["dIUT"]);
        let z = p256_ecdh(&d, &pt65(&r["QCAVSx"], &r["QCAVSy"]));
        assert_eq!(z.map(|z| hx(&z)), Some(r["ZIUT"].clone()), "COUNT {}", r["COUNT"]);
        assert_eq!(p256_public_key(&d).map(|p| p.to_vec()), Some(pt65(&r["QIUTx"], &r["QIUTy"])), "COUNT {}", r["COUNT"]);
        n += 1;
    }
    assert_eq!(n, 25);
}

/// Strip leading 00 octets down to 32, left-pad shorter values to 32.
fn norm32(b: &[u8]) -> Vec<u8> {
    let mut v = b;
    while v.len() > 32 && v[0] == 0 {
        v = &v[1..];
    }
    assert!(v.len() <= 32, "value longer than 32 octets");
    let mut out = vec![0u8; 32 - v.len()];
    out.extend_from_slice(v);
    out
}

#[test]
fn wycheproof_ecdh() {
    let (mut n, mut valid) = (0, 0);
    for (_, t) in wp("wycheproof/ecdh_secp256r1_ecpoint_test.json") {
        let id = t.get("tcId").num();
        let d = norm32(&hex(t.get("private").str()));
        let p = hex(t.get("public").str());
        let got = p256_ecdh(&d, &p);
        if p.len() == 65 && t.get("result").str() == "valid" {
            assert_eq!(got.map(|z| hx(&z)).as_deref(), Some(t.get("shared").str()), "tcId {id}");
            valid += 1;
        } else {
            assert_eq!(got, None, "tcId {id} ({}, {} octets)", t.get("result").str(), p.len());
        }
        n += 1;
    }
    assert_eq!((n, valid), (355, 330));
}

/// Splits `30 len 02 lr r 02 ls s` (short-form lengths, as the valid rows use) into r, s.
fn der_rs(sig: &[u8]) -> (Vec<u8>, Vec<u8>) {
    assert_eq!(sig[0], 0x30);
    assert_eq!(sig[1] as usize, sig.len() - 2);
    assert_eq!(sig[2], 0x02);
    let lr = sig[3] as usize;
    let r = &sig[4..4 + lr];
    assert_eq!(sig[4 + lr], 0x02);
    let ls = sig[5 + lr] as usize;
    let s = &sig[6 + lr..6 + lr + ls];
    assert_eq!(6 + lr + ls, sig.len());
    (norm32(r), norm32(s))
}

#[test]
fn wycheproof_ecdsa_der() {
    let mut n = 0;
    for (_, t) in wp("wycheproof/ecdsa_secp256r1_sha256_test.json") {
        if t.get("result").str() != "valid" {
            continue;
        }
        let sig = hex(t.get("sig").str());
        let (r, s) = der_rs(&sig);
        let mut out = Vec::new();
        serialize_ecdsa_der(&cat(&[&r, &s]), &mut out);
        assert_eq!(out, sig, "tcId {}", t.get("tcId").num());
        n += 1;
    }
    assert_eq!(n, 174);
}
