use crypto::rsa::{rsa_pss_sha256_sign, RsaPrivateKey};
use crypto::sha256::sha256;
use rsa::traits::{PrivateKeyParts, PublicKeyParts};
use rsa::BoxedUint;

mod vecdata;

fn h(s: &str) -> Vec<u8> {
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

// Minimal big-endian bytes, as a PKCS#8 INTEGER would give them.
fn min(b: &[u8]) -> Vec<u8> {
    let z = b.iter().take_while(|&&x| x == 0).count();
    b[z..].to_vec()
}

fn key(p_hex: &str, q_hex: &str) -> (RsaPrivateKey, rsa::RsaPrivateKey) {
    let u = |s: &str| BoxedUint::from_be_slice_vartime(&h(s));
    let k = rsa::RsaPrivateKey::from_p_q(u(p_hex), u(q_hex), BoxedUint::from(65537u32)).unwrap();
    let ours = RsaPrivateKey {
        n: min(&k.n().to_be_bytes()),
        e: min(&k.e().to_be_bytes()),
        d: min(&k.d().to_be_bytes()),
        p: min(&k.primes()[0].to_be_bytes()),
        q: min(&k.primes()[1].to_be_bytes()),
    };
    (ours, k)
}

fn mgf1(seed: &[u8], len: usize) -> Vec<u8> {
    let mut out = Vec::new();
    let mut c = 0u32;
    while out.len() < len {
        let mut m = seed.to_vec();
        m.extend_from_slice(&c.to_be_bytes());
        out.extend_from_slice(&sha256(&m));
        c += 1;
    }
    out.truncate(len);
    out
}

fn check(p: &str, q: &str, bits: u32) -> Vec<u8> {
    let (ours, k) = key(p, q);
    assert_eq!(k.n().bits(), bits);
    let salt: Vec<u8> = (0..32).collect();
    let msg = b"TLS 1.3, server CertificateVerify";
    let s = rsa_pss_sha256_sign(&ours, msg, &salt);
    assert_eq!(s.len(), ((bits + 7) / 8) as usize);
    assert_eq!(rsa_pss_sha256_sign(&ours, msg, &salt), s);
    let mut salt2 = salt.clone();
    salt2[0] ^= 1;
    assert_ne!(rsa_pss_sha256_sign(&ours, msg, &salt2), s);
    let pubk = k.to_public_key();
    pubk.verify(rsa::Pss::<sha2::Sha256>::new_with_salt(32), &sha256(msg), &s).unwrap();
    // salt recovery from s^e mod n
    let m = rsa::hazmat::rsa_encrypt(&pubk, &BoxedUint::from_be_slice(&s, k.n_bits_precision()).unwrap()).unwrap();
    let be = m.to_be_bytes();
    let em_len = ((bits - 1 + 7) / 8) as usize;
    let em = &be[be.len() - em_len..];
    assert_eq!(em[em_len - 1], 0xbc);
    let hh = &em[em_len - 33..em_len - 1];
    let mask = mgf1(hh, em_len - 33);
    let db: Vec<u8> = em[..em_len - 33].iter().zip(&mask).map(|(a, b)| a ^ b).collect();
    assert_eq!(&db[db.len() - 32..], &salt[..]);
    s
}

// The selftest vector crypto::rsa::rsa_pss_sign_inner (tools/ct-driver/selftest.txt): the signature
// of pss_rfc9500_2048 (checked by RustCrypto's verifier inside check), and the n and d that
// rsa_pss_sha256_sign hands rsa_pss_sign_inner for that key.
const SIG2048: &str = "8febad92958e60a78526f46a4054d7f864a71c7821b5a320dd941eaffdd8c1aa9c910479b6d778a02f388c942fefd72065b0f105fd5a2b4f9fdfb394a007967926a39a8700f5e9c504078b12d90c8cf5a8c259b9b292bb69c9bd6b2d9f2c141ba8a8f64fa49da75b4c790d82231d0109ae243b1bdd2789c8d9a8a1775f5a201ad6858474c811a379b7df3ec17d906420f67faa09ed0a35325166251371b83fd97404bb646280cdbe3b34d24b0412f56809644d4ffa5cb0806bb05a5e37ccc4319c9dd13763ade7d9c893681d5fc968460373a9ec382a642c25e340616ad7584745e4adc67a649ef63d11221f45b39c82869ce96f4ebf97fb4efb2e15eb57286b";
const N2048: &str = "b0f9e81943a7ae9892aade17ca7c40f8744fed2f8148e6c8eaa27b7d001548fb5192ab28b56c5060b118ccd131e594874c6ca989b56c27296f09fb93a034df32e97c6ff0998cfd8e6f42dda58acd1fa97986f144f3d154d67650175e6854b3a952003bc06887b8455ac2b19f7b2f76504ebc98ec945571b07892150ddc6a74ca0fbcd35497ce81534daf9418844b13aea31f9d5a6b9557bbdf619efd4e887f2d42b8dd8bc987eae1bf89cab85ee21e356305df6c07a8838e3ef41c595dcce43dafc49123ef4d8abba93d3905e4028d7ba91484a27596e07b4b6ed992f077b524d3dcfe7ddd5549be7cce8da035cfa0b3fb8f9e46f732b2a86b460165c08f5313";
const D2048: &str = "061a931863f94c3a9e3c5f17ea4cea1f67963b73a5a8325ad59f85ab79ad979720be1d41c9d812d6f2e4b713b3fe86113b353837b4012741f4e9743ad2e35ff0ad4034757e3b9af726fbe311cae8138d25d033516728b3735e2099b310dd7300dbaa29babe2032de797de38b16403c7abd41cb48703e98d836f5b0323530456cdaa2afd4edb75478f3ea60342662e493734b2b6c42a1c36d2b33ebffec76079daa507059e8148498758095fe9f2460bfd95715404884240ac1607a1de13a9e52601e0152a136da9226341bf827c85595116120ef202c8d42c44ca47babdd33ab7755885008bbe8cb5ec6d25180f1bf0dcace91972544ea44bc4a13b59b74d6f9";
const P2048: &str = "dd105702382f232b3681f53791e22617c7bf4e9acb81ed48daf6d6995da3eab642839aff012d2ea628b90af279fd3e6f7c93cd80f072f01ff2443b3ee8f24ed469a79613a41bd24020f92fd11059bd1d0f301b5ba7a9d3637ca8d65c1a9815417d8eab734b0b4f3a2c661d9a1a82f3ac734c40530669ab8e473045a58e65539d";
const Q2048: &str = "ccf1e5bb90c8e9781ea75bebf10bc252e11eb023a0260f1887552a56863f4a6421e8c600bf523d6cb1b0adbdd65bfee4a88a037e3d1a415e5bb95648da5a0ca26b54f4a63948522c3d5f89b94a72efff95134d5940ce45758f308980908956588eef575b3e4bc4c368cfe813ee9c252c2b02e0df91f1aa01938d38685d60ba6f";

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

#[test]
fn pss_rfc9500_2048() {
    let s = check(P2048, Q2048, 2048);
    assert_eq!(hex(&s), SIG2048);
}

// key() gives minimal big-endian bytes, as PKCS#8 would; rsa_pss_sha256_sign passes key.n and
// key.d to rsa_pss_sign_inner unchanged.
#[test]
fn pss_rfc9500_2048_inner_args() {
    let (ours, _) = key(P2048, Q2048);
    assert_eq!(hex(&ours.n), N2048);
    assert_eq!(hex(&ours.d), D2048);
}

#[test]
fn pss_rsa2049_len_and_salt() {
    let _ = check(
        "01fa9ff01c702938f8290b7fe5099537cf6c0d0b48a1f9ef02a02614387c464ab96737256ee4d1cb82c27c71f748737adb1939bd1aa6732ea3da37355f1b516b6c7052da370af35f9df697cdf0da1d140f29fd9b87bd777f21523030824f3ce0ffab10b79aeb16dba61509d65841c38f8721db01fcb63dab8c82a82312de30ca63",
        "cc0ecbe9727c4d3d1651a1be964f3f89e202875507f8686b1168565b262ace6724e33d24b23471ea83d13966f35c5aa8a2cdb9b556862c9f09b2c5afccec2868742a7b9b63a92e72a4145117a61fd8f33a74e2b1b32d45a08827cdc59dd8bc39c3a10fc341fd31a01b2362a0dad100c91ec4af744c23e68aba202b23da2403dd",
        2049,
    );
}

// 2052 bits: emBits = 2051, so 5 leftmost bits of maskedDB are cleared. The signature is the
// literal RFC 8017 §8.1.1/§9.1.1 transcription (Python), verified by pyca/cryptography.
#[test]
fn pss_rsa2052_masking_kat() {
    let s = check(
        "0359e29889111427d45e0a7d1b5c4fcd20e9385365d6ba47237a07f61f43b9749dbb0c4ca0eb731d3505fa1a9fc7f7523e6c50834c294e22c524e43aeeb0b55838130129e1f44cbd55f65573b7c241692a297239ab52fb2aeb9b83b5aaa35367c28d8a98818559deb516bebdd3ff5d2feefda32eb265a0e6b2045463b3752856d7",
        "03a2b01240d78fc8bd35a783bc29d19d100eb37822718cbde0cc246fc1bb49532f7354f1b0aa87bc5ba741eb43e5542ee7611dc7907d37ed6573590269c94fcc528907746d7dca3d7dfaddeba94578e47d176de829c93365099f7f1dcd23b918bae692e04987b30c9e7082ff5f6594b456755ecc7c5938e8ec8bdd6b2c85bcc92d",
        2052,
    );
    assert_eq!(s, h("04a08314b43fed2b7ea3d175947e1680f6b9b515e96c5e597935b5fcbb51e4f9e4d297e3e95b9a7d2865c5aa3d71b394295be3a0d23684d892a92fe81041304162ae6c1500e67821c05d2d8f02b654517a2a5cb890cc513be2a1e89d05ebf6cbbaf4b7ad62d4c90645952724280d5784289a0555f4d040b8f26cfbada65ac5006bc98a5920f708144f89b52d8ee326e53a64738d409ab946000965fcd0a0e717d4af6bcd5cfed126fa0088531a9b8b5fda2aded8ddf5c5bd4e4c3ab596f118847be17ebab2ba75d03854011a515e854538bcc04cc2a208d8b3c75e8d050872d6290ce7bda30129bd9c8f91ee35561465242362a9cd961fd77cc09f4c8252e751bb"));
}

// "Leading zeros allowed": zero-padded n, e, d, p and q sign identically.
#[test]
fn pss_zero_padded_fields() {
    let (ours, _) = key(
        "dd105702382f232b3681f53791e22617c7bf4e9acb81ed48daf6d6995da3eab642839aff012d2ea628b90af279fd3e6f7c93cd80f072f01ff2443b3ee8f24ed469a79613a41bd24020f92fd11059bd1d0f301b5ba7a9d3637ca8d65c1a9815417d8eab734b0b4f3a2c661d9a1a82f3ac734c40530669ab8e473045a58e65539d",
        "ccf1e5bb90c8e9781ea75bebf10bc252e11eb023a0260f1887552a56863f4a6421e8c600bf523d6cb1b0adbdd65bfee4a88a037e3d1a415e5bb95648da5a0ca26b54f4a63948522c3d5f89b94a72efff95134d5940ce45758f308980908956588eef575b3e4bc4c368cfe813ee9c252c2b02e0df91f1aa01938d38685d60ba6f",
    );
    let pad = |v: &Vec<u8>| [vec![0u8; 5], v.clone()].concat();
    let padded = RsaPrivateKey { n: pad(&ours.n), e: pad(&ours.e), d: pad(&ours.d), p: pad(&ours.p), q: pad(&ours.q) };
    let salt: Vec<u8> = (0..32).collect();
    let s = rsa_pss_sha256_sign(&ours, b"m", &salt);
    assert_eq!(rsa_pss_sha256_sign(&padded, b"m", &salt), s);
}

#[test]
fn cavp_pss_3072() {
    let u = |s: &str| BoxedUint::from_be_slice_vartime(&vecdata::hex(s));
    let (mut nh, mut eh, mut dh) = (String::new(), String::new(), String::new());
    let mut count = 0;
    for r in vecdata::rsp_records(&vecdata::data("nist/SigGenPSS_186-3.txt")) {
        if r.contains_key("n") || r.contains_key("e") {
            // n, then e and d, each in its own blank-line record; keep the latest
            for (k, dst) in [("n", &mut nh), ("e", &mut eh), ("d", &mut dh)] {
                if let Some(v) = r.get(k) {
                    *dst = v.clone();
                }
            }
            continue;
        }
        if r.get("mod").map(|m| m == "3072") != Some(true) || r.get("SHAAlg").map(|a| a == "SHA256") != Some(true) {
            continue;
        }
        let salt = vecdata::hex(&r["SaltVal"]);
        assert_eq!(salt.len(), 32);
        let k = rsa::RsaPrivateKey::from_components(u(&nh), u(&eh), u(&dh), vec![]).unwrap();
        let ours = RsaPrivateKey {
            n: min(&k.n().to_be_bytes()),
            e: min(&k.e().to_be_bytes()),
            d: min(&k.d().to_be_bytes()),
            p: min(&k.primes()[0].to_be_bytes()),
            q: min(&k.primes()[1].to_be_bytes()),
        };
        let s = rsa_pss_sha256_sign(&ours, &vecdata::hex(&r["Msg"]), &salt);
        assert_eq!(s, vecdata::hex(&r["S"]), "vector {count}");
        count += 1;
    }
    assert_eq!(count, 10);
}

// The first SHA-256 key of Wycheproof's 4096-bit file; p and q recovered by from_components.
#[test]
fn pss_4096_verifies() {
    let j = vecdata::parse_json(&vecdata::data("wycheproof/rsa_pkcs1_4096_sig_gen_test.json"));
    let groups = j.get("testGroups").arr();
    let pk = groups.iter().find(|g| g.get("sha").str() == "SHA-256").unwrap().get("privateKey");
    let u = |f: &str| BoxedUint::from_be_slice_vartime(&vecdata::hex(pk.get(f).str()));
    let k = rsa::RsaPrivateKey::from_components(u("modulus"), u("publicExponent"), u("privateExponent"), vec![]).unwrap();
    let ours = RsaPrivateKey {
        n: min(&k.n().to_be_bytes()),
        e: min(&k.e().to_be_bytes()),
        d: min(&k.d().to_be_bytes()),
        p: min(&k.primes()[0].to_be_bytes()),
        q: min(&k.primes()[1].to_be_bytes()),
    };
    let salt = [0x5au8; 32];
    let msg = b"TLS 1.3, server CertificateVerify";
    let s = rsa_pss_sha256_sign(&ours, msg, &salt);
    assert_eq!(s.len(), 512);
    k.to_public_key().verify(rsa::Pss::<sha2::Sha256>::new_with_salt(32), &sha256(msg), &s).unwrap();
}
