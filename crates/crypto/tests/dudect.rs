//! dudect-style timing tests (Phase 7a; docs/crypto-binary-audit.md, "Timing tests"). Ignored, so
//! run by hand, pinned to one P-core. crypto has no libc dev-dependency, so pinning is taskset's
//! job; each line printed carries the CPUs the process may run on and the load average:
//!
//!     cargo test --release -p crypto --test dudect --no-run
//!     taskset -c 2 cargo test --release -p crypto --test dudect -- --ignored --nocapture --test-threads 1
//!
//! Each target test first runs the leaky control through the same harness; the target's verdict
//! counts only if the control gives |t| > 10.

use crypto::aes::aes128_encrypt_block;
use crypto::ecdsa::p256_ecdsa_sign;
use crypto::gcm::{aes128_gcm_open, aes128_gcm_seal};
use crypto::p256::{p256_ecdh, p256_public_key};
use crypto::rsa::{rsa_pss_sha256_sign, RsaPrivateKey};
use crypto::sha256::sha256;
use rsa::traits::{PrivateKeyParts, PublicKeyParts};
use rsa::BoxedUint;
use std::hint::black_box;
use std::time::Instant;

const T_MAX: f64 = 10.0;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn bytes<const N: usize>(&mut self) -> [u8; N] {
        core::array::from_fn(|_| self.next() as u8)
    }
}

#[cfg(target_arch = "x86_64")]
fn now() -> u64 {
    use core::arch::x86_64::{_mm_lfence, _rdtsc};
    // SAFETY: lfence and rdtsc are baseline x86-64.
    unsafe {
        _mm_lfence();
        let t = _rdtsc();
        _mm_lfence();
        t
    }
}

#[cfg(not(target_arch = "x86_64"))]
fn now() -> u64 {
    static T0: std::sync::OnceLock<Instant> = std::sync::OnceLock::new();
    T0.get_or_init(Instant::now).elapsed().as_nanos() as u64
}

/// Welch's t of the two classes, after dropping every measurement above the pooled 95th
/// percentile. Also returns the kept count, the class means (`[random, fixed]`) and the standard
/// error of their difference.
fn welch_cropped(ts: &[u64], fixed: &[bool]) -> (f64, usize, [f64; 2], f64) {
    let mut s = ts.to_vec();
    s.sort_unstable();
    let cut = s[s.len() * 95 / 100];
    let (mut n, mut m, mut q) = ([0f64; 2], [0f64; 2], [0f64; 2]);
    for (&x, &c) in ts.iter().zip(fixed) {
        if x > cut {
            continue;
        }
        let (k, x) = (c as usize, x as f64);
        n[k] += 1.0;
        let d = x - m[k];
        m[k] += d / n[k];
        q[k] += d * (x - m[k]);
    }
    let se = (q[0] / (n[0] - 1.0) / n[0] + q[1] / (n[1] - 1.0) / n[1]).sqrt();
    ((m[1] - m[0]) / se, (n[0] + n[1]) as usize, m, se)
}

fn proc_field(path: &str, key: &str) -> String {
    let s = std::fs::read_to_string(path).unwrap_or_default();
    let l = s.lines().find(|l| l.starts_with(key)).unwrap_or("?");
    l[key.len().min(l.len())..].split_whitespace().take(3).collect::<Vec<_>>().join(" ")
}

/// Times calls of `f`, each on the fixed input or a fresh `gen` one, the class drawn per call by a
/// fixed-seed xorshift, until at least `n` survive the crop. Inputs are built in batches outside
/// the timed region, and one warm-up batch is discarded. Prints the result, with 10 standard
/// errors: the smallest mean difference this run would flag. Returns Welch's t.
fn dudect<I: Clone>(name: &str, n: usize, fixed: I, mut gen: impl FnMut(&mut Rng) -> I, mut f: impl FnMut(&I)) -> f64 {
    const BATCH: usize = 100;
    let (wall, load) = (Instant::now(), proc_field("/proc/loadavg", ""));
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let (mut ts, mut cs) = (Vec::with_capacity(n), Vec::with_capacity(n));
    let mut inputs = Vec::with_capacity(BATCH);
    for b in 0..=(n * 100).div_ceil(95).div_ceil(BATCH) {
        inputs.clear();
        let classes: Vec<bool> = (0..BATCH).map(|_| rng.next() & 1 == 1).collect();
        for &c in &classes {
            inputs.push(if c { fixed.clone() } else { gen(&mut rng) });
        }
        for x in &inputs {
            let t0 = now();
            f(black_box(x));
            let t1 = now();
            if b > 0 {
                ts.push(t1 - t0);
            }
        }
        if b > 0 {
            cs.extend(classes);
        }
    }
    let (t, kept, m, se) = welch_cropped(&ts, &cs);
    assert!(kept >= n);
    println!(
        "dudect {name}: n {} kept {kept} |t| {:.2} mean fixed {:.1} random {:.1} 10se {:.1} ({}), wall {:.1} s, load {load} -> {}, cpus {}",
        ts.len(),
        t.abs(),
        m[1],
        m[0],
        10.0 * se,
        if cfg!(target_arch = "x86_64") { "TSC ticks" } else { "ns" },
        wall.elapsed().as_secs_f64(),
        proc_field("/proc/loadavg", ""),
        proc_field("/proc/self/status", "Cpus_allowed_list:"),
    );
    t
}

/// The leaky control: an early-exit compare. `black_box` per byte keeps LLVM from merging the
/// loop into one wide compare.
#[inline(never)]
fn leaky_eq(a: &[u8; 16], b: &[u8; 16]) -> bool {
    for i in 0..16 {
        if black_box(a[i]) != b[i] {
            return false;
        }
    }
    true
}

fn control() {
    let s = [0x5au8; 16];
    let t = dudect("control (early-exit compare)", 1_000_000, s, |r| r.bytes(), |x| {
        black_box(leaky_eq(x, &s));
    });
    assert!(t.abs() > T_MAX, "control |t| = {:.2}: the harness missed a known leak, so no target verdict counts", t.abs());
}

fn check<I: Clone>(name: &str, n: usize, fixed: I, gen: impl FnMut(&mut Rng) -> I, f: impl FnMut(&I)) {
    control();
    let t = dudect(name, n, fixed, gen, f);
    // Written so that a NaN fails.
    assert!(t.abs() <= T_MAX, "{name}: |t| = {:.2} > {T_MAX}: possible timing leak", t.abs());
}

const KEY: [u8; 16] = [0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c];
// RFC 6979 A.2.5's P-256 private key.
const D: [u8; 32] = [
    0xc9, 0xaf, 0xa9, 0xd8, 0x45, 0xba, 0x75, 0x16, 0x6b, 0x5c, 0x21, 0x57, 0x67, 0xb1, 0xd6, 0x93, 0x4e, 0x50, 0xc3, 0xdb, 0x36,
    0xe8, 0x9b, 0x12, 0x7b, 0x8a, 0x62, 0x2b, 0x12, 0x0f, 0x67, 0x21,
];

#[test]
#[ignore]
fn aes128_encrypt_block_key() {
    let b = [0u8; 16];
    check("aes128_encrypt_block (key)", 1_000_000, KEY, |r| r.bytes(), |k| {
        black_box(aes128_encrypt_block(k, &b));
    });
}

// gf128_mul_exec is private; seal with no plaintext and 1024 AAD blocks runs it 1025 times with
// H = E_K(0), plus the key expansion and two AES blocks (about 12% of the time).
#[test]
#[ignore]
fn ghash_h() {
    let (nonce, aad) = ([0u8; 12], [0x11u8; 16384]);
    check("GHASH via aes128_gcm_seal (key, so H)", 1_000_000, KEY, |r| r.bytes(), |k| {
        black_box(aes128_gcm_seal(k, &nonce, &aad, &[]));
    });
}

// Both classes are rejected: the fixed tag is wrong in its last byte, the random one at a
// random position by a random nonzero xor.
#[test]
#[ignore]
fn gcm_open_tag_compare() {
    let nonce = [0u8; 12];
    let good = aes128_gcm_seal(&KEY, &nonce, &[], &[0u8; 16]);
    let wrong = |pos: usize, x: u8| {
        let mut c = good.clone();
        c[16 + pos] ^= x;
        c
    };
    assert!(aes128_gcm_open(&KEY, &nonce, &[], &good).is_some() && aes128_gcm_open(&KEY, &nonce, &[], &wrong(15, 1)).is_none());
    let gen = |r: &mut Rng| wrong(r.next() as usize % 16, (r.next() % 255 + 1) as u8);
    check("aes128_gcm_open tag compare (wrong byte position)", 1_000_000, wrong(15, 1), gen, |c| {
        black_box(aes128_gcm_open(&KEY, &nonce, &[], c));
    });
    // Power probe, no verdict: the same calls plus a planted early-exit compare of the tag.
    let tag = |c: &Vec<u8>| -> [u8; 16] { c[16..].try_into().unwrap() };
    let good_tag = tag(&good);
    dudect("aes128_gcm_open + planted early-exit tag compare", 1_000_000, wrong(15, 1), gen, |c| {
        black_box(aes128_gcm_open(&KEY, &nonce, &[], c));
        black_box(leaky_eq(&tag(c), &good_tag));
    });
}

// A random d is outside [1, n - 1] with probability about 2^-32.
#[test]
#[ignore]
fn p256_ecdsa_sign_d() {
    check("p256_ecdsa_sign (d)", 1_000_000, D, |r| r.bytes(), |d| {
        black_box(p256_ecdsa_sign(d, b"sample"));
    });
}

#[test]
#[ignore]
fn p256_ecdh_d() {
    let peer = p256_public_key(&[0x42; 32]).unwrap();
    check("p256_ecdh (d)", 1_000_000, D, |r| r.bytes(), |d| {
        black_box(p256_ecdh(d, &peer));
    });
}

// Same n (RFC 9500's 2048-bit key) and 64 more valid key pairs: d = e^-1 mod lcm(p - 1, q - 1)
// for random odd e. Every d is zero-padded to k = 256 octets, as the loader must (pad_be's cost
// depends on d's encoded length, public under spec D7). 10^4 calls, not 10^6: one takes ~6 ms.
#[test]
#[ignore]
fn rsa_pss_sha256_sign_d() {
    let p = "dd105702382f232b3681f53791e22617c7bf4e9acb81ed48daf6d6995da3eab642839aff012d2ea628b90af279fd3e6f7c93cd80f072f01ff2443b3ee8f24ed469a79613a41bd24020f92fd11059bd1d0f301b5ba7a9d3637ca8d65c1a9815417d8eab734b0b4f3a2c661d9a1a82f3ac734c40530669ab8e473045a58e65539d";
    let q = "ccf1e5bb90c8e9781ea75bebf10bc252e11eb023a0260f1887552a56863f4a6421e8c600bf523d6cb1b0adbdd65bfee4a88a037e3d1a415e5bb95648da5a0ca26b54f4a63948522c3d5f89b94a72efff95134d5940ce45758f308980908956588eef575b3e4bc4c368cfe813ee9c252c2b02e0df91f1aa01938d38685d60ba6f";
    let u = |s: &str| BoxedUint::from_be_slice_vartime(&(0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect::<Vec<_>>());
    let pad = |b: Vec<u8>, k: usize| {
        let z = b.iter().take_while(|&&x| x == 0).count();
        [vec![0u8; k.saturating_sub(b.len() - z)], b[z..].to_vec()].concat()
    };
    let (msg, salt) = (b"TLS 1.3, server CertificateVerify", [7u8; 32]);
    let mut keys = Vec::new();
    let mut r = Rng(0x2545_f491_4f6c_dd1d);
    let mut e = 65537u64;
    while keys.len() < 65 {
        if let Ok(k) = rsa::RsaPrivateKey::from_p_q(u(p), u(q), BoxedUint::from(e)) {
            assert_eq!(k.n().bits(), 2048);
            let ours = RsaPrivateKey {
                n: pad(k.n().to_be_bytes().to_vec(), 0),
                e: pad(k.e().to_be_bytes().to_vec(), 0),
                d: pad(k.d().to_be_bytes().to_vec(), 256),
                p: pad(k.primes()[0].to_be_bytes().to_vec(), 0),
                q: pad(k.primes()[1].to_be_bytes().to_vec(), 0),
            };
            let s = rsa_pss_sha256_sign(&ours, msg, &salt);
            k.to_public_key().verify(rsa::Pss::<sha2::Sha256>::new_with_salt(32), &sha256(msg), &s).unwrap();
            keys.push(ours);
        }
        e = (r.next() % ((1 << 33) - 4) + 3) | 1;
    }
    assert!(keys.iter().all(|k| k.n == keys[0].n && k.d.len() == 256));
    check("rsa_pss_sha256_sign 2048 (d, same n)", 10_000, 0usize, |r| 1 + r.next() as usize % 64, |&i| {
        black_box(rsa_pss_sha256_sign(&keys[i], msg, &salt));
    });
}

#[test]
fn welch_cropped_sanity() {
    let cs: Vec<bool> = (0..1000).map(|i| i % 2 == 0).collect();
    let same: Vec<u64> = (0..1000).map(|i| (i / 2) % 50).collect();
    assert_eq!(welch_cropped(&same, &cs).0, 0.0);
    let mut shifted: Vec<u64> = same.iter().zip(&cs).map(|(&x, &c)| x + 100 * c as u64).collect();
    shifted[1] = 1 << 40; // an outlier in the random class, cropped
    let (t, kept, m, _) = welch_cropped(&shifted, &cs);
    assert!(t > 10.0 && kept >= 950 && m[0] < 50.0, "{t} {kept} {m:?}");
}
