## Trusted base (from the design spec)

- rustc, Verus, Z3, and vstd's specs of std.
- The OS UDP stack, the clock, and getrandom (used for connection IDs, the ECDHE private key and stateless-reset tokens).
- The unverified IO shell and the `main` binary, including loading the certificate chain and parsing the PEM/PKCS#8 P-256 private key and, when configured, the PKCS#8 RSA private key.
- **The hand-written Verus formalization of each RFC** (`spec` modules). Proofs show the code matches these specs; they can't show the specs match the RFC text. Keeping the specs small and readable, with each one citing its RFC section, is how the risk stays manageable.
- **Temporary:** each crypto `external_body` backed by the RustCrypto shim (phases 3-4). Phase 5 removes every one of these entries.

## Pinned versions

- Verus 0.2026.10.04.426d8b0 (toolchain 1.98.1)
- Z3 4.16.0 (bundled with Verus)
- vstd 0.0.0-2026-10-04-0306 (must equal the pin in vest_lib 0.2.2)

The shipped artifact is built by plain `cargo build` on the user's default stable rustc (unpinned; currently 1.92.0), with `verus!` erasure done by `verus_builtin_macros` (version from `Cargo.lock`, currently 0.0.0-2026-09-20-0158). Verification used Verus's own rustc 1.98.1 frontend, so the compiler that checks the proofs is not the compiler that builds the binary. No `rust-toolchain.toml` is needed.

- RustCrypto shim (crates/crypto), removed in phase 5: sha2 =0.11.1

## Trusted items

| Item | File | Why trusted | Removed in phase |
|------|------|-------------|------------------|
| vest_lib 0.2.2: 31 `external_body` + 3 `assume_specification` + 1 `pub broadcast axiom fn` + 1 `external_type_specification` (its proofs are re-checked by `cargo verus verify`; these are not) | `asn1/bmpstring.rs` (1 eb), `asn1/universalstring.rs` (1 eb), `asn1/utf8string.rs` (1 eb, 1 as), `combinators/bytes/spec.rs` (1 axiom: `axiom_array_from_seq`, line 16), `combinators/bytes/exec.rs` (1 eb, 1 as, 1 external_type_specification, line 17), `combinators/marker/exec.rs` (1 eb), `combinators/sints/exec.rs` (12 eb), `combinators/star/exec.rs` (2 eb), `combinators/uints/exec.rs` (12 eb), `core/exec/output.rs` (1 as) | Exec int conversions, std API specs and similar bodies Verus cannot check | never (third-party dependency) |
| Derived `Debug`/`PartialEq`/`Eq` on `h3::frame::{Frame, FrameHeader}` | `crates/h3/src/frame.rs` | Generated impls inside `verus!` are not verified; used by tests only | never (test support) |
| Derived `Debug`/`PartialEq`/`Eq` on `h3::qpack::int::PrefixInt` and `h3::qpack::static_table::StaticMatch` (the latter emitted by `scripts/gen_tables.py`) | `crates/h3/src/qpack/int.rs`, `crates/h3/src/qpack/static_table.rs` | Generated impls inside `verus!` are not verified; used by tests only | never (test support) |
| Generated trusted specs `spec_static_entry` and `spec_huff_code`, produced by `scripts/gen_tables.py` from `crates/h3/rfc/*.txt`. Trusted: the excerpt fidelity, the generator, and the wrapped-row join heuristic (shared with the Rust re-parse test). Ground truth: one-time review check against rfc9204.xml (99/99) and the h2 crate's HPACK tables (257/257), plus the hand-pinned wrapped-rows test. `huff_len_info`/`huff_sorted` are proof-checked against `spec_huff_code` (not trusted) | `crates/h3/src/qpack/static_table.rs`, `crates/h3/src/qpack/huffman_table.rs` | Specs are transcribed by a script, not derived by proof | never (RFC transcription) |
| crypto::sha256::sha256: 1 external_body (RustCrypto sha2 via shim::sha256) | crates/crypto/src/sha256.rs | exec body is unverified RustCrypto; ensures trusted | 5 |
| `crates/crypto/src/shim.rs`: every RustCrypto call (no escape token, but trusted code) | crates/crypto/src/shim.rs | Unverified plain Rust behind the external_body fns | 5 |
| Constants `SHA256_K`, `SHA256_H0` and the SHA-256 specs (FIPS 180-4 transcription; constants re-derived from prime roots by `tests/sha256.rs`, spec fns not machine-checked until phase 5) | crates/crypto/src/sha256.rs, crates/crypto/src/bytes.rs | Specs are transcribed by hand, not derived by proof | never (standard transcription) |
