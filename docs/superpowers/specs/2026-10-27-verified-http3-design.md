# Verified HTTP/3 server in Rust + Verus — design & roadmap

## Context

The user wants an HTTP/3 server, written in Rust, that is proven correct against the specs. They want everything in Verus, all the way down through TLS 1.3 and the crypto primitives. Right now it's a learning/research project, but it should be able to go into production one day. Starting point: `/home/tavern/Projects/rust/web-server` is empty, Rust 1.92 is installed, and Verus/Z3 are not.

Decisions made (user's):
- **Proof scope: everything.** Verus proofs for HTTP/3, QPACK, QUIC, TLS 1.3 and the crypto primitives, all written from scratch in Verus.
- **Verus is the tool.** This was evaluated against Aeneas/Lean, hax/F*, F*/Low*, Kani and Creusot. Verus has no runtime cost (specs and proofs are erased at compile time), mostly automatic SMT proofs, and an existing verified parser library (Vest).
- **Conformance: every MUST first.** Satisfy every mandatory requirement in the RFCs and legally decline the optional ones. The design stays open to adding optional features later, one at a time.

Calls I made (the user can override them):
- **Server only.** No HTTP/3 client role, and we never verify other parties' certificates, so there's no X.509 parser. The certificate chain is sent as opaque DER bytes.
- **Target clients: real browsers** (production goal), plus curl/quiche/h3spec. That leads to:
  - **One curve: P-256 for both key exchange (secp256r1) and signatures (ECDSA P-256).** Both are MUST-implement in RFC 8446 §9.1, browsers accept them, and one set of field-arithmetic proofs covers both.
  - **X25519 comes later.** It's a SHOULD. Browsers that only send an X25519 key share get a HelloRetryRequest asking for secp256r1, which is conformant.
  - **Cipher suite: TLS_AES_128_GCM_SHA256 only.** It's the MUST, and QUIC Initial packets need AES-128-GCM anyway.
- **RSA (RFC 8446 §9.1), user decision 2026-10-27.** RSA is implemented literally.
  - The server can be configured with an RSA certificate and key. It then signs CertificateVerify with rsa_pss_rsae_sha256: RSASSA-PSS, MGF1-SHA256, salt length 32 (RFC 8446 §4.2.3).
  - rsa_pkcs1_sha256 and rsa_pss_rsae_sha256 are recognized in the client's `signature_algorithms` / `signature_algorithms_cert` when choosing which configured chain to send.
  - **Ruling:** no RSA *verification* code is written. The server verifies no peer signatures, because client certificates are declined. "Support for certificates" is met by sending chains signed with those schemes and by negotiating the codepoints. Revisit this if client authentication is ever added.
  - RSA certificates must not be deployed before the key loader that establishes `rsa_key_wf`. Phase 7a delivered the binary-level checks (an object-code gate in `verify.sh` and dudect-style timing tests run by hand; `TRUSTED.md`'s timing rows say what they cover). Phase 5e replaced the shim (RUSTSEC-2023-0071, Marvin), but MIR-level constant time does not carry to the binary: LLVM turned a masked select into a branch on the exponent until `ct_mask` was added. Signing is also 7-8x slower than the shim was (no CRT or window): 6 ms at 2048 bits and 45 ms at 4096 on a P-core, triggered by one unauthenticated Initial. Deployment also needs Retry or a per-source handshake limit in the shell, or a faster proved exponentiation.
- **"No migration" has a narrow meaning:** we send `disable_active_migration` and never initiate migration. Path validation (PATH_CHALLENGE → PATH_RESPONSE) is still implemented, because it's a MUST.
- **ECDSA nonces are deterministic (RFC 6979, HMAC-DRBG).** Signing then doesn't depend on the RNG, and proofs reuse the HMAC proofs.
- **Sans-IO core.** The verified code is pure state machines that take bytes, time and random values as inputs. A thin, unverified shell owns the UDP socket, clock, getrandom and timers. It starts as a blocking `std::net::UdpSocket` loop; an async (tokio) shell can come later for production. Verified code avoids async, trait objects and closures.

## Goals / non-goals / anti-goals

- **Goal:** every RFC MUST/MUST NOT for an HTTP/3 server maps to a Verus spec plus proof, or to a documented reason it doesn't apply.
- **Goal:** working interop with Chrome, Firefox, curl `--http3` and quiche; h3spec passes.
- **Non-goal, for now:** 0-RTT, resumption/PSK, connection migration, Retry, server push, QPACK dynamic table (capacity 0), ChaCha20/AES-256, X25519, client certificates, HTTP/3 extensions (datagrams, WebTransport, extended CONNECT).
- **Non-goal: proven constant-time execution, at binary level.** Constant time is proven at MIR level for crypto since Phase 8a (`ctcore::ni::theorem_ct`, checked by `scripts/ct-check.sh` in `verify.sh`, for the manifest roots under their declared labels, relative to the `ct-declassify:` rows and the CT trust-boundary rows (front end, manifest, semantics/leakage model) in `TRUSTED.md`); binary level is unverified. Verus itself can't express timing properties. Since Phase 7a there are two unverified binary-level checks: `scripts/ct-binary.sh` in `verify.sh` fails when crypto's shipped object code changes without a fresh read (it detects change, not leaks), and dudect-style timing tests (`crates/crypto/tests/dudect.rs`, `--ignored`, run by hand) measured six crypto targets on one CPU. The gap stays documented in production readiness.
- **Anti-goal:** saying "proven" for anything that isn't. Every trusted component and every `assume`/`external_body` is listed in `TRUSTED.md`.

## Trusted base (documented in `TRUSTED.md`)

- rustc, Verus, Z3, and vstd's specs of std.
- The OS UDP stack, the clock, and getrandom (used for connection IDs, the ECDHE private key and stateless-reset tokens).
- The unverified IO shell and the `main` binary, including loading the certificate chain and parsing the PEM/PKCS#8 P-256 private key and, when configured, the PKCS#8 RSA private key.
- **The hand-written Verus formalization of each RFC** (`spec` modules). Proofs show the code matches these specs; they can't show the specs match the RFC text. Keeping the specs small and readable, with each one citing its RFC section, is how the risk stays manageable.
- **Temporary:** each crypto `external_body` backed by the RustCrypto shim (phases 3–4). Phase 5 removes every one of these entries.

## Architecture

Cargo workspace. Each crate is a verification unit (Verus verifies one crate at a time, which keeps re-verification fast). Crates are added only when their phase starts:

```
crates/
  wire/     varint, byte cursor, shared Vest combinators      (phase 1)
  h3/       HTTP/3 frames, QPACK (static + Huffman), streams,
            control-stream/SETTINGS/GOAWAY rules, request
            validation (RFC 9114 §4, RFC 9110 message rules)   (phase 2)
  quic/     packets, frames, packet-number spaces, stream and
            flow-control state machines, ACK, idle/close       (phase 3)
  tls/      TLS 1.3 server handshake state machine, key
            schedule, QUIC-TLS glue (RFC 9001)                 (phase 4)
  crypto/   SHA-256, HMAC, HKDF, AES-128, GCM, P-256 field/
            scalar/point, ECDH, ECDSA+RFC 6979
            (specs + shim in phase 3, verified impls phase 5)
  server/   unverified shell: UDP loop, clock, RNG, static
            response handler, binary                           (phase 3+)
```

Inside each verified crate:
- **spec items** (`spec fn`, RFC-cited, `//= rfc…#section` comments for Duvet)
- **exec code** with `ensures` that connect it to the spec
- **lemmas**

Parsers and serializers use `vest_lib` combinators, with round-trip and reject-malformed properties proven once per format.

**Key proof obligations by layer:**
- **Codecs:** `parse(serialize(x)) == x`; `serialize(parse(b)) == b[..consumed]`, which rules out ambiguous or malleable encodings; malformed input is rejected with the error code the RFC names; no panics or overflow.
- **State machines:**
  - every transition the code takes is allowed by the RFC state diagram (RFC 9000 §3, RFC 8446 handshake);
  - flow-control limits are never exceeded;
  - every RFC-mandated connection/stream error is produced on the triggering input.
- **Crypto:** functional correctness against spec functions that transcribe FIPS 180-4/197, SP 800-38D, RFC 2104/5869/6979, and SEC1/FIPS 186-5. Test vectors cross-check the specs themselves.

**Conformance traceability:** use Duvet (AWS's tool that annotates code with RFC citations). RFC 9114, 9204, 9000, 9001, 9002 and 8446 are loaded as requirements. Each MUST is annotated at its spec fn or proof, or listed as an exception with a reason. The Duvet report is the "completely conformant" checklist.

## Phases (each gets its own detailed implementation plan when it starts)

0. **Toolchain + requirements.**
   - Install Verus from its GitHub release; confirm whether the zip includes Z3 and which rustc toolchain it pins (install that with rustup). Confirm how a Verus crate builds for release: `cargo verus build` vs. plain cargo with `verus!` erasure.
   - Set up the workspace, `TRUSTED.md`, and one trivially verified function.
   - Set up Duvet with RFCs 9114, 9204, 9000, 9001, 9002 and 8446, and extract the server-side MUST list. Check each item against the RFC text, and assign it to a phase or to an exception that names a reason under "Calls I made". MUSTs that are easy to miss:
     - the 3× anti-amplification limit before address validation (RFC 9000 §8.1);
     - discarding Initial packets that arrive in UDP datagrams under 1200 bytes;
     - answering PATH_CHALLENGE with PATH_RESPONSE;
     - NEW_CONNECTION_ID / RETIRE_CONNECTION_ID and `active_connection_id_limit`;
     - rejecting 0-RTT correctly: no `early_data` in EncryptedExtensions, and 0-RTT packets discarded.

   **Exit:** `cargo verus verify` passes, the binary runs, and the MUST list is assigned in full.
1. **`wire`.** QUIC variable-length integer (RFC 9000 §16) with spec, parse, serialize and round-trip proofs, including the minimal-encoding question. Add `vest_lib` and confirm it works with the pinned toolchain.
   **Exit:** proofs verify, plus one runnable test of RFC 9000 Appendix A.1 sample encodings.
2. **`h3`.** Frame codecs (DATA, HEADERS, SETTINGS, GOAWAY, CANCEL_PUSH, MAX_PUSH_ID, PUSH_PROMISE rejection, reserved/unknown frame types); QPACK static table + Huffman with zero dynamic capacity and stream-level error rules; HTTP/3 stream and connection rules as a pure state machine, with error codes per RFC 9114 §8.
   **Exit:** proofs verify; RFC 9204 Appendix B examples (static-only) pass.
3. **`quic` + crypto specs.**
   - First, add `crypto` with **spec** functions transcribed from FIPS 180-4/197, SP 800-38D, RFC 2104/5869/6979 and SEC1. Add their exec signatures as `external_body`, with `ensures` clauses stated in terms of those specs and backed by a RustCrypto shim. Upper layers prove against the specs from day one. Include RSASSA-PSS-SHA256 signing (2048–4096-bit modulus).
   - QUIC: long/short headers, all transport frames, transport parameters, packet-number encoding/decoding, stream states, connection/stream flow control, ACK generation, idle timeout, close/draining, version negotiation, stateless reset, anti-amplification, minimum Initial datagram size, path validation and connection-ID management.

   **Exit:** proofs verify; the `server` shell exchanges Initial packets with a test harness.
4. **`tls`.**
   - TLS 1.3 server state machine: ClientHello → [HRR] → ServerHello/EE/Cert/CertVerify/Finished.
   - Extensions, by name:
     - supported_versions, supported_groups, key_share, signature_algorithms;
     - ALPN `h3`, with the `no_application_protocol` alert when nothing matches;
     - `quic_transport_parameters`;
     - no `early_data`.
   - Key schedule as spec.
   - QUIC-TLS integration: CRYPTO frames, key phases/key update, header protection, Initial secrets.

   Vest has already done TLS 1.3 message formats; reuse its approach.

   **Exit:** proofs verify; RFC 9001 Appendix A sample packets reproduce byte-for-byte; **first real interop**: `curl --http3` and the quiche client fetch a response.
5. **`crypto` implementations.** Replace each `external_body` with verified code behind the same `ensures`, in this order: SHA-256 → HMAC → HKDF → AES-128 → GCM → P-256 (field, scalar, point ops) → ECDH → ECDSA (RFC 6979) → RSASSA-PSS-SHA256 signing (bignum modexp, MGF1, EMSA-PSS encoding; no CRT, see the 5e plan). Upper layers need no changes. This is the largest phase. Bit-vector and nonlinear arithmetic proofs come in small lemma steps, using Verus `by (bit_vector)` / `by (nonlinear_arith)`.
   **Exit:** proofs verify; NIST CAVP + Wycheproof vectors pass; the RustCrypto shim and its `TRUSTED.md` entries are gone.
6. **Loss recovery & congestion control (RFC 9002).** RTT estimation, PTO, NewReno, plus proofs of invariants such as bytes in flight ≤ cwnd.
   **Exit:** proofs verify; behavior stays stable under induced loss.
7. **Full conformance & browsers.** h3spec, h3i, quic-interop-runner (server role), Chrome and Firefox with a P-256 certificate from a local CA. The Duvet report has no unannotated MUSTs. A binary-level constant-time check of every crypto root (dudect-style timing, and an object-code gate that runs on every crypto change, since inlining moves with codegen units).
   - **7a delivered** (docs/crypto-binary-audit.md, "Gate" and "Timing tests"): the gate, run by `verify.sh` (`binary ok (<n> fns)`), which pins every function of the shipped crypto rlib to the object code that was read; and timing tests of `aes128_encrypt_block`, GHASH (through `aes128_gcm_seal`), the GCM tag compare, `p256_ecdsa_sign`, `p256_ecdh` and `rsa_pss_sha256_sign`, run by hand against a leaky control.
   - **Remains:** timing of SHA-256, HMAC, HKDF and `p256_public_key`; other CPUs (and this one's E-cores), frequency scaling and SMT; cache attacks beyond the dudect signal; leaks below each test's resolution; every non-crypto secret path. RSA certificates stay undeployed until the shell's loader establishes `rsa_key_wf` and Retry or a per-source handshake limit exists. The conformance and browser items above are untouched.
8. **Verified analyses.** 8a CT checker (MIR level, crypto); 8b step bounds: 19/36 parser targets bounded (`verify.sh` prints `cost 19/36`); bounds are core steps, not time or memory, and not a DoS bound for the server (every frame, payload and field-section decoder is `none`). Design: `docs/superpowers/specs/2026-10-28-phase-8-verified-ct-cost-design.md`.
   **Exit (8a):** `verify.sh` runs `scripts/ct-check.sh` and the declassify gate, and prints `ct ok (D declassify)`.

## Verification (whole project)

- `cargo verus verify` across the workspace: zero errors, and every `assume`/`external_body` is listed in `TRUSTED.md`.
- `cargo test`: RFC sample vectors, CAVP/Wycheproof, Vest round-trip examples.
- Conformance: h3spec run against the server, a clean Duvet report, interop-runner results.
- Manual: `curl --http3 https://localhost:4433/` and Chrome loading a page via `--origin-to-force-quic-on`.

## First execution step after approval

Copy this design to `docs/superpowers/specs/2026-10-27-verified-http3-design.md`, then write the detailed implementation plan for **Phases 0–1** (superpowers:writing-plans) and carry it out.
