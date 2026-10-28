# Phase 0–1: Toolchain, Requirements Matrix, Verified QUIC Varint — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Set up a reproducible Verus workspace and an RFC requirements matrix, and deliver the first verified component: the QUIC variable-length integer codec (RFC 9000 §16).

**Architecture:** This is a Cargo workspace. Each crate under `crates/` is verified separately with `cargo verus verify`. The `wire` crate defines the QUIC varint as a Vest format, modeled on Vest's own Bitcoin varint, and proves it equivalent to a small spec transcribed directly from the RFC. Duvet tracks requirements: each RFC requirement is linked to code or listed as an exception.

**Tech Stack:**
- **Verus** `0.2026.10.04.426d8b0`, which ships its own Z3 and pins the Rust toolchain `1.98.1-x86_64-unknown-linux-gnu`.
- **vstd** `=0.0.0-2026-10-04-0306`.
- **vest_lib** `0.2.2`, whose vstd pin matches the one above.
- **duvet** `0.4.3`.

**Spec:** `docs/superpowers/specs/2026-10-27-verified-http3-design.md`

## Global Constraints

- **Versions are pinned exactly.** Verus is 0.2026.10.04.426d8b0. Its vstd pin `=0.0.0-2026-10-04-0306` must equal the one in vest_lib 0.2.2. **Do not upgrade either one alone**: Vest pins vstd exactly, and newer Verus releases ship a different vstd.
- **Every `assume`, `admit`, `external_body`, `assume_specification` and `#[verifier::external]` in a verified crate gets a matching entry in `TRUSTED.md`.** Phase 0–1 should have **zero** of them in `crates/`. Escapes inside dependencies are listed in `TRUSTED.md` instead.
- **Checked in a probe before this plan was written:**
  - `cargo verus verify` re-verifies dependencies: vstd (2060 items) and vest_lib (3255 items), 0 errors. `cargo verus focus` skips them, which is fine for quick iteration, but the final check must be `verify`.
  - vest_lib 0.2.2 builds on the default stable toolchain.
  - vest_lib 0.2.2 itself contains 31 `external_body` (mostly the exec int conversions in `combinators/uints/exec.rs`) and 3 `assume_specification` (e.g. `split_at_mut_unchecked` in `core/exec/output.rs`).
- **Each RFC-transcribed spec fn carries a Duvet citation comment** (`//= https://www.rfc-editor.org/rfc/rfc9000#section-16` followed by `//# <quoted requirement text>`).
- **Verified code uses no async, trait objects or closures**, except the `spec_fn` closures inside Vest format definitions, which are ghost.
- **`cargo build` and `cargo test` must work with the user's default stable toolchain**, because production builds don't need Verus. If they don't, add `rust-toolchain.toml` pinning `1.98.1` and record why in `TRUSTED.md`.

## Review Focus

1. **Truncated input:** the first byte promises N bytes but fewer arrive. Expected: parse returns `Err` and never panics. Pinned in Task 4: `rejects_truncated`.
2. **Non-minimal encodings:** `0x4025` is 37 encoded in two bytes. Expected: `QuicVarInt::<false>` accepts it and `QuicVarInt::<true>` rejects it as non-canonical. Pinned in Task 4: `rfc_a1_samples`, `minimal_rejects_overlong`.
3. **Value ≥ 2⁶²:** an out-of-range value reaches the serializer from unverified code. Expected: `prepare` returns `Err`, and the verified `serialize_into` can't be called because its `consistent` precondition fails. Pinned in Task 4: `prepare_rejects_out_of_range`.
4. **Boundary values:** 63/64, 16383/16384, 2³⁰−1/2³⁰ and 2⁶²−1 must encode at the minimal lengths 1/2, 2/4, 4/8 and 8 and round-trip. Pinned in Task 4: `boundaries_roundtrip`.
5. **Trailing bytes after the varint:** expected result is that the consumed count equals the encoded length and the extra bytes are left alone. Pinned in Task 4: `rfc_a1_samples` (it appends a trailing byte).

---

### Task 1: Toolchain install and workspace skeleton

**Files:**
- Create: `Cargo.toml` (workspace), `.gitignore`, `scripts/verify.sh`, `TRUSTED.md`, `README.md`
- Create: `crates/wire/Cargo.toml`, `crates/wire/src/lib.rs`

**Interfaces:**
- Produces:
  - `scripts/verify.sh` runs `cargo verus verify` in every `crates/*/` directory and exits non-zero on any error.
  - `VERUS_HOME` defaults to `$HOME/.local/opt/verus/0.2026.10.04.426d8b0`.
  - Crate `wire` exists with `vstd` + `vest_lib` dependencies.

- [ ] **Step 1: Install Verus at the pinned path.** Unzip `verus-0.2026.10.04.426d8b0-x86-linux.zip`, from the GitHub release `release/0.2026.10.04.426d8b0`, into `~/.local/opt/verus/0.2026.10.04.426d8b0/`. It's already downloaded at `~/.local/opt/verus-dl/`; move it rather than re-downloading. Toolchain 1.98.1 is already installed.
  Run `~/.local/opt/verus/0.2026.10.04.426d8b0/verus-x86-linux/verus --version`.
  Expected: `Version: 0.2026.10.04.426d8b0`.
  Adjust `VERUS_HOME` to the real directory containing the `verus` binary. Delete `~/.local/opt/verus-dl/`, including the unused 10.26 release.
- [ ] **Step 2: Create the workspace and the `wire` crate.**
  - Root `Cargo.toml`: `[workspace] members = ["crates/*"]`, `resolver = "2"`.
  - `crates/wire/Cargo.toml`: copy the layout `cargo verus new --lib` generates, meaning `[package.metadata.verus] verify = true` and the `unexpected_cfgs` lint for `cfg(verus_only)`. Dependencies: `vstd = "=0.0.0-2026-10-04-0306"` and `vest_lib = "=0.2.2"`. Enable whatever vest_lib features `Vec` output needs (`alloc`/`std`); check its `Cargo.toml`.
  - `src/lib.rs` starts as `use vstd::prelude::*; verus! { }` plus `pub mod varint;`, which Task 3 creates. Until then, leave the module line out so this task compiles alone.
- [ ] **Step 3: Write `scripts/verify.sh`** (POSIX sh, `set -e`). It prepends `$VERUS_HOME` to `PATH`, then runs `(cd "$c" && cargo verus verify)` for each `crates/*/`. Make it executable.
- [ ] **Step 4: Prove the harness catches failures.** Temporarily put `proof fn smoke() { assert(1u8 + 1u8 == 3u8); }` inside `verus!` in `wire/src/lib.rs`.
  Run `scripts/verify.sh`.
  Expected: `assertion failed`, exit code ≠ 0.
  Remove the smoke fn and run it again.
  Expected: `verification results:: N verified, 0 errors`, exit 0.
- [ ] **Step 5: Plain toolchain check.** Run `cargo build && cargo test` at the root with the default toolchain.
  Expected: success.
  If vest_lib fails to compile on the default toolchain, add `rust-toolchain.toml` with `channel = "1.98.1"` and note the reason in `TRUSTED.md`.
- [ ] **Step 6: Write `TRUSTED.md` and `README.md`.**
  - `TRUSTED.md`: copy the "Trusted base" section from the spec, add the exact Verus, Z3 and vstd versions, and add a table headed `| Item | File | Why trusted | Removed in phase |`. Its first row is vest_lib 0.2.2: its proofs are re-checked by `cargo verus verify`, but its 31 `external_body` + 3 `assume_specification` items are trusted. List the files by running `grep -rnE 'external_body|assume_specification' ~/.cargo/registry/src/*/vest_lib-0.2.2/src`.
  - `README.md`: how to install the pinned Verus (Step 1), how to run `scripts/verify.sh`, and a pointer to the spec. Keep it short.
- [ ] **Step 7: Commit** on branch `phase-0-1` (create it first): `git add -A && git commit -m "chore: Verus workspace skeleton with pinned toolchain"`. The design doc in `docs/` goes into this first commit too.

---

### Task 2: Duvet setup and requirements matrix

**Files:**
- Create: `.duvet/config.toml`, or whatever `duvet init` generates
- Create: `docs/requirements.md`
- Modify: `.gitignore` (Duvet's cache/report output dirs)

**Interfaces:**
- Produces:
  - `docs/requirements.md`, the phase-assignment matrix that every later phase plan reads to scope its work.
  - Running `duvet report` produces a report covering RFC 9114, 9204, 9000, 9001, 9002 and 8446.

- [ ] **Step 1: Install and initialize.** Run `cargo install duvet --version 0.4.3 --locked`, then `duvet --help` and `duvet init`. Configure the six specs by URL `https://www.rfc-editor.org/rfc/rfcNNNN`, and source patterns for `crates/**/*.rs`.
  Run `duvet report`.
  Expected: the report builds and lists requirements for all six RFCs, with 0 cited.
- [ ] **Step 2: Build `docs/requirements.md`.**
  - **Structure:** one section per RFC. Each has a table at **section granularity** with columns `| § | Topic | #MUST/MUST NOT | Server applies? | Phase | Notes |`.
  - **Phase values:** a phase number 1–7, or `N/A (client-only)`, or `Declined (optional: <feature>)`.
  - **When to go below section level:** any requirement that is not simply "implemented in phase N" gets its own row with the quoted text. That covers declined optional features, client-only rules inside mixed sections, and reinterpretations.
  - **Reinterpreted MUSTs:** each one needs a matching entry under "Calls I made" in the spec. The RFC 8446 §9.1 RSA reading is the first.
  - **Parallelize:** one subagent per RFC. Each reads the RFC text (rfc-editor.org) and the Duvet extraction, and returns its table.
- [ ] **Step 3: Check the five easy-to-miss MUSTs.** Each must appear, assigned to phase 3 unless the RFC text says otherwise:
  - RFC 9000 §8.1, anti-amplification (3×);
  - RFC 9000 §14.1, discarding Initial packets in UDP datagrams under 1200 bytes;
  - RFC 9000 §8.2.2, PATH_CHALLENGE → PATH_RESPONSE;
  - RFC 9000 §5.1.1/§19.15/§19.16 and §18.2, NEW_CONNECTION_ID, RETIRE_CONNECTION_ID and `active_connection_id_limit`;
  - RFC 9001 §4.6 (0-RTT acceptance and rejection), plus RFC 8446 §4.2.10, rejecting 0-RTT. That goes in phase 4.
  Run `grep -nE '8\.1|14\.1|8\.2\.2|19\.15|4\.6' docs/requirements.md`.
  Expected: every one of them appears.
- [ ] **Step 4: Check coverage.** Every numbered section of each RFC that contains MUST/MUST NOT/REQUIRED/SHALL appears in the matrix.
  Check by comparing the section list from the Duvet extraction with the table rows. A short throwaway script in the scratchpad is fine.
  Expected: no missing sections.
- [ ] **Step 5: Commit:** `git commit -am "docs: RFC requirements matrix and Duvet config"`. Add the new files first.

---

### Task 3: RFC-transcribed varint spec and the Vest format, proven equivalent

**Files:**
- Create: `crates/wire/src/varint.rs`
- Modify: `crates/wire/src/lib.rs` (add `pub mod varint;`)
- Reference (read, don't copy blindly): `~/.cargo/registry/src/*/vest_lib-0.2.2/src/primitives/btcvarint.rs`. That's the template for the format type, the `derived_specs`/`derived_proofs` modules, and the exec impls.

**Interfaces:**
- Produces (all in `wire::varint`):
  - `pub const VARINT_MAX: u64 = 0x3FFF_FFFF_FFFF_FFFF;` (2⁶²−1)
  - `pub open spec fn rfc_varint_decode(b: Seq<u8>) -> Option<(nat, u64)>` is the RFC transcription. It returns `None` when `b.len() == 0` or when `b.len() < len`. Here `len = 1 << (b[0] >> 6)` and the value is `b[0] & 0x3f` followed by the next `len - 1` bytes, big-endian. Write it as a direct transcription of the RFC 9000 Appendix A.1 pseudocode, with the Duvet citation.
  - `pub open spec fn rfc_varint_min_len(v: u64) -> nat` returns 1 if v ≤ 63, 2 if v ≤ 16383, 4 if v ≤ 2³⁰−1, and 8 otherwise.
  - `pub struct QuicVarInt<const MINIMAL: bool>;` implements the same spec and proof traits as Vest's `VarInt<MINIMAL>`:
    - `SpecParser`, `Consistency`, `SpecSerializer(Dps)`, `SpecByteLen`, `SafeParser`, `Productive`, `NonTailFmt`, `GoodSerializer`, `SPRoundTripDps`, `NoLookAhead`, `EquivSerializers(General)`;
    - `SoundParser` and `NonMalleable` only for `QuicVarInt<true>`.
  - **Consistency:** `v <= VARINT_MAX`. The serializer always emits the minimal encoding.
  - `pub proof fn theorem_matches_rfc(b: Seq<u8>)` with these ensures:
    - `QuicVarInt::<false>.spec_parse(b) == rfc_varint_decode(b).map(|(n, v)| (n as int, v))` (or equivalent match form);
    - `QuicVarInt::<true>.spec_parse(b) is Some <==> (rfc_varint_decode(b) matches Some((n, v)) && n == rfc_varint_min_len(v))`, and when `Some`, the values agree.
  - `pub proof fn theorem_serialize_matches_rfc(v: u64)` requires `v <= VARINT_MAX`. It ensures `rfc_varint_decode(QuicVarInt::<true>.spec_serialize(v)) == Some((rfc_varint_min_len(v), v))` and `QuicVarInt::<true>.spec_serialize(v).len() == rfc_varint_min_len(v)`.

- [ ] **Step 1: Write the RFC spec fns** `VARINT_MAX`, `rfc_varint_decode` and `rfc_varint_min_len`, with Duvet citations. Quote RFC 9000 §16 for the 2-bit length prefix and its Table 4, and §16 for "Values do not need to be encoded on the minimum number of bytes necessary, with the sole exception of the Frame Type field".
  Run `scripts/verify.sh`.
  Expected: 0 errors. Spec fns have nothing to prove beyond well-formedness.
- [ ] **Step 2: State both theorems with `admit()` bodies** so the target is fixed before the proof work.
  Run `scripts/verify.sh`.
  Expected: it passes. `admit()` is only allowed temporarily, inside this task.
- [ ] **Step 3: Define the Vest format** `quic_varint_fmt<const MINIMAL: bool>()`. Use `Bind(U8, |b1| ...)` on the first byte's top two bits (`b1 >> 6`), choosing a `Sum` of `Empty` / `Fixed<1>` / `Fixed<3>` / `Fixed<7>`. Refine the trailing bytes with `MINIMAL ==> value >= <previous length's max + 1>`. Map the result to `u64`. This mirrors `varint_fmt` in btcvarint.rs. Wire up `QuicVarInt` with the `derived_specs`/`derived_proofs` delegation, the same way btcvarint does.
  Run `scripts/verify.sh`.
  Expected: the trait obligations verify. If the mapper's losslessness obligation fails, prove the bit-packing lemmas separately with `by (bit_vector)`:
  - `((b0 & 0x3f) as u64) << 8*(len-1) | rest` is the inverse of the split;
  - top-bit tags round-trip.
- [ ] **Step 4: Prove `theorem_matches_rfc` and `theorem_serialize_matches_rfc`** by replacing the `admit()`s. Expect to need per-length lemmas (one for each of 1/2/4/8) that relate the big-endian fold in `rfc_varint_decode` to Vest's `Fixed` + mapper value.
  Run `scripts/verify.sh`.
  Expected: 0 errors.
  Run `grep -rn 'admit\|assume\|external_body' crates/wire/src`.
  Expected: no output.
- [ ] **Step 5: Commit:** `git add crates/wire && git commit -m "feat(wire): QUIC varint spec + Vest format proven equal to RFC 9000 §16"`

---

### Task 4: Exec parser/serializer and RFC sample tests

**Files:**
- Modify: `crates/wire/src/varint.rs` (exec impls)
- Test: `crates/wire/tests/varint.rs` (plain `cargo test`, unverified, for checking the specs themselves against RFC vectors)

**Interfaces:**
- Consumes: `QuicVarInt<MINIMAL>` and `VARINT_MAX` from Task 3.
- Produces:
  - `impl<'i, const MINIMAL: bool> Parser<&'i [u8]> for QuicVarInt<MINIMAL>` (`type PT = u64`, `min_byte_len` = 1);
  - `impl<Output: OutputBuf, const MINIMAL: bool> Serializer<Output, u64> for QuicVarInt<MINIMAL>`;
  - `impl<const MINIMAL: bool> Prepare<u64> for QuicVarInt<MINIMAL>`: returns `Ok(rfc_varint_min_len(v))` (1/2/4/8), and `Err(PreSerializeError …)` when `v > VARINT_MAX`.
  These are the APIs phase 2 frame codecs compose with.

- [ ] **Step 1: Write the failing tests** in `crates/wire/tests/varint.rs`, using vest_lib's exec API (`Parser::parse`, `SerializerExt::serialize_with_vec`, `Prepare::prepare`):

```rust
// RFC 9000 Appendix A.1. A trailing 0xAA byte checks that it isn't consumed.
#[test] fn rfc_a1_samples() {
    let cases: &[(&[u8], u64, usize)] = &[
        (&[0xc2,0x19,0x7c,0x5e,0xff,0x14,0xe8,0x8c,0xAA], 151_288_809_941_952_652, 8),
        (&[0x9d,0x7f,0x3e,0x7d,0xAA], 494_878_333, 4),
        (&[0x7b,0xbd,0xAA], 15_293, 2),
        (&[0x25,0xAA], 37, 1),
        (&[0x40,0x25,0xAA], 37, 2), // non-minimal, accepted by the lenient parser
    ];
    for (bytes, v, n) in cases { assert_eq!(QuicVarInt::<false>.parse(bytes).unwrap(), (*n, *v)); }
}
#[test] fn minimal_rejects_overlong() { assert!(QuicVarInt::<true>.parse(&&[0x40u8, 0x25][..]).is_err()); }
#[test] fn rejects_truncated() {
    for b in [&[][..], &[0x40][..], &[0x80,0,0][..], &[0xc0,0,0,0,0,0,0][..]] {
        assert!(QuicVarInt::<false>.parse(&b).is_err());
    }
}
#[test] fn boundaries_roundtrip() {
    for (v, len) in [(0,1),(63,1),(64,2),(16383,2),(16384,4),((1u64<<30)-1,4),(1u64<<30,8),(VARINT_MAX,8)] {
        let mut out = Vec::new();
        QuicVarInt::<true>.serialize_with_vec(&v, &mut out);
        assert_eq!(out.len(), len);
        assert_eq!(QuicVarInt::<true>.parse(&out.as_slice()).unwrap(), (len, v));
    }
}
#[test] fn prepare_rejects_out_of_range() {
    assert!(QuicVarInt::<true>.prepare(&(VARINT_MAX + 1)).is_err());
    assert_eq!(QuicVarInt::<true>.prepare(&VARINT_MAX).unwrap(), 8);
}
```

  Adjust the `parse` call shape to whatever vest_lib's `Parser<&[u8]>` takes (`&&[u8]`) and the exact `PResult` shape. Keep the assertions and values exactly as written.
- [ ] **Step 2: Run** `cargo test -p wire`.
  Expected: it fails to compile because `Parser`/`Serializer`/`Prepare` aren't implemented for `QuicVarInt`.
- [ ] **Step 3: Implement `Parser`, `Serializer` and `Prepare`** following btcvarint.rs's exec section:
  - **Parser:** read the first byte, branch on `b >> 6`, read 0/1/3/7 more bytes, assemble big-endian, and apply the `MINIMAL` check with `ParseError::non_canonical()`. Verus proves this matches `spec_parse` through the trait's `ensures`.
  - **Serializer:** pick the length by value range, OR the 2-bit tag into the first byte, and write big-endian.
  - **Prepare:** returns `Err` above `VARINT_MAX`. Check vest_lib's `PreSerializeError` for the right variant.
- [ ] **Step 4: Verify and test.**
  Run `scripts/verify.sh && cargo test -p wire`.
  Expected: `0 errors`, and 5 tests pass.
  Run `grep -rn 'admit\|assume\|external_body' crates/wire/src`.
  Expected: no output.
- [ ] **Step 5: Duvet citations.** Run `duvet report`.
  Expected: RFC 9000 §16 shows its requirements cited by `varint.rs`. `docs/requirements.md` marks §16 as done.
- [ ] **Step 6: Commit:** `git add -A && git commit -m "feat(wire): verified QUIC varint exec codec + RFC 9000 A.1 tests"`

---

## Exit criteria (Phase 0–1)

- `scripts/verify.sh` reports 0 errors, and `grep` finds no `admit`/`assume`/`external_body` in `crates/`.
- `cargo build && cargo test` pass.
- `docs/requirements.md` assigns every server-applicable MUST section in the six RFCs to a phase or a documented exception.
- `duvet report` shows RFC 9000 §16 cited.
