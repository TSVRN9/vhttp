# Binary constant-time audit of crates/crypto (main at e6c1c00)

**Status at 8b32220.** The body below is the audit of e6c1c00, unedited. Since then the shim is deleted (F2 and G1 are obsolete; the "Phase 5" deployment line it quotes is superseded by TRUSTED's RSA row). F1 is closed by `#[inline(never)]` on `scalar_in_range`. The shipped rlib is now 2 units; 7 of the 30 functions changed and were re-read, the other 23 have the same opcodes. The RSA read is the next section. Where the bodies below say verify.sh re-checks none of this, they predate the gate in the next section. Where they say no timing was measured, they predate "Timing tests" below.

## Gate (Phase 7a)

`scripts/ct-binary.sh`, run by `verify.sh`, which prints `binary ok (<n> fns)`. It detects change in the object code read here, not leaks: a passing gate means the shipped code is the code read, not that the code is constant time. Nothing mechanical ties `--update` to a read beyond the commit tripwire below: the read itself is on trust.

**What it checks.**

- It runs the recipe's build: a plain workspace `cargo build --release --locked`, in `target/ct-binary` (fixed, not configurable). The dir is kept warm behind a content stamp: a sha256 over every non-test file under `crates/` (`crates/*/tests` and `crates/*/target` excluded), `Cargo.toml`, `Cargo.lock` and `rust-toolchain.toml`. Any change to that content wipes the dir, so the build is fresh whenever a source changed, whatever its mtime (cargo alone trusts mtimes for path packages). Otherwise the build is warm, and cargo's fingerprints cover toolchain and profile changes.
- It refuses to run if `RUSTFLAGS`, `CARGO_ENCODED_RUSTFLAGS`, `CARGO_BUILD_*`, `CARGO_PROFILE_*`, `CARGO_TARGET_*_RUSTFLAGS`, `CARGO_INCREMENTAL`, `RUSTC` or a `RUSTC_*WRAPPER` is set. It does not look at cargo config files, `CARGO_HOME` or `RUSTUP_TOOLCHAIN` (none is in use today). In normal mode a build they change shows as a digest diff, but `--update` would record it as if it were the shipped build.
- The rlib holds only `lib.rmeta`, `lib.rmeta-link` and `.rcgu.o` units, and the unit count equals the `units` line of `docs/crypto-binary-digests.txt`, today 2. The `objdump` line records `objdump --version`, because the digests hash objdump's text: a binutils update (a distro rebuild included, since the line carries the package release) can move every digest with no code change, and the message then points to update protocol step 7.
- It disassembles each unit with `objdump -dr --no-show-raw-insn -C`, splits the output per function symbol and normalises each function. It then diffs one `<sha256> <symbol>` line per function against `docs/crypto-binary-digests.txt`. That covers every function in both units, 49 at 8b32220's source: the 30 non-RSA functions, the RSA and bignum functions, and the 9 `alloc`/`vstd` instantiations (read below).
- Normalisation:
  - drops the file-format and section headers, which carry paths and mangled crate hashes;
  - drops each line's offset column and objdump's `# ...` comments;
  - strips `.llvm.N` suffixes, the per-unit hash in `anon.<hash>.N` and `.Lanon.<hash>.N`, and the function ordinal in `.LCPI<k>_N`;
  - squeezes blanks.

  Opcodes, operands (function-relative jump and call targets included) and relocations stay. Section-symbol relocations (`.text._RNv...`) keep the mangled crate hash, and the `anon.N`/`.Lanon.N` counters stay: both fail closed.
- Dependents: every other workspace rlib in `target/ct-binary/release/` (its `.rcgu.o` units only) must define no symbol whose path contains `crypto::`, and its sorted `U crypto::` references are tracked as the `U <crate> <symbol>` block of the digests file (12 lines: 9 `tls`, 3 `quic` since Phase 3e). A reference that disappears means a call became inlined code.
- Structural checks run in every mode, `--update` included, which refuses to write the file if any fails:
  - `crypto::bignum::ct_mask` is one out-of-line function, and its body is `mov`/`neg`/`ret`;
  - `crypto::p256::scalar_in_range` is one out-of-line function (F1);
  - the call sites read above, as `R_X86_64_PLT32` relocations against the symbol or its `.text` section: `ct_mask` at least 8 times in `rsa_pss_sha256_sign` and once each in `cond_sub` and `select_n`; `scalar_in_range` once each in `p256_public_key` and `p256_ecdh`, twice in `p256_ecdsa_sign`;
  - no dependent defines a `crypto::` symbol;
  - at least one dependent rlib was read, and the `U` block has `tls` lines, so `--update` cannot write a digests file without them.
- Commit tripwire: the last commit touching `docs/crypto-binary-digests.txt` also touches this doc, and an uncommitted change to the digests file comes with one to this doc.
- Once the build has run, every check is reported, not only the first failure, and each message names what to re-read. The pre-checks (tools, environment, build, rlib members, unit count zero, the digest count) stop at the first failure. A missing tool, a build failure or no `.rcgu.o` member fails the gate.

**What it does not check.**

- Leaks. A function whose digest is unchanged carries its earlier reading, nothing more. That reading has the limits stated in its section: tiers, loop-shape tracing, not dudect.
- Data. Only executable sections are hashed. A constant or table in `.rodata` or `.data.rel.ro` is covered only through the relocations that reference it, not by its contents. Contents change values, not which addresses are touched or which branches run; jump tables and indexed lookups show in the hashed code.
- Other builds: LTO, `codegen-units`, `target-cpu`, other targets, and a linked binary (`crates/server`'s, since 3e).
- Code inlined into a dependent from its first build. `nm` sees only out-of-line copies and the references that remain, so a new call to crypto that is inlined from the start leaves no trace. Protocol step 2 covers it.
- tls's own constant-time sites read above (`ct_eq32` inlined into `on_crypto`, the zero-share check in `build_flight`) are not hashed: a change to them is not detected.
- Toolchain and profile are not checked separately. A change to either is expected to show as a digest change.

**Update protocol.**

1. When the gate fails on a digest, the diff lists the changed, added and removed symbols. The script leaves the full dump and the per-function text in `target/ct-binary/ct-binary/`.
2. Read every changed or added symbol per the Recipe (under "RSA object read"). Read it at least at the tier of its earlier reading, and whole if it is new or it calls `ct_mask` or `scalar_in_range`. Earlier tiers are recorded in four places: the Coverage table (the 30 non-RSA functions), "Jump classes, shipped rlib" (RSA and bignum), "Non-RSA symbols re-read" (the 7 re-read and `scalar_in_range`) and Gate records (the 9 instantiations, which need tier B, every jump and its flag producer, or a whole read). Tier C means re-running the criteria listed under Coverage; the script itself is not in the repo. A changed `units` line means every function is re-read. For a new or changed `pub fn` of crypto, confirm it appears as `U crypto::...` in its dependents' block. A removed `U` line: confirm in the dependent's source that the call is gone; otherwise it was inlined, so read the inlined code in the dependent's caller per the Recipe and record it.
3. Record the read in this doc: date, commit, toolchain, the symbols and their verdicts.
4. Then run `scripts/ct-binary.sh --update`, and commit the digests file together with the read.

   4a. If a changed symbol is a timed target or is inlined into one, rerun the timing tests per "Timing tests" and record the run.
5. A structural failure is not cleared by `--update`. Restore the barrier in the source, or change the check in the script in a reviewed commit that carries a fresh read.
6. A change to the normalisation alone (the script, not the code) may be re-digested without a fresh read, provided the recipe's whole-dump md5 is unchanged and the old rules applied to the new build reproduce the old digests. Record both in this doc. This does not cover an `objdump` change: both conditions hash objdump's own text. Use step 7 for that.
7. `objdump` only (the gate reports a new `objdump` line). Identical `.text` bytes are not enough: in a relocatable object every call and data reference is a zero displacement plus a relocation entry.
   1. Build the commit that last wrote the digests file (`git log -1 --format=%H -- docs/crypto-binary-digests.txt`) in a scratch worktree, with the same toolchain, as the Recipe builds it.
   2. `cmp` each of its extracted `.rcgu.o` units against the same-named unit of the current build (`target/ct-binary/ct-binary/`). Whole objects, so the relocation tables are compared too.
   3. If every unit is identical, the code is the code read: run `--update` with no read. Record in Gate records the new `objdump` line, the recipe's whole-dump md5 under the new objdump, and the commit compared against.
   4. Otherwise, read per step 2 every symbol whose digest changed.

### Gate records

- **2026-11-03, b3b5d8a (crates/crypto source as at 8b32220), rustc 1.98.1, GNU objdump 2.46.1.** Normalisation-only re-digest (step 6): `.Lanon.<hash>.N` lost its unit hash, and the `objdump` line and the `U` block were added. The recipe's md5 on the gate's own units is still `a247bd0fc9216f57f9ba2fe5fc376e88`, and the previous rules applied to this build reproduce the previous 49 digest lines byte for byte.
- **2026-11-03, b3b5d8a, same toolchain.** Whole read of the 9 `alloc`/`vstd` instantiations (each at most 52 instructions). Every conditional jump below is on a length, a capacity, an index or an allocator result. Under spec D7 and the MIR leakage model, lengths, capacities (allocation sizes), indices and subslice bounds are public, and allocation failure is a public abort. The indirect `call/jmp *0x0(%rip)` are GOT loads of fixed symbols. **Clean.**

  | Instantiation | Instructions | Jumps (conditional + `jmp`) | Each conditional jump and its flag producer |
  |---|---|---|---|
  | `vstd::slice::slice_subrange::<u8>` | 16 | 2 + 0 | `sub %rdx,%rdi; jb` end < start; `cmp %rsi,%rcx; ja` end > len. Both to `slice_index_fail` |
  | `RawVecInner::reserve::do_reserve_and_handle` | 32 | 2 + 0; 2 cmov | `add %rdx,%rsi; jb` len + additional overflows; `cmpl $0x1,(%rsp); je` `finish_grow` returned Err. `cmova`/`cmovae` are max(2 cap, required) and max(8, ...) |
  | `RawVecInner::finish_grow` | 42 | 5 + 3 | `test %rcx,%rcx; js` new size > isize::MAX; `test %rsi,%rsi; je` no old allocation (alloc vs realloc); `test %rax,%rax; jne` realloc result; `test %r14,%r14; je` size 0; `test %rax,%rax; jne` alloc result. The one indexed store `mov %r14,(%rbx,%rax,1)` has `%rax` = 8 or 16, set from constants on each path |
  | `RawVecInner::try_allocate_in` | 52 | 5 + 3 | `mul %rsi; seto; cmp; seta; or; je` capacity x element size overflows or exceeds isize::MAX - align; `test %r15,%r15; je` size 0; `test %bpl,%bpl; je` zeroed or not (the caller's init kind); `test %rax,%rax; je`, `test %rax,%rax; jne` allocator results. `mul` multiplies the capacity by the element size |
  | `Vec<u8>::reserve` | 7 | 1 + 0 | `cmp %rax,%rdx; ja` additional > cap - len, a tail jump to `do_reserve_and_handle` |
  | `VecAdditionalExecFns::set` | 11 | 1 + 0 | `cmp %rax,%rsi; jae` i >= len, to `panic_bounds_check`. The store `mov %dl,(%rax,%rsi,1)` is at index i, the caller's index (an index event in the MIR model) |
  | `RawVec<u8>::drop` | 7 | 1 + 1 | `test %rsi,%rsi; je` capacity 0, else a tail jump to `__rust_dealloc` |
  | `Vec<u8>::drop` | 1 | 0 | `ret` |
  | `drop_glue::<Vec<u8>>` | 7 | 1 + 1 | Same instructions as `RawVec<u8>::drop` |

- **2026-11-03, this commit on base 7e95f7f, rustc 1.98.1, GNU objdump 2.46.1.** Dependent added: quic (Phase 3e Task 1, `quic::hp::hp_mask`), 1 `U` line (`U quic crypto::aes::aes128_encrypt_block`), no `D` line, digests unchanged. Protocol step 2: the line is `U`, a call (`nm -C libquic.rlib` shows no defined `crypto::` symbol, so nothing was inlined); no crypto symbol changed, so no symbol read is due.
- **2026-11-03, this commit on base 7e95f7f, rustc 1.98.1, GNU objdump 2.46.1.** Dependent extended: quic (Phase 3e Task 2, `quic::aead::{seal_packet, open_packet}`), 2 `U` lines (`U quic crypto::gcm::aes128_gcm_open`, `U quic crypto::gcm::aes128_gcm_seal`), no `D` line, digests unchanged. Protocol step 2: both lines are `U`, calls (`nm -C libquic.rlib` shows no defined `crypto::` symbol, so nothing was inlined); no crypto symbol changed, so no symbol read is due.

## Timing tests (Phase 7a)

`crates/crypto/tests/dudect.rs`, dudect-style, std only. Every target test is `#[ignore]`d: the tests run by hand and are not in `verify.sh`. crypto has no `libc` dev-dependency, so `taskset` does the pinning, and every result line prints the allowed CPUs and the load average. Pick a P-core (CPUs 0-3 on this machine):

```sh
cargo test --release -p crypto --test dudect --no-run
taskset -c 2 cargo test --release -p crypto --test dudect -- --ignored --nocapture --test-threads 1
scripts/ct-binary.sh && cmp target/release/deps/libcrypto-*.rlib target/ct-binary/release/libcrypto.rlib   # timed code = gated code
```

Each run fails unless `/proc/self/status`'s `Cpus_allowed_list` is a single CPU. The `cmp` needs exactly one `libcrypto-*.rlib` in `target/release/deps`; if there are several, compare the one the test binary linked.

**When to run.** By hand, after any gate digest update that touches a timed symbol or its callees, and on any new CPU or toolchain the server ships on. Record each run here.

**Harness.**

- There are two classes, fixed and random. A fixed-seed xorshift draws the class for each call, so the classes interleave, and it also draws the random inputs. Inputs are built in batches of 100 outside the timed region; for the fixed class, the batch slot gets a copy of the fixed input. One warm-up batch is discarded.
- Each call is timed with `lfence; rdtsc` on both sides (with `Instant` off x86-64). TSC ticks are invariant ticks, not core cycles.
- Every measurement above the pooled 95th percentile is dropped. Welch's t is computed on the rest, with Welford's means and variances. The harness measures until at least `n` measurements survive the crop.
- Verdict: a target fails at |t| > 10, and a NaN fails too. The test is first-order with one crop: dudect proper also tests several crop percentiles and a second-order (variance) statistic, and this harness does neither.
- The control runs first, in the same process and harness, before every target. It is `leaky_eq`, an early-exit 16-byte compare (`black_box` per byte), fixed = equal input, random = random input, at 10^6 measurements. It must give |t| > 10, or the target's verdict does not count.
- `10 SE` is ten standard errors of the mean difference. A true difference of 10 SE is flagged with about even odds; about 12 SE is needed for 95% detection.
- What a pass bounds: the fixed-versus-random class mean for one fixed secret, not leak size. A leak that averages equally over typical secrets is not detected at any n. For example, a cost linear in Hamming weight: the fixed P-256 d has popcount 128, exactly the expected value, and the fixed RSA d is within 1σ of the random keys' mean.

**Targets.** One secret varies, and everything else is fixed.

| Target | Secret varied (fixed vs random) | n kept |
|---|---|---|
| `aes128_encrypt_block` | key; block fixed | 10^6 |
| GHASH, through `aes128_gcm_seal` (`gf128_mul_exec` is private) | key, so H = E_K(0); 16 KiB AAD, no plaintext, so 1025 multiplies by H, plus key expansion and two AES blocks | 10^6 |
| tag compare, through `aes128_gcm_open` | key fixed; both classes are wrong tags: the fixed one is wrong in byte 15, the random one in a random byte by a random nonzero xor | 10^6 |
| `p256_ecdsa_sign` | d (fixed: RFC 6979 A.2.5's key; random: 32 random bytes, out of [1, n-1] with probability about 2^-32); msg fixed | 10^6 |
| `p256_ecdh` | d, as above; peer a fixed valid point | 10^6 |
| `rsa_pss_sha256_sign`, 2048 bits | d over 65 valid key pairs with RFC 9500's n: d = e^-1 mod lcm(p-1, q-1), fixed e = 65537, random one of 64 precomputed keys with a random odd e < 2^33 (not a fresh d per call). Each key is checked by signing and verifying with RustCrypto. d is zero-padded to 256 octets, as the loader must do: `pad_be`'s cost depends on d's encoded length, which is public under D7. msg and salt fixed | 10^4, a choice: a signature takes about 6 ms, so 10^6 would take about 100 min (P-256 ran 10^6 at a similar cost; at 10^6 RSA's floor would be about 2.3 µs) |

**Power.** The control's gap is about 6 ticks, on a 60-tick call. On a target the noise grows with the call's length, so a pass says only that the class means differ by less than about that run's 10 SE (see Harness for the odds). To check the tag compare at its own scale, `gcm_open_tag_compare` adds a probe with no verdict: the same calls followed by `leaky_eq` on the tag. Its gap is about 3 ticks, against a 10 SE of about 35. It gave |t| 1.01, so **this test cannot see a 16-byte early-exit compare inside `aes128_gcm_open`**. The tag compare's evidence for constant time is the MIR proof plus the object read; the timing test bounds only larger leaks. **No leak was planted at the P-256 or RSA scale**: their floors (2.4-3.1 µs, 23 µs) come from the SE alone. The RSA test is not shown to detect `ct_mask`'s historical failure, and structurally is unlikely to: the branch chooses between equal-cost copies. The gate's `ct_mask` and call-site checks, shown to fail when `#[inline(never)]` is removed, are the check for it. Its signal would be a difference in mispredict counts, of order 10^2-10^3 cycles against a 23 µs floor.

**Not covered:**

- other CPUs and microarchitectures, including this CPU's E-cores (4-7);
- data-dependent frequency (Hertzbleed-style). With an invariant TSC, scaling that does not depend on the data shows only as noise, and per-call interleaving smears DVFS effects across both classes;
- SMT: this CPU has 1 thread per core, so it is untestable here;
- cache attacks beyond the dudect signal: one process, warm caches, no co-resident attacker;
- leaks below each run's 10 SE, and leaks that average equally over typical secrets (no atypical, e.g. low-weight, fixed secret was run);
- leaks confined to the cropped top 5%, or to the variance alone (one crop, first-order test only);
- the timing of SHA-256, HMAC, HKDF and `p256_public_key`;
- every non-crypto secret path (TRUSTED's CT check scope row).

### Timing records

- **2026-11-03, tree 0b846ce plus the test file (crates/crypto source as at 8b32220, gate digests unchanged), rustc 1.98.1, Intel Core Ultra 7 258V (Lunar Lake; P-cores 0-3, no SMT).** The timed `libcrypto` rlib is byte-identical to the gate's (`cmp`, checked after the run by the Task 2 review and again on 2026-11-03 before fix round 1); the timed regions call all six targets out of line (the review's disassembly of the test binary). The runs went in parallel on P-cores 1, 2 and 3, one `taskset -c` process each, with the documented command filtered by test name. Load is the 1-minute average at start and end. It includes these three runs, so about 3 when all three were going. The TSC runs at about 3.3 GHz (ticks over wall time). **All pass.**

  | Target | n measured / kept | \|t\| | Mean fixed / random (ticks) | 10 SE (ticks) | Wall | CPU | Load |
  |---|---|---|---|---|---|---|---|
  | control, before each target | 1052700 / 1009938-1041064 | 280.72-329.85 | 63.1-70.3 / 57.4-63.1 | 0.2 | 0.1 s | 1, 2, 3 | 1.36-3.36 |
  | `aes128_encrypt_block` | 1052700 / 1001478 | 0.89 | 39411.3 / 39409.6 | 19.6 | 12.7 s | 1 | 1.36 -> 1.72 |
  | GHASH via `aes128_gcm_seal` | 1052700 / 1000112 | 0.27 | 610087.3 / 610095.0 | 280.3 | 195.2 s | 1 | 2.57 -> 3.36 |
  | tag compare via `aes128_gcm_open` | 1052700 / 1000879 | 0.77 | 71822.7 / 71820.2 | 33.4 | 23.1 s | 1 | 1.72 -> 2.30 |
  | (probe: + planted early exit) | 1052700 / 1000450 | 1.01 | 71921.4 / 71917.8 | 35.5 | 23.1 s | 1 | 2.30 -> 2.57 |
  | `p256_ecdsa_sign` | 1052700 / 1000066 | 0.84 | 17001636.2 / 17000967.1 | 7980.0 | 5450.5 s | 2 | 1.39 -> 1.21 |
  | `p256_ecdh` | 1052700 / 1000066 | 0.43 | 16597248.1 / 16597682.6 | 10173.3 | 5322.7 s | 3 | 1.36 -> 2.34 |
  | `rsa_pss_sha256_sign` 2048 | 10600 / 10071 | 1.83 | 20404680.7 / 20390815.2 | 75566.3 | 66.3 s | 1 | 3.36 -> 3.54 |

  10 SE as a fraction of the call: AES 0.05%, GHASH 0.05%, tag compare 0.05%, ECDSA 0.05%, ECDH 0.06%, RSA 0.37%. In absolute terms that is about 6 ns, 85 ns, 10 ns, 2.4 µs, 3.1 µs and 23 µs. The P-256 calls take about 5 ms each here, as long as an RSA signature. They ran at the brief's 10^6 anyway: about 90 min each.

## RSA object read (Phase 5e, source 8b32220)

The object code of `crates/crypto` at 8b32220, rustc 1.98.1 / x86-64-unknown-linux-gnu, as a plain workspace build ships it. **Result: no secret-dependent branch or index in anything read, and `ct_mask` stays a real call. Without it, the branches on the exponent bit and the final subtraction return.**

This is evidence about this source and build only. Any edit to `crates/crypto`, the toolchain or the profile can move inlining, and `verify.sh` re-checks none of it. It is not a dudect result: no timing was measured. Registers feeding jumps were traced by loop shape and flag producer, not by whole-function dataflow.

### Recipe

```sh
git checkout 8b32220   # or any commit with the same crates/crypto non-test source, toolchain and profile
T=<fresh absolute dir>; A=<empty dir>
cargo build --release --target-dir "$T"
cd "$A" && ar x "$T/release/libcrypto.rlib"
ar t "$T/release/libcrypto.rlib" | grep -c 'rcgu\.o$'   # 2
for m in $(ar t "$T/release/libcrypto.rlib" | grep 'rcgu\.o$'); do
    objdump -dr --no-show-raw-insn -C "$m"
done | grep -v 'file format' | sed -E 's/\.llvm\.[0-9]+//g' | md5sum
# a247bd0fc9216f57f9ba2fe5fc376e88
```

Then the same read on `cargo rustc --release -p crypto --lib -- --emit=obj` (1 unit, different inlining, so a second data point and not the shipped code). A checkout at another path, and a second fresh build, gave 2 units and the same opcodes.

### Exponent bit, shipped rlib

`mod_pow_ct`, `pow_step_ct` and `select_n` are inlined into `rsa_pss_sha256_sign`. The byte is loaded at a public index, then only shifted into `ct_mask`, at 8 sites, each a relocation. Nothing tests it.

```
9dc: mov 0x8(%rsp),%rdi ; 9e1: shr $0x7,%edi ; 9e4: call 9e9 <c::rsa::rsa_pss_sha256_sign+0x9e9> ; 9e5: PLT32 c::bignum::ct_mask-0x4
b43: shr $0x6,%edi ; b46: and $0x1,%edi ; b49: call b4e <c::rsa::rsa_pss_sha256_sign+0xb4e> ; b4a: PLT32 c::bignum::ct_mask-0x4
cb3: shr $0x5,%edi ; cb6: and $0x1,%edi ; cb9: call cbe <c::rsa::rsa_pss_sha256_sign+0xcbe> ; cba: PLT32 c::bignum::ct_mask-0x4
e23: shr $0x4,%edi ; e26: and $0x1,%edi ; e29: call e2e <c::rsa::rsa_pss_sha256_sign+0xe2e> ; e2a: PLT32 c::bignum::ct_mask-0x4
f93: shr $0x3,%edi ; f96: and $0x1,%edi ; f99: call f9e <c::rsa::rsa_pss_sha256_sign+0xf9e> ; f9a: PLT32 c::bignum::ct_mask-0x4
1106: and $0x1,%al ; 1108: movzbl %al,%edi ; 110b: call 1110 <c::rsa::rsa_pss_sha256_sign+0x1110> ; 110c: PLT32 c::bignum::ct_mask-0x4
1275: and $0x1,%al ; 1277: movzbl %al,%edi ; 127a: call 127f <c::rsa::rsa_pss_sha256_sign+0x127f> ; 127b: PLT32 c::bignum::ct_mask-0x4
13de: mov 0x8(%rsp),%rdi ; 13e3: and $0x1,%edi ; 13e6: call 13eb <c::rsa::rsa_pss_sha256_sign+0x13eb> ; 13e7: PLT32 c::bignum::ct_mask-0x4
```

`ct_mask` itself:

```
<c::bignum::ct_mask>:
 0: mov %rdi,%rax
 3: neg %rax
 6: ret
```

### Final subtraction, shipped rlib

In `cond_sub` the borrow reaches `ct_mask` with no jump, and the copy is `pand/por` and `and/or`:

```
 a2: xor %edi,%edi
 a4: cmp %r13,(%r14,%rbx,8)
 a8: sbb %rdi,%rdi
 ab: inc %rdi
 ae: xor $0x1,%rdi
 b2: call b7 <c::bignum::cond_sub+0xb7>
 b3: PLT32 c::bignum::ct_mask-0x4
 b7: mov %rax,%r12
```

### Jump classes, shipped rlib

| Function | Jumps | Classes |
|---|---|---|
| `rsa_pss_sha256_sign` | 90, 20 cmov | `nl` and 0x40 bounds, exponent loop counter on `k`, `d`-length bound, allocation failure, capacity, length-driven MGF1 and PS loops, drop paths. 18 cmovs are `modulus_bits` over public `n`, 2 are `nl` loop bounds |
| `cond_sub` | 8 | `nl` and the 0x40 bound |
| `select_n` | 5 | `nl` and the 0x40 bound; 1 `ct_mask` relocation |
| `mont_mul_n` | 11 | Counters and bounds. Carries go through `setb`, never a jump |
| `pow2_mod` | 10 | Counters on `nl` and bits |
| `pad_be` | 9 | Lengths, capacity, allocation. No byte of `d` decides anything |
| `limbs_from_be_n` | 11 | Bounds and lengths |
| `limbs_to_be_n` | 25 | Bounds, lengths, allocation |

The one variable shift in the signer (`shl %cl,%dl` at 0x600) takes `%cl` from the public bit length. The signer was read whole to its 750th line and from the loop exit on; between those, every jump with its flag producer.

In the 1-unit `--emit=obj` the verdict is the same: 127 signer jumps of the same classes, the bit from `bt %rax,%rcx; setb` with the loop index in `%rax`, and `cond_sub` as `cmp %r13,(%r14,%rbx,8); sbb %rdi,%rdi; inc %rdi; xor $0x1,%rdi; call ct_mask`. `test $0x80,%al` in the signer and `inc %rax; je` in `cond_sub` appear 0 times in both builds.

### Non-RSA symbols re-read

An opcode comparison with a rebuilt e6c1c00 (5 units) over the 30 functions gives 23 the same (their text also matches once addresses and relocations are stripped, so the body's reading carries), and these 7 different. `scalar_in_range` is a new symbol.

| Symbol | Instructions, e6c1c00 -> now | Jumps now | Verdict |
|---|---|---|---|
| `p256_ecdsa_sign` | 1408 -> 1259 | 29 (was 31) | Clean. `test %al; je` after each `scalar_in_range` call (`#1`, `#2`); `or`s of r and s, `je` (`#3`, `#4`); the rest HMAC pad counters and 32-byte copy bounds |
| `p256_public_key` | 366 -> 287 | 1 (was 2) | Clean. `call scalar_in_range; test %al,%al; je` |
| `p256_ecdh` | 435 -> 355 | 11 (was 12) | Clean. One branch on the range bit; peer length and tag; coordinate range and on-curve limb compares on public peer data; q.inf |
| `aes128_gcm_seal` | 96 -> 94 | 4 | Clean. Length overflow, allocation, capacity |
| `hkdf_expand` | 257 -> 202 | 12 | Clean. Length and block counter; cmovs are min(32, rest) |
| `sha256` | 6 -> 11 | 0 | Clean. Thin wrapper |
| `sha256_cat` | 172 -> 171 | 9 | Clean. Lengths only |
| `scalar_in_range` | new | 0 | Clean, closes F1: `setne %cl; test %rdx,%rdx; sete %al; and %cl,%al` |

### Control

`select_n` and `cond_sub` with inline `0u64.wrapping_sub` in place of `ct_mask`, in a scratch copy. The branches return in both builds, so the read can tell the two apart. The signer goes from 90 jumps (127 in `--emit=obj`) to 142, and `cond_sub` from 8 to 12. The edit also moves the workspace rlib from 2 units to 1, which is why a read is bound to its source.

Workspace rlib:

```
 12e2: movzbl 0x58(%rsp),%eax
 12e7: mov 0x18(%rsp),%ecx
 12eb: shl %cl,%al
 12ed: test $0x80,%al
 12ef: je 1300 <c::rsa::rsa_pss_sha256_sign+0x1300>
 a6: cmp %r13,%rbp
 a9: sbb %r12,%r12
 ac: mov %r12,%rax
 af: inc %rax
 b2: je e5 <c::bignum::cond_sub+0xe5>
```

`--emit=obj`:

```
 12e2: movzbl 0x58(%rsp),%eax
 12e7: mov 0x18(%rsp),%ecx
 12eb: shl %cl,%al
 12ed: test $0x80,%al
 12ef: je 1300 <c::rsa::rsa_pss_sha256_sign+0x1300>
 b8: cmp %r13,%rbp
 bb: sbb %r12,%r12
 be: mov %r12,%rax
 c1: inc %rax
 c4: je f7 <c::bignum::cond_sub+0xf7>
```

---

## Audit of e6c1c00

Date: 2026-11-02. Toolchain: rustc 1.98.1 / LLVM 22.1.8, x86-64-unknown-linux-gnu, no `target-cpu`, no `.cargo/config`.

## Result

In the MIR-checked crypto code (AES, GHASH/GCM, P-256, ECDSA, SHA-256, HMAC, HKDF), the only branches on secret-derived data are at the `ct-declassify:` sites. At the four range-check sites (F1) the binary branches on two sub-predicates separately, which is finer than the declassified bit. No secret-indexed memory access or division was found. This covers the 30 functions at the coverage tiers below, not more. The mask-to-branch miscompilation found in the new RSA code did not occur in any of them.

| Severity | Count |
|---|---|
| Critical / High / Medium | 0 |
| Low | 1 (F2, RSA shim) |
| Info | 1 (F1, range check) |
| Not classified, known gap | 1 (G1, RSA shim and crypto-bigint) |

## Which object was audited

The object from the suggested `cargo rustc --release -p crypto --lib -- --emit=obj` is not the shipped code. It produced 1 CGU. A plain `cargo build --release` produces 5 CGUs with different inlining (`point_add_ct` 784 vs 313 instructions, `add_mod`/`sub_mod` outlined, `ecdh` 352 vs 398, `rsa_pss_sha256_sign` 2469 vs 31).

- **Primary evidence:** the 5 `.rcgu.o` members of `libcrypto-*.rlib` from a plain workspace `cargo build --release`. All addresses below are from these.
- **Secondary:** the 1-CGU object was also read. Same verdicts. Functions whose text matched after normalising addresses carry that reading over.
- **Profile:** `[profile.release]` sets only `overflow-checks`; `crypto` sets it false. No `lto`, `codegen-units` or `opt-level` override, so opt-level 3 and no cross-crate LTO.
- **Real binary:** `crates/server`'s binary (since 3e) is the only one besides `tools/ct-driver`'s. With LTO off, it links these objects unchanged, unless its profile changes.
- **Cross-crate inlining:** `nm` on the `tls` and `quic` rlibs shows no locally defined `crypto::` symbol. `tls` calls `p256_ecdsa_sign`, `serialize_ecdsa_der`, `hkdf_expand`, `hkdf_extract`, `hmac_sha256`, `p256_ecdh`, `p256_public_key`, `rsa_pss_sha256_sign`, `sha256` as external symbols.
- **No in-workspace GCM caller:** neither `tls` nor `quic` references `crypto::gcm` or `crypto::aes` in the release objects, so priority 1 is not yet reachable from released code.

## Coverage: 30 first-party non-RSA functions

| Tier | Meaning | n | Functions |
|---|---|---|---|
| A | Every instruction read, on the shipped text or a text differing by at most 1 instruction | 10 | `add_mod`, `sub_mod`, `limbs_from_be`, `load_be64`, `mont_pow`, `scalar_mult_ct`, `gctr_append`, `aes128_gcm_open`, `expand_key`, `encrypt_rk` |
| B | Every conditional jump and its flag producer read on shipped text, plus all cmovs and indexed operands | 10 | `ghash_padded`, `gcm_tag_exec`, `aes128_gcm_seal`, `hkdf_expand`, `compress`, `sha256_cat`, `hmac_sha256_core`, `p256_ecdsa_sign`, `p256_ecdh`, `p256_public_key` |
| C | Script: 0 conditional jumps, 0 indirect jumps, 0 non-`lea` indexed memory operands, 0 div or bit scans. Read in part | 8 | `sbox_ct`, `sub_bytes_exec`, `mont_mul`, `point_add_ct`, `aes128_encrypt_block`, `hkdf_extract`, `hmac_sha256`, `sha256` |
| D | Looser: source and counts only, data is a public signature | 2 | `serialize_ecdsa_der`, `push_der_uint` |

So 20 by reading (10 whole, 10 by every branch), 8 by script plus partial reading, 2 loosely. RSA code is separate (G1).

Limits of tier B: registers feeding counter-style jumps were traced over a few lines and by loop shape, not whole-function dataflow. Indexed operands were judged by loop shape (`add`/`inc` then `cmp` against a constant or length), not by complete register tracing. `ghash_padded` and `gcm_tag_exec` were also read whole on the 1-CGU build.

The script: no `div`/`idiv`, `bsf`/`bsr`, `tzcnt`/`lzcnt`, `popcnt`, `rep` or `jmp *` in any of the 30. Variable shifts by `%cl` appear only in GHASH, where `%cl` is the public round counter (0x7f down to 0).

## Function table

Secret labels are from `ct::secret`. Jump classes: **len** public length or bound check, **ctr** loop counter, **decl** declassified value.

### 1. GCM / GHASH

| Function | Secret | Verdict | Evidence (shipped asm) |
|---|---|---|---|
| `ghash_padded` (holds inlined `gf128_mul_exec`, 2 sites) | y, H, data | Clean. 27 jumps, all ctr or len; 13 cmov | Bit loops at 0x280-0x2d8 and 0x550-0x5aa: `test $0x40,%cl; cmovne; and %r15,%r8; and %r12,%r9; or %r8,%r9; cmove %rbx,%r8; cmove %rbx,%rdx; xor; test $0x1,%al; cmovne %r11,%rdx; add $-1,%rcx; jb 280`. The H and data bits select through cmov. The only loop jump is on `%rcx`. Others: `cmp 0x8(%rsp),<off>; jae` bounds, on data length |
| `gcm_tag_exec` (third inlined GF multiply, length block) | rk, c | Clean. 13 jumps: 1 ctr, 12 nonce bounds | 0x1f0-0x24b same shape, `jb 1f0`. `cmp $0x1..0xb,%rcx; je` on nonce length |
| `gctr_append` | rk, x, out | Clean. 17 jumps | Nonce bounds; `cmp %r15,%r12; jae` length; `cmp %r13,%r14; je` min(16, rest); `cmp (%rbx),%r12; jne` Vec capacity, a function of output length |
| `aes128_gcm_open` tag compare | key, tag | Clean | 0x7b `pcmpeqb 0x20(%rsp),%xmm0; pmovmskb; xor $0xffff,%eax; je a8`. LLVM vectorised the loop: all 16 bytes compared, one branch on accept/reject. `ct-declassify: aes128_gcm_open#1` holds |
| `aes128_gcm_seal` | key, pt | Clean. 4 jumps | Length overflow, allocation failure, capacity. All on output length |

### 2. AES

| Function | Secret | Verdict | Evidence |
|---|---|---|---|
| `sbox_ct` | x | Clean, no table in the binary. 0 jumps; 7 cmov | 775 instructions of `sar $7`, `and $0x1b`, `and`, `xor`. All 57 indexed operands are `lea` doubling (`(%rbx,%rbx,1)`, `0x0(,%rdi,8)`). 7 `cmovns` after `test %r8b,%r8b`. 0 `rip` loads. Read in part (tier C) |
| `sub_bytes_exec` | s | Clean | 16 `movzbl; call sbox_ct; mov` at fixed offsets |
| `encrypt_rk` | rk, block | Clean. 17 jumps: 16 block-length bounds, 1 ctr | Round loop `add $0x10,%r13; cmp $0xa0,%r13; jne`. MixColumns uses SSE `pcmpgtb/pand/pxor`. One indexed load `(%r14,%r13,1)`, round-key offset |
| `expand_key` | key | Clean. 18 jumps: 16 key-length bounds, 2 ctr | `test $0x3,%al; jne 160` and `test $0x3,%r12b; cmovne` on word index. `cmp $0x2d,%r12; je` |
| `aes128_encrypt_block` | key, block | Clean | 2 calls, 0 jumps |

### 3. P-256 and ECDSA

| Function | Secret | Verdict | Evidence |
|---|---|---|---|
| `mont_mul` (final subtraction, source mont.rs:481-486) | a, b | Clean. 0 jumps, 0 cmov | Mask kept: 0x434 `cmp %r14,%r11; mov $1,%r11d; sbb $0,%r11; lea -1(%r11),%r14; neg %r11; and; and; or`. Whole-function count by script, tail read |
| `add_mod` / `sub_mod` (hold `select4`) | a, b | Clean. 0 jumps | `sbb $0,%rsi; lea -1(%rsi),%rdi; neg %rsi; and; and; or` at 0xa1; `sbb %rbx,%r10; lea -1(%r10),%rcx; neg %r10; and; and; or` at 0x6f |
| `scalar_mult_ct` | k, pt | Clean. 3 jumps: ctr, ctr, k-length bound | 0xa2 `bt %r14,%r12; setb %al; mov %rax,%rcx; neg %rcx; dec %rax` then `pand/por` on x, y and `and/or` on inf. Unlike the RSA case, masks not unswitched: `0x163 add $0xff,%r14b; jb 80`, `0x175 cmp $0x20,%rcx; jne 60`, `0x60 cmp (%rsp),%rcx; je` |
| `point_add_ct` (holds `sel_pt`, `eq4`, `is_zero4`) | a, b | Clean. 0 jumps; 1 cmov | 0x90 `sete %bl`; 0x4b0 `or 0x50(%rsp),%rsi; cmove %rax,%rdx`. Calls `add_mod`, `sub_mod`, `mont_mul`, `mont_pow`. Script plus partial reading |
| `mont_pow` (field and scalar inversion) | x | Clean. 9 jumps, all on the public exponent | `movzbl (%rax,%r12,1),%r13d` loads e; `test $0x40,%r13b; je`. Square-and-multiply does branch per bit, on e only. `e` is `ct::public`; the callers pass constants `P256_P_MINUS_2` (p256.rs:480) and `P256_N_MINUS_2` (ecdsa.rs:627) |
| `load_be64`, `limbs_from_be` | b | Clean. 8 jumps | `cmp %rsi,%rax; jae` offset vs length |
| `p256_public_key` | d | **F1**. 2 jumps, both range check | 0x130 `or ...,%r13; je 571` then 0x13e `test %rcx,%rcx; jne 573` |
| `p256_ecdh` | d (peer public) | **F1** at 0x136/0x13f. The rest clean: 12 jumps | 0x145 `cmpq $0x41`, 0x156 `cmpb $4`: peer length, tag. 0x22a, 0x2e1, 0x313: peer coordinate >= p, public. 0x48e-0x4d0: 4 `cmp; jne` on-curve limb compare with early exit, on public peer only. 0x55e `cmpq $1,0x1f0(%rsp)`: q.inf, `p256_ecdh#2` holds |
| `p256_ecdsa_sign` (holds inlined RFC 6979 HMAC, `scalar_in_range`, `is_zero4`, `reduce_n`, `ecdsa_s_exec`) | d, k | **F1** at 0x151/0x15a (d) and 0xe2d/0xe36 (k). The rest clean: 31 jumps | 0x1499 `or`s of r, `je 940`: `#3` holds. 0x14c1 `or`s of s, `je 940`: `#4` holds. HMAC pads: `cmp $0x1f,%rax`, `cmp $0x40,%rax`, on counter. 0x3fe, 0x490: length and copy loop on 32-byte lengths |
| `serialize_ecdsa_der`, `push_der_uint` | none: signature, public | Not secret. 125 + 10 jumps | Source only. Strips zeros and tests top bits of public r, s |

### 4. SHA-256, HMAC, HKDF

| Function | Secret | Verdict | Evidence |
|---|---|---|---|
| `compress` | src | Clean. 9 jumps, 9 cmov, all on offsets and bounds | `cmp $0x40,%rax; jne 2d0` schedule; `cmp $0x100,%rax; jne 360` rounds. K table read `add (%rax,%rcx,1),%ebx` at 0x39d, `%rax` the round counter stepping by 4 |
| `sha256_cat` (padding) | prefix, msg | Clean. Lengths only | `cmp $0x40,%r15; jb`, `cmp $0x38,%r14; jb 1e8` one-or-two-block padding on `len mod 64`. Message length is public by spec D7 |
| `hmac_sha256_core` | key, msg | Clean. Lengths only | `cmp $0x40,%rdx; jbe` key > 64, `cmp $0x1f,%r14`, `cmp %rax,%rdx`: on key length, public by D7 |
| `hkdf_expand` | prk | Clean. Lengths only | `cmp $1,%r13`, `cmp %r15,%r13`: block counter; `cmp %rbx,%r14`; `cmovae`: min(32, rest). `memcpy` lengths public |
| `hkdf_extract`, `hmac_sha256`, `sha256` | - | Clean | Thin wrappers, 0 jumps |

### `ct-declassify:` rows

| Row | Value branched on in asm | Holds |
|---|---|---|
| `aes128_gcm_open#1` | 16-byte compare mask, once | Yes |
| `p256_public_key#1`, `p256_ecdh#1`, `p256_ecdsa_sign#1`, `#2` | `d == 0` and `d >= n` separately | No, finer than one bit: **F1** |
| `p256_ecdh#2`, `p256_ecdsa_sign#3`, `#4` | `q.inf`; `r == 0`; `s == 0` | Yes |
| `fe_from_be#1`, `sec1_decode_exec#1` | Peer coordinate range; on-curve limbs with early exit, finer than one bit but all public | Yes (peer is public) |

### Outside crates/crypto, spot-checked

| Site | Verdict | Evidence |
|---|---|---|
| `tls::server::ct_eq32` (inlined into `on_crypto`) | Clean | 0x838-0x85e `pcmpeqb; pand; pmovmskb; cmp $0xffff,%ax; jne`. All 32 bytes, one branch |
| Zero-share check in `tls::flight::build_flight` | Clean | 0x19a-0x1af `por; pcmpeqb; pmovmskb; xor $0xffff,%eax; je`. One branch on all-zero, a public abort outcome |

## Findings

### F1: Info. Key and nonce range check branches twice

- **Where:** `p256_public_key` 0x130/0x13e, `p256_ecdh` 0x136/0x13f, `p256_ecdsa_sign` 0x151/0x15a and 0xe2d/0xe36. Source p256.rs:257-277: `(lt & nz) == 1`, with `declassify` as a plain identity and `#[inline(always)]`.
- **What happens:** inlined into `if !...`, LLVM splits the `and` of the two bits into two branches.
- **What an attacker could learn:** only for a rejected value, whether it was 0 or >= n. For a valid d or k both branches fall through the same way. A rejected RFC 6979 candidate is discarded (`>= n` about 2^-32, `== 0` about 2^-256), and an invalid d is a config error. Nothing about a value that gets used.
- **Tested fix:** `#[inline(never)]` on `scalar_in_range`, in a throwaway copy. Result: `scalar_in_range` has 0 jumps (`setne %cl; test %rdx,%rdx; sete %al; and %cl,%al`), and each caller has one branch on the returned bit (`p256_public_key` 2 to 1 jumps, `p256_ecdh` 12 to 11, `p256_ecdsa_sign` 31 to 29). `cargo test --release -p crypto` passes.
- **Proof impact:** none. With both fixes applied to the copy, `cargo verus verify` in `crates/crypto` reported 0 errors (2060 and 1778 verified across its two result lines) and `scripts/ct-check.sh` passed (`crypto ok (84 fns, 10 roots, 10 declassify)`, negative control rejected). The attribute adds a source line, so TRUSTED.md line citations after p256.rs:257 (rows citing p256.rs:512 and :802, and the p256.rs:800 mentions) would need bumping by one.

### F2: Low. RSA shim scans d's leading zero bytes

- **Where:** `crypto::shim::rsa_pss_sign` 0x40-0x4e: `cmpb $0x0,0x0(%r13,%rdi,1); jne 55; inc %rdi; cmp %rdi,%r12; jne 40`. Source shim.rs:35, `d.iter().take_while(|&&b| b == 0).count()`.
- **What an attacker could learn:** the number of leading zero bytes of d. About 1 key in 256 has any, and d's byte length is close to public. Small next to G1.
- **Tested fix:** take a suffix by public length, `&d[d.len().saturating_sub(n.bits_precision() as usize / 8)..]`. The `cmpb` loop is gone from the shim. `pss_rsa2049_len_and_salt`, `pss_rsa2052_masking_kat` and the other RSA tests pass. Phase 5e deletes this code anyway.
- **Proof impact:** none possible. `shim.rs` is plain Rust outside `verus!`, behind the `external_body` `rsa_pss_sha256_sign`, not a CT root.

### G1: Not classified. RSA shim and crypto-bigint

`crypto::rsa` is not a CT root, and TRUSTED.md already records this: unblinded private operation, RUSTSEC-2023-0071 unpatched, "RSA certificates must not be deployed before Phase 5", constant time a non-goal. This audit adds no evidence either way on the modular exponentiation.

- Looked at: shim source; `rsa_decrypt`'s path (unblinded when `rng` is `None`, `&c % p_wide` with secret p, `cq.pow(dq)`); jump counts in the object (`rsa_pss_sign` 137, `div_rem_assign` 58, `partial_cmp` 14). The first 70 lines of the jump listing for `div_rem_assign` were read without classifying them.
- Not looked at: `BoxedMontyForm::pow`, `invert_mod`, `from_components` and the rest of crypto-bigint/rsa in their own rlibs.
- Do not read the absence of a High here as RSA being safe. It stays undeployable per TRUSTED.md.

## Why no fix to the masks is needed now, and what stays fragile

The `sext(i1)` select pattern is reachable here too: `select4`, `mont_mul`'s subtraction and `scalar_mult_ct` all use `0u64.wrapping_sub(b)`, and they compile to `sbb/lea/neg/and/or`. That they kept their masks is a property of this compiler at this CGU partition, not a guarantee. `scalar_mult_ct` holds its mask inside a loop body, but the mask changes per bit, so it is not loop-invariant and there is nothing to unswitch. Any toolchain bump, LTO change or CGU reshuffle needs this audit re-run; verify.sh has no binary-level gate. The two builds disagreeing on inlining here is direct evidence that small profile changes alter this code.

## Not checked

- Fat or thin LTO, `codegen-units=1` as a real profile (the 1-CGU object is a close stand-in), a linked binary (`crates/server`'s, since 3e), other `target-cpu` values, other targets.
- `tls` key schedule glue, `hkdf_expand_label`, transcript handling, beyond the two spot checks above. `quic` references no `crypto::` symbol in its release objects; `h3` and `wire` were not disassembled.
- RSA shim beyond F2, and all of crypto-bigint/rsa/sha2 (G1). `sha2::compress256` is only used by the shim.
- Not dudect: no timing was measured. Nothing about data cache behaviour beyond the indices above, instruction cache, branch predictor state from public branches, speculation (Spectre, including bounds-check bypass), `mul` latency on old CPUs, or flag-dependent `cmov` behaviour on future microarchitectures. `cmov` was taken as data-independent as instructed.
- No zeroisation check. Secrets on the stack and in freed `Vec`s were not examined.

## Method notes

- Worktree at e6c1c00, plain build, `ar x`, `objdump -dr --no-show-raw-insn -C`, split per function. Nothing committed; fixes were built in a throwaway copy under the session scratchpad.
- Conditional jumps counted by `j*` other than `jmp`. Panic stubs filtered from views after their addresses were listed; all are `panic_bounds_check` on the public-length checks above.
