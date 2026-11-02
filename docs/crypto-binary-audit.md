# Binary constant-time audit of crates/crypto (main at e6c1c00)

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
- **Real binary:** none exists on main. The only `main.rs` is `tools/ct-driver`. No `[[bin]]`. With LTO off, a future binary links these objects unchanged, unless its profile changes.
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

- Fat or thin LTO, `codegen-units=1` as a real profile (the 1-CGU object is a close stand-in), a linked binary (none exists), other `target-cpu` values, other targets.
- `tls` key schedule glue, `hkdf_expand_label`, transcript handling, beyond the two spot checks above. `quic` references no `crypto::` symbol in its release objects; `h3` and `wire` were not disassembled.
- RSA shim beyond F2, and all of crypto-bigint/rsa/sha2 (G1). `sha2::compress256` is only used by the shim.
- Not dudect: no timing was measured. Nothing about data cache behaviour beyond the indices above, instruction cache, branch predictor state from public branches, speculation (Spectre, including bounds-check bypass), `mul` latency on old CPUs, or flag-dependent `cmov` behaviour on future microarchitectures. `cmov` was taken as data-independent as instructed.
- No zeroisation check. Secrets on the stack and in freed `Vec`s were not examined.

## Method notes

- Worktree at e6c1c00, plain build, `ar x`, `objdump -dr --no-show-raw-insn -C`, split per function. Nothing committed; fixes were built in a throwaway copy under the session scratchpad.
- Conditional jumps counted by `j*` other than `jmp`. Panic stubs filtered from views after their addresses were listed; all are `panic_bounds_check` on the public-length checks above.
