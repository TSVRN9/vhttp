# Root-cause catalog of review / test / interop findings

Status as of Phase 9r (2026-11-06). Each entry ends with its class and that class's status; a status is one of: caught now (a gate in scripts/ fails on the class), partial, scheduled (owner phase named), open. Owners: C5/C7 9a, 9b, 9c; C12/C14 design section 7 of 9a; C6/C8/C10/C11 "9r2" (a later phase to be planned). Spot-check results are in section 5.

Sources read in full: `.superpowers/archive/{3d2,3e,4c,5e,7a,8b,8c,8d}-final-review.md` and `-ledger.md` (the ledgers carry every task-review verdict and ruling), `wt-9a/.../{progress,preflight}.md`, and `git log main | grep -iE 'fix|review'` (175 commits). Task-level review files in `archive/<phase>/` were NOT opened; their findings enter only as the ledgers summarise them (finding ids are the ledger's: "T3 I1" = Task 3 review Important 1). Older phases (1-5d) appear only as subject-line group entries (S1-S6).

Format: each entry has id, defect, severity as reviewed (C/I/M or ruling), fix commit, ESCAPE (why the existing check missed it), and a class tag. EXISTING CATCH NOW and PROPOSED CATCH are per class (section 2), because every entry of a class shares them; each entry ends `-> Cn`.

Severity key: C critical, I important, M minor, R = ruled by controller with no letter, pre = caught at plan preflight (never reached code).
Existing-gate abbreviations: V = `scripts/verify.sh` (verus verify of all crates at default rlimit, `duvet report`, declassify 3-way diff, escape/`external_body` gate, crypto normal-deps gate, ct-binary digests, ct-check output); CC = `scripts/ct-check.sh` (selftest, semconf, cost pin 36/predicted-bounded, done-roots coverage, dumps tests); CB = `scripts/ct-binary.sh`.

---
## 1. Entries

### Phase 3d2 (quic connection integration)
- **3d2-pre C1** (pre, C): `wf_dcids` required `dcid(hs_path) is Some` and allowed two paths to share a DCID, a traced counterexample to RFC 9000 §9.5. Fix: plan amendment 562cf62, repaired in 1b (590dc15). ESCAPE: wf was written from the code's behaviour, not from the RFC sentence; no independent RFC-phrased invariant to compare. -> C8 [scheduled 9r2]
- **3d2 T1a-i I1-I4** (I x4): wf lacked used-DCID tie, in-flight record bound, `complete ==> !live_i && !live_h`, `paths.has(hs_path)`. Fix 7746fcb. ESCAPE: wf frozen before consumers existed; only review by reading found the missing conjuncts ("each later fix would reopen every proved helper"). -> C8 [scheduled 9r2]
- **3d2 T1a-ii I1** (I): unknown paths were inserted before the packet passed `gate_packet`; three spoofed garbage datagrams permanently fill the 4 path slots and kill the connection at the client's next NAT rebinding. Fix 64f24b3. Residual recorded not fixed: an on-path attacker racing first copies can still take slots (paths never evict). ESCAPE: no ensures says "state grows only on gated input"; tests covered happy path. -> C10 [scheduled 9r2]
- **3d2 T1a-ii I2** (I): `gate_spec` stated as one-way implication; a gate that drops everything verifies. Fix 64f24b3/a4d8093 (biconditional, count_ch ensures). ESCAPE: ensures states safety only, not which packets are accepted. -> C6 [scheduled 9r2]
- **3d2 T1b I1-I3** (I x3): `rewrite_active` did not keep the surviving-seq CID; `peer_used` not tied to the packet DCID; `on_cid_frame` missed `assign_owed`/`challenge_owed`. Fix 590dc15, ca4cb53. ESCAPE: contracts omitted these frame facts; mutants survived. -> C6 [scheduled 9r2]
- **3d2 T1b I4** (I): with a stale active-path CID and no unused CID, the code shared a CID across paths, knowingly violating the §9.5 row. Fix 590dc15 (silent close, per-state P14 wording). ESCAPE: row claimed proved, but wf could not state it; TRUSTED note "not a theorem over send history" added. -> C8 [scheduled 9r2]
- **3d2 T2a-i I1-I4** (I x4): ACK timer, records, frame-source commits, RETIRE_CONNECTION_ID only in tests/comments. Fix 027bda3, 7403e79. ESCAPE: ensures silent; call-site HD mutant reproduced in re-review. -> C6 [scheduled 9r2]
- **3d2 T2b I1** (I): `path_frames_of` not exact (at most one PATH_RESPONSE, recorded challenge data); M3: path packets did not call `on_eliciting_sent` (§10.1). Fix 96561ec, 878ccae, b98ec44. ESCAPE: ensures silent; V1/V2 mutants required to fail. -> C6 [scheduled 9r2]
- **3d2 T3 I1-I3** (I x3): `next_timeout` could stay in the past three ways, i.e. a shell that sleeps on it busy-loops. Fix e3f1a07, 5aa1efa (reviewer's liveness patch, `settled_later`). ESCAPE: timers proven per function, not composed; tests wake at hand-picked times. -> C9 [open]
- **3d2 T3 I4** (I): RFC 9002 §6.2 exception had no TRUSTED row. Fix e3f1a07/docs. ESCAPE: no check that every `//= exception` has a TRUSTED row. -> C1 [partial]
- **3d2 T3 I5** (I): `on_timeout` issued CIDs on a non-Open connection (routes for a dead connection). Fix e3f1a07 (`issue_cids` under Open). ESCAPE: action not state-gated in the contract. -> C8 [scheduled 9r2]
- **3d2 T3 M3** (M): one-range ACK withheld at room 265 though it fits (§13.2 MUST not excused by §8.1). Fix e3f1a07. -> C6 [scheduled 9r2]
- **3d2 T4 I1** (I): `one_call` omitted h3's Reset critical-close and non-critical clauses and the Data id%4 close; skip mutant verified. Fix 66a0b3d. ESCAPE: adapter ensures one-sided. -> C6 [scheduled 9r2]
- **3d2 T4 M1** (M): `flush_copies_tail` (cost-only mutant) survived verification. Fix 66a0b3d (tests/h3_alloc.rs counting allocator). ESCAPE: cost is not in any contract. -> C15 [open]
- **3d2 final I1** (I): in Closing/Draining nothing scheduled the §9.3.2 path-expiry steps; the code comment, ruling and row claimed a MUST that the driver never triggers; two tests woke at a time `next_timeout` never returns. Fix ac9274a, 3665ec8 (option a). ESCAPE: per-fn `timers_cover` proven, Closing arm omitted path expiries; tests used hand-picked wake times instead of `next_timeout()`. -> C9 [open], C1 [partial]
- **3d2 final M1** (M): `H3Server` did not carry `settled_later`; Phase 4's driver uses it. Fix b62c56a (proved). -> C9 [open]
- **3d2 final M2** (M): one 1-RTT packet carrying PATH_RESPONSEs can use up challenge slices before `migrate`; plan said it cannot. Fix b62c56a (note + ponytail). ESCAPE: plan claim hand-argued. -> C1 [partial]
- **3d2 final M3, M4** (M x2): TRUSTED plain-Rust list and capacity paragraph missing 3 accessors / H3Server queue; plan E6 memory bound stale. Fix b62c56a, 34ef25d. -> C2 [open]
- **3d2 final M5** (M): 1-RTT packet coalesced with client Finished always dropped (first-request latency, interop). Fix: fallback plus `early_one_rtt_refed`; real fix in 4c (`refeed_one_rtt`). ESCAPE: no interop client existed until 4c. -> C3 [partial]
- **3d2 final re-review N1** (I): plan note let the shell decrypt 1-RTT before completion (RFC 9001 §5.7). Fix 0a622b0 (plan text). -> C2 [open]
- **3d2 preflight** (pre, 1 C, 8 I, 15 M): C1 above, plus Paths::len/id_at, ACK room, token-invariant ensures, etc., all plan-level. -> C16 [open]

### Phase 3e (packet-protection shell)
- **3e T1 I1** (I): HP masks 0x0f/0x1f not pinned by tests. Fix dd7e94e. -> C6 [scheduled 9r2]
- **3e ruling correction** (R): controller had called RFC 9001 §9.5 a SHOULD; it is a MUST. Fix dd7e94e (remove_hp/apply_hp over all 4 candidate bytes, branch-free pn decode). ESCAPE: ruling C4 read §9.5 as a SHOULD and the quote was not re-read before the ruling (the ledger does not say why; 'from memory' is an inference). -> C14 [scheduled 9a design section 7]
- **3e T2 I1-I2** (I x2): `KeyPair/PacketKeys` lacked DeepView; derived `Debug` printed key/iv/hp bytes. Fix 586d6d6. ESCAPE: nothing scans derive(Debug) on secret-holding types. -> C17 [open]
- **3e T2 M1** (M): `rfc_nonce` accepted any u64 (pn <= PN_MAX not required). Fix 586d6d6. -> C6 [scheduled 9r2]
- **3e T3 I1** (I): `poll_transmit` did not ensure `pn < PN_MAX`. Fix 4077ed6. -> C6 [scheduled 9r2]
- **3e T3 M1** (M): protect.rs doc and report misstated the padding-loop CT residual. Fix 4077ed6. -> C1 [partial]
- **3e T3 M2** (M): `protect_datagram` §14.1 length ensures missing; mutation 2 survived verification. Fix 4077ed6. -> C6 [scheduled 9r2]
- **3e T4 M1-M3** (M x3): long-header `consumed`/ZeroRtt ensures missing so the m4 and ZeroRtt->Handshake remap mutants survived; coalesced §5.4.2 and tiny-datagram tests missing. Fix 998ab72. -> C6 [scheduled 9r2]
- **3e T5 I1** (I, security): `receive` closed on `rx.error` without the error packet passing the gate; any off-path or 42-byte Initial (public Initial keys) with a frame error closed a live connection; regressed the closed §14.1 row. Fix 88c25aa (error moved into `on_datagram`, gated like a packet). ESCAPE: the brief mandated it; ensures said only "closes with this code"; no clause "close requires gated". -> C5 [caught now (ratchet); proofs 9a/9b/9c]
- **3e T5 C1** (R, MUST): RFC 9000 §8.1 counting of every datagram byte was pinned only by test; mutant "skip on_datagram for empty list" survived the proof. Fix cdbfe74 (`recv_counted` prefix property on amp trace). -> C6 [scheduled 9r2]
- **3e T5 C4** (R): `accept_datagram`'s §5.7 gate in no contract; residual bypass via a body not using `open_first` remains (accepted). Fix 88c25aa. -> C6 [scheduled 9r2]
- **3e T6 M1-M8** (M): `IPV6_V6ONLY` set after bind in the first cut, Outbox, shared `rnd(1)`, stale audit line, TRUSTED wording. Fix 7e66875. ESCAPE: shell is unverified Rust, only reviewer probes (spoofing, 200k fuzz) caught these. -> C18 [open]
- **3e preflight C1, C2, C4** (pre): draft shell pushed any new address (spoof slot fill, = 3d2 I1); `next_timeout() <= Some(now)` true for `None` (every idle conn spun); `crypto_read`/`poll_cid_updates` outside the proved wake sequence. Fixed in plan (Decisions 14, 18, 21). -> C10 [scheduled 9r2], C18 [open], C9 [open]
- **3e preflight C9, C14, C23, C26, C27, C28** (pre): stale shim/escape-count text, lost scratch checkers after /tmp wipe, wrong plan cross-refs, verify.sh failing at intermediate commits, instruction that replayed from cache. -> C16 [open], C3 [partial], C11 [scheduled 9r2]
- **3e final I1** (I): TRUSTED:42 and requirements:422 claimed "no branch, loop count or index on pn length"; padding loop, `put_pn` copy length, `open_one` split are pn_len-dependent and "Three operations" undercounted. Fix ef6b37a. ESCAPE: TRUSTED row written in Task 4 did not carry the Task 3 doc correction; hand-typed claim. -> C1 [partial], C14 [scheduled 9a design section 7]
- **3e final M1** (M): audit says quic references no crypto symbol (false since Task 1). Fix ef6b37a. -> C2 [open]
- **3e final M2** (M): `H3Server::on_datagram` passes `error None` (would silently drop §17.2/§17.3.1 errors in Phase 4). Binding note only; status in 4c not verified by me. -> C3 [partial]
- **3e final M3-M5** (M): plan stale after Task 5 round; accept's first-decrypted packet may not be the packet whose DCID chose the Initial keys (fixed in 4c by the DCID check); long doc line. -> C2 [open], C3 [partial]

### Phase 4c (quic-TLS glue, server shell, interop)
- **4c T1 BLOCKED** (R): importing a quic item into tls pulls vest_lib broadcast lemmas into tls; `spec_drain` 0.45M -> 19.1M and `build_flight` 11.65M -> 16.5M at rlimit 4. Fix: new crate `quictls` (cf5128e). ESCAPE: rlimit sensitivity to imports is invisible until a fresh rlimit-4 run. -> C11 [scheduled 9r2]
- **4c T2 M1** (M): `refeed_one_rtt` guard "no-op unless Open" in no ensures; a Closing refeed would owe a second CONNECTION_CLOSE. Fix 3ee5578, 60dc1ae. -> C6 [scheduled 9r2]
- **4c T3 M1** (R, MUST gap): RFC 9001 §4.1.3 "unread data" ignored out-of-order bytes. Fix 6fa13ef. ESCAPE: `unread` was reader-only; no completeness (violation ==> close) lemma. -> C7 [scheduled 9a, 9b, 9c]
- **4c T3 M2** (R, MUST gap): Initial CRYPTO end forgotten across discard, so Initial data past the end was not seen by `superseded`. Fix 6fa13ef (`new_at`). -> C7 [scheduled 9a, 9b, 9c]
- **4c T3 M3-M5** (M x3): `init_end` set late; matrix row hid the log-push gap; 1-RTT keys retained on a pre-completion close. Fix 6fa13ef. -> C1 [partial], C8 [scheduled 9r2]
- **4c T3 re-review** (new M): a legal zero-length CRYPTO frame past the consumed end closed with PROTOCOL_VIOLATION (reassembly insert grew the window for empty data). Fix 753ec2d. ESCAPE: close not proved RFC-required; over-strictness is invisible to safety ensures. -> C5 [caught now (ratchet); proofs 9a/9b/9c]
- **4c preflight C9 / T3 C1** (pre): a TLS failure cleared the 1-RTT slot even after completion; tls_step snapshot. Fix 80c63cc (proved post-completion half). -> C6 [scheduled 9r2]
- **4c final I1** (I): nothing merged recorded that the Phase 4 exit was half met; `quiche_fetches` printed `ok` when it skipped; stop-at-first-Busy untested. Fix a327d2d (strict mode panics, docs); quiche half met later d06282e. Busy path declared dead under config (carried). ESCAPE: skip is a pass; ledger rulings are in gitignored `.superpowers/`. -> C4 [caught now], C3 [partial]
- **4c final M1** (M): "every TLS error closes" and §4.1.3 PROTOCOL_VIOLATION code stated as proved; only test-pinned (`report`/`on_tls_alert`/`feed` ensures omit phase). Fix a327d2d (wording). Proof not added. -> C5 [caught now (ratchet); proofs 9a/9b/9c], C1 [partial]
- **4c final M2** (M): §9.5 owner Phase 7 in matrix vs "never" in TRUSTED. Fix 3c25636. -> C1 [partial]
- **4c final M3** (M): `Rand` doc "no array goes to two calls" false in `accept`. Fix a327d2d. -> C1 [partial]
- **4c T5 M1-M3** (M): no Server-level handshake test, test fixtures lacked README, TRUSTED wording. Fix 4fee0da. -> C1 [partial]
- **4c preflight** (pre, 9 C, 7 I, 10 M): e.g. tls->quic import (above), `cap.py` gone, contradictions with main. -> C16 [open]

### Phase 5e (RSA vectors, verified RSA-PSS)
- **5e pre C1** (pre, C): LLVM turned the MIR-constant-time masked select into a branch on d's bits; ct-check (MIR) cannot see it. Fix: `ct_mask` `#[inline(never)]` plus one-time object read. ESCAPE: MIR-level CT does not imply binary CT; found only by reading objdump. -> C14 [scheduled 9a design section 7]
- **5e audit** (Low/Info): shim in tree (deleted), `scalar_in_range` branch finer than a bit (F1, closed by `#[inline(never)]`). -> C14 [scheduled 9a design section 7]
- **5e final I1** (I): the RSA object read lives only in a gitignored report; the audit doc cited for it says RSA was not read. Fix: docs-only (4ac8251 merge). ESCAPE: evidence in `.superpowers/`. -> C3 [partial], C1 [partial]
- **5e final I2** (I): TRUSTED implied only a toolchain change voids the object read; any `crates/crypto` edit can (rlib 5 -> 2 units); `ct_mask` read as a guarantee. Fix: docs. Later 7a digests gate closes part. -> C1 [partial], C14 [scheduled 9a design section 7]
- **5e final I3** (I): RSA signing 7-8x slower than the shim (6 ms at 2048, 45 ms at 4096), one unauthenticated Initial triggers it, no Retry; plan D2's "no worse off" wrong. Fix: docs (spec line 22, TRUSTED). ESCAPE: no measurement in any gate. -> C10 [scheduled 9r2], C1 [partial]
- **5e final m1** (M): crypto dependency gate was a denylist of 3 names. Fix: exact `vstd` compare (verify.sh:34-35 now). -> C4 [caught now]
- **5e final m2-m6** (M): `(0)` counts tokens not trust; "later item" stale; zero-pad loader option only in plan; requirements row claims "verified and CT-checked" with no limit; stale lock text; Wycheproof licence copy missing. -> C1 [partial], C2 [open]
- **5e T5 M3** (M): `sha256_cat` at 1.49x, `build_flight` 1.03x of rlimit 4 carried. -> C11 [scheduled 9r2]
- **5e T5 carry** (R): loader must size-check a short modulus (panics/exhausts memory on first ClientHello). -> C3 [partial]

### Phase 7a (binary CT gate, timing tests)
- **7a T1 I1-I2** (I x2): `CT_BINARY_TARGET_DIR` could point the stamp anywhere; 9 alloc/vstd instantiations hashed but unread. Fix 0b846ce. -> C4 [caught now], C14 [scheduled 9a design section 7]
- **7a T1 re-review N1-N3** (M x3): `find|sort` masks find failure; `--update` with no U block; objdump version pipe. Fix cefd566. ESCAPE: shell pipelines without pipefail semantics. -> C4 [caught now]
- **7a T2 I1-I2** (I x2): timing tests overclaimed: tag compare cannot see a byte-wise leak (planted, missed); RSA test not shown to catch the historical `ct_mask` failure; per-row 10 SE floors. Fix 94b91b5 (docs, pinning assert). -> C1 [partial], C14 [scheduled 9a design section 7]
- **7a final I1** (I): the objdump-bump advice ("compare raw .text") cannot distinguish code (relocations are zero displacements). Fix a36a8e8 (step 7: cmp whole .rcgu.o units of the commit that last wrote digests). -> C4 [caught now]
- **7a final m1-m6** (M): TRUSTED says gate "fails until re-read" (it fails until `--update`, on trust); disappearing U line not handled; tier pointers; digest update not linked to timing rerun; RSA key size; README binutils. Fix a36a8e8. -> C1 [partial], C4 [caught now]

### Phase 8b (cost analyser)
- **8b pre C1, C2** (pre): option A (Mut provenance) unsound as worded; untyped Val atom. Fix: option B, typed atom. -> C12 [scheduled 9a design section 7]
- **8b T1b I1** (I): drop-impl cache keyed on crate name. Fix c93823d. -> C13 [open]
- **8b T1b I2** (I): vest_lib exception to `-Zinline-mir=no` missing from TRUSTED. Fix c93823d. -> C1 [partial]
- **8b T2 C1** (C): about to freeze a `len_nat` that cannot reach parse's double-ref input (theorem would not accept real loops); I1 "19/36" recorded as measured but was a hand read. Fix b6beb17, 18b0726. ESCAPE: found by reviewer discharging `theorem_cost` on a real loop; no in-repo sanity of that kind existed. -> C12 [scheduled 9a design section 7], C1 [partial]
- **8b T4/T6 M6, I1** (I): `check_cert` true says nothing for an ill-typed program; a wf-only gate mutant gave `bounded` on `cost_neg_not_typed_declassify`. Fix adc350e (fixture), cc1cf85. -> C4 [caught now]
- **8b final I1** (I): nothing says no packet/request-level function is bounded; the 19 are helpers; DoS aim unmet and unstated. Fix 83c93b0. -> C1 [partial]
- **8b final I2** (I): Task 8 not-attempted record only in gitignored ledger; "13 translator gaps" overstated (2 of 13 predicted bounded). Fix 83c93b0. -> C3 [partial], C1 [partial]
- **8b final I3** (I): re-recording `expected-cost.txt` waved through a lost bound (18/35 passes). Fix 83c93b0 (CC:171-190 pins predicted-bounded and 36). -> C4 [caught now]
- **8b final I4** (I): gate kept only `deg`, not the atoms; a bound in `len(..)` could become `k*n` unseen. Fix 83c93b0. -> C4 [caught now]
- **8b final M1-M3, M5, M6** (M): "terminating run"; stale spec example; TRUSTED omitted vest_lib; no fixture for dropping a secret enum; script tidying. Fix 83c93b0. -> C1 [partial], C2 [open]
- **8b final M4** (M): parser-only manifest lines sat in the file crypto's check loads (widens crypto rules for future code). Fix 83c93b0 (manifest-parsers.txt). -> C13 [open]

### Phase 8c (verified CT front end)
- **8c T1 I1-I2** (I x2): dump closure missed Pat Range consts / TyConstId; insts.def missing. Fix 993e093. -> C12 [scheduled 9a design section 7]
- **8c T4 I1** (I): `ctmir::sem` could give None on in-subset code, making theorems vacuous; also &str, entry_local. Fix da0595a, 889fbda (4-way outcome, `in_subset`, progress theorem). -> C12 [scheduled 9a design section 7]
- **8c T5 C1** (R, faithfulness): `call_ok` checked arity only; a rust-call closure body bound to a tuple would give a wrong Done. Also I1 ZST arrays, I2 indexed call destination, I3 per-root key map, M6 declassify arg type. Fix a1f436d, 6cc5a76. -> C12 [scheduled 9a design section 7]
- **8c T6 seat B C1** (C): H5/H11 made unit-like arrays ([T;0], [ZST;n]) Panic where Rust completes; `ok` would be vacuous; no test caught it, only the clean-room audit. Fix dad19a5, b6bdb1b, 60d9a59 (+ lowers reject). -> C12 [scheduled 9a design section 7]
- **8c T6 BLOCKED** (R): exact simulation false on ill-typed dumps; two representations of unit-like values. Fix: align producers (8a5a37e etc.). -> C12 [scheduled 9a design section 7]
- **8c T7 C1, I1** (I): decoding existential (report_sound about some j, m); labels tied to printed line not `decl_spec`. Fix 13f6ad1, 53efee3 (print injective); decode functionality left as TRUSTED row. -> C12 [scheduled 9a design section 7]
- **8c T8 M2, M4, M6** (M): ct-front without timeout, wanted-value widths unchecked, ct-zarr failed open. Fix 5e1c405. -> C4 [caught now]
- **8c T9 I1** (I): TRUSTED list of unfolded spec fns incomplete. Fix 4479e5b. -> C1 [partial]
- **8c final I1** (I): no check exercised `ctmir::sem` (interp ran core; theorem_sim one-directional); three docs said vectors test it; never-Stuck had no executable evidence. Fix 908c3c4 (text), 8d (evaluator). ESCAPE: doc claim by construction; Task 6 C1 had already shown the risk. -> C12 [scheduled 9a design section 7], C1 [partial]
- **8c final M1-M4** (M): "listed in this row" incomplete; `policy_of` exec-only restrictions (label_spec Some, declassify shape) absent from spec; step-count wording; nits. Fix 908c3c4. -> C1 [partial], C12 [scheduled 9a design section 7]

### Phase 8d (MIR evaluator)
- **8d preflight** (pre, 2 C, 4 I, 10 M): e.g. panic vectors are no never-Stuck evidence (Out::Panic includes stuck), mir_entry totality. Fix 6124c84, fe7adf3. -> C12 [scheduled 9a design section 7], C16 [open]
- **8d T4 I1** (I): hand-traced Huffman vectors not labelled. Fix 63f8ec9. -> C1 [partial]
- **8d T4 M2** (M): coverage gate passed with zero roots. Fix 63f8ec9 (`-gt 0`). -> C4 [caught now]
- **8d final I1** (I): TRUSTED rows 45/48 and selftest.txt header say all non-Huffman parser values are native; 9 of 13 are derived from enclosing-call assertions. Fix 14a7ded. ESCAPE: provenance is free text in vectors file; hand-typed claim. -> C1 [partial]
- **8d final I2** (I): spec said "none gave Panic" while 217 semconf vectors pass through `Panic`. Fix 14a7ded. -> C1 [partial]
- **8d final M3, M4** (M): cost-targets.txt non-`cost-root` lines would split cpol; `eval_probe --exact` could run 0 tests. Fix 14a7ded (guards, demos fail closed). -> C4 [caught now]
- **8d final M1, M2, M5, M6** (M): stale semconf header, stale `interp` mentions in code and 8c spec, wording. Fix 14a7ded. -> C2 [open]

### Phase 9a (pilot, in flight; fixes pending in wt-9a)
- **9a plan finding 1** (new bug on main): an empty CRYPTO frame ending past base+16384 closes CRYPTO_BUFFER_EXCEEDED (window checked before the empty filter); sibling of 753ec2d. Fix: pending (Task 3). ESCAPE: 753ec2d fixed the instance; no ensures says which codes are allowed. -> C5 [caught now (ratchet); proofs 9a/9b/9c]
- **9a pre C1** (C): the planned `Connection::lemma_crypto_end_received` pushes `RecvStream::on_data` past rlimit 4 (4 reproductions; 98.3% before). Fix: pending (Task 0 restructuring, varB shape). -> C11 [scheduled 9r2]
- **9a pre I1** (I, directive): deleting `superseded`'s second close rested on an argued, not proved, invariant; needs `crypto_kept` + base-monotonic ensures on every call. Pending (Task 3b). -> C6 [scheduled 9r2]
- **9a pre I2** (I): tight atoms +17.9% in `poll_transmit`; plan's ±5% guard trips; Z3 perturbs untouched fns (`Reassembly::insert` 6.85M..11.54M). Pending. -> C11 [scheduled 9r2]
- **9a pre I3** (I): RecvStream empty STREAM insert grows the window (audit item "no fix"). Pending (Task 6). -> C5 [caught now (ratchet); proofs 9a/9b/9c], C10 [scheduled 9r2]
- **9a pre I4** (I): acceptance clauses stop at `on_crypto`; `on_crypto_frame`/`on_frame`/`on_counted`/`apply` carry none, so "end to end" untrue. Pending/9c. -> C5 [caught now (ratchet); proofs 9a/9b/9c]
- **9a pre I6** (I): `tp_allowed_err` `Err(_) => true` makes the clause vacuous on the parse-error path. Pending (Task 4). -> C5 [caught now (ratchet); proofs 9a/9b/9c]
- **9a pre m3, m4, m11** (M): mutants fail on the plan's own precondition rather than the claim; duplicate test; no mutation shows `trailing_bytes_before_bad_tp_pv` can fail. -> C6 [scheduled 9r2]
- **9a pre m9** (M): span window vs RFC "4096 bytes of data" floor undecided (set possibly wider/narrower than RFC). -> C5 [caught now (ratchet); proofs 9a/9b/9c]

### Older phases, from the fix-commit log only (subject lines; severity unknown)
- **S1** (Phases 1-2, h3/QPACK): 6ac2563 sender MUSTs in serializers; ca6c1b7 message validation hardening; d2576fb `te` connection-specific, CONNECT authority-form; ea6a38a HEAD + content-length per status; 52e8122 final responses only; e4ed141 skip unknown control frames without buffering; 1d1831e GOAWAY highest. ESCAPE (shared): ensures/matrix claimed clauses the code did not enforce until a task review. -> C7 [scheduled 9a, 9b, 9c], C5 [caught now (ratchet); proofs 9a/9b/9c]
- **S2** (3a-3c, quic): 6e458fb spin bit missing in short-header serializer; a2a92f0 poll_frames not tied to bytes sent/credit; 3889c1c, ceb1fa1, 0db5249 send/reassembly copies O(n) per ack/pop (algorithmic cost). -> C6 [scheduled 9r2], C15 [open]
- **S3** (3d, quic): e6b31c7/f6debe4 repeated NEW_CONNECTION_ID with raised RPT not acted on / replay an error; 7be9295 reset-token check after routing; 327cf4c handshake path not MTU-validated; 57eb957/a240cc0 an ack-eliciting range could be dropped unreported; b74be1b unbounded CID table admission; 5c173cc retire backlog budget. -> C7 [scheduled 9a, 9b, 9c], C10 [scheduled 9r2]
- **S4** (4a-4b, tls): 03a25b2 SHA-1-free chain pass; 31add70 offered-scheme MUST; 4b27342 ClientHello extension floor; d73bad6 reserved scheme/group preconditions; e587b9e TlsEvent Debug printed traffic secrets. -> C7 [scheduled 9a, 9b, 9c], C17 [open]
- **S5** (5a-5d, crypto): 1bd393b RSA key wf did not require d < n; a6a5534 compute certificates split to pass at rlimit 0.35; 07add7a spinoff_prover on sha256 fns (rlimit); 613a228 3a final fix wave. -> C8 [scheduled 9r2], C11 [scheduled 9r2]
- **S6** (8a, CT): 4e956ff declassify only GCM accept/reject bit (was wider); 0c43030 one declassify per line; 98f7bc2 fail closed on ambiguous keys, missing manifest, rootless crates. -> C14 [scheduled 9a design section 7], C13 [open]

---
## 2. Classes: existing catch and proposed catch

**C1 DOC-OVERCLAIM** (doc/TRUSTED/matrix/comment says proved, checked, native, live, bounded beyond the evidence; hand-typed numbers and provenance).
 EXISTING NOW: V checks only declassify/escape rows against source; `duvet report` checks RFC quotes exist; CC pins counts of bounded roots and pass lines. No check on prose.
 PROPOSED: (1) generated claims: replace hand-typed counts and verdicts in TRUSTED.md/spec/requirements with `<!--gen:KEY-->` markers that `scripts/claims.sh` (in V, fail-closed) diffs against ct-check/ct-binary/verify output (S). (2) Evidence-tagged rows: every requirements.md row marked done carries `[proved:<fn>|tested:<test>|review]` and V greps that the fn/test exists, and TRUSTED rows containing "proved|verified|native" need a tag (M). (3) Provenance column in selftest/semconf vectors (`native|derived|hand-traced`), the gate prints counts per kind and TRUSTED embeds the generated line (S). (4) `//= exception` and TRUSTED-row pairing check like the declassify 3-way diff (S).
 STATUS: partial (R3: quote existence caught now; prose claims open)

**C2 STALE-TEXT** (plan/audit/comment not updated after a ruling or code change).
 EXISTING NOW: none (plans/ledgers not linted).
 PROPOSED: `scripts/doclint.sh` in V: every backticked identifier and `path:line` in TRUSTED.md, requirements.md, audit docs and comments cited from them must resolve with `grep -F` in the tree (identifiers) or the line must still contain the named token (S); "proposed/TODO/later item" words in TRUSTED.md fail (S).
 STATUS: open

**C3 CARRYOVER-IN-PROSE / UNTRACKED EVIDENCE** (rulings, binding notes, tool outputs, scratch checkers only in gitignored `.superpowers/`, /tmp, or plan text).
 EXISTING NOW: memory file `phase-2-carryover.md` (not in repo); nothing in V.
 PROPOSED: tracked `docs/carryovers.tsv` (id, owner phase, closing evidence = test name | proof fn | doc anchor); V fails if an item whose owner phase is <= the current phase has no resolving closing evidence (M). A merge checklist script copies any ledger line containing "Parked|carry|binding note" into carryovers.tsv. Move `check_quotes.py`, `rows.py`, `rl.py`, `mut.py` into `scripts/` or `tools/` (S).
 STATUS: partial (R1: tools tracked; carryover gate open)

**C4 GATE-FAIL-OPEN** (gate or test can pass with nothing checked, can be re-recorded, or masks a failing pipeline).
 EXISTING NOW: instance fixes only: CC:171-190 (lost-bound, 36 pin), CC:183 (cost-targets only cost-root), `-gt 0` coverage guard, eval_probe "1 passed", verify.sh:34-35 exact deps, ct-binary stamp/pre-checks, strict-quiche panic.
 PROPOSED: (1) `scripts/gate-demos.sh` in V (or CI): for each gate, apply a canned mutation (drop a root, empty a list, rename a test, delete a TRUSTED row) and assert non-zero exit; 8d did this by hand per task (M). (2) `shellcheck` + require `set -eu` and no unguarded `|` in scripts/ (S). (3) Test-skip policy: `#[ignore = "reason"]` only; an early `return` on missing env must `panic!` under `STRICT` (S).
 STATUS: caught now (R2, R5; shellcheck out of scope)

**C5 ERROR-PATH NOT PROVED RFC-REQUIRED** (a close/Err is unrestricted or over-strict: any code, any trigger; includes vacuous allowed-sets).
 EXISTING NOW: only the 9a pilot design (not merged): `allowed_err` predicates for `on_crypto`, `close_spec`; elsewhere tests and reviewer reading. Closed-instance fixes (88c25aa, 753ec2d).
 PROPOSED: proof obligation. Every exec `Err(c)` return and `close(code)` call site in verus! fns must have `ensures Err(c) ==> allowed_<site>_err(inputs, c)` where `allowed_*` is a spec fn whose body lists RFC conditions with `//#` duvet citations and is never `true`/`Err(_)=>true`. Enforce by a lint in V that greps `close(`/`Err(` inside `verus!` blocks and requires the enclosing fn's ensures to mention an `allowed_` name or a `//# allowed_err_exempt:` reason (M, scheduled as 9a-9c; L to cover all of quic/quictls/h3).
 STATUS: caught now (R4 ratchet); proofs scheduled 9a, 9b, 9c

**C6 MUST ONLY TEST-PINNED / MUTANT SURVIVES THE PROOF** (ensures weaker than behaviour or RFC; a deletion/inversion still verifies).
 EXISTING NOW: manual mutation sweeps recorded in ledgers ("all N mutants fail"), scripts untracked (`mut.py` in evidence dirs); some residuals documented in TRUSTED.
 PROPOSED: tracked mutant registry `tools/mutants/*.toml` (file, search/replace, expected failing item: verify error or test name) and `scripts/mutate.sh` run at every phase merge (too slow for V); a surviving mutant must be listed in TRUSTED as "test-pinned". Pair with iff-form ensures for gates and counters (the 3d2/3e pattern) so the sweep is a regression check, not discovery (M-L).
 STATUS: scheduled 9r2

**C7 REQUIRED CLOSE/ACTION MISSING (MUST gap)** (completeness direction absent: input violating a MUST is not shown to close/reject).
 EXISTING NOW: duvet MUST-annotation coverage (the 3d2 final review reran an ad-hoc script `musts.py`), tests per row.
 PROPOSED: for each MUST of the form "MUST treat as connection error of type X", a spec predicate `violates_<id>(state,input)` and an ensures `violates ==> closed_with(X)` on the dispatcher; V cross-checks duvet MUST quotes containing "connection error of type" against `//# proved-by: <fn>` tags that resolve (M-L). Pair with C5 (the two directions of the same iff).
 STATUS: scheduled 9a, 9b, 9c

**C8 INVARIANT TOO WEAK / STATE GATING** (wf admits an RFC-violating state; action allowed in a wrong phase).
 EXISTING NOW: manual counterexample tracing by preflight/review; wf conjuncts added over time.
 PROPOSED: write each RFC invariant as a separate spec `rfc_inv()` straight from the RFC sentence (not from code), add `ensures final.rfc_inv()` on all pub Connection fns and a lemma `wf ==> rfc_inv`; the proof then fails if wf is weaker than the RFC (M). Plus a seeded random-op-sequence test in `tests/` that checks a runtime copy of `rfc_inv` after every op (S).
 STATUS: scheduled 9r2

**C9 COMPOSITION GAP** (each contract proved, the shell/driver sequence or a state arm not covered).
 EXISTING NOW: `settled_later` for `Connection` and `H3Server`, `timers_cover/timers_later` incl. Closing/Draining arms (ac9274a, b62c56a), `pipeline::settled_later` for the wake sequence.
 PROPOSED: a V lint that every `Connection`/`H3Server` method called from `crates/server` and `crates/quictls` appears in TRUSTED's "shell calls" row with its `requires`, and that the wake sequence is a single proved spec composition (S for lint). Test: tests must wake at `next_timeout()`, never at a literal (grep, S).
 STATUS: open

**C10 UNAUTHENTICATED RESOURCE EXHAUSTION** (state slots, memory, CPU driven by unauthenticated input).
 EXISTING NOW: path-slot gating (64f24b3), capacity tests, h3_alloc.rs, cost analyser (19/36, helpers only), bounded CID tables.
 PROPOSED: proof: `ensures` that unauth-reachable tables grow only on a gated packet (`!gated ==> final.slots == old.slots`) for Paths, CidTable, route, shell address table (M); a seeded 200k-datagram invariant test promoted from reviewer probe into `crates/server/tests` (S); handshake CPU benchmark with a generated number in TRUSTED (C1 marker) (S).
 STATUS: scheduled 9r2

**C11 PROOF-BUDGET FRAGILITY** (rlimit cap, Z3 perturbation across modules, import-triggered blow-up, cache replay).
 EXISTING NOW: controller's manual fresh rlimit-4 run with fingerprint deletion (checks.sh/rl.py outside the repo); V runs default rlimit and does not detect a replay; crate split quictls.
 PROPOSED: V (or a nightly job) runs `cargo verus verify -- --rlimit 4 --output-json --time-expensive` with `touch`-invalidated fingerprints, fails if verified count == 0 ("Finished"), and fails if any query exceeds 8M (2/3 of cap); commit `docs/rlimit-top.txt` and diff top-8 each run (M; 40 min cost, so merge-time).
 STATUS: scheduled 9r2

**C12 TRUSTED SEMANTICS / TRANSLATOR UNFAITHFUL, UNEXERCISED OR VACUOUS**.
 EXISTING NOW: 8d exec evaluator (`pass_ok`: each ok/bounded root reaches Done on a real input; CC "done roots 11/11, bounded 19/19"), semconf 31723, `sem_sanity` facts, two clean-room audits, `ct-zarr.py`, dumps tests in CC.
 REMAINING GAP: never-Stuck for unexercised inputs; `decode_crate` functionality (both TRUSTED rows).
 PROPOSED: backward simulation `lowers && wt_args && core Some ==> MIR Done` or never-Stuck under typing premises (L); prove `decode_crate` functional (L); seeded differential fuzz of `sem` vs native on generated in-subset functions (M).
 STATUS: scheduled 9a design section 7

**C13 CHECKER IDENTITY / BLAST RADIUS** (maps keyed by name, shared manifests widen another check).
 EXISTING NOW: crate-id key (c93823d), split manifest (83c93b0), fail-closed ambiguous keys (98f7bc2); crypto report `cmp` against a baseline done by hand.
 PROPOSED: tracked `tools/ct-fixtures/expected-crypto-report.txt` and CC diffs it (S); lint `HashMap<String` keyed by path in ct-driver plus a two-crate same-name fixture (S).
 STATUS: open

**C14 BINARY vs MIR CT / CT STYLE** (MIR proof does not bind LLVM; spec-RFC §9.5 style claims).
 EXISTING NOW: CB digest gate (49 fns), audit doc, dudect tests (`--ignored`, not in V), `ct_mask` `#[inline(never)]`.
 PROPOSED: quic packet protection as CT roots with the pn secret (8c follow-up, closes §9.5 residual) (L); LLVM-IR check that no `br` consumes a `ct_mask`-derived value in crypto (L); dudect run recorded by a generated TRUSTED line (S).
 STATUS: scheduled 9a design section 7

**C15 ALGORITHMIC COST NOT IN CONTRACTS** (quadratic copies, per-event O(n), cost-only mutants survive).
 EXISTING NOW: h3_alloc.rs (one case), 8b cost gate (parser helpers only, no network-driven function).
 PROPOSED: ratio tests (op at n, 2n, 4n; allocations/copied bytes must scale <= linear) for each streaming op in quic/h3 (S each); extend cost targets to `parse_payload`, `decode_field_section` after 8b's follow-ups (L).
 STATUS: open

**C16 PLAN DRIFT** (plans reference missing paths, tools, or stale baselines).
 EXISTING NOW: opus preflight scan before each phase (manual, effective: 3d2 1C/8I, 3e 28, 4c 9C, 5e 1C, 8b 2C, 8d 2C, 9a 1C).
 PROPOSED: `scripts/plan-lint.sh BASE plan.md`: every path, `fn`, `file:line`, verify.sh final-line literal and script name in a plan must resolve at BASE (S). Keeps preflight for judgement only.
 STATUS: open

**C17 SECRET HYGIENE** (derive(Debug)/Clone on key material).
 EXISTING NOW: hand-written redacting Debug (PacketKeys 586d6d6, TlsEvent e587b9e); TRUSTED non-zeroisation row.
 PROPOSED: V grep: structs in crypto/tls/quic/quictls with fields of type `[u8; 16|32]`/`Key`/`Secret` must not `#[derive(Debug)]` (allowlist file) (S).
 STATUS: open

**C18 UNVERIFIED SHELL CODE** (crates/server, quictls glue shell).
 EXISTING NOW: shell.rs/initial_exchange.rs/respond.rs/interop tests, strict quiche; reviewer fuzz not kept.
 PROPOSED: tracked seeded fuzz of `Server::on_datagram/on_wake` asserting slot growth only on gated packets and settled `deadline()`; `getsockopt` assertions for V6ONLY/DF in a socket test (S).
 STATUS: open

---
## 3. Summary table (ordered by count x severity)

| class | count | entries | existing catch | proposed catch | size | status |
|---|---|---|---|---|---|---|
| C1 DOC-OVERCLAIM | 24 | 3d2 T3 I4, final I1, M2; 3e T3 M1, final I1; 4c T3 M3-5, final M1-M3, T5; 5e I1, I2, I3, m2-m6; 7a T2, m1-m6; 8b T1b I2, T2 C1, final I1, I2, M1-M3; 8c T9 I1, final I1, M1-M4; 8d T4 I1, final I1, I2 | none for prose (V checks declassify/escape rows only) | generated-claim markers + evidence-tagged rows + vector provenance column | M | partial (R3: quote existence caught now; prose claims open) |
| C12 SEMANTICS UNFAITHFUL/UNEXERCISED | 13 | 8b pre C1/C2, T2 C1; 8c T1, T4, T5, T6 x2, T7, final I1, M1-M4; 8d pre | 8d evaluator, semconf, sem_sanity, audits | backward simulation / never-Stuck proof; decode functional proof; differential fuzz | L | scheduled 9a design section 7 |
| C6 MUST ONLY TEST-PINNED | 20 | 3d2 1a-ii I2, 1b I1-I3, 2a-i, 2b, 3 M3, 4 I1; 3e T1, T2 M1, T3 I1, M2, T4, T5 C1, C4; 4c T2, preflight C9; 9a I1, m3/m4/m11; S2 | manual mutation sweeps (untracked) | tracked mutant registry + `mutate.sh` at merge; iff-form ensures | M-L | scheduled 9r2 |
| C5 ERROR PATH NOT PROVED REQUIRED | 9 | 3e T5 I1; 4c T3 re-review, final M1; 9a f1, I3, I4, I6, m9; S1 | 9a pilot design only | `allowed_*_err` ensures on every Err/close site + lint | L | caught now (R4 ratchet); proofs scheduled 9a, 9b, 9c |
| C7 REQUIRED CLOSE MISSING (MUST gap) | 8 | 4c T3 M1, M2; S1, S3, S4 | duvet annotations, tests | `violates ==> closed_with(X)` + duvet proved-by tags | M-L | scheduled 9a, 9b, 9c |
| C4 GATE FAIL-OPEN | 17 | 4c final I1; 5e m1; 7a T1 I1, N1-N3, final I1, m1-m6 (as group); 8b T4/T6, final I3, I4; 8c T8; 8d T4 M2, final M3, M4 | instance guards (CC:171-190, 183, `-gt 0`, deps gate) | gate-demos.sh, shellcheck/pipefail, no-skip-as-pass policy | M | caught now (R2, R5; shellcheck out of scope) |
| C8 INVARIANT TOO WEAK / STATE GATING | 7 | 3d2-pre C1, 1a-i, 1b I4, T3 I5; 4c T3 M3-5; S5 | review by reading | separate `rfc_inv()` + `wf ==> rfc_inv`, random-op test | M | scheduled 9r2 |
| C9 COMPOSITION GAP | 6 | 3d2 T3 I1-I3, final I1, M1; 3e preflight C4 | `settled_later`, timers_cover/later | shell-call whitelist lint, wake-at-next_timeout lint | S | open |
| C10 UNAUTH RESOURCE EXHAUSTION | 7 | 3d2 1a-ii I1; 3e preflight C1; 5e I3; 9a I3; S3 | slot gating, capacity tests | grow-only-on-gated ensures, tracked fuzz, CPU benchmark claim | M | scheduled 9r2 |
| C11 PROOF-BUDGET FRAGILITY | 8 | 3e preflight C27; 4c T1; 5e T5 M3; 9a pre C1, I2; S5 | manual rlimit-4 runs outside repo | rlimit-4 + replay + 8M profile gate at merge | M | scheduled 9r2 |
| C14 BINARY vs MIR CT | 7 | 3e ruling, final I1; 5e pre C1, audit, I2; 7a T1 I2, T2; S6 | ct-binary.sh digests, dudect (not gated) | quic CT roots, LLVM IR check | L | scheduled 9a design section 7 |
| C3 CARRYOVER IN PROSE | 8 | 3d2 final M5; 3e final M2, M4; 4c final I1; 5e I1, T5; 8b final I2; 3e preflight | memory file only | carryovers.tsv gate, scripts tracked | M | partial (R1: tools tracked; carryover gate open) |
| C2 STALE TEXT | 9 | 3d2 final M3, M4, re-review; 3e final M1, M3; 5e m2-m6; 8b M; 8d M | none | doclint.sh | S | open |
| C13 CHECKER IDENTITY | 3 | 8b T1b I1, final M4; S6 | crate-id key, split manifest | baseline report diff, lint | S | open |
| C15 ALGORITHMIC COST | 3 | 3d2 T4 M1; S2 | h3_alloc.rs | ratio tests | S each | open |
| C16 PLAN DRIFT | 7 | preflights of 3d2, 3e, 4c, 5e, 8b, 8d, 9a | manual preflight | plan-lint.sh | S | open |
| C17 SECRET HYGIENE | 3 | 3e T2 I2; S4 e587b9e; (4c Rand) | hand-written Debug | derive(Debug) grep gate | S | open |
| C18 UNVERIFIED SHELL | 2 | 3e T6; 3e preflight C1/C2 | shell tests, reviewer probes | tracked seeded fuzz + getsockopt test | S | open |

Counts are findings (a grouped entry such as "T1a-i I1-I4" counts once per group, preflights once per phase); an entry tagged with two classes is counted in both.

## 4. Observations for the controller
1. The two classes that recur across the most phases at Important severity are C1 (doc overclaim) and C6/C5/C7 (the contract does not say which behaviour is allowed or required). The 9a plan already targets C5/C7 for the CRYPTO path; the other 90 percent of error paths in quic/h3 are not covered.
2. C4 and C1 are cheap and mechanical (S-M) and would have caught roughly 40 of the 109 entries; do these first.
3. 9a's own preflight re-found the 753ec2d bug class (empty CRYPTO frame) on main one phase later: the instance was fixed, the class (C5) was not.
4. verify.sh does not run at rlimit 4 or detect cache replay; every phase's "rlimit 4, N verified" claim comes from outside the repo (C11, C3).

## 5. Spot-check against the archived reviews (Phase 9r R1)

Checked against `.superpowers/archive/` ledgers and review files; all 109 hash-like tokens resolve to commits.

| entry | class | source read | result |
|---|---|---|---|
| 3d2 T1a-ii I1 | C10 | 3d2-ledger.md:43 | confirmed (defect, fix 64f24b3) |
| 3d2 T3 I1-I3 | C9 | 3d2/task-3-review.md I1-I3; ledger:84 | fixed: fix commits were e3f1a07 and 5aa1efa, entry named only the first |
| 3d2 T3 I4 | C1 | 3d2/task-3-review.md I4 | confirmed |
| 3d2 final M5 | C3 | 3d2-ledger.md:105, 4c-ledger.md:4 | confirmed |
| 3e ruling correction | C14 | 3e-ledger.md:134,137 | fixed: the ledger does not say the ruling was made "from memory"; reworded as an inference |
| 3e T2 I1-I2 | C17 | 3e-ledger.md:143 | confirmed |
| 4c T3 re-review | C5 | 4c-ledger.md:29-30 | confirmed (753ec2d) |
| 4c T3 M1, M2 | C7 | 4c-ledger.md:28 | confirmed (6fa13ef) |
| 5e pre C1, final I3 | C14, C10 | 5e-ledger.md; 5e-final-review.md:53-62 | confirmed (7-8x, 6 ms / 45 ms) |
| 7a T1 I1-I2 | C4 | 7a-ledger.md:6-7 | confirmed (0b846ce) |
| 8b T2 C1 | C12 | 8b-ledger.md:86-96 | confirmed (b6beb17, 18b0726) |
| 8c final I1 | C12 | 8c-final-review.md:61-70 | confirmed |
| 8d final M3, M4 | C4 | 8d-ledger.md:20-21 | confirmed (14a7ded) |
| 9a plan finding 1 | C5 | crates/quic/src/crypto_stream.rs:89-98 on main | confirmed (window check precedes the empty filter) |
| S2 6e458fb, S3 7be9295, 327cf4c, S4 e587b9e, S5 1bd393b, S6 98f7bc2 | C6..C14 | git log subjects | confirmed |
