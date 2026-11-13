# Roadmap

Every phase this project has named, its status and the order of the open ones. Open work items are rows of
`docs/carryovers.tsv` (`#id owner status evidence source text`); each row's owner is an id of the table below.
`scripts/carryovers.sh` (run by `scripts/verify.sh`) fails when a `merged` phase owns an `open` row, when a row's owner
is not in this table, when a closed row's evidence does not resolve, when a row present in an earlier copy of the tsv
is deleted (closing is a status change), and when a `TRUSTED.md` row's removal cell names neither a phase below nor
`never (` and a reason.

Status: `merged` (on main; the plan / merge cell names a commit that is an ancestor of HEAD, normally the merge;
a phase once `merged` stays `merged`, and every first-parent `Merge phase-<id>` commit needs `<id>` merged), `in progress` (a branch exists), `planned` (a plan file
exists, no branch), `unplanned` (named in a spec, a plan's binding notes or the audit, no plan file yet). Order is
the owner's decision on audit F11 (2026-11-09): Phase 6 lands before the parts of 9b/9c that touch the `conn.rs`
send and recovery paths; parts of 9b/9c that do not touch them may go earlier. Plans are in `docs/superpowers/plans/`.

| id | title | status | order | plan / merge |
|---|---|---|---|---|
| 0-1 | toolchain, workspace and `wire` varint | merged | - | `2026-10-27-phase-0-1-toolchain-and-varint.md`; committed on main, last 1833f2f |
| 2a | h3 frame and QPACK codecs | merged | - | `2026-10-27-phase-2a-h3-qpack-codecs.md`; 7055ab3 |
| 2b | h3 connection layer | merged | - | `2026-10-27-phase-2b-h3-connection.md`; cc9389e |
| 3a | crypto specs and RustCrypto shims | merged | - | `2026-10-27-phase-3a-crypto-specs.md`; 5465de7 |
| 3b | QUIC codecs | merged | - | `2026-10-27-phase-3b-quic-codecs.md`; fa472e2 |
| 3c | QUIC streams and flow control | merged | - | `2026-10-28-phase-3c-quic-streams.md`; c7ef8f0 |
| 3d | QUIC connection building blocks | merged | - | `2026-10-29-phase-3d-quic-connection.md`; 510aac3 |
| 3d2 | QUIC Connection and the H3 adapter | merged | - | `2026-10-29-phase-3d2-quic-connection-integration.md`; 55d9f55 |
| 3e | packet protection and the server shell | merged | - | `2026-11-03-phase-3e-packet-protection-shell.md`; c1329b9 |
| 4a | TLS 1.3 message codecs | merged | - | `2026-10-28-phase-4a-tls-codecs.md`; e1bb618 |
| 4b | TLS 1.3 server handshake | merged | - | `2026-10-28-phase-4b-tls-handshake.md`; ee72841 |
| 4c | QUIC-TLS glue, shell, first interop | merged | - | `2026-11-05-phase-4c-quic-tls-glue.md`; ecd54a2, quiche d06282e |
| 4d | QUIC key update and AEAD limits | unplanned | 8 | none; `2026-11-05-phase-4c-quic-tls-glue.md:674-679` |
| 5a | verified SHA-256, HMAC, HKDF | merged | - | `2026-10-28-phase-5a-hash-kdf.md`; 9af3a0d |
| 5b | verified AES-128 and GCM | merged | - | `2026-10-28-phase-5b-aes-gcm.md`; 60b940d |
| 5c | verified P-256, ECDH, ECDSA | merged | - | `2026-10-28-phase-5c-p256.md`; 11fdf92 |
| 5d | P-256 group law | merged | - | `2026-10-28-phase-5d-group-law.md`; c5aecf9 |
| 5e | verified RSA-PSS signing, vectors | merged | - | `2026-11-02-phase-5e-rsa-vectors.md`; 4ac8251 |
| 6 | loss recovery and congestion control (RFC 9002) | unplanned | 5 | none; design spec `:118-119` |
| 7a | binary CT gate and timing tests | merged | - | `2026-11-03-phase-7a-binary-ct-gate.md`; 7e95f7f |
| 7 | full conformance and browsers (rest of Phase 7) | unplanned | 9 | none; design spec `:120-122` |
| 8a | verified constant-time checker | merged | - | `2026-10-28-phase-8a-ct-checker.md`; 6641fa2 |
| 8b | verified step-bound analyser | merged | - | `2026-10-28-phase-8b-cost-analyser.md`; e6c1c00 |
| 8c | verified MIR front end | merged | - | `2026-11-03-phase-8c-verified-front-end.md`; 0b0061c |
| 8d | verified MIR evaluator | merged | - | `2026-11-05-phase-8d-mir-evaluator.md`; 73cc244 |
| 9r | RCA catalog and first class catches | merged | - | `2026-11-06-phase-9r-rca-catches.md`; 244e61b |
| 9r2 | class catches in verify.sh | merged | - | `2026-11-07-phase-9r2-class-catches.md`; f4f0c9c |
| 9r3 | audit gates and the roadmap | merged | - | `2026-11-09-phase-9r3-audit-gates-and-roadmap.md`; d416f34 |
| 9a | acceptance pilot, Tasks 0-4 and 6 | merged | - | `2026-11-05-phase-9a-acceptance-pilot.md`; ed35647 |
| 9a2 | acceptance pilot, Tasks 3b, 5, 3c' (sparse CRYPTO store) | merged | - | `2026-11-05-phase-9a-acceptance-pilot.md`; 680a3f0 |
| 9b | spec-only acceptance lemmas, rule 2(b) | unplanned | 4 (P3), 6 (P4) | none; Phase 9 spec `:50`, `:131-141` |
| 9b1 | a Frags index: the out-of-order CRYPTO store on a verified AVL of chunks, cost proved per call (C15) | in progress | 4 | `2026-11-12-phase-9b1-frags-index.md` |
| 9b2 | a verified de-amortized byte queue for every quic/tls byte buffer on input paths (CryptoStream buf and read, HsReader, Reassembly, send_stream, the TLS transcript) | unplanned | 4 (after 9b1, before Phase 6) | none; 9b1 spec D10 (owner decision 2026-11-12); `docs/rca/2026-11-12-cost-sweep.md` |
| 9b3 | h3 input costs (the quadratic cookie merge first, with its RCA; reqs/unis remove+insert; request buffers) | unplanned | 4 (after 9b1, before Phase 6) | none; 9b1 spec D10 (owner decision 2026-11-12); `docs/rca/2026-11-12-cost-sweep.md` |
| 9b4 | the remaining sites of docs/rca/2026-11-12-cost-sweep.md (server conns table, tls ext bitmap, ack/inflight/route tables, builders) and the sweep as a gate | unplanned | 4 (after 9b1, before Phase 6) | none; 9b1 spec D10 (owner decision 2026-11-12); `docs/rca/2026-11-12-cost-sweep.md` |
| 9b5 | incremental parsing: TLS handshake messages, h3 frames and QPACK field sections parsed as bytes arrive, so no call does more than O(d + log n) | unplanned | 4 (after 9b4, before Phase 6) | none; owner decision 2026-11-12; 9b2 spec Open questions 1 |
| 9c | frame errors, h3 to quic closes, tls own limits | unplanned | 4 (parts that touch no `conn.rs` send or recovery path), 6 (the rest) | none; Phase 9 spec `:51`, `:143-161` |
| 9t1 | `decode_crate` functional | unplanned | 7 | none; Phase 9 spec `:271` |
| 9t2 | `mir_run` fuel monotonicity | unplanned | 7 | none; Phase 9 spec `:272` |
| 9t3 | quic packet protection and tls glue as CT roots | unplanned | 7 | none; Phase 9 spec `:273` |
| 9t4 | cost bounds for network-driven fns | unplanned | 7 | none; Phase 9 spec `:274` |
| 9t5 | `respond`'s Busy ordering proved | unplanned | 7 | none; Phase 9 spec `:275` |
| 9t6 | never-Stuck for bounded roots | unplanned | 7 | none; Phase 9 spec `:276` |
| 9t7 | ct-front's `main` and ct-check.sh's decisions in verified code | unplanned | 7 | none; review I3 of 9r3 Task 5 (TRUSTED.md `:46`) |
| 9t8 | vest_lib's escapes verified in-tree | unplanned | 7 | none; controller ruling, 9r3 Task 5 fix round 1 (TRUSTED.md `:28`) |
| 9t9 | crypto trust items proved: declassified outcomes, constants | unplanned | 7 | none; review I3 and controller ruling, 9r3 Task 5 fix round 1 (TRUSTED.md `:52-58`, `:66`, `:69`) |
| 10a | admission and bounds | unplanned | 6 | none; audit F2, F10, F14, F15 |
| 11 | composed end-to-end theorem | unplanned | 10 | none; audit F8 |
| 12 | production readiness | unplanned | 11 | none; audit F10 |
| t1 | toolchain upgrade procedure (design only) | unplanned | - | none; audit F12 |
| q1 | scripts/quick.sh, a scoped inner-loop check (owner request 2026-11-10) | merged | - | none (owner request); aed556e |

"design spec" is `docs/superpowers/specs/2026-10-27-verified-http3-design.md`; "Phase 9 spec" is
`docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md`; "audit" is `docs/audit-2026-11-09.md`.
The `9t` ids are trust-base sub-phases after 9c, sharing order 7: 9t1-9t6 are the Phase 9 spec's (`:268-276`); 9t7-9t9
were added by the 9r3 Task 5 review (I3) and the controller's ruling on it, so that no TRUSTED row a proof could remove
stays `never`.
`t1` has no slot in the owner's order: it is a design, done before any toolchain upgrade.

## Open phases

### 10a: admission and bounds

- Scope: the server's DoS goal. The handshake deadline (F2, a bug: RCA, class and catch), MAX_CONNS admission and
  slot eviction under RFC 9000 §10.1's 3·PTO floor, Retry or a per-source handshake limit, the SipHash CID and token
  index, path-slot eviction, the RSA key loader that establishes `rsa_key_wf`, the shell's per-datagram walk (F14),
  the per-connection memory figure (F15), transmit-loop termination, and proved server-level running-time and
  memory bounds. Owns catalog class C10.
- Owner decision (2026-11-10): Phase 6 goes before 10a (orders 5 and 6; 10a shares 6 with 9b/9c's `conn.rs` parts), so 10a's handshake deadline is proved once, on
  Phase 6's re-proved `open_timeout` (`bind-timers`). F2's slot exhaustion stays open until 10a.
- Sources: audit F2 (`:72-87`), F10 (`:176-189`), F14, F15; 3d2 plan `:799`, `:804-805`; 3e plan `:445`; 4c plan
  `:680`; `docs/rca/catalog.md:206-209`; TRUSTED.md `:34`.
- Carryovers: `aud-F2`, `bind-maxconns`, `bind-retry`, `bind-siphash`, `aud-s6`, `tr-34`, `aud-F14`, `aud-F15`,
  `aud-s4`, `cat-C10`, `cat-C15-ratio`, `cat-C18`, `mem-fs-copy`, `req-10a`.

### 9b: spec-only acceptance lemmas and rule 2(b)

- Scope: P3 (one `allowed_x` and one lemma per `rfc_*` codec spec) and P4 (the CONNECTION_CLOSE is emitted, through
  `poll_transmit`). P3 touches no `conn.rs` send or recovery path and runs at order 4, before Phase 6; P4 goes after
  it, at 6. The `Frags` index that was Task 1 is phase 9b1.
- Sources: Phase 9 spec `:50`, `:131-141`; audit F6, F7 (inputs to the plan).
- Carryovers: `mem-h3-0705`, `mem-h3-21`, `mem-gen-tables`, `mem-naming`, `req-9b`.

### 9b1: a Frags index (C15)

- Scope: 9a2's sparse CRYPTO store (`quic::frags::Frags`) on a verified join-based AVL of chunks (`quic::avl`), with a
  worst-case cost per call proved in the ensures, the cost-charge gate and its demos, and mutants 9b1-M1..M4.
- Sources: `docs/superpowers/specs/2026-11-10-phase-9b1-frags-index-design.md`; `docs/rca/catalog.md:232-235`.
- Carryovers: `cat-C15` (closed by this phase).

### 9b2, 9b3, 9b4, 9b5: the 2026-11-12 cost sweep and the per-call rule

- Scope: the sites of `docs/rca/2026-11-12-cost-sweep.md` where network input pays std's amortized growth, a front
  drain or a shift: 9b2 the quic/tls byte buffers (one verified de-amortized byte queue), 9b3 h3 (the quadratic
  cookie merge first, with its RCA), 9b4 the rest and the sweep as a gate. Owner decision 2026-11-12: they run after
  9b1, before Phase 6. Owner decision 2026-11-12: the per-call rule is O(d + log n), d the bytes that call was given,
  so a call delivering a run of r bytes does not meet it: 9b2 also makes in-order delivery lazy (CRYPTO and
  Reassembly), and 9b5, after 9b4, parses TLS handshake messages, h3 frames and QPACK field sections incrementally.
- Sources: 9b1 spec D10; `docs/rca/2026-11-12-cost-sweep.md`; the 9b2 spec's Open questions 1 (9b5).
- Carryovers: `cat-C15-9b2`, `cat-C15-9b3`, `cat-C15-9b4`, `cat-C15-stream-parse`.

### 6: loss recovery and congestion control

- Scope: RFC 9002 RTT estimation, PTO with probes instead of the E8 placeholder that declares records lost, NewReno,
  per-path congestion state, and the proved invariants (bytes in flight <= cwnd). It rewrites `fire_pto` and
  `Recovery` in `conn.rs`, which is why it lands before 9b/9c's `conn.rs` parts. 21 requirements rows (`open:6`: the 19 RFC 9002 rows and the two RFC 9000 recovery halves, §9.4 and §13.3).
- Sources: design spec `:118-119`; 3d2 plan `:29` (E8), `:808-815`; TRUSTED.md `:37`.
- Carryovers: `tr-37`, `bind-amp-path`, `bind-timers`, `bind-path-amp`, `bind-sent-size`, `req-6`.

### 9c: frame errors, h3 to quic closes, tls own limits

- Scope: P5 (rule 1 and 2(a) for frame errors inside packets), P6 (h3 to quic closes), P7 (the tls own-limit
  escapes), the quictls `apply`/`feed`/`tls_step` lift, STREAM flow control and final size in both directions, and the
  acceptance and close-code gate widening of audit F6 and F7. Parts that touch no `conn.rs` send or recovery path (the
  gate widening, P7's tls predicates, the h3-side lemmas) may run at order 4; the rest goes after Phase 6, at 6.
- Sources: Phase 9 spec `:51`, `:143-161`; audit F6 (`:123-136`), F7 (`:138-150`); `docs/rca/catalog.md` C5-C9.
- Carryovers: `aud-F6`, `aud-F7`, `cat-C5`, `cat-C6`, `cat-C7`, `cat-C8`, `cat-C9`, `mem-tls-close`,
  `mem-stream-fc`, `r9a2-vstd`, `r9a2-p5`, `r9a2-resolver`, `r9a2-sup-body`, `r9a2-accept-rl`,
  `cat-C5-insert`, `req-9c`.

### 9t1 to 9t6: trust-base sub-phases

Each is its own sub-phase with a plan, after 9c (Phase 9 spec `:270-276`).

- 9t1, `decode_crate` functional: the CT front end's schema decoder is a function of its input. Carryovers: `tr-45`.
- 9t2, `mir_run` fuel monotonicity. Carryovers: `tr-49-fuel`.
- 9t3, quic packet protection, quictls key handling and the tls key-schedule glue as CT roots (RFC 9001 §9.5), plus
  the other secret compares outside crypto and per-call-site label summaries. Carryovers: `tr-42`, `tr-35-36`,
  `mem-labels`, `req-9t3`.
- 9t4, cost bounds for network-driven fns (8b's unmet DoS aim). Carryovers: `tr-51`.
- 9t5, `respond`'s stop-at-first-Busy ordering proved or moved into verified code. Carryovers: `mem-busy`.
- 9t6, never-Stuck for bounded roots via their cost proofs. Carryovers: `tr-49-stuck`, `mem-signed-cast`.
- 9t7, ct-front's 37-line `main` and the decisions in `scripts/ct-check.sh` (dump, run, coverage join) moved into verified
  code, file IO aside; the report's statements stay the claim's definition. Carryovers: `tr-46`.
- 9t8, vest_lib's 31 `external_body`, 3 `assume_specification`, 1 axiom and 1 `external_type_specification` proved
  in-tree (verified replacements, a vendored and proved copy, or dropping the dependency). Carryovers: `tr-28`.
- 9t9, crypto trust items a proof can remove: each declassified value that is the fn's own public outcome proved a
  function of that outcome (TRUSTED `:52-55`, `:58`; the RFC 6979 retry rows `:59-61` rest on a probability argument and
  stay `never`), `SHA256_K`/`SHA256_H0` derived from the prime roots and `P256_P` equal to its formula by compute.
  Carryovers: `tr-52-58`, `tr-67`, `tr-70`.

### 4d: key update and AEAD limits

- Scope: RFC 9001 §5.3 (third MUST), §5.5, §6.1-§6.4, §6.6; 7 requirements rows (20 MUSTs).
- Sources: `docs/requirements.md:19`; 4c plan `:674-679`; 3e plan `:444`.
- Carryovers: `bind-4d`, `req-4d`.

### 7: full conformance and browsers

- Scope: h3spec, h3i, quic-interop-runner, Chrome and Firefox with a local-CA P-256 certificate; a duvet report with
  no unannotated MUSTs (no script checks this exit today); the binary-level CT items 7a left ("Remains" in the design
  spec).
- Sources: design spec `:120-122`; 3e plan `:450`; audit F16.
- Carryovers: `aud-F16`, `cat-C14`, `mem-binary-ct`, `mem-duvet-7541`, `mem-exceptions`, `req-duvet`.

### 11: composed end-to-end theorem

- Scope: state at `QuicServer`'s API what the lower layers prove. First re-export the clauses the quictls wrapper
  drops (`one_response`), then request to response, which frames may appear in which space, STREAM bytes equal
  written bytes, peer limits respected, a `Request` event comes from authenticated bytes, and the keys are TLS's.
- Sources: audit F8 (`:152-164`); TRUSTED.md `:38`.
- Carryovers: `aud-F8`, `tr-38`, `req-11`.

### 12: production readiness

- Scope: logging and metrics, CI, a handler API beyond the one static body, an async shell with its decisions in
  verified code, zeroisation of secrets, certificate-derived `chain_schemes`, the shell's ignored errors, and the
  class catches no phase has taken yet (C1 prose claims, C2 doclint, C4's remaining ct-check stages, C13, C16, C17,
  the smaller gate holes of the audit).
- Sources: audit F10 (`:186-188`), "Smaller items" (`:251-258`); design spec `:32` (the missing production-readiness
  document); 4c plan `:680`; TRUSTED.md `:43`, `:65`; `docs/rca/catalog.md` C1, C2, C4, C13, C16, C17.
- Carryovers: `tr-43`, `tr-66`, `bind-chain-schemes`, `aud-prod`, `aud-s1`, `aud-s2`, `aud-s3`, `aud-s5`, `cat-C1`,
  `cat-C2`, `cat-C4`, `cat-C13`, `cat-C16`, `cat-C17`, `mem-escape-checked`, `mem-ct-spaces`, `x-shellcheck`, `req-12`, `r9a2-plan-mut`, `cat-C3-resid`, `x-dev-deps`.

### t1: toolchain upgrade procedure (design only)

- Scope: a written procedure, not an upgrade (the toolchain stays pinned). It must settle: how `tools/rlimit-ceilings.txt`
  is reset when a new Verus or Z3 raises measured rlimits (the ratchet has no reset today, `docs/rca/README.md:45-47`),
  and which functions are restructured first for headroom; how `docs/crypto-binary-digests.txt` is re-read when
  objdump or codegen changes (`docs/crypto-binary-audit.md`'s update protocol); how the MIR schema specs that mirror
  rustc 1.98.1 (TRUSTED.md `:45`) are re-checked; how vstd stays equal to vest_lib's pin; and how a dependency version
  bump is gated (deps-gate checks names only).
- Sources: audit F12 (`:198-201`); `docs/rca/catalog.md:266` (C11).
- Carryovers: `aud-F12`, `cat-C11`, `x-dep-bump`, `mem-rlimit3-fs`, `mem-case-splits`, `mem-sbox-rl3`.

## Where each audit finding went (docs/audit-2026-11-09.md)

- F1 (work not backed up): the owner pushed main and phase-9a2 on 2026-11-09; each later push needs its own go-ahead.
  No row.
- F2 (a client holds a slot forever): phase 10a, row `aud-F2`. It is a bug and needs an RCA, a class and a catch there.
- F3 (no roadmap): this file and `docs/carryovers.tsv`, gated by `scripts/carryovers.sh` (9r3 Task 5), row `aud-F3`.
- F4 (the mutant gate accepts an unrun run): fixed in 9r3 Task 2 (`docs/rca/2026-11-09-audit.md`), row `aud-F4`.
- F5 (a green run not tied to its commit or Verus): fixed in 9r3 Task 1 (`docs/rca/2026-11-09-audit.md`).
- F6 (acceptance gate skips non-`Result` error paths): phase 9c, row `aud-F6`.
- F7 (literal-code closes invisible): phase 9c (H3Server's in 9b or 9c), row `aud-F7`.
- F8 (no end-to-end statement): phase 11, row `aud-F8`.
- F9 (requirements rows marked done): 9r3 Task 6, row `aud-F9` (closed: the Status column and `scripts/requirements.sh`); the rows still open are `req-*` rows of their owner phases.
- F10 (the DoS goal has no phase): phase 10a for admission and bounds, phase 12 for logging, CI, the handler API and
  the async shell; row `aud-F10` (closed), each item a row owned by 10a or 12.
- F11 (phase order): decided by the owner; the order column above follows it. No row.
- F12 (a toolchain upgrade cannot land): `t1`, row `aud-F12`.
- F13 (interop never re-checked; test floor): fixed in 9r3 Task 4.
- F14 (every datagram walks all connections): phase 10a, row `aud-F14`.
- F15 (memory per connection): phase 10a, row `aud-F15`.
- F16 (the binary gate hashes code only): phase 7, row `aud-F16`.
- F17 (the dependency gate covers one crate): fixed in 9r3 Task 3.
- F18 (TRUSTED's removal column): each `TRUSTED.md` row now names a phase above or `never (` and a reason, checked by
  `scripts/carryovers.sh`; row `aud-F18`.
- F19 (old evidence worktrees): the owner had them deleted; the committed citations of their logs are rewritten and
  gated (row `aud-F19`); 9a2's own citation was rewritten on its branch (row `x-9a2-evidence`, closed
  with fceacf3 by the merge of main into 9r3).
- Smaller items: `aud-s1`, `aud-s2`, `aud-s3`, `aud-s5` (phase 12), `aud-s4`, `aud-s6` (phase 10a).
