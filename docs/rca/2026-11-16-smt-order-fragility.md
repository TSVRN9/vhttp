# SMT declaration-order fragility: proofs that pass on one solver path (C11, phase 9b3)

Status: fixed for h3 in phase 9b3 Task 4b (the commit that adds this file). The gate covers h3. 9b4 extends it to every
crate.

- **Defect**: several h3 proofs verified only on the path Z3 happened to take. Any edit that changed the SMT query's
  shape (not its meaning) sent them past `--rlimit 4` or far up toward it. The trigger was 9b3 Task 4 (05adcf1), which
  rewrote `build_headers` and removed h3's last `Vec::extend_from_slice` call. vstd's `extend_from_slice` spec was the
  only reachable item that put `View::view` before `Seq::new` and `array_view` in the crate's declaration order. Without
  it, every h3 module's SMT prelude lists the same declarations and axioms in a different order. The content is
  identical; only the order changes. To reproduce: run `cargo verus focus -- --rlimit 4 --verify-only-module
  qpack::field_section --log smt --log-dir DIR` in crates/h3 at 12ec841 (before) and at 05adcf1 with
  `smt_order_anchor` deleted (after), then diff `DIR/qpack__field_section.smt2`: only moved lines differ. The table is
  `scripts/quick.sh h3` (one crate run, seed 0) at 12ec841 and at 05adcf1 without the anchor:

  | fn | before | after the reorder |
  |---|---:|---:|
  | `conn::H3Conn::send_response` | 11,044,302 | fails (12,000,000) |
  | `qpack::field_section::encode_field_section` | 9,564,387 | 12,932,746 |
  | `qpack::field_section::decode_lines` | 885,720 | 8,891,693 |
  | `uni::UniStream::consume_control` | 2,722,003 | 5,524,092 |

  Task 4 shipped a stop-gap: a never-called `smt_order_anchor` fn holding one `extend_from_slice`. A sweep under Z3
  seeds 0-4 then showed the anchor only pinned one path. With it, 10 h3 fns still failed or exceeded their cap or
  ceiling under some seed: `send_response`, `write_response`, `encode_field_section`, `encode_name_line` and
  `encode_literal_line` failed (12,000,000); `decode_lines_bounded` reached 9,948,312, `RequestStream::on_data`
  8,207,462 and `request::lemma_frame_at` failed (seed 2).
- **Incidents**:
  1. 9b3 Task 4, above.
  2. 9b3 Task 4: `validate_request` gained a `requires`. That alone (bisected) moved `request::lemma_frame_at` from
     10,315,117 to 10,688,086, over its ceiling, through the shared request-module solver process.
  3. 9b3 Task 4, mutant 9b3-M2: a mutation that only changes an allocation argument also failed `build_headers`' cost
     postcondition, which it does not touch (a solver-path effect, not a real failure).
  4. Earlier instances of the same class are in `catalog.md` under C11: 4c T1 (`tls` `build_flight` 11.65M to 16.5M
     when an import added vest_lib's broadcast lemmas) and 9a pre I2 (`Reassembly::insert` 6.85M to 11.54M with no
     edit to it).
  5. 9b3 Task 8: two new proof fns (`lemma_encoder_stream_err`, `lemma_decoder_stream_err`) added beside the unchanged
     `qpack::instructions::lemma_encoder_stream_split` sent it to 10,077,156 at seed 0 (crate max before: 6,442,976 over
     5 seeds), and the unchanged-text `uni::UniStream::on_data` measured 10,498,662 in the same crate run. Fixed at the
     source, not by placement: the two split lemmas `hide(rfc_prefix_int)` (they use it only through
     `lemma_prefix_int_*`), which took them to at most 879,604 on every seed, and the new lemmas stay beside them. In
     the same task `uni::UniStream::determine` spread 1.54M-4.19M over seeds 0-4 (2.7x); its fix round moved its
     sequence reasoning into per-path lemmas behind an opaque `determined` predicate (1.58M-1.77M, 1.12x), and
     `on_data` likewise behind `fed` (2.32M-2.37M).
  6. 9b3 Task 9: the proof fns behind the constant 421/501 answers (`lemma_answer_421`/`_501` and the lemmas they call)
     measured 3.5M-4.9M in conn's shared solver process, though each only chains lemmas over hidden specs. A bisect
     pinned it to the solver's state, not the proof: the body of `lemma_answer_421` cost 1,840 alone, and 3.5M once its
     ensures restated a fact the last lemma call had just ensured. Marking every one of these lemmas
     `#[verifier::spinoff_prover]` took `lemma_answer_421` to 621,513 and `lemma_answer_501` to 896,005 (seed 0). Later
     in the task a one-unit cost edit in `conn::deliver` sent the unchanged-text `conn::H3Conn::uni_data` to 9,144,302
     (seed 1) and `conn::H3Conn::shutdown` to 8,205,126 (seed 3), both over the cap. Both are now spun off too, so their
     query no longer depends on what the shared process verified before them: over seeds 0-4, `shutdown` 4.72M-6.10M
     (3.50M-4.73M at Task 8; spinning it off does not lower it, it pins it) and `uni_data` 2.63M-3.98M. `shutdown` joins
     the Residual's list below for the next restructuring.
- **Escape**: the rlimit gate (`scripts/rlimit-gate.sh`, `tools/rl.py --gate`) and the ceilings ratchet
  (`scripts/rlimit-ceilings.sh`) measure one run under Z3's default seed. A number from one run says nothing about the
  margin: a proof can pass at 7.9M on that path and fail on the next. The ceilings file even recorded fns above the
  8,000,000 cap as accepted (h3 had four lines), which is what a one-path proof looks like from outside. No check varied
  the path.
- **Class**: C11 PROOF-BUDGET FRAGILITY (rlimit cap, Z3 perturbation across modules, import-triggered blow-up). This
  is its "Z3 perturbation" part, which the catalog left partial: a proof whose cost depends on the solver path rather
  than on the proof.
- **Catch**: `scripts/rlimit-seeds.sh CRATE [N]` (default 5) verifies the crate whole at `--rlimit 4` under
  `smt.random_seed` 0..N-1 and fails (`tools/rlseeds.py`) if any fn fails under any seed, or a fn exceeds its
  `tools/rlimit-ceilings.txt` line or 8,000,000 under any seed. It prints each fn's maximum over the seeds.
  `scripts/verify.sh` runs it for h3 after the rlimit gate. It also fails when Verus exits non-zero under any seed, and
  when every seed gives identical per-fn numbers (the seed option had no effect, so the sweep would be one run repeated).
  A seed sweep perturbs the solver path as an unrelated edit does. h3 passes 5 seeds under both declaration orders seen
  (anchor in and out). Passing a sample raises the bar; it does not prove robustness.
  - Fixing the instance (this commit): every flagged fn was restructured with no ensures, requires or exec change.
    Proof blocks moved into `proof fn lemma_*` with narrow requires (`lemma_line_out`, `lemma_name_out`,
    `lemma_literal_out`, `lemma_exact_out`, `lemma_section_step`, `lemma_section_out`, `lemma_prefix_zero`,
    `lemma_lines_*` over the new `lines_inv`/`lines_bounded_inv`, `lemma_write_wire`, `lemma_one_write`). Recursive
    and serialization specs a body only names as terms were hidden (`hide(rfc_field_line)`, `rfc_field_lines`,
    `rfc_decode_field_section`, `spec_prefix_int_bytes`, `rfc_req`, `rfc_headers`, `ctrl_preamble`, `goaway_frames`,
    `spec_frame_bytes`, `spec_varint`, `rfc_control`, ...). The profile of `send_response` showed why: 72% of its
    quantifier instantiations were vstd's `array_index` and `Seq::new` index axioms, reached through the control
    stream's serialization specs, which it never needs to unfold. To reproduce: at 4bf5976 with `smt_order_anchor`
    deleted, run `cargo verus focus -- --rlimit 4 --verify-only-module conn --verify-function H3Conn::send_response
    --profile --smt-option smt.random_seed=0` in crates/h3 (the top two quantifiers are vstd array.rs:57 and
    seq.rs:1403).
  - `smt_order_anchor` is deleted. h3 passes 5 seeds with the reorder in force, and also with the anchor added back
    (both orders checked).
  - h3's ceiling lines are all deleted: every fn is now below 8,000,000 under every seed.
  - Residual (owner 9b4): the gate runs on h3 only. Every other crate is still measured on one path; 9b4 extends
    `rlimit-seeds.sh` to every crate (and carries tls `build_flight` and the crypto/ctcore ceilings into it).
    Seeds are a sample, not a proof of robustness: 5 seeds bound the cost of the gate (about 2 minutes for h3). At
    9b3 Task 8's fix round (5 seeds): the h3 maximum is `conn::H3Conn::request_data` at 5,309,193 (text unchanged since
    9b3 Task 1); the widest spreads among fns above 2,000,000 are the untouched `conn::H3Conn::lemma_step_trans`
    (0.49M-3.10M, 6.3x) and `qpack::field_section::lemma_name_out` (0.48M-2.40M, 5.0x), then `conn::H3Conn::uni_data`
    (2.24M-4.51M, 2.0x, rewritten by 9b3 Task 11). The next restructuring of h3's proofs should start with those.
- **Evidence**:
  - Gate demos (`scripts/gate-demos.sh`): "rlimit-seeds: passes seed 0, FAIL row under seed 1", "rlimit-seeds: over
    the cap under seed 1 only", "rlimit-seeds: over its ceiling line", "rlimit-seeds: a malformed ceilings line",
    "rlimit-seeds: a seed's run not clean", "rlimit-seeds: a seed that verified nothing", "rlimit-seeds: an empty seed
    log", "rlimit-seeds: identical runs (the seed had no effect)", each after "rlimit-seeds: unchanged fixture passes";
    and "rlimit-seeds.sh: verus exits non-zero under seed 2 only" (the script with a stub `cargo`), after
    "rlimit-seeds.sh (stub cargo)".
  - The h3 sweep: before this commit (05adcf1/4bf5976 sources, anchor in place) `scripts/rlimit-seeds.sh h3 5` failed
    on the 10 fns above; after it, `rlimit-seeds: h3 5 seeds ok`, with the per-fn maxima in the table below.

  | fn | max over seeds 0-4 before, anchor in | before, no anchor | after (no anchor) |
  |---|---:|---:|---:|
  | `conn::H3Conn::send_response` | fails | fails | 2,081,801 |
  | `conn::write_response` | fails | fails | 1,302,770 |
  | `qpack::field_section::encode_field_section` | fails | fails | 494,994 |
  | `qpack::field_section::encode_name_line` | fails | fails | 268,549 |
  | `qpack::field_section::encode_literal_line` | fails | 6,939,503 | 268,743 |
  | `qpack::field_section::decode_lines` | 6,078,961 | 8,891,693 | 346,753 |
  | `qpack::field_section::decode_lines_bounded` | 9,948,312 | 4,850,081 | 413,366 |
  | `request::RequestStream::on_data` | 8,207,462 | 8,585,106 | 2,528,260 |
  | `request::lemma_frame_at` | fails | fails | 1,221,972 |
  | `uni::UniStream::consume_control` | 4,792,014 | 5,524,092 | 1,888,490 |

  ("fails": a FAIL row under at least one seed.) The heaviest h3 fn after the change is
  `qpack::huffman::lemma_unique_bits` at 6,425,562 (untouched; under the cap).
