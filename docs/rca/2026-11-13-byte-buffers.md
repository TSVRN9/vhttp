# Byte buffers on input paths (C15): growth by std's strategy and eager delivery (phase 9b2)

Status: Task 1 (measurement and sweep re-read). Task 11 completes this entry (Escape, Catch and Evidence once the fix
is in).

- **Defect**: quic's and tls's input-path byte buffers (`CryptoStream`, `Reassembly`, `SendStream`, `HsReader`, the TLS
  transcript) grow by `Vec::push`/`extend_from_slice`/`append`, so a call can pay a `realloc` that copies everything
  buffered, and the receive paths deliver a whole contiguous run in the call that completes it, so one input call of
  `d` bytes can copy or hand over far more than `d` (spec `docs/superpowers/specs/2026-11-12-phase-9b2-byte-queue-design.md`,
  "The cost today"; sweep `docs/rca/2026-11-12-cost-sweep.md` §A-C).
- **Escape** (spec D16): vstd models a `Vec`'s length, not its capacity, so neither Verus nor review saw a realloc; std
  documents no growth strategy, so "amortized O(1)" was a belief; cost and delivery size were in no contract, and the
  receive specs delivered eagerly by definition, so a gap fill copying the run looked free; the `ponytail:` and
  `shortcut:` comments that admitted it (handshake.rs:186, send_stream.rs:984, conn.rs:3392) had no tracker.
- **Class**: C15.
- **Catch**: spec D15 (Task 11 records it here).
- **Evidence**: the measurement below; the gate demos and mutants of Task 11.

## Sweep rows re-read (9b2 Task 1, merged tip 0d7c37c)

Each 9b2 row of the sweep, read line by line at 0d7c37c (main a293f81 with 9b1 merged in). None of these files changed
between d0f4392 (the spec's line numbers) and 0d7c37c except `frags.rs` (9b1's AVL), so every site is where the spec's
table puts it; the cost column says where the re-read and the measurement refine the spec's text.

| row | site (spec, d0f4392) | site at 0d7c37c | cost, re-read |
|---|---|---|---|
| Q4 | `CryptoStream::read`, crypto_stream.rs:491 | same (fn at :471, `out.append(&mut self.buf)` at :491, `self.buf = Vec::new()` at :493) | as the spec: hands over every unread byte. "std's growth of `out`": quictls passes a fresh empty `b` (Q-T1), and `append` into an empty `Vec` reserves once (one alloc, no realloc); growth happens only into a non-empty `out`, i.e. `crypto_drop`'s `sink` (Q6) |
| Q5 | `CryptoStream::on_fill`, crypto_stream.rs:457 | same (`on_fill` at :443, `self.ooo.take_front(self.contig, &mut self.buf)` at :457); `Frags::take_front` is now 9b1's at frags.rs:4164 (`take_front_w`) | as the spec: the newly contiguous run is pushed into `buf`, whose reallocs copy the unread bytes (3-5 reallocs per fill, measured below). Bounded by `MAX_CRYPTO_BUFFER` held bytes plus the frame |
| Q6 | `Connection::crypto_drop`, conn.rs:3392-3396 | same (`shortcut:` at :3392, `sink` at :3393, three `read`s :3394-3396) | as the spec |
| Q-T1 | quictls `feed`, quictls/src/server.rs:1084-1090 | same (`let mut b: Vec<u8> = Vec::new()` at :1084, `crypto_read` at :1090) | `b` is fresh and empty, so each feed is one exact allocation of every unread byte, not std's doubling; the cost is the byte count (Q4/Q5's), not growth |
| T1 | `HsReader::push`, handshake.rs:137 | same (`self.buf.push(data[i])` at :137) | as the spec: 11, 12, 13 reallocs for a 16, 32, 64 KiB message pushed a byte at a time (below) |
| T2 | `HsReader::next_message`, handshake.rs:186-188 | same (`ponytail:` at :186, `split_off(4 + len)` at :187, swap at :188) | as the spec; not exercised by `reader_one_byte_push` (with one-byte pushes no tail follows a message, so `split_off` copies nothing) |
| T3 | ServerHs HRR transcript, server.rs:1330-1331 | same (`message_hash` at :1330, `extend_from_slice(hrr)` at :1331); `message_hash` at schedule.rs:92 (`Vec::new` :100, four `push` :101-104, `extend_from_slice` :105) | as the spec |
| T4 | ServerHs CH transcript, server.rs:1357-1359 | same (`extend_from_slice(m)` at :1359) | as the spec |
| T5 | `build_flight`'s `append`, flight.rs:387-393 | same (`fn append` at :388, `extend_from_slice` at :392; calls on `t` at :535, :555, :577, :607, :617 and on `data` at :556, :578, :608, :618) | as the spec ("five `extend_from_slice`" on `t`; `data` gets four more) |
| T6 | `build_flight` th1..th4, flight.rs:540-613 | `sha256(t.as_slice())` at :540, :583, :613 and :622 (th4 lies past the spec's range) | as the spec; unchanged in 9b2 (D14) |
| Q1 | `Reassembly::insert`, reassembly.rs:548-565 | same (`insert` at :515, the zero-fill `while` at :548, `buf.push(0)`/`have.push(false)` at :563-564) | as the spec: the 1-byte frame at offset W-1 requested 65520, 131056, 262128 bytes for W = 16, 32, 64 KiB (both `Vec`s doubling) |
| Q2 | `Reassembly::pop`, reassembly.rs:688-691 | same (`split_off(self.head)` at :688 and :690, inside `head >= len - head` at :680; `Vec::new()` when all is read, :683-684) | as the spec; not exercised by `stream_reverse_fill`, which reads everything in one pop (the `Vec::new()` branch) |
| Q3 | `Reassembly::run_end`, reassembly.rs:620 | same (`out.push(self.buf[n])` at :620) | as the spec: the last frame (offset 0) delivers all W bytes, pushed into a fresh `Vec` by doubling |
| Q7 | `SendStream::on_data_acked`, send_stream.rs:1023 | same (`ponytail:` at :984, `split_off((nb - ab))` at :1023) | as the spec: the largest 1 KiB ACK requested 131136, 262208, 524352 bytes (half the stream plus 64) for 256 KiB, 512 KiB, 1 MiB; each `split_off` is a fresh allocation, not a realloc |
| Q8 | `SendStream::write`, send_stream.rs:519 | same (`extend_from_slice(data)` at :519) | as the spec, but only from the second write on: a first write into the empty `buf` is one exact allocation (`send_ack_1k` writes once, so it does not exercise Q8) |

## Measured (9b2 Task 1, release, code at 0d7c37c, tests as committed with this file)

`crates/quic/tests/input_cost.rs` and `crates/tls/tests/reader_cost.rs` (all `#[ignore]`d; run with
`cargo test --release -p quic --test input_cost -- --ignored --test-threads=1 --nocapture` and
`cargo test --release -p tls --test reader_cost -- --ignored --nocapture`). A per-thread counting allocator; each input
call measured on its own; time is the fastest of 3 runs. "bytes" is requested bytes (alloc sizes plus realloc new
sizes). Bounds checked:

- per call (the allocator is deterministic): no `realloc`; requested bytes at most `8·d + 4096`, `d` the bytes the call
  was given (`A = 8` from the spec's `7d + 4` push and `n + 3` take, `B = 4096` for the constant terms: a 56-byte node
  per chunk, at most 258 eight-byte ring slots and two 256-byte page arrays), except that, in the tests whose structure
  is a `ByteQueue` after 9b2 (`send_ack_1k`, `reader_one_byte_push`; not the CRYPTO and STREAM tests, whose stores are
  `Frags` and the ring), one allocation of a call may exceed that budget if it can be a queue buffer: requested
  capacity is memory, not work (an uninitialized `with_capacity` is one allocator call, and D4 bounds the copies into
  it at 3 per byte pushed), so the call must have been given bytes (D4 allocates only in `push_slice` with `d > 0`; an
  ACK or a read creates no buffer), the allocation must be at most `3·(bytes held after the call) + MIN_CAP` (D4's
  memory bound, `MIN_CAP` = 64), the rest of the call stays within the budget, and a run excuses at most
  `2·log2(peak held / 64) + 4` calls so (controller rulings, 2026-11-13). The allocator sees no copy into such a buffer:
  the work bound on it rests on D15's proved cost (`push_slice` at most `7d + 4`), not on these tests. A delivering call
  hands over at most `d` bytes. An ACK
  call is given no stream bytes (`d = 0`); `next_message` is given none and is held to `8·message + 4096` (one copy of
  the completed unit, D14);
- across sizes: bytes at most 3x per doubling; total time at 4n at most 8x that at n plus 20 ms; the slowest call at 4n
  at most 4x that at n plus 1 ms; the gap fill at most 8x the slowest other call plus 1 ms.

`crypto_one_byte_frames` sends the stream one byte per frame in runs of 8192: bytes `b+1..b+8192` in order (held out
of order), then `b`, whose frame closes the gap and makes the run deliverable (the shape of 9b1's `crypto_cost`
patterns; a read after every in-order frame never finds more than one byte).

| test (Task) | n | calls | bytes | alloc | realloc | total time | slowest call | largest call: bytes for d |
|---|---|---|---|---|---|---|---|---|
| `crypto_one_byte_frames` (6) | 16 KiB | 16384 | 14974208 | 231634 | 14 | 16.9 ms | 10.1 µs | 37752 for 1 (close) |
| | 32 KiB | 32768 | 29948416 | 463268 | 28 | 33.7 ms | 8.8 µs | 37752 for 1 |
| | 64 KiB | 65536 | 59896832 | 926536 | 56 | 67.6 ms | 18.9 µs | 37752 for 1 |
| `crypto_runs_then_fill` (6) | 1024 | 1025 | 1199160 | 22577 | 3 | 0.60 ms | 77.3 µs (fill) | 43400 for 2048 (fill) |
| | 2048 | 2049 | 2627640 | 49241 | 4 | 1.20 ms | 137.6 µs (fill) | 86464 for 4096 |
| | 4096 | 4097 | 5714536 | 106675 | 5 | 2.55 ms | 276.3 µs (fill) | 173096 for 8192 |
| `send_ack_1k` (8) | 256 KiB | 477 | 801792 | 484 | 0 | 0.05 ms | 7.3 µs (write) | ACK: 131136 for 0 |
| | 512 KiB | 951 | 1604608 | 959 | 0 | 0.10 ms | 14.7 µs (write) | ACK: 262208 for 0 |
| | 1 MiB | 1900 | 3210240 | 1909 | 0 | 0.19 ms | 31.3 µs (write) | ACK: 524352 for 0 |
| `stream_reverse_fill` (10) | 16 KiB | 16384 | 98440 | 4 | 33 | 0.60 ms | 28.0 µs | 65520 for 1 (first frame) |
| | 32 KiB | 32768 | 196744 | 4 | 36 | 1.14 ms | 54.1 µs | 131056 for 1 |
| | 64 KiB | 65536 | 393352 | 4 | 39 | 2.31 ms | 115.3 µs | 262128 for 1 |
| `reader_one_byte_push` (7) | 16 KiB | 16385 | 32760 | 1 | 11 | 0.63 ms | 4.1 µs | 16384 for 1 |
| | 32 KiB | 32769 | 65528 | 1 | 12 | 1.24 ms | 4.1 µs | 32768 for 1 |
| | 64 KiB | 65537 | 131064 | 1 | 13 | 2.39 ms | 6.4 µs | 65536 for 1 |

`alloc_zeroed` was 0 in every run; deallocs equal allocs except in `reader_one_byte_push` (the message `Vec` is
returned). Every test fails today; the assertions that fail (at n, 2n, 4n):

| test | per-call realloc | per-call bytes over budget (queue tests: beyond one queue buffer) | hands over > d | across sizes |
|---|---|---|---|---|
| `crypto_one_byte_frames` | 2, 4, 8 calls (each closing frame, 7 reallocs) | 2, 4, 8 calls (37752 bytes for d = 1, largest single 8256, 0 held after) | 2, 4, 8 calls (8192 bytes for d = 1) | hold |
| `crypto_runs_then_fill` | the fill (3, 4, 5 reallocs) | the fill (43400, 86464, 173096 for d = 2048, 4096, 8192; 0 held after) | hold (2n for d = 2n) | hold |
| `send_ack_1k` | hold | 6, 7, 8 ACKs (the largest 131136, 262208, 524352 for d = 0: `split_off` copies half the stream, Q7; a call given no bytes gets no queue-buffer allowance) | n/a | hold |
| `stream_reverse_fill` | 2 calls (the worst the first frame: 22, 24, 26 reallocs) | 2 calls (the worst the first frame: 65520, 131056, 262128 for d = 1, of which the largest single 16384, 32768, 65536) | the last frame (W bytes for d = 1, Q3) | hold |
| `reader_one_byte_push` | 11, 12, 13 pushes (1 each, T1) | hold (each realloc is at most twice the bytes held, inside the queue-buffer allowance; the realloc itself fails) | n/a | hold |

Per call kind: `crypto_one_byte_frames`' 1-byte frames that do not close a gap request at most 1281 bytes;
`crypto_runs_then_fill`'s runs at most 1521; `send_ack_1k`'s write requests exactly n and each 1200-byte poll at most
1200; `reader_one_byte_push`'s single `next_message` moves the reader's `Vec` (the `split_off` tail is empty), so its
cost is the push reallocs (T1). The patterns do not exercise Q2 (one pop takes everything), Q8 (one write) or T2 (no
tail).

## mem-9b2-send-cap: send room counted lengths, the allocator held capacity (9b2 Task 8)

- **Defect**: once `SendStream`'s buffer became a `ByteQueue` (Task 8, 60d5cc3), `Streams::send_room` and the
  `MAX_SEND_BUFFER` sum in `Streams::wf` still counted buffered lengths, while a queue keeps both of its buffers until it
  is empty (D4: `drop_front` frees nothing; capacity up to `2·max(MIN_CAP, 3·peak)`). Measured: 64 KiB written, every
  1 KiB piece but the last acknowledged, 310,272 bytes held for 1,024 buffered; a peer withholding one ACK per stream
  freed room while each part kept about 6x its peak, so a connection's memory was bounded by its live parts, not by
  1 MiB.
- **Escape**: the old buffer (`split_off` on ACK) dropped its acknowledged prefix's memory, so "length bounds memory"
  held by construction and was never a proof obligation; Task 8 changed the representation and the sum kept its
  meaning on paper only. vstd models lengths, not capacity (spec D16), so nothing flagged it; the queue's own
  `requested()` bound was per queue, never summed.
- **Fix** (owner decisions 2026-11-16 and 2026-11-17): each sending part holds a reservation, `max(128, 6·peak)` while
  its queue is non-empty and 0 once it empties (`SendStream::held_spec`, an exec `peak` with `peak == buf.peak()` in
  `wf`). `Streams::wf` sums the reservations against `MAX_SEND_BUFFER`, `send_room(id)` is `B/6 − len` of the part's
  share `B`, and `SendStream::lemma_held` proves the queue's `requested()` (both buffers while migrating) within the
  reservation.
- **Catch**: `Streams::lemma_wf` exports `tx_capacity() <= tx_held() <= MAX_SEND_BUFFER`, where `tx_capacity` sums
  `requested()` itself; a path that lets a queue's capacity outgrow its share fails verification at every `Streams`
  mutator that ensures `wf`. Against the allocator's own sizes (`SendStream::buf_capacity`, the queue's `caps`):
  `held_capacity_within_cap` (40 streams × 64 KiB, every piece but the last acknowledged: Σ capacity at most 1 MiB
  after every call) and `room_refills_as_acks_arrive` in `crates/quic/tests/stream_bounds.rs`.
- **Evidence**: Task 8's report (fix rounds 0 and 1); carryovers `mem-9b2-send-cap`, `mem-9b2-send-room`.

## SendStream range lists: unbounded, quadratic, reachable by any client after the handshake (9b2 Task 8a, D10)

- **Defect** (class C15, a bug): `SendStream`'s `acked` and `lost` were `Vec<(u64, u64)>` lists whose lengths no `wf`
  clause bounded, and `range_insert`/`range_remove` rebuilt the whole `Vec` per call. Measured by the plan's ruling-11
  experiment (2026-11-13, ledger `progress.md`): under a peer that acknowledges odd pieces and loses even ones each list
  reached about B/(2m) ranges (B bytes buffered, m the piece size): 2048 at 4 KiB in 1-byte pieces, 437 at 1 MiB in
  1200-byte pieces, 7283 in the plan's selective-ACK scenario against the 66 it planned; a run of ACKs cost quadratic
  time, and memory reached about 16 MiB per connection at 1-byte pieces. streams.rs:26-28 documented "about 2·64 per
  send stream", pinned at 129 by `range_gate_pto_cycles` and `alternate_ack_range_growth`: never true.
- **Why it could occur**: `MAX_SEND_RANGES` gated only `poll_data`'s new data, at call time, while ACK arrivals and
  `retransmit`'s split of `lost[0]` were ungated; no `wf` clause bounded the lists, and send_stream.rs:184's `ponytail:`
  said so ("per-stream hole bound is tested (D4), not proven"); `range_insert` and `range_remove` proved only `in_bounds`
  ("Order and merging are exec behavior (tested)", and :92's `ponytail:` deferred an interval tree); the two tests ran
  only the credit-drip adversary, and `range_gate_pto_cycles`'s doc named the retransmit-split adversary "Not exercised"
  with no tracker. A collection bound held by a gate, a test and a comment, not by a proof.
- **Fix** (owner 2026-11-13, D10): `quic::ranges` on 9b1's AVL, `RangeSet` (merged) for `acked` and `lost` and
  `PieceSet` (exact pieces) for `flight`, each op O(log n) with its cost in its ensures. `SendStream::wf` holds the
  partition (every byte of `[acked_base, sent_end)` acknowledged, lost or in exactly one piece in flight; no acked range
  starts at `acked_base`), the item rule (each item at least `FLOOR` = 256 bytes long or holding a whole open slot, at
  most `MAX_FLUSH` = 4 short new pieces open) and the bound `acked + lost + flight <= (sent_end − acked_base)/256 +
  slots` (`ranges::lemma_bound`, from piece edges: ACKs and losses move whole pieces, a cut leaves both parts at least
  FLOOR). Tiny writes coalesce to flush points (`flush`; `Connection::stream_write` and `crypto_write` flush). Per stream
  at most `⌊W/256⌋ + 4` nodes of 40 bytes (`node_size`); ACK, loss and poll at most `400·(h + 1) + 40` cost units
  (`on_data_acked_w`, `on_data_lost_w`, `poll_data_w`). conn's `on_acked_record` no longer coalesces STREAM frames
  (`stream_run` and its `ponytail:` go): each frame is one piece.
- **Catch**: the bound and the partition in `SendStream::wf`, proved at every mutator; the cost ensures under
  `scripts/cost-charge.sh` (send_stream.rs and ranges.rs in its `FILES`, the six wrappers in `WRAPPERS`); mutants
  9b2-M16 (retransmit without the floor), 9b2-M17 (a short piece with no slot), 9b2-M18 (an ACK leaving its piece in
  flight) and 9b2-M19 (slots closed `FLOOR` past `acked_base`), each killed by Verus under `scripts/mutants.sh run`;
  the selective-ACK tests (`send_ranges_bounded_under_selective_acks`, `input_cost::send_selective_acks`: after every
  call the three sets within
  `buffered()/256 + 4`, each ACK or loss at most `8·(h + 1)` node allocations and one live node more, no realloc) and
  `partition_never_forgets`; `range_gate_pto_cycles` and `alternate_ack_range_growth` now check the proved bound. No
  mutant drops a tree without `free`: an implicit `Drop` is invisible to Verus and to the gate (D15); review checks it.
- **Class sweep** (a collection bound held by test or comment, not proof): `grep -rniE "not proven|tested,? not prov"
  crates/*/src` at this commit finds two hits, neither a collection bound: crates/h3/src/conn.rs:9 and
  crates/quic/src/streams.rs:9, each the heading of its module's caller-obligation list (event order, abort signals,
  output routing), stated for the caller to keep (owner: the caller, the server's pipeline; checked by its own proofs
  and the interop tests). streams.rs:26-28's "tested not proven" range claim is gone, replaced by the proved bound.
- **Evidence**: tests `ranges::ranges_model`, `send_stream::partition_never_forgets`,
  `send_stream::send_ranges_bounded_under_selective_acks`, `send_stream::range_gate_closes`,
  `input_cost::send_selective_acks`; mutants 9b2-M16..M19, `scripts/mutants.sh run 9b2-M16 9b2-M17 9b2-M18 9b2-M19` at
  e0037c5: "mutants: run ok (4 mutants killed)" (M16 at `SendStream::retransmit`, resend_piece's item rule; M17 at
  `push_piece`; M18 at `ack_piece`; M19 at `drop_prefix`); spec D10, D15, D16.
