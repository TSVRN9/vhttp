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
| Q4 | `CryptoStream::read`, crypto_stream.rs:491 | same (fn at :471, `out.append(&mut self.buf)` at :491, `self.buf = Vec::new()` at :493) | as the spec: hands over every unread byte. "std's growth of `out`": quictls passes a fresh empty `b` (Q-T1), and `append` into an empty `Vec` reserves once (one alloc, no realloc, measured below); growth happens only into a non-empty `out`, i.e. `crypto_drop`'s `sink` (Q6) |
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
sizes). Bounds checked: bytes at most 3x per doubling; total time at 4n at most 8x that at n plus 20 ms; `realloc == 0`;
a delivering call hands over at most its own input's bytes; the slowest call at 4n at most 4x that at n plus 1 ms; for
the gap fill, its time at most 8x the slowest other call plus 1 ms.

| test (Task) | n | calls | bytes | alloc | realloc | dealloc | total time | slowest call | largest call (bytes) | verdict today |
|---|---|---|---|---|---|---|---|---|---|---|
| `crypto_one_byte_frames` (6) | 16 KiB | 16384 | 3162112 | 114688 | 0 | 114688 | 3.00 ms | 7.3 µs | 193 | passes |
| | 32 KiB | 32768 | 6324224 | 229376 | 0 | 229376 | 5.37 ms | 3.8 µs | 193 | |
| | 64 KiB | 65536 | 12648448 | 458752 | 0 | 458752 | 7.95 ms | 4.4 µs | 193 | |
| `crypto_runs_then_fill` (6) | 1024 | 1025 | 1199160 | 22577 | 3 | 22577 | 0.73 ms | 90.8 µs (fill) | 43400 (fill) | FAILS: realloc |
| | 2048 | 2049 | 2627640 | 49241 | 4 | 49241 | 1.49 ms | 169.1 µs (fill) | 86464 (fill) | |
| | 4096 | 4097 | 5714536 | 106675 | 5 | 106675 | 3.13 ms | 325.2 µs (fill) | 173096 (fill) | |
| `send_ack_1k` (8) | 256 KiB | 477 | 801792 | 484 | 0 | 484 | 0.06 ms | 8.2 µs (write) | 262144 (write); ACK 131136 | passes |
| | 512 KiB | 951 | 1604608 | 959 | 0 | 959 | 0.12 ms | 18.1 µs (write) | 524288 (write); ACK 262208 | |
| | 1 MiB | 1900 | 3210240 | 1909 | 0 | 1909 | 0.31 ms | 64.2 µs | 1048576 (write); ACK 524352 | |
| `stream_reverse_fill` (10) | 16 KiB | 16384 | 98440 | 4 | 33 | 4 | 0.94 ms | 25.7 µs | 65520 | FAILS: realloc; 1 call hands over 16384 bytes for d = 1 |
| | 32 KiB | 32768 | 196744 | 4 | 36 | 4 | 1.79 ms | 43.0 µs | 131056 | 1 call: 32768 for d = 1 |
| | 64 KiB | 65536 | 393352 | 4 | 39 | 4 | 3.51 ms | 81.2 µs | 262128 | 1 call: 65536 for d = 1 |
| `reader_one_byte_push` (7) | 16 KiB | 16385 | 32760 | 1 | 11 | 0 | 0.50 ms | 4.1 µs | 16384 | FAILS: realloc |
| | 32 KiB | 32769 | 65528 | 1 | 12 | 0 | 1.00 ms | 3.8 µs | 32768 | |
| | 64 KiB | 65537 | 131064 | 1 | 13 | 0 | 1.99 ms | 8.4 µs | 65536 | |

`alloc_zeroed` was 0 in every run. Per call kind:

- `crypto_runs_then_fill`: the runs' slowest call 1.2, 3.2, 3.8 µs and largest 1297, 1409, 1521 bytes; the fill call
  (2n bytes given, 2n handed over) 90.8, 169.1, 325.2 µs, within 8x the slowest run plus 1 ms. It fails only on the
  fill's reallocs.
- `send_ack_1k`: write 8.2, 17.4, 45.2 µs; poll (1200-byte chunks) at most 1200 bytes and 0.3 µs; the slowest 1 KiB
  ACK 5.1, 9.1, 40.3 µs, requesting half the stream (Q7). Every bound holds: the ACK's copy is linear in n, which the
  "4x + 1 ms" bound on the slowest call admits, and the `split_off`s are fresh allocations (about 3n bytes in all), not
  reallocs.
- `crypto_one_byte_frames`: 193 bytes and 7 allocations per 1-byte frame (the `Frags` chunk, `buf`, `out`), flat in
  n; a read after every frame finds one byte, so Q4's and Q5's copies never exceed the frame. It passes every bound.
- `stream_reverse_fill`: the first call (1 byte at W-1) is the largest by bytes (Q1's zero fill of `buf` and `have`);
  the last (1 byte at 0) hands over all W bytes (Q3).
- `reader_one_byte_push`: the single `next_message` returns the whole message by moving the reader's `Vec` (the
  `split_off` tail is empty); the cost is the push reallocs (T1).

Two of the five tests pass on today's code at the brief's sizes: `crypto_one_byte_frames` and `send_ack_1k`. They are
kept `#[ignore]`d with that stated, to be un-ignored by Tasks 6 and 8 with the converted code. The assertion set cannot
see Q7's per-ACK copy at these sizes (it is linear per call, and per-call requested bytes are not bounded by `d`, since
a queue migration allocates `3·S` at once), nor Q8 (one write) or T2 (no tail).
