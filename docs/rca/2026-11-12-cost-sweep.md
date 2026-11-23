# Cost sweep (2026-11-12): amortized growth and front drains on network-input paths

Raw output of a grep-driven read-only sweep (an agent, not line-by-line), input to phase 9b2's scope. Not yet verified row by row.

# 9b2 sweep: non-worst-case copy/shift sites on network-input paths
Base: /home/tavern/Projects/rust/web-server (main). Paths below are relative to crates/. PRE = reachable before handshake completes.
Not exhaustively verified line-by-line: ghost `Seq::push/remove/insert` in verus proofs are excluded. Class B (small Vec::new+push builders) is listed by file, not per line.

## A. quic
| # | file:line | container / op | driver | PRE | worst extra per call | bound |
|---|-----------|----------------|--------|-----|----------------------|-------|
| Q1 | quic/src/reassembly.rs:561-565 (`insert`) | Reassembly.buf and .have: `push(0)`/`push(false)` byte-by-byte up to `end` of the frame | STREAM frame offset (gap fill): a 1-byte frame at offset W-1 pushes ~W bytes into each Vec, plus realloc moves | no (1-RTT) | whole receive window: 16 KiB per stream x2 Vecs | window = initial_max_stream_data (server/src/lib.rs:105 = 16384), conn 65536 (lib.rs:104); `wf`: base+buf.len-head <= VARINT_MAX only; real bound is flow credit |
| Q2 | quic/src/reassembly.rs:688-691 (`pop`) | `buf.split_off(head)`, `have.split_off(head)` when head >= len-head | in-order delivery on STREAM frame | no | whole unread tail (<= half of buf, <= ~16 KiB) | same window; doc says amortized O(1) |
| Q3 | quic/src/reassembly.rs:620 (`run_end`) | `out.push(buf[n])` per byte into fresh Vec | delivery | no | O(delivered) plus Vec growth reallocs | window |
| Q4 | quic/src/crypto_stream.rs:491 (`read`) | `out.append(&mut self.buf)` | every datagram via quictls feed (quictls/src/server.rs:1084-1090) | YES (Initial/Handshake CRYPTO) | copies whole buf; `out` is fresh/empty each call so cost = bytes read | buf holds contiguous bytes since last read; drained every datagram (crypto_drained) |
| Q5 | quic/src/frags.rs `take_front` (frags.rs:1373 at 58e6d14; an AVL of chunks since 9b1) via crypto_stream.rs:455 (`on_fill`) | appends the whole contiguous ooo run to `self.buf` | CRYPTO frame closing a gap | YES | up to all held out-of-order bytes (not "bytes given") | MAX_CRYPTO_BUFFER = 16384 (crypto_stream.rs:21), MAX_CRYPTO_RANGES = 4096. frags.rs being rewritten in 9b1; skipped otherwise |
| Q6 | quic/src/conn.rs:3392-3396 | `shortcut:` copy-and-drop of all three CRYPTO streams into `sink` on discard/close | key discard / close | YES | all unread CRYPTO bytes (<= 16 KiB + one datagram) | as Q4/Q5 |
| Q7 | quic/src/send_stream.rs:1023 | `buf.split_off(nb-ab)` trimming acked prefix (ponytail at :984) | incoming ACK frame | no (1-RTT) | tail copy up to ~half the stream's unacked data: up to ~512 KiB from one ACK | Σ send buffers <= MAX_SEND_BUFFER = 1<<20 (streams.rs:72); ranges <= MAX_SEND_RANGES = 64 (send_stream.rs:187) |
| Q8 | quic/src/send_stream.rs:519 | `buf.extend_from_slice(data)` past capacity | app response writes (not wire-driven, but reached from request) | no | realloc moves whole send buffer (<= 1 MiB) | MAX_SEND_BUFFER |
| Q9 | quic/src/h3_server.rs:526,537 | `pending.remove(0)` (ponytail :650) | stream_write drain | no | shift of queue (<= ~100 Pending structs) | at most one per open bidi stream (MAX_LOCAL_STREAMS = 100) plus control writes; no `wf` length bound |
| Q10 | quic/src/h3_server.rs:242-262 (`kept`/`purge`) | rebuilds whole `pending` into new Vec (`r.push`) | Reset / write error / ResetStream output | no | whole queue rebuild O(queue) | same as Q9 |
| Q11 | quic/src/h3_server.rs:705 | `pending.push(Pending{data..})` | h3 StreamWrite output | no | amortized growth | same |
| Q12 | quic/src/h3_server.rs:765-777,918 | `app.push(AppEvent)` | request head/body/end events | no | growth only; event holds moved Vec | per call |
| Q13 | quic/src/cid.rs:1198-1210 | loop `retire_pending.push(s)` for s in largest_rpt..rpt; `active.split_off(k)` | NEW_CONNECTION_ID retire_prior_to | no (post-HS frame) | loop length = rpt-largest_rpt, bounded by requires clause | `retire_pending+retire_unacked+delta <= 2*PEER_CID_CAP` (PEER_CID_CAP = 8, cid.rs:55) |
| Q14 | quic/src/cid.rs:1294 `active.insert(pos,x)`, :624,783,1372-1398,2218 `remove`/`insert(0..)`, :474,1841 `pending/retire_pending.remove(0)`, :1904,1968 `retire_unacked.remove(i)` | peer CID table | NEW_CONNECTION_ID / RETIRE_CONNECTION_ID / ACK | no | shift <= 8-16 entries | PEER_CID_CAP = 8; ISSUE_CAP_ACTIVE = 4, ISSUE_CAP_LIFETIME = 16 |
| Q15 | quic/src/ack_track.rs:928,945 | `v.remove(i)`, `v.insert(i,..)` ack ranges (ponytail :14,:438) | every received packet number | YES (all spaces) | shift <= 32 ranges | "ranges <= 32" (ack_track.rs:14) |
| Q16 | quic/src/sent.rs:293 `inflight.push`, :417 `remove(i)`, :473 `out.append`, :623-627 rebuild `out`/`kept`, :301 ponytail O(inflight x 65) | in-flight packet list | incoming ACK; timeouts | YES (Initial/Handshake ACKs) | O(inflight) rebuild per ACK | cwnd cap 64 packets (recovery.rs:12 placeholder); no `wf` constant cited |
| Q17 | quic/src/path.rs:877,931 | `responses.push`, `responses.remove(0)` (ponytail :930) | PATH_CHALLENGE | no | shift <= 3 | MAX_RESPONSES = 4 (path.rs:27) |
| Q18 | quic/src/path.rs:614,680 | `paths.push` | new path / migration | no | tiny | MAX_PATHS = 4 (path.rs:19) |
| Q19 | quic/src/route.rs:994,998 `conns.push`/`cids.push`; :1019 `cids.remove(i)`; :1052 `tokens.remove(i)`; :181; :808,910 rebuild `r.push` (drop_conn) | global CID / token / conn tables | Initial (accept) and every CidUpdate; peer-triggered | YES (every unauthenticated Initial adds entries) | shift <= 512 CID entries (each holds a Vec<u8>) / 816 tokens; drop_conn rebuilds whole table | MAX_TABLE = 512, PER_CONN = 5, MAX_CONNS = 102, MAX_TOKENS = 816 (route.rs:16-30) |
| Q20 | quic/src/streams.rs:1156,3502 `entries.push`; :1474 `entries.remove(i)` (ponytail :57) | open streams | STREAM / RESET / FIN completion | no | shift <= ~100 Entry structs (each embeds Reassembly etc.) | MAX_LOCAL_STREAMS = 100 and advertised windows |
| Q21 | quic/src/streams.rs:1390,2873,3062 ; recv_stream.rs:1708,1818 | `ev.push`/`out.push(f)` event & frame builders | STREAM data / STOP_SENDING | no | growth | per call |
| Q22 | quic/src/payload.rs:544 | `out.push(f)` per parsed frame (ponytail :477) | any received packet | YES | growth up to #frames <= payload bytes | datagram size |
| Q23 | quic/src/frame.rs:1161 | `slice_to_vec` for CRYPTO/STREAM data | received frame | YES (CRYPTO) | O(frame) = bytes given | fine |
| Q24 | quic/src/conn.rs:8965-8967 (`stream_run`) | `run.extend_from_slice` merging contiguous STREAM frames | received packet | no | O(packet) with growth | datagram size |
| Q25 | quic/src/protect.rs:1572 `packets.push(q)`; datagram.rs:661-663 remove/insert(i) on packets; conn.rs:5846 | coalesced packets in one datagram | received datagram | YES | tiny | <= datagram size |
| Q26 | quic/src/conn.rs:3851,3890 | `out.append(&mut taken)` events / cid_updates | poll | n/a | O(taken) | per call |
| Q27 | quic/src/conn.rs:668-669,1727,3236,3683 `cid_updates.push` | CidUpdate Vec | accept / retire | YES | growth | per call |
Class B (outbound builders, Vec::new + push, growth only, bounded by MTU/datagram): conn.rs:4213,4286,6176,6286,6621,6631,6853,9873,9949; header.rs:743,803-810,918; stateless.rs:92-104; protect.rs:271,349-350; pn.rs:617; frame.rs:1664; lifecycle.rs:265-275.

## B. tls
| # | file:line | container / op | driver | PRE | worst extra per call | bound |
|---|-----------|----------------|--------|-----|----------------------|-------|
| T1 | tls/src/handshake.rs:137 (`HsReader::push`) | `buf.push(data[i])` per byte (via server.rs:1456-1457 `initial.push`/`handshake.push`) | CRYPTO bytes fed from quictls | YES | amortized growth: realloc copies whole buffer | reader < 4 + MAX_HS_BODY (server.rs:384), MAX_HS_BODY = 1<<16 (codes.rs:96, handshake.rs:180) |
| T2 | tls/src/handshake.rs:187 (`next_message`, ponytail :186) | `buf.split_off(4+len)` then swap: copies the tail after the first message | completed message | YES | whole unread tail (< 64 KiB) | as T1 |
| T3 | tls/src/server.rs:1331 | `t.extend_from_slice(hrr)` on transcript (after message_hash) | CH1 -> HRR | YES | growth of 36-byte Vec; HrrSent transcript <= 0x1000 (server.rs:390) | 0x1000 |
| T4 | tls/src/server.rs:1359 | `t0.extend_from_slice(m)` | CH2 / CH1 proceed | YES | appends whole CH (<= 64 KiB+4) to a possibly 4 KiB transcript: realloc copies it | transcript <= 0x2_0000 (server.rs:1163,1400) |
| T5 | tls/src/flight.rs:392 `append` (calls :535,:555,:577,:607,:617) | `t.extend_from_slice` per flight message; also `data` | CH completion | YES | transcript grows by SH+EE+Cert+CV+Fin; each push may realloc whole transcript; Cert size = config chain, up to 0xff_ffff by cert_chain_ok (server_msgs.rs:117) | config-bounded, not wire |
| T6 | tls/src/flight.rs:540,583,613 (+th4) | `sha256(t.as_slice())` over whole transcript four times | CH completion | YES | 4 x O(transcript) hash (no copy) | as T4/T5 |
| T7 | tls/src/server.rs:1135,1146 (`push_event`, `append_events` -> `acc.append(evs)`) | event acc Vec; evs moved | each on_crypto | YES | O(events), events carry data Vecs by move | few events per call |
| T8 | tls/src/flight.rs:632-641 | `evs.push` x5 | flight | YES | small | 5 |
| T9 | tls/src/ch_ext.rs:336 (key shares), :392 (generic list), ext.rs:192 (extensions), pl.rs:291 (u16 list), plus `slice_to_vec` copies at ch_ext.rs:334,389,451,482; client_hello.rs:541-543,685; ext.rs:190 | parsed-ClientHello Vecs built by push | CH completion | YES | amortized growth; total copies = CH size (<= 64 KiB), all in the one completing call (deferred O(message)) | MAX_HS_BODY |
| T10 | tls/src/ext.rs:245-262 (ponytail) | 1024 x `seen.push(0)` zeroed bitmap (8 KiB) per ClientHello, twice with HRR | CH completion | YES | 8 KiB fixed regardless of input | constant |
| T11 | tls/src/server_msgs.rs:203,225,277; pl.rs:302-333 (`put_vec` byte loop); sign.rs:58-64; hkdf_label.rs:50; schedule.rs:101-105 | outbound serialisers with Vec::new + push | server flight | YES | growth only | config/constant |

## C. quictls
| # | file:line | op | PRE | note |
|---|-----------|----|-----|------|
| Q-T1 | quictls/src/server.rs:1084,1090 | `let mut b = Vec::new(); crypto_read(.., &mut b)` per feed | YES | fresh Vec each feed: O(bytes read) + growth; bytes read = all newly contiguous CRYPTO (see Q4/Q5) |
| Q-T2 | quictls/src/server.rs:1119,1129 | `ev` Vec passed to on_crypto; `apply(ev)` iterates | YES | events moved, no shift |
| Q-T3 | quictls/src/server.rs:522,526,1118,1386,1393 | `self.log@.push` | ghost only (Ghost log) | not exec |
No exec drain/insert(0)/rotate/remove(0) in quictls.

## D. h3
| # | file:line | container / op | driver | PRE | worst extra per call | bound |
|---|-----------|----------------|--------|-----|----------------------|-------|
| H1 | h3/src/message.rs:1398-1403 (`build_headers`, ponytail :1372) | cookie merge: `slice_to_vec(out[k].value)` + extend x2, per extra cookie line | HEADERS decode | no | copies the whole accumulated cookie per line: quadratic. 64 KiB section with ~2000 lines gives tens of MB copied in one call | MAX_FIELD_SECTION_SIZE = 65536 (limits.rs:24), 32 B/line overhead; comment says <= 2048 lines |
| H2 | h3/src/message.rs:1412-1429 | `find_first(out, "cookie")` scan + `out.push(copy_line(f))` | HEADERS decode | no | O(#lines) rescans, quadratic in lines; copies every field again (`copy_line`) | same |
| H3 | h3/src/request.rs:1649,1680 | `self.buf = slice_to_vec(s[n..])` after `run` | request stream data | no | copies the unconsumed remainder; first branch is <= bytes given, second branch (buf non-empty) copies up to the buffered partial frame | REQ_BUF_CAP = 65552 (request.rs:362) |
| H4 | h3/src/request.rs:1721-1735 (`top_up`) | `slice_to_vec(piece)` + `buf.append` | request stream data | no | O(piece) <= given; but then `run(self.buf)` re-parses the whole buffered partial frame on every call (1-byte chunks re-parse header/payload prefix) | REQ_BUF_CAP |
| H5 | h3/src/request.rs:866,874,1035,1060,1574 | `events.push(ReqEvent::..)` with `slice_to_vec` body chunks | request stream | no | O(chunk) | per call |
| H6 | h3/src/uni.rs:1231 | `buf.append` first 8 bytes (stream type) | uni stream | no | <= 8 | 8 |
| H7 | h3/src/uni.rs:1683-1684 (`top_up`), :1715-1716 (`consume_qpack`, appends the whole `seg`), :1742 and :1522 (`buf = slice_to_vec(buf[n..])`), :554 (`skip_vec`), :1640 | peer control / QPACK stream buffer: append then front-trim by copying the remainder | control + QPACK streams | no | copy of whole buffered remainder per call; consume_qpack appends the full segment even when n is large | UNI_BUF_CAP = 1040 (uni.rs:383), MAX_SETTINGS_FRAME = 1024 (limits.rs:9). QPACK `seg` itself bounded by the 16 KiB window per call |
| H8 | h3/src/frame.rs:550 `pairs.push`; ponytail :243 O(n^2) duplicate scan; :474,485 `slice_to_vec(payload)` | SETTINGS parse | peer control stream | no | O(frame) | MAX_SETTINGS_FRAME = 1024 -> 512 pairs |
| H9 | h3/src/qpack/field_section.rs:582,618,636,795,818 (`slice_to_vec` per name/value), :741,911 `out.push(f)`, huffman.rs:724 `out.push(c)` per decoded byte | QPACK decode | HEADERS | no | growth; O(section) in completing call | MAX_FIELD_SECTION_SIZE |
| H10 | h3/src/conn.rs:2951-3003, 3327-3335 `reqs.remove(i)` then `reqs.insert(i,e)` (update-in-place done as remove+insert); :3163,3200,3431 same for `unis`; :3452 `reqs.remove(i)`; :3073,3128,3210 `push` | per-request-stream entries (ReqEntry moves, embeds request parser state) | every stream event / fin | no | shift of all later entries twice per event; plus `find_req` linear scan | no h3-level length bound; only transitively QUIC stream cap 100 (streams.rs:68) |
| H11 | h3/src/conn.rs:682 (`r.push` reverse loop), :697-707, :728, :730, :823, :875, :1344, :1362, :1817-1916, :2624-2696, :2815 | outbound response building (status_line, `copy fields`), `out.push(w)` | outputs | no | growth; response field copy | response is server-defined |
| H12 | h3/src/qpack/field_section.rs:1004-1005 `slice_to_vec(s); out.append(&mut tmp)`; int.rs:505-537 | encode | outbound | no | copy | server-defined |

## E. server
| # | file:line | container / op | driver | PRE | worst extra | bound |
|---|-----------|----------------|--------|-----|-------------|-------|
| S1 | server/src/lib.rs:192 | `owed.remove(0)` | each answered request | no | shift of owed list | no cap; roughly bounded by stream limit 100 (lib.rs:107) but entries persist while Busy |
| S2 | server/src/lib.rs:177 | `owed.push(stream_id)` | Request event | no | growth | as S1 |
| S3 | server/src/lib.rs:329 | `self.conns.remove(i)` | connection close | n/a | shifts up to 101 `Conn` structs, each embeds a whole `QuicServer` (large inline struct): memmove of many KB | MAX_CONNS = 102 (route.rs); linear scans noted in ponytail lib.rs:200 |
| S4 | server/src/lib.rs:267 | `self.conns.push(c)` | every accepted unauthenticated Initial | YES | amortized growth reallocs all Conns | MAX_CONNS = 102 (has_room) |
| S5 | server/src/lib.rs:250,257 | `addrs.push`, `addrs.truncate(p)` | datagram from new source | maybe | tiny | MAX_PATHS = 4 |
| S6 | server/src/lib.rs:234,319,337 | `send.push((self.out.clone(), addr))`, `send.drain(..)` | outputs | YES | clone of each datagram (<= MAX_UDP_PAYLOAD); `Outbox` unbounded within a call, bounded by MAX_POLLS | MAX_POLLS per service |
| S7 | server/src/lib.rs:175 | `app.drain(..)` full drain (not front-partial) | after receive | n/a | O(events) | fine |
| S8 | server/src/lib.rs:393,410-413,516,525 | PEM/base64 load | startup only | no | not network | n/a |
| S9 | server/src/lib.rs:203,347 | `vec![0; MAX_UDP_PAYLOAD]` | once per run | n/a | n/a | n/a |

## F. `shortcut:` / `ponytail:` comments that admit these costs
- tls/src/handshake.rs:186 ponytail: front drain of Vec in next_message (T2).
- quic/src/h3_server.rs:649-650 ponytail: `Vec::remove(0)` and whole-queue purge (Q9, Q10).
- quic/src/send_stream.rs:984 ponytail: split_off trim, up to 2x slack (Q7). :92, :184 O(ranges).
- quic/src/conn.rs:3392 shortcut: crypto bytes copied out and dropped (Q6).
- quic/src/crypto_stream.rs:20 shortcut: fixed 16 KiB ooo hold (bound for Q5).
- quic/src/frags.rs:1147 (at 58e6d14) shortcut: frame adding positions copies touched fragments and moves list; 0.2 s/1 s/1.8 s per connection (Initial, pre-auth). Closed by 9b1: the comment is gone, `insert` is O(log n + d) per frame, proved (`cat-C15`).
- quic/src/path.rs:930 ponytail: shifts at most MAX_RESPONSES-1 (Q17).
- quic/src/ack_track.rs:438 ponytail: O(ranges) insert, <= 32 (Q15).
- quic/src/sent.rs:301 ponytail: O(inflight x 65) per ACK (Q16).
- quic/src/streams.rs:57,66 ponytail: linear scans (Q20). route.rs:16,30; server/src/lib.rs:200 (Q19, S3).
- quic/src/payload.rs:477 ponytail: one Frame per byte of 1-byte frames (Q22).
- quic/src/conn.rs:1561 ponytail: per-ACK work 64 records x runs x O(R); :9906 and datagram.rs:404 serialize-to-measure scratch buffers.
- tls/src/ext.rs:245 ponytail: 8 KiB bitmap zeroed per CH, pre-auth (T10).
- tls/src/codes.rs:95 ponytail: MAX_HS_BODY = 64 KiB (bounds T1/T2/T9).
- h3/src/message.rs:1372 ponytail: cookie rescans O(n^2) (H1/H2). It says nothing about the O(n^2) value copy in :1399-1402, which is worse.
- h3/src/frame.rs:243 and limits.rs:6 ponytail: O(n^2) SETTINGS dup scan, 512 pairs (H8).
- h3/src/conn.rs:2159 ponytail: linear lookup over open streams (H10).
- quic/src/cid.rs:51, quic/src/stream_id.rs:55, quic/src/recovery.rs:12 (placeholder), lifecycle.rs:442,494: not copy costs.

## Status of 9b2's rows (9b2 Task 11, 2026-11-21, phase-9b2 at d77e4ef)

The rows 9b2 closed (spec `docs/superpowers/specs/2026-11-12-phase-9b2-byte-queue-design.md`, Coverage), each with its
status and evidence, and the rows it marks unchanged. A column per row in the tables above would break their raw
layout, so the status sits here, keyed by row id. "Forbidden patterns" is a fresh grep of each converted fn's body at
this commit for the patterns that grew or shifted a byte `Vec` (`extend_from_slice`, `.append(`, `split_off`,
`insert(0`, `remove(0`, `Vec::new()` and `vec![`, the start of a push loop into a fresh `Vec`). The cost tests named
below count allocations and bytes (a counting allocator, release build); none times anything.

| row | status | fn at d77e4ef | forbidden patterns in its body | evidence |
|---|---|---|---|---|
| Q1 | closed (D11, D12) | `Reassembly::insert`, quic/src/reassembly.rs:560 | none | the stream's bytes are a `quic::ring::Ring` of 256-byte pages, each an exact `CapVec`, written in place (`Ring::wf`: a page is allocated iff it holds a byte at or past `base`); `input_cost::stream_reverse_fill`: 0 reallocs, largest frame call 2624 bytes at 64 KiB (Task 1: 262128 bytes for 1) |
| Q2 | closed (D11, D12) | `Reassembly::pop`, reassembly.rs:660 | none | delivers at most `max` bytes per call through `Ring::deliver` (ring.rs:1658) into one exact `CapVec`; `stream_reverse_fill`: no call hands over more than it was given |
| Q3 | closed (D12) | `run_end` is gone | - | delivery is lazy (D12: `SpecRecvIn::Deliver { max }`, `pump_backlog`'s STREAM half), each delivery one exact `CapVec` of at most `B_PUMP` bytes; `stream_reverse_fill`: pump calls at most 4256 bytes |
| Q4 | closed (D6) | `CryptoStream::read`, quic/src/crypto_stream.rs:660 | none | `read(max, out)` takes `k = min(max, contiguous − base)` bytes into the caller's exact `CapVec` (`take_front_c`, at most `18·max + 5608`); `input_cost::crypto_one_byte_frames`: 0 reallocs, no call hands over more than its 1 byte (Task 1: 8192 for 1) |
| Q5 | closed (D6, D7) | `CryptoStream::on_fill`, crypto_stream.rs:617 | none | the run stays in the `Frags` store (no copy at fill time); `on_fill`'s cost `9d + 16,078` is in its ensures (Task 10d); `input_cost::crypto_runs_then_fill`: 0 reallocs (Task 1: 3 to 5 in the fill) |
| Q6 | closed (D6) | `Connection::crypto_drop`, quic/src/conn.rs:6029 | none | each non-empty store moves to its level's teardown slot (no byte copied), freed by `pump_backlog`; `conn_rx::crypto_drop_two_levels_to_slots` |
| Q7 | closed (D10) | `SendStream::on_data_acked`, quic/src/send_stream.rs:2635, and `on_data_acked_w`, :2676 | none | the buffer is a `byteq::queue::ByteQueue`; an ACK drops a prefix with no copy; `input_cost::send_ack_1k`: largest ACK call 1600 bytes at 1 MiB (Task 1: 524352 for 0), `ack_copies_no_stream_bytes` |
| Q8 | closed (D4, D10) | `SendStream::write`, send_stream.rs:1480 | none | `ByteQueue::push_slice`, at most `7d + 4` units with migration at copy rate 3 (D4); `send_ack_1k`: 0 reallocs |
| Q-T1 | closed (D6, D13) | quictls `feed`, quictls/src/server.rs:1785 | none | reads at most `min(d, MAX_FEED)` bytes into an exact `CapVec`; the rest waits for `pump_backlog` (`B_PUMP` per call) |
| T1 | closed (D8) | `HsReader::push`, tls/src/handshake.rs:142 | none | the reader is a `ByteQueue` (handshake.rs:108); `reader_cost::reader_one_byte_push`: 0 reallocs (Task 1: 11 to 13) |
| T2 | closed (D8) | `HsReader::next_message`, handshake.rs:166 | none | takes the message with one exact `take_front`; the tail stays in the queue (D14 (1): one copy of the completed message, 9b5's to remove) |
| T3 | closed (D9) | `message_hash`, tls/src/schedule.rs:94; the HRR transcript, tls/src/server.rs:1343-1348 | none | `CapVec::new(36 + hrr.len())`, two `push_slice`s, no realloc; its O(transcript) is D14 (3) |
| T4 | closed (D9) | the ClientHello transcript, tls/src/server.rs:1376-1378 | none | `CapVec::new(tr.len() + m.len())`, two `push_slice`s |
| T5 | closed (D9) | `build_flight`, tls/src/flight.rs:619 | five `Vec::new()` (:761, :776, :796, :837, :846): the outbound message builders `sh`, `ee`, `cert`, `cv`, `fin`, the sweep's T11 (class B, `cat-C15-9b4`), not the transcript | the transcript is one exact `CapVec` (:801), and the second (:852) too; `fn append` is gone |
| Q-T2 | no change | quictls `feed`'s event vector | - | events are moved, never shifted (the sweep's own note) |
| Q-T3 | no change | quictls `log` | - | ghost only, not exec |
| Q23 | no change | quic/src/frame.rs `slice_to_vec` of CRYPTO/STREAM data | - | O(frame) = bytes given |

Rows not 9b2's keep their owners: Q9-Q22, Q24-Q27, T7, T8, T11, S1-S9 and class B (`cat-C15-9b4`), T6, T9 and T10
(`cat-C15-stream-parse`, 9b5; T6's chain hashing also `cat-C15-9b4-chain`), H1-H12 (`cat-C15-9b3`).

## Status of 9b3's rows (9b3 Task 13, 2026-11-23, phase-9b3 at 9bd1b68)

The h3 rows of §D, the four h3_server rows of §A and the sites the 9b3 spec added (N1-N6; spec
`docs/superpowers/specs/2026-11-14-phase-9b3-h3-input-costs-design.md`, "The cost today"), each with its status and
evidence, keyed by row id as 9b2's table above. Every closed row's cost is a proved `Ghost<nat>` ensures (the commit
names the fn), and `crates/h3/tests/input_cost.rs` counts allocations and requested bytes per call (a counting
allocator, release build; it times nothing). "Open" rows name their carryover. Completed-frame work is proved linear
in the frame and stays O(frame) in the call that completes it until 9b5's incremental parsing
(`cat-C15-stream-parse`).

| row | status | evidence |
|---|---|---|
| H1 | closed by 9b3 (170a39b) | `build_headers` merges in two passes into exact `CapVec`s (`cookie_scan`, then pushes): `r.1@ <= c_bh()·(fields_size + n + 1)`; `input_cost::cookie_lines_linear`: 0 reallocs, 211,125 bytes for 32,557 (Task 1: 44,216,017); the RCA `docs/rca/2026-11-14-cookie-merge.md` |
| H2 | closed by 9b3 (170a39b) | the rescan is gone (pass 1 counts the merged length, pass 2 tracks the first cookie's index); `input_cost::cookie_rescans_linear` |
| H3 | closed by 9b3 (8755ee5) | the sweep's claim was corrected in the spec (at most `d`, 15 bytes); `RequestStream.buf` is a `byteq::queue::ByteQueue`, no `slice_to_vec` of the remainder; `input_cost::headers_bytewise` |
| H4 | closed by 9b3 (8755ee5) | `top_up` pushes into the `ByteQueue` (`push_slice`, no realloc, the migration charged); the header parse reads `as_slice()[..min(16, len)]` (N5); `input_cost::headers_bytewise`: 0 reallocs over 50,399 calls |
| H5 | closed by 9b3 (8755ee5, 317480a) | events in an exact `CapVec<ReqEvent>` of `MAX_REQ_EVENTS`, one `Body` per call; `input_cost::data_frames_events` |
| H6 | closed by 9b3 (11faf1e) | the stream type is read through the `ByteQueue` (at most 8 bytes); `input_cost::control_bytewise` |
| H7 | closed by 9b3 (11faf1e) | control and QPACK stream buffers are `ByteQueue`s with no remainder copy; `UniStream::on_data` costs `c_uni·(d + 16) + c_uni_frame·buffered`; `input_cost::control_bytewise`, `control_preamble_one_call`, `qpack_bytewise` |
| H8 | closed by 9b3 (aa1417a) | `sort_ids_w` (a verified merge sort on two `CapVec<u64>`), `settings_ok` and `parse_settings` return proved costs, O(p log p); the MIR analysis now reports `settings_ok deg=1` (was `deg=2`, expected-cost.txt); H3_SETTINGS_ERROR kept (RFC 9114 §7.2.4's receiver MAY, N2) |
| H9 | closed by 9b3 for growth and the proof of linearity (98765cc); parsing open | `decode_lines_bounded`, `huffman_decode_w`, `decode_string`, `scan_string` and `decode_field_line` on exact `CapVec`s with proved costs; `input_cost::huffman_max_expansion`; the O(frame) parse in the completing call is `cat-C15-stream-parse` (9b5) |
| H10 | closed by 9b3 (e5e3ce8) | `H3Conn`'s request and uni tables are `byteq::avl` trees keyed by id, an update is take and put (no remove plus insert, no `find_req` scan); `on_stream_data`, `on_stream_reset` and `on_stop_sending` prove `O(d + log n)` per call with the height from `lemma_ht_of`; `input_cost::stream_table_flat` |
| H11 | input part closed by 9b3 (808aa19, 317480a, 7af3915); the rest open | `rev` and `deliver` on exact `CapVec`s with proved costs and the answered return's `c_step`; constant-size answers (`input_cost::answers_constant`). Response building for `send_response` (`status_line`, `copy_fields`, `fits_peer_x`, `write_response`, `start`, `send_goaway`) is not a network-input call but is an application-API entry point, so it is `cat-C15-9b4`'s (scaffold H3-7) |
| H12 | open, `cat-C15-9b4` (scaffold H3-7, `mem-fs-copy`) | encode only (`encode_string`, `serialize_prefix_int`): output, not network input; unchanged |
| Q9 | open, `cat-C15-9b4` | h3_server.rs `pending.remove(0)`; 9b3 touched h3_server.rs only at `lemma_flushed` (a lemma split for rlimit) |
| Q10 | open, `cat-C15-9b4` | `kept`/`purge` |
| Q11 | open, `cat-C15-9b4` | `apply_one`'s `pending.push` |
| Q12 | open, `cat-C15-9b4` | `apply_one`'s and `feed`'s `app.push` |
| N1 | open, `cat-C15-9b4` | `H3Server::flush` from an ACK or MAX_STREAM_DATA: output moved by an input call (O7, the flush budget) |
| N2 | closed by 9b3 (aa1417a) | the duplicate-SETTINGS error is kept and its citation gains the receiver's MAY (frame.rs:134-139); no bug section |
| N3 | open, `cat-C15-9b4` (the whole of it) | 9b3 makes the cost independent of the stream count (an `avl` tree, `log n`); the memory bound on tracked streams and h3_server's queue, proved against QUIC's stream limits, is 9b4's (TRUSTED.md line 7's pending-queue sentence stays) |
| N4 | huffman.rs:756 (now :881) to `cat-C15-stream-parse`; limits.rs:19 corrected (Task 13: the stale comment deleted, the doc comment under it states the decoded budget); h3_server.rs:649 open, `cat-C15-9b4`; static_table.rs:361 no change | static_table.rs:361 is a constant scan over 99 entries on the encode side, not an input path |
| N5 | closed by 9b3 (8755ee5, 11faf1e) | `parse_frame_header` reads a prefix of at most 16 bytes: request.rs's `min(16, len)` lemma and uni.rs's control preamble; costs `c_fhdr() == 17` from `parse_frame_header_w` (3468ebf) |
| N6 | open, `cat-C15-teardown` (9b4) | removing an entry frees its trailer lines in the removing call; charged as the `removed_fields` term of `on_stream_data`, `on_stream_reset` and `on_stop_sending` (85ffc05), excluded from the O(d + log n) bound; the API is 9b4's |
