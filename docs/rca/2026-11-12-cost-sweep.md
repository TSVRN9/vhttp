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
| Q5 | quic/src/frags.rs `take_front` (frags.rs:1373 at bd2708a; an AVL of chunks since 9b1) via crypto_stream.rs:455 (`on_fill`) | appends the whole contiguous ooo run to `self.buf` | CRYPTO frame closing a gap | YES | up to all held out-of-order bytes (not "bytes given") | MAX_CRYPTO_BUFFER = 16384 (crypto_stream.rs:21), MAX_CRYPTO_RANGES = 4096. frags.rs being rewritten in 9b1; skipped otherwise |
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
- quic/src/frags.rs:1147 (at bd2708a) shortcut: frame adding positions copies touched fragments and moves list; 0.2 s/1 s/1.8 s per connection (Initial, pre-auth). Closed by 9b1: the comment is gone, `insert` is O(log n + d) per frame, proved (`cat-C15`).
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
