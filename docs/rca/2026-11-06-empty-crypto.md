# RCA: window check before the empty filter in CryptoStream::on_crypto

- **Defect:** `crates/quic/src/crypto_stream.rs:89-98` (on main) returns `CRYPTO_BUFFER_EXCEEDED` for an empty CRYPTO frame whose offset is past `base + MAX_CRYPTO_BUFFER`, because the window check runs before the `data.len() == 0` filter. A legal zero-length frame closes the connection. Found by the 9a plan preflight (finding 1).
- **Escape:** the `ensures` of `on_crypto` prove buffer bounds but say nothing about which errors are allowed, so an over-strict close verifies. The bug is a sibling of fix 753ec2d, which closed only the instance (empty frame past the consumed end at a key change) and left the class: no clause says when `Err` is permitted.
- **Class:** C5, error path not proved RFC-required (see `catalog.md`).
- **Catch:** 9a Task 3's `crypto_allowed_err` (`Err(c) ==> crypto_allowed_err(inputs, c)` on `on_crypto`), plus R4's ratchet `scripts/acceptance.sh`, which fails when an error-returning exec fn in `verus!` has no `allowed_` clause and is not in `tools/acceptance-baseline.txt`; the baseline only shrinks.
- **Evidence:** the ratchet fires on a new unannotated `Result` fn (demo `acceptance: new unannotated fn` in `scripts/gate-demos.sh`). The proof-side evidence (that `crypto_allowed_err` rejects this input) lands with 9a Task 3.
