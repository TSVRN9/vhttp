# Verified HTTP/3 server

Rust + Verus. Design: `docs/superpowers/specs/2026-10-27-verified-http3-design.md`.

## Install Verus (pinned)

Download `verus-0.2026.10.04.426d8b0-x86-linux.zip` from the GitHub release `release/0.2026.10.04.426d8b0` and unzip it into `~/.local/opt/verus/0.2026.10.04.426d8b0/`, so the binary is at `~/.local/opt/verus/0.2026.10.04.426d8b0/verus-x86-linux/verus`. Rust toolchain 1.98.1 must be installed via rustup. Override the location with `VERUS_HOME`.

## Verify

    scripts/verify.sh

`cargo build` and `cargo test` work with plain stable Rust.
