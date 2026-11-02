# Verified HTTP/3 server

This is an experiment to write an http server from scratch proving its correctness with verus-lang. With agents, code is cheap and exploits are too. I think it's likely that software will transition to being written by LLMs and formally verified at compile-time, and I'd like to get a peek into this potential future. WIP!

## Goals:
- write an HTTP/3 server that makes the same assumptions as verus (not checking LLVM, rustc) conformant to current standards
- crypto also only reliant on verus
- additional checker to prove bounds on running time (DOS mitigation)
- become actually usuable?

AI generated text below:

## Design
Rust + Verus. Design: `docs/superpowers/specs/2026-10-27-verified-http3-design.md`.

## Install Verus (pinned)

Download `verus-0.2026.10.04.426d8b0-x86-linux.zip` from the GitHub release `release/0.2026.10.04.426d8b0` and unzip it into `~/.local/opt/verus/0.2026.10.04.426d8b0/`, so the binary is at `~/.local/opt/verus/0.2026.10.04.426d8b0/verus-x86-linux/verus`. Rust toolchain 1.98.1 must be installed via rustup. Override the location with `VERUS_HOME`, which must point at the `verus-x86-linux` directory that contains `verus` and `cargo-verus`.

## Verify

    scripts/verify.sh

`cargo build` and `cargo test` work with plain stable Rust.

## Requirements coverage (Duvet)

    cargo install duvet --version 0.4.3 --locked
    duvet report

The report is written to `.duvet/reports/report.html`.
