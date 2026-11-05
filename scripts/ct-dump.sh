#!/bin/sh
# MIR dumps for the verified front end: build tools/ct-driver, then one CT_MODE=dump build per run
# (crypto, the fixtures, the negative control, the parser crates wire,h3,quic, the semconf
# conformance fixtures), with the analysis flags ct-check.sh uses. Writes
# $CT_OUT/<run>/mir-<crate>.json, checks each with scripts/ct-zarr.py (no unit-like array local,
# ZeroSized constant or call destination), and prints each dump's size and the run's wall time. Target dirs live under CT_TARGET_DIR (default $root/target/ct-dump), one
# subdir per run. The driver fails the build on a dangling id (dump.rs `dangling`).
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root" # rust-toolchain.toml pins rustc 1.98.1, the one ct-driver links against
CT_TARGET_DIR=${CT_TARGET_DIR:-$root/target/ct-dump}
CT_OUT=${CT_OUT:-$CT_TARGET_DIR/out}
# Every cargo call passes --target-dir; nothing inherits a target dir or the driver's RUSTFLAGS.
unset CARGO_TARGET_DIR RUSTFLAGS
fail() { echo "ct-dump: $*" >&2; exit 1; }

sr=$(rustc --print sysroot)
RUSTC_BOOTSTRAP=1 RUSTFLAGS="-L $sr/lib -C link-args=-Wl,-rpath,$sr/lib" \
    cargo build --release --locked -q --manifest-path "$root/tools/ct-driver/Cargo.toml" \
    --target-dir "$CT_TARGET_DIR/driver" || fail "driver build failed"
driver=$CT_TARGET_DIR/driver/release/ct-driver

# dump <run> <crates> <manifest> <cargo args..>: a fresh dump build of each of the comma-separated
# <crates> (cargo skips fresh crates, and manifests and CT_* are not cargo inputs, so clean them
# first); fails unless each crate's mir-<crate>.json exists.
dump() {
    run=$1 crates=$2 manifest=$3
    shift 3
    td=$CT_TARGET_DIR/$run
    rm -rf "${CT_OUT:?}/$run"
    pkgs=$(printf '%s' "$crates" | tr ',' '\n' | sed 's/^/-p /' | tr '\n' ' ')
    for c in $(printf '%s' "$crates" | tr ',' ' '); do
        cargo clean --release -q -p "$c" "$@" --target-dir "$td"
    done
    t0=$(date +%s%N)
    # shellcheck disable=SC2086 # $pkgs is the word list `-p a -p b ..`
    RUSTC_WORKSPACE_WRAPPER=$driver RUSTC_BOOTSTRAP=1 CT_CRATES=$crates CT_MANIFEST=$manifest \
        CT_OUT=$CT_OUT/$run CT_MODE=dump \
        cargo build --release --locked -q $pkgs "$@" --target-dir "$td" \
        || fail "$run: dump build failed"
    ms=$(( ($(date +%s%N) - t0) / 1000000 ))
    for c in $(printf '%s' "$crates" | tr ',' ' '); do
        f=$CT_OUT/$run/mir-$c.json
        [ -f "$f" ] || fail "$run: no $f"
        python3 -I "$root/scripts/ct-zarr.py" "$f" || fail "$run: $f holds a unit-like array site (above)"
        echo "ct-dump: $run $c $(wc -c < "$f" | tr -d ' ') bytes"
    done
    echo "ct-dump: $run ${ms}ms"
}

ct=$root/tools/ct-driver
fx=$root/tools/ct-fixtures
dump crypto crypto "$ct/manifest.txt"
dump fixtures ct_fixtures "$fx/manifest.txt" --manifest-path "$fx/Cargo.toml"
export RUSTFLAGS='--cfg ct_negative'
dump negative crypto "$ct/manifest.txt:$ct/manifest-negative.txt"
unset RUSTFLAGS
dump parsers wire,h3,quic "$ct/manifest.txt:$ct/manifest-parsers.txt"
dump semconf semconf "$ct/manifest.txt" --manifest-path "$fx/semconf/Cargo.toml"
