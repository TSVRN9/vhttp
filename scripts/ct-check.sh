#!/bin/sh
# Constant-time checker runs: build tools/ct-driver, then analyse the fixtures under it and diff
# their verdicts against tools/ct-fixtures/expected.txt. Target dirs live under CT_TARGET_DIR
# (default $root/target/ct), one subdir per run; reports under $CT_OUT/<run>.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root" # rust-toolchain.toml pins rustc 1.98.1, the one ct-driver links against
CT_TARGET_DIR=${CT_TARGET_DIR:-$root/target/ct}
CT_OUT=${CT_OUT:-$CT_TARGET_DIR/out}
# Every cargo call passes --target-dir; nothing inherits a target dir or the driver's RUSTFLAGS.
unset CARGO_TARGET_DIR RUSTFLAGS
fail() { echo "ct-check: $*" >&2; exit 1; }

sr=$(rustc --print sysroot)
RUSTC_BOOTSTRAP=1 RUSTFLAGS="-L $sr/lib -C link-args=-Wl,-rpath,$sr/lib" \
    cargo build --release --locked -q --manifest-path "$root/tools/ct-driver/Cargo.toml" \
    --target-dir "$CT_TARGET_DIR/driver" || fail "driver build failed"
driver=$CT_TARGET_DIR/driver/release/ct-driver

# analyse <run> <crate> <manifest> <cargo args..>: a fresh check-mode build of <crate> (cargo
# skips fresh crates, and manifests and CT_* are not cargo inputs, so clean it first).
analyse() {
    run=$1 crate=$2 manifest=$3
    shift 3
    rm -rf "${CT_OUT:?}/$run"
    cargo clean --release -q -p "$crate" "$@" --target-dir "$CT_TARGET_DIR/$run"
    RUSTC_WORKSPACE_WRAPPER=$driver RUSTC_BOOTSTRAP=1 CT_CRATES=$crate CT_MANIFEST=$manifest \
        CT_OUT=$CT_OUT/$run CT_MODE=check \
        cargo build --release --locked -q -p "$crate" "$@" --target-dir "$CT_TARGET_DIR/$run" \
        || fail "$run: analysis build failed"
    report=$CT_OUT/$run/report-$crate.txt
    [ -f "$report" ] || fail "$run: no $report"
}

# verdicts <report>: one line per root, `ok <path>` or `reject <path> <K1,K2,..>` (kinds sorted
# and unique), sorted.
verdicts() {
    { awk '$1 == "root" && $3 == "ok" { print "ok", $2 }' "$1"
      awk '$1 == "reject" { print $2, $3 }' "$1" | LC_ALL=C sort -u |
          awk '{ k[$1] = ($1 in k) ? k[$1] "," $2 : $2 } END { for (p in k) print "reject", p, k[p] }'
    } | LC_ALL=C sort
}

# no_missing <manifest> <verdicts file>: every manifest root has a verdict line.
no_missing() {
    awk '{ print $2 }' "$2" | LC_ALL=C sort -u > "$2.paths"
    missing=$(awk '$1 == "root" { print $2 }' "$1" | LC_ALL=C sort | LC_ALL=C comm -23 - "$2.paths")
    [ -z "$missing" ] || fail "roots with no verdict: $missing"
}

fx=$root/tools/ct-fixtures
analyse fixtures ct_fixtures "$fx/manifest.txt" --manifest-path "$fx/Cargo.toml"
got=$CT_OUT/fixtures/verdicts.txt
verdicts "$report" > "$got"
no_missing "$fx/manifest.txt" "$got"
diff -u "$fx/expected.txt" "$got" || fail "fixtures: verdicts differ from expected.txt"
n=$(wc -l < "$fx/expected.txt" | tr -d ' ')
echo "ct-check: fixtures $n/$n"
