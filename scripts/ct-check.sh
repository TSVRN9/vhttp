#!/bin/sh
# Constant-time checker runs: build tools/ct-driver, then analyse the fixtures under it and diff
# their verdicts against tools/ct-fixtures/expected.txt, then run the interpreter selftest
# (tools/ct-driver/selftest.txt) over crates/crypto, then check crypto's roots (all must be ok) and
# the negative control (--cfg ct_negative; exactly its one reject). Target dirs live under CT_TARGET_DIR
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

# analyse <run> <crate> <manifest> <mode> <cargo args..>: a fresh <mode> build of <crate> (cargo
# skips fresh crates, and manifests and CT_* are not cargo inputs, so clean it first); sets
# $report to its output file.
analyse() {
    run=$1 crate=$2 manifest=$3 mode=$4
    shift 4
    rm -rf "${CT_OUT:?}/$run"
    cargo clean --release -q -p "$crate" "$@" --target-dir "$CT_TARGET_DIR/$run"
    RUSTC_WORKSPACE_WRAPPER=$driver RUSTC_BOOTSTRAP=1 CT_CRATES=$crate CT_MANIFEST=$manifest \
        CT_OUT=$CT_OUT/$run CT_MODE=$mode CT_SELFTEST=$root/tools/ct-driver/selftest.txt \
        cargo build --release --locked -q -p "$crate" "$@" --target-dir "$CT_TARGET_DIR/$run" \
        || fail "$run: analysis build failed"
    case $mode in selftest) report=$CT_OUT/$run/selftest-$crate.txt ;; *) report=$CT_OUT/$run/report-$crate.txt ;; esac
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
analyse fixtures ct_fixtures "$fx/manifest.txt" check --manifest-path "$fx/Cargo.toml"
got=$CT_OUT/fixtures/verdicts.txt
verdicts "$report" > "$got"
no_missing "$fx/manifest.txt" "$got"
diff -u "$fx/expected.txt" "$got" || fail "fixtures: verdicts differ from expected.txt"
n=$(wc -l < "$fx/expected.txt" | tr -d ' ')
echo "ct-check: fixtures $n/$n"

# Selftest: every vector line of selftest.txt must report `pass` (they are all crypto's).
analyse selftest crypto "$root/tools/ct-driver/manifest.txt" selftest
grep -v '^pass ' "$report" >&2 && fail "selftest: vectors failed (above)"
v=$(grep -c '^[^#[:space:]]' "$root/tools/ct-driver/selftest.txt")
p=$(grep -c "^pass " "$report" || true)
[ "$p" -eq "$v" ] || fail "selftest: $p of $v vectors passed"
echo "ct-check: selftest $p/$v"

# Crypto: every manifest root ok, no reject. F = distinct checked fns, R = manifest roots, D =
# declassify sites.
cm=$root/tools/ct-driver/manifest.txt
analyse crypto crypto "$cm" check
grep '^reject ' "$report" >&2 && fail "crypto: rejects (above)"
got=$CT_OUT/crypto/verdicts.txt
verdicts "$report" > "$got"
no_missing "$cm" "$got"
f=$(awk '$1 == "checked" { print $2 }' "$report" | LC_ALL=C sort -u | wc -l | tr -d ' ')
r=$(grep -c '^root ' "$cm")
d=$(grep -c '^declassify ' "$report" || true)
echo "ct-check: crypto ok ($f fns, $r roots, $d declassify)"

# Negative control: crypto::ct_negative::secret_branch (compiled only with --cfg ct_negative) is
# the one reject, as SecretSwitch; every manifest.txt root stays ok.
export RUSTFLAGS='--cfg ct_negative'
analyse negative crypto "$cm:$root/tools/ct-driver/manifest-negative.txt" check
unset RUSTFLAGS
rj=$(grep '^reject ' "$report" || true)
case $rj in
    "reject crypto::ct_negative::secret_branch SecretSwitch "*) ;;
    *) fail "negative: expected one SecretSwitch reject of secret_branch, got: ${rj:-none}" ;;
esac
[ "$(printf '%s\n' "$rj" | wc -l)" -eq 1 ] || fail "negative: more than one reject: $rj"
got=$CT_OUT/negative/verdicts.txt
verdicts "$report" > "$got"
no_missing "$cm" "$got"
echo "ct-check: negative control rejected"
