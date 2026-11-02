#!/bin/sh
# Constant-time checker runs: build tools/ct-driver, then analyse the fixtures under it and diff
# their verdicts against tools/ct-fixtures/expected.txt, then run the interpreter selftest
# (tools/ct-driver/selftest.txt) over crates/crypto and over the parser crates (wire, h3, quic),
# then diff the fixtures' step bounds against expected-cost.txt, then check crypto's roots (all
# must be ok) and the negative control (--cfg ct_negative; exactly its one reject). Target dirs
# live under CT_TARGET_DIR (default $root/target/ct), one subdir per run, except that selftest
# shares crypto's (same flags); reports under $CT_OUT/<run>.
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

# analyse <run> <crates> <manifest> <mode> <cargo args..>: a fresh <mode> build of each of the
# comma-separated <crates> (cargo skips fresh crates, and manifests and CT_* are not cargo inputs,
# so clean them first); sets $reports to their output files, one per crate, and $report to the
# first.
analyse() {
    run=$1 crates=$2 manifest=$3 mode=$4
    shift 4
    case $run in selftest) td=$CT_TARGET_DIR/crypto ;; *) td=$CT_TARGET_DIR/$run ;; esac
    rm -rf "${CT_OUT:?}/$run"
    pkgs=$(printf '%s' "$crates" | tr ',' '\n' | sed 's/^/-p /' | tr '\n' ' ')
    for c in $(printf '%s' "$crates" | tr ',' ' '); do
        cargo clean --release -q -p "$c" "$@" --target-dir "$td"
    done
    # shellcheck disable=SC2086 # $pkgs is the word list `-p a -p b ..`
    RUSTC_WORKSPACE_WRAPPER=$driver RUSTC_BOOTSTRAP=1 CT_CRATES=$crates CT_MANIFEST=$manifest \
        CT_OUT=$CT_OUT/$run CT_MODE=$mode CT_SELFTEST=$root/tools/ct-driver/selftest.txt \
        cargo build --release --locked -q $pkgs "$@" --target-dir "$td" \
        || fail "$run: analysis build failed"
    reports=
    for c in $(printf '%s' "$crates" | tr ',' ' '); do
        case $mode in selftest) r=selftest- ;; cost) r=cost- ;; *) r=report- ;; esac
        r=$CT_OUT/$run/$r$c.txt
        [ -f "$r" ] || fail "$run: no $r"
        reports="$reports $r"
    done
    report=${reports# }
    report=${report%% *}
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

# cost_verdicts <report>: its lines without coefficients, a first error's text or a `CalleeNone` or
# `Validator` index (the closure's own numbering), sorted.
cost_verdicts() {
    sed -E 's/^(bounded .* deg=[012]) steps <= .*$/\1/
            s/^(none .* (Unsupported|Unresolved)) .*$/\1/
            s/ (CalleeNone|Validator)\([0-9]+\)$/ \1/' "$1" | LC_ALL=C sort
}

# cost_no_missing <manifest> <report>..: every cost-root has a verdict line in some report. Grepped
# whole, because a path may hold spaces (`<a::B as a::C>::f`).
cost_no_missing() {
    sed -nE 's/^[[:space:]]*cost-root[[:space:]]+//; T; s/[[:space:]]+#.*$//; p' "$1" > "$CT_OUT/cost-roots.txt"
    shift
    while IFS= read -r p; do
        grep -qF -e "bounded $p deg=" -e "none $p " "$@" || fail "cost-root with no verdict: $p"
    done < "$CT_OUT/cost-roots.txt"
}

fx=$root/tools/ct-fixtures
analyse fixtures ct_fixtures "$fx/manifest.txt" check --manifest-path "$fx/Cargo.toml"
got=$CT_OUT/fixtures/verdicts.txt
verdicts "$report" > "$got"
no_missing "$fx/manifest.txt" "$got"
diff -u "$fx/expected.txt" "$got" || fail "fixtures: verdicts differ from expected.txt"
n=$(wc -l < "$fx/expected.txt" | tr -d ' ')
echo "ct-check: fixtures $n/$n"

# Selftest: every vector line of selftest.txt must report `pass`; counted per crate prefix.
st=$root/tools/ct-driver/selftest.txt
analyse selftest crypto "$root/tools/ct-driver/manifest.txt" selftest
grep -v '^pass ' "$report" >&2 && fail "selftest: vectors failed (above)"
v=$(grep -c '^crypto::' "$st")
p=$(grep -c "^pass " "$report" || true)
[ "$p" -eq "$v" ] || fail "selftest: $p of $v vectors passed"
echo "ct-check: selftest $p/$v"

# The parser crates' vectors, under their own target dir (wire compiles with -Zalways-encode-mir).
analyse parsers wire,h3,quic "$root/tools/ct-driver/manifest.txt" selftest
# shellcheck disable=SC2086 # $reports is a list of paths without spaces
cat $reports > "$CT_OUT/parsers/selftest.txt"
grep -v '^pass ' "$CT_OUT/parsers/selftest.txt" >&2 && fail "selftest parsers: vectors failed (above)"
v=$(grep -c -E '^(wire|h3|quic)::' "$st")
p=$(grep -c "^pass " "$CT_OUT/parsers/selftest.txt" || true)
[ "$p" -eq "$v" ] || fail "selftest parsers: $p of $v vectors passed"
echo "ct-check: selftest parsers $p/$v"

# The fixtures' step bounds.
analyse cost-fixtures ct_fixtures "$fx/manifest.txt:$fx/cost-manifest.txt" cost --manifest-path "$fx/Cargo.toml"
cost_no_missing "$fx/cost-manifest.txt" "$report"
got=$CT_OUT/cost-fixtures/verdicts.txt
cost_verdicts "$report" > "$got"
diff -u "$fx/expected-cost.txt" "$got" || fail "cost fixtures: verdicts differ from expected-cost.txt"
n=$(wc -l < "$fx/expected-cost.txt" | tr -d ' ')
echo "ct-check: cost fixtures $n/$n"

# The driver keys declassify sites by file:line, so a second call on a line would go uncounted.
calls=$(grep -rho --include='*.rs' 'declassify(' "$root/crates/crypto/src" | wc -l)
lines=$(grep -rh --include='*.rs' 'declassify(' "$root/crates/crypto/src" | wc -l)
[ "$calls" -eq "$lines" ] || fail "one declassify per line"

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
