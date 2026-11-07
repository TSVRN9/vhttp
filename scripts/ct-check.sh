#!/bin/sh
# Constant-time and step-bound checks through the verified front end. Builds tools/ct-driver (the
# decision-free MIR dumper) and tools/ct-front (I/O around the verified ctmir::pipeline), then
# dumps each run's crates (scripts/ct-zarr.py checks every dump) and runs ct-front over the dumps:
# the fixtures' verdicts against tools/ct-fixtures/expected.txt; the selftest vectors
# (tools/ct-driver/selftest.txt) over crypto and over the parser crates (wire, h3, quic); the
# fixtures' and the parser targets' step bounds against their expected-cost.txt; crypto's roots
# (all must be ok) with every `checked` line pinned by tools/ct-driver/expected-labels.txt; the
# negative control (--cfg ct_negative; exactly its one reject); and the semconf conformance check:
# its native vectors (tools/ct-fixtures/semconf) are regenerated and diffed against vectors.txt,
# and every vector must pass ct-front's verified selftest (which runs ctmir::sem through the
# verified evaluator) within a time bound; finally every dump
# must parse and decode with no `Unknown` (ctmir's `dumps` tests). Every ct-front run
# is under `timeout` and must exit 0 and write its report into a freshly emptied run dir. Target
# dirs live under CT_TARGET_DIR (default $root/target/ct), one subdir per run; dumps and reports
# under $CT_OUT/<run>.
set -eu
set -o pipefail
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
cargo build --release --locked -q --manifest-path "$root/tools/ct-front/Cargo.toml" --target-dir "$CT_TARGET_DIR/front" \
    || fail "ct-front build failed"
front_bin=$CT_TARGET_DIR/front/release/ct-front

# dump <run> <crates> <encode> <cargo args..>: a fresh dump build of each of the comma-separated
# <crates> (cargo skips fresh crates, and CT_* are not cargo inputs, so clean them first), the
# comma-separated <encode> crates with -Zalways-encode-mir; empties $CT_OUT/<run>, fails unless
# each crate's mir-<crate>.json exists and passes ct-zarr.py.
dump() {
    run=$1 crates=$2 em=$3
    shift 3
    td=$CT_TARGET_DIR/$run
    rm -rf "${CT_OUT:?}/$run"
    pkgs=$(printf '%s' "$crates" | tr ',' '\n' | sed 's/^/-p /' | tr '\n' ' ')
    for c in $(printf '%s' "$crates" | tr ',' ' '); do
        cargo clean --release -q -p "$c" "$@" --target-dir "$td"
    done
    # shellcheck disable=SC2086 # $pkgs is the word list `-p a -p b ..`
    RUSTC_WORKSPACE_WRAPPER=$driver RUSTC_BOOTSTRAP=1 CT_CRATES=$crates CT_ENCODE_MIR=$em CT_OUT=$CT_OUT/$run \
        cargo build --release --locked -q $pkgs "$@" --target-dir "$td" \
        || fail "$run: dump build failed"
    for c in $(printf '%s' "$crates" | tr ',' ' '); do
        f=$CT_OUT/$run/mir-$c.json
        [ -f "$f" ] || fail "$run: no $f"
        python3 -I "$root/scripts/ct-zarr.py" "$f" >&2 || fail "$run: $f holds a unit-like array site (above)"
    done
}

# front <secs> <mode> <dump> <out> <manifest>..: ct-front under a <secs> time bound; fails unless
# it exits 0 and writes <out> (an Err writes no out-file, and <out> is removed first).
front() {
    secs=$1 mode=$2 d=$3 o=$4
    shift 4
    rm -f "$o"
    timeout "$secs" "$front_bin" "$mode" "$d" "$o" "$@" || fail "ct-front $mode $d failed or ran past $secs s"
    [ -f "$o" ] || fail "ct-front $mode $d wrote no $o"
}

. "$root/scripts/ct-lib.sh"

ct=$root/tools/ct-driver
fx=$root/tools/ct-fixtures
cm=$ct/manifest.txt
pm=$ct/manifest-parsers.txt
st=$ct/selftest.txt
# The parser crates' translate-crate lines name the crates compiled with -Zalways-encode-mir
# (vest_lib, a registry dependency, is outside the wrapper and keeps rustc's own encoding).
encode=$(sed -nE 's/^[[:space:]]*translate-crate[[:space:]]+([^[:space:]#]+).*/\1/p' "$pm" | paste -sd, -)
dump fixtures ct_fixtures "" --manifest-path "$fx/Cargo.toml"
dump crypto crypto ""
dump parsers wire,h3,quic "$encode"
export RUSTFLAGS='--cfg ct_negative'
dump negative crypto ""
unset RUSTFLAGS
# The other runs take seconds; 300 s only bounds a hang. The crypto selftest runs every vector on
# ctmir::sem through the verified evaluator (p256_ecdsa_sign is 1.5e8 MIR steps); it takes about a
# minute and gets its own 150 s bound (8d addendum decision 5), so the bound is enforced.
t=300

front $t check "$CT_OUT/fixtures/mir-ct_fixtures.json" "$CT_OUT/fixtures/report-ct_fixtures.txt" "$fx/manifest.txt"
got=$CT_OUT/fixtures/verdicts.txt
verdicts "$CT_OUT/fixtures/report-ct_fixtures.txt" > "$got"
no_missing "$fx/manifest.txt" "$got"
diff -u "$fx/expected.txt" "$got" || fail "fixtures: verdicts differ from expected.txt"
n=$(wc -l < "$fx/expected.txt" | tr -d ' ')
echo "ct-check: fixtures $n/$n"

# Selftest: every vector line of selftest.txt must report `pass`; counted per crate prefix.
r=$CT_OUT/crypto/selftest-crypto.txt
front 150 "selftest=$st" "$CT_OUT/crypto/mir-crypto.json" "$r" "$cm"
grep_hits -v '^pass ' "$r" >&2 && fail "selftest: vectors failed (above)"
v=$(grep -c '^crypto::' "$st")
p=$(grep -c "^pass " "$r" || true)
[ "$p" -eq "$v" ] || fail "selftest: $p of $v vectors passed"
echo "ct-check: selftest $p/$v"

for c in wire h3 quic; do
    front $t "selftest=$st" "$CT_OUT/parsers/mir-$c.json" "$CT_OUT/parsers/selftest-$c.txt" "$cm" "$pm"
done
r=$CT_OUT/parsers/selftest.txt
cat "$CT_OUT/parsers/selftest-wire.txt" "$CT_OUT/parsers/selftest-h3.txt" "$CT_OUT/parsers/selftest-quic.txt" > "$r"
grep_hits -v '^pass ' "$r" >&2 && fail "selftest parsers: vectors failed (above)"
v=$(grep -c -E '^(wire|h3|quic)::' "$st")
p=$(grep -c "^pass " "$r" || true)
[ "$p" -eq "$v" ] || fail "selftest parsers: $p of $v vectors passed"
echo "ct-check: selftest parsers $p/$v"

# The fixtures' step bounds.
r=$CT_OUT/fixtures/cost-ct_fixtures.txt
front $t cost "$CT_OUT/fixtures/mir-ct_fixtures.json" "$r" "$fx/manifest.txt" "$fx/cost-manifest.txt"
cost_no_missing "$fx/cost-manifest.txt" "$r"
got=$CT_OUT/fixtures/cost-verdicts.txt
cost_verdicts "$r" > "$got"
diff -u "$fx/expected-cost.txt" "$got" || fail "cost fixtures: verdicts differ from expected-cost.txt"
n=$(wc -l < "$fx/expected-cost.txt" | tr -d ' ')
echo "ct-check: cost fixtures $n/$n"

# The parser targets' step bounds: tools/ct-driver/cost-targets.txt through wire, h3 and quic. A
# header index moves with any edit to the function, so NotCounted payloads are stripped here (the
# fixtures keep theirs); the gate is about verdicts and the atoms of each bound. Any difference
# fails. Re-recording expected-cost.txt cannot hide a lost bound: every `# predicted: bounded`
# target must still be bounded, and the root count is the pre-registered 36.
for c in wire h3 quic; do
    front $t cost "$CT_OUT/parsers/mir-$c.json" "$CT_OUT/parsers/cost-$c.txt" "$cm" "$pm" "$ct/cost-targets.txt"
done
reports="$CT_OUT/parsers/cost-wire.txt $CT_OUT/parsers/cost-h3.txt $CT_OUT/parsers/cost-quic.txt"
# shellcheck disable=SC2086 # $reports is a list of paths without spaces
cost_no_missing "$ct/cost-targets.txt" $reports
got=$CT_OUT/parsers/cost-verdicts.txt
# shellcheck disable=SC2086 # $reports is a list of paths without spaces
cat $reports | sed -E 's/ NotCounted\([0-9]+\)$/ NotCounted/' > "$CT_OUT/parsers/cost-all.txt"
cost_verdicts "$CT_OUT/parsers/cost-all.txt" atoms > "$got"
diff -u "$ct/expected-cost.txt" "$got" || fail "cost parsers: verdicts differ from tools/ct-driver/expected-cost.txt"
if grep_hits -v '^[[:space:]]*(#|$|cost-root[[:space:]])' "$ct/cost-targets.txt" > /dev/null; then
    fail "cost-targets.txt holds a line that is not a cost-root line (the selftest and the cost run must share one cpol)"
fi
nt=$(grep -c -E '^[[:space:]]*cost-root[[:space:]]' "$ct/cost-targets.txt")
[ "$nt" -eq 36 ] || fail "cost targets: $nt roots, the pre-registered denominator is 36"
for p in $(sed -nE 's/^[[:space:]]*cost-root[[:space:]]+([^ ]+)[[:space:]]+# predicted: bounded.*/\1/p' "$ct/cost-targets.txt"); do
    grep -q "^bounded $p deg=" "$got" || fail "lost a bound the targets file predicts: $p"
done
nb=$(grep -c '^bounded ' "$got" || true)
echo "ct-check: cost $nb/$nt bounded"

# The pipeline keys declassify sites by file:line, so a second call on a line would go uncounted.
calls=$({ grep -rho --include='*.rs' 'declassify(' "$root/crates/crypto/src" || [ $? -eq 1 ]; } | wc -l)
lines=$({ grep -rh --include='*.rs' 'declassify(' "$root/crates/crypto/src" || [ $? -eq 1 ]; } | wc -l)
[ "$calls" -eq "$lines" ] || fail "one declassify per line"

# Crypto: every manifest root ok, no reject, and every `checked` line (each fn's labels) as pinned.
# F = distinct checked fns, R = manifest roots, D = declassify sites. verify.sh reads this report.
report=$CT_OUT/crypto/report-crypto.txt
front $t check "$CT_OUT/crypto/mir-crypto.json" "$report" "$cm"
CT_OUT=$CT_OUT "$root/scripts/ct-report.sh" "$report" "$cm" "$ct/expected-labels.txt" "$CT_OUT/crypto" || exit 1
f=$(awk '$1 == "checked" { print $2 }' "$report" | LC_ALL=C sort -u | wc -l | tr -d ' ')
r=$(grep -c '^root ' "$cm")
d=$(grep -c '^declassify ' "$report" || true)
echo "ct-check: crypto ok ($f fns, $r roots, $d declassify)"

# Coverage (8d): every crypto `root .. ok` and every parser `bounded` root has a `pass <path> steps=<n>`
# line, i.e. (report_sound's pass_ok) a vector on which mir_run reaches Done. The join is on the path,
# awk `$2`, so a premise is checked first and the run fails closed if it breaks: no root, bounded or
# pass line carries a path with a space (such a path would shift the fields and drop out of the awk
# selections below). The reports line up because the selftest and the check/cost runs read the same
# dump under the same cpol (cost-targets.txt holds only `cost-root` lines, and cpol reads only
# declassify and ghost lines, so adding it to the selftest's manifests changes nothing).
# cover <label> <paths file> <selftest report>..: the number of paths, failing unless each has a pass line.
cover() {
    label=$1 paths=$2
    shift 2
    cat "$@" > "$paths.sel"
    awk '$1 == "pass" && NF != 3 { bad = 1 } END { exit bad }' "$paths.sel" || fail "$label: a pass line is not 3 fields (a path with a space?)"
    awk '$1 == "pass" && $3 ~ /^steps=[0-9]+$/ { print $2 }' "$paths.sel" | LC_ALL=C sort -u > "$paths.pass"
    LC_ALL=C sort -u "$paths" > "$paths.sorted"
    missing=$(LC_ALL=C comm -23 "$paths.sorted" "$paths.pass")
    [ -z "$missing" ] || fail "$label: no vector reaches Done (a 'pass .. steps=' line) for: $missing"
    wc -l < "$paths.sorted" | tr -d ' '
}
awk '$1 == "root" && NF != 3 { bad = 1 } END { exit bad }' "$report" || fail "coverage: a crypto root line is not 3 fields (a path with a space?)"
awk '$1 == "bounded" && $3 !~ /^deg=[0-9]+$/ { bad = 1 } END { exit bad }' "$CT_OUT/parsers/cost-all.txt" || fail "coverage: a bounded line has a path with a space"
awk '$1 == "root" && $3 == "ok" { print $2 }' "$report" > "$CT_OUT/crypto/ok-roots.txt"
awk '$1 == "bounded" { print $2 }' "$CT_OUT/parsers/cost-all.txt" > "$CT_OUT/parsers/bounded-roots.txt"
R=$(wc -l < "$CT_OUT/crypto/ok-roots.txt" | tr -d ' ')
B=$(wc -l < "$CT_OUT/parsers/bounded-roots.txt" | tr -d ' ')
a=$(cover "coverage crypto" "$CT_OUT/crypto/ok-roots.txt" "$CT_OUT/crypto/selftest-crypto.txt") || exit 1
b=$(cover "coverage parsers" "$CT_OUT/parsers/bounded-roots.txt" "$CT_OUT/parsers/selftest.txt") || exit 1
[ "$R" -gt 0 ] && [ "$B" -gt 0 ] || fail "coverage: no root or bounded lines in the reports"
[ "$a" -eq "$R" ] && [ "$b" -eq "$B" ] || fail "coverage: $a of $R ok roots, $b of $B bounded roots have a vector"
echo "ct-check: done roots $a/$R, bounded $b/$B"

# Negative control: crypto::ct_negative::secret_branch (compiled only with --cfg ct_negative) is
# the one reject, as SecretSwitch; every manifest.txt root stays ok.
report=$CT_OUT/negative/report-crypto.txt
front $t check "$CT_OUT/negative/mir-crypto.json" "$report" "$cm" "$ct/manifest-negative.txt"
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

# Semantics conformance (8c): semconf's vectors come from native runs (its tests/vectors.rs) and must
# equal the committed vectors.txt, so a native change shows up; then its dump runs through
# ct-front's verified selftest, and every vector must pass.
sc=$fx/semconf
cargo test --release --locked -q --manifest-path "$sc/Cargo.toml" --target-dir "$CT_TARGET_DIR/semconf-native" > /dev/null \
    || fail "semconf: native vector run failed"
diff -u "$sc/vectors.txt" "$CT_TARGET_DIR/semconf-native/semconf-vectors.txt" || fail "semconf: native vectors differ from vectors.txt"
dump semconf semconf "" --manifest-path "$sc/Cargo.toml"
got=$CT_OUT/semconf/selftest-semconf.txt
# A `=> panic` vector passes only when the MIR run panics (running out of fuel, 2^32 blocks per
# activation, is a `fail`); the whole run takes well under a second, and the 60 s bound stops a
# looping vector.
front 60 "selftest=$sc/vectors.txt" "$CT_OUT/semconf/mir-semconf.json" "$got" "$sc/manifest.txt"
grep_hits -v '^pass ' "$got" >&2 && fail "semconf: vectors failed (above)"
v=$(grep -c '^semconf::' "$sc/vectors.txt")
p=$(grep -c '^pass ' "$got" || true)
[ "$p" -eq "$v" ] || fail "semconf: $p of $v vectors passed"
echo "ct-check: semconf $p/$v"

# The evaluator's and the selftest's own tests (tiny.json fixtures; not part of verify.sh's proofs),
# then eval_probe over the crypto dump: sha256 and p256_public_key on mir_eval must take the step
# counts the deleted core interpreter took (about 16 s).
timeout 600 cargo test --release --locked -q -p ctmir --test eval --test interp --target-dir "$CT_TARGET_DIR/ctmir-tests" > "$CT_OUT/ctmir-tests.log" 2>&1 \
    || { cat "$CT_OUT/ctmir-tests.log" >&2; fail "ctmir: the eval/interp tests failed or ran past 600 s"; }
CT_DUMP_DIR=$CT_OUT timeout 300 cargo test --release --locked -q -p ctmir --test eval --target-dir "$CT_TARGET_DIR/ctmir-tests" \
    -- --ignored --exact eval_probe > "$CT_OUT/eval-probe.log" 2>&1 \
    || { cat "$CT_OUT/eval-probe.log" >&2; fail "ctmir: eval_probe (MIR steps equal the core's) failed or ran past 300 s"; }
grep -q '^test result: ok. 1 passed' "$CT_OUT/eval-probe.log" || { cat "$CT_OUT/eval-probe.log" >&2; fail "ctmir: eval_probe did not run exactly one passing test"; }

# Every dump above parses with the verified reader and decodes with no `Unknown` variant (a
# rustc_public variant the schema does not mirror): ctmir's `dumps` tests over $CT_OUT.
n=$(find "$CT_OUT" -name 'mir-*.json' | wc -l | tr -d ' ')
CT_DUMP_DIR=$CT_OUT cargo test --release --locked -q -p ctmir --test json --test schema --target-dir "$CT_TARGET_DIR/ctmir-tests" \
    -- --ignored --exact --nocapture dumps > "$CT_OUT/dumps-test.log" 2>&1 || { cat "$CT_OUT/dumps-test.log" >&2; fail "dumps: a dump does not parse or holds an Unknown"; }
k=$(grep -c ' 0 with Unknown$' "$CT_OUT/dumps-test.log" || true)
[ "$k" -eq "$n" ] || fail "dumps: $k of $n dumps decoded with no Unknown"
echo "ct-check: dumps $k/$n"
