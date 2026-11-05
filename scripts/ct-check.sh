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
# and every vector must pass ct-front's verified selftest within a time bound; finally every dump
# must parse and decode with no `Unknown` (ctmir's `dumps` tests). Every ct-front run
# is under `timeout` and must exit 0 and write its report into a freshly emptied run dir. Target
# dirs live under CT_TARGET_DIR (default $root/target/ct), one subdir per run; dumps and reports
# under $CT_OUT/<run>.
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

# cost_verdicts <report> [atoms]: its lines without coefficients, a first error's text or a
# `CalleeNone` or `Validator` index (the closure's own numbering), sorted. With a second argument a
# `bounded` line keeps its non-constant monomials' atoms (`bounded p deg=1 len(b)`), so a bound that
# stops being in `len(..)` atoms shows as a diff.
cost_verdicts() {
    sed -E 's/^(bounded .* deg=[012]) steps <= (.*)$/\1 \2/
            s/^(none .* (Unsupported|Unresolved)) .*$/\1/
            s/ (CalleeNone|Validator)\([0-9]+\)$/ \1/' "$1" |
        awk -v atoms="${2:-}" '$1 == "bounded" { out = $1 " " $2 " " $3
                if (atoms == "") { print out; next }
                sub(/^bounded [^ ]+ deg=[012] ?/, ""); n = split($0, t, / \+ /); seen = ""
                for (i = 1; i <= n; i++) { m = t[i]; sub(/^[0-9]+\*/, "", m); if (m ~ /[a-z_#]/) seen = seen " " m }
                print out seen; next } { print }' | LC_ALL=C sort
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
# The selftest of crypto (p256_ecdsa_sign runs 1.5e8 core steps) takes about 20 s; the other runs
# take seconds. 300 s only bounds a hang.
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
front $t "selftest=$st" "$CT_OUT/crypto/mir-crypto.json" "$r" "$cm"
grep -v '^pass ' "$r" >&2 && fail "selftest: vectors failed (above)"
v=$(grep -c '^crypto::' "$st")
p=$(grep -c "^pass " "$r" || true)
[ "$p" -eq "$v" ] || fail "selftest: $p of $v vectors passed"
echo "ct-check: selftest $p/$v"

for c in wire h3 quic; do
    front $t "selftest=$st" "$CT_OUT/parsers/mir-$c.json" "$CT_OUT/parsers/selftest-$c.txt" "$cm" "$pm"
done
r=$CT_OUT/parsers/selftest.txt
cat "$CT_OUT/parsers/selftest-wire.txt" "$CT_OUT/parsers/selftest-h3.txt" "$CT_OUT/parsers/selftest-quic.txt" > "$r"
grep -v '^pass ' "$r" >&2 && fail "selftest parsers: vectors failed (above)"
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
nt=$(grep -c -E '^[[:space:]]*cost-root[[:space:]]' "$ct/cost-targets.txt")
[ "$nt" -eq 36 ] || fail "cost targets: $nt roots, the pre-registered denominator is 36"
for p in $(sed -nE 's/^[[:space:]]*cost-root[[:space:]]+([^ ]+)[[:space:]]+# predicted: bounded.*/\1/p' "$ct/cost-targets.txt"); do
    grep -q "^bounded $p deg=" "$got" || fail "lost a bound the targets file predicts: $p"
done
nb=$(grep -c '^bounded ' "$got" || true)
echo "ct-check: cost $nb/$nt bounded"

# The pipeline keys declassify sites by file:line, so a second call on a line would go uncounted.
calls=$(grep -rho --include='*.rs' 'declassify(' "$root/crates/crypto/src" | wc -l)
lines=$(grep -rh --include='*.rs' 'declassify(' "$root/crates/crypto/src" | wc -l)
[ "$calls" -eq "$lines" ] || fail "one declassify per line"

# Crypto: every manifest root ok, no reject, and every `checked` line (each fn's labels) as pinned.
# F = distinct checked fns, R = manifest roots, D = declassify sites. verify.sh reads this report.
report=$CT_OUT/crypto/report-crypto.txt
front $t check "$CT_OUT/crypto/mir-crypto.json" "$report" "$cm"
grep '^reject ' "$report" >&2 && fail "crypto: rejects (above)"
got=$CT_OUT/crypto/verdicts.txt
verdicts "$report" > "$got"
no_missing "$cm" "$got"
grep '^checked ' "$report" > "$CT_OUT/crypto/labels.txt" || true
diff -u "$ct/expected-labels.txt" "$CT_OUT/crypto/labels.txt" || fail "crypto: checked lines differ from tools/ct-driver/expected-labels.txt"
f=$(awk '$1 == "checked" { print $2 }' "$report" | LC_ALL=C sort -u | wc -l | tr -d ' ')
r=$(grep -c '^root ' "$cm")
d=$(grep -c '^declassify ' "$report" || true)
echo "ct-check: crypto ok ($f fns, $r roots, $d declassify)"

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
# A `=> panic` vector passes when the core run does not complete, and running out of fuel (2^32
# blocks per activation) would count; the whole run takes well under a second, so a 60 s bound
# keeps a looping vector from passing that way.
front 60 "selftest=$sc/vectors.txt" "$CT_OUT/semconf/mir-semconf.json" "$got" "$sc/manifest.txt"
grep -v '^pass ' "$got" >&2 && fail "semconf: vectors failed (above)"
v=$(grep -c '^semconf::' "$sc/vectors.txt")
p=$(grep -c '^pass ' "$got" || true)
[ "$p" -eq "$v" ] || fail "semconf: $p of $v vectors passed"
echo "ct-check: semconf $p/$v"

# Every dump above parses with the verified reader and decodes with no `Unknown` variant (a
# rustc_public variant the schema does not mirror): ctmir's `dumps` tests over $CT_OUT.
n=$(find "$CT_OUT" -name 'mir-*.json' | wc -l | tr -d ' ')
CT_DUMP_DIR=$CT_OUT cargo test --release --locked -q -p ctmir --test json --test schema --target-dir "$CT_TARGET_DIR/ctmir-tests" \
    -- --ignored --exact --nocapture dumps > "$CT_OUT/dumps-test.log" 2>&1 || { cat "$CT_OUT/dumps-test.log" >&2; fail "dumps: a dump does not parse or holds an Unknown"; }
k=$(grep -c ' 0 with Unknown$' "$CT_OUT/dumps-test.log" || true)
[ "$k" -eq "$n" ] || fail "dumps: $k of $n dumps decoded with no Unknown"
echo "ct-check: dumps $k/$n"
