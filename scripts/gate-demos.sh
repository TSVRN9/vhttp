#!/bin/sh
set -eu
set -o pipefail
# gate-demos.sh: each cheap gate gets a canned bad input (a temp copy of a fixture in
# tools/gate-demos/ with one change applied) and must exit non-zero with its message; every fixture
# first passes unchanged, so a demo cannot fail for the wrong reason. Covers lint-scripts,
# check-quotes, acceptance (three bad changes) and escape-gate (three). Takes a few seconds.
root=$(cd "$(dirname "$0")/.." && pwd)
fx=$root/tools/gate-demos
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
n=0
die() { echo "gate-demos: $*" >&2; exit 1; }
# expect_fail <name> <message> <cmd..>: <cmd> must exit non-zero and print <message>.
expect_fail() {
    name=$1 msg=$2
    shift 2
    rc=0
    out=$("$@" 2>&1) || rc=$?
    [ "$rc" -ne 0 ] || die "$name: the gate PASSED the bad input"
    printf '%s\n' "$out" | grep -F -- "$msg" >/dev/null || die "$name: failed (rc=$rc) without the message '$msg':
$out"
    echo "gate-demos: $name: fails as expected"
    n=$((n + 1))
}
# expect_pass <name> <cmd..>: the unchanged fixture passes.
expect_pass() {
    name=$1
    shift
    out=$("$@" 2>&1) || die "$name: the unchanged fixture fails:
$out"
    echo "gate-demos: $name: unchanged fixture passes"
}
# fresh <dir>: a clean copy of the fixture tree in $tmp/<dir>.
fresh() { rm -rf "${tmp:?}/$1"; cp -r "$fx/$1" "$tmp/$1"; }

# lint-scripts: a script without pipefail; an empty directory.
fresh lint
expect_pass "lint-scripts" "$root/scripts/lint-scripts.sh" "$tmp/lint"
sed -i '/pipefail/d' "$tmp/lint/good.sh"
expect_fail "lint-scripts: script without pipefail" "lacks: pipefail" "$root/scripts/lint-scripts.sh" "$tmp/lint"
mkdir "$tmp/empty"
expect_fail "lint-scripts: no scripts" "no *.sh" "$root/scripts/lint-scripts.sh" "$tmp/empty"

# check-quotes: a quote altered by one word.
fresh quotes
expect_pass "check-quotes" "$root/scripts/check-quotes.sh" "$tmp/quotes/crates"
sed -i 's/integers are encoded/integers are NEVER encoded/' "$tmp/quotes/crates/demo/src/lib.rs"
expect_fail "check-quotes: altered quote" "quote not in section" "$root/scripts/check-quotes.sh" "$tmp/quotes/crates"

# acceptance: a new unannotated Result fn; a vacuous allowed_ fn; a stale baseline line; a baseline line whose fn has the clause.
acc() { python3 -I "$root/tools/acceptance.py" --root "$tmp/acceptance" --baseline "$tmp/acceptance/baseline.txt"; }
fresh acceptance
expect_pass "acceptance" acc
lib=$tmp/acceptance/crates/demo/src/lib.rs
sed -i 's/^} \/\/ verus!$//' "$lib"
cat >> "$lib" <<'X'
pub fn fresh_err(n: u64) -> (r: Result<(), u64>)
    ensures
        r is Ok ==> n == 0,
{
    if n == 0 { Ok(()) } else { Err(1) }
}

} // verus!
X
expect_fail "acceptance: new unannotated fn" "new error-returning fn without an allowed_ ensures clause" acc
echo "demo::fresh_err" >> "$tmp/acceptance/baseline.txt"
expect_pass "acceptance: fn listed in the baseline" acc
echo "demo::gone" >> "$tmp/acceptance/baseline.txt"
expect_fail "acceptance: stale baseline line" "stale baseline line, no such fn: demo::gone" acc
fresh acceptance
echo "demo::demo" >> "$tmp/acceptance/baseline.txt"
expect_fail "acceptance: baseline line for an annotated fn" "now carries the clause" acc
fresh acceptance
sed -i 's/    n > 10 \&\& c == 7/    true/' "$lib"
expect_fail "acceptance: allowed_ fn with body true" "vacuous spec fn" acc
fresh acceptance
sed -i 's/    n > 10 \&\& c == 7/    match c { 7 => true, _ => true }/' "$lib"
expect_fail "acceptance: allowed_ fn, match with all arms true" "vacuous spec fn" acc

# escape-gate: assume( in a temp crate (the whole-file scan reports it, as it does for a split one); assume split across lines; external_body outside crypto.
esc() { "$root/scripts/escape-gate.sh" "$tmp/escape"; }
fresh escape
expect_pass "escape-gate" esc
printf 'pub fn bad() { assume(false); }\n' >> "$tmp/escape/crates/demo/src/lib.rs"
expect_fail "escape-gate: assume(" "escape across lines" esc
fresh escape
printf '#[verifier::external_body]\npub fn bad() {}\n' >> "$tmp/escape/crates/demo/src/lib.rs"
expect_fail "escape-gate: external_body outside crypto" "unaccounted escape" esc
fresh escape
printf 'pub fn bad() { assume\n(false); }\n' >> "$tmp/escape/crates/demo/src/lib.rs"
expect_fail "escape-gate: assume split across lines" "escape across lines" esc

echo "gate-demos: $n demos, all fail as expected"
