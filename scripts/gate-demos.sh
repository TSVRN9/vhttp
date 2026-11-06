#!/bin/sh
set -eu
set -o pipefail
# gate-demos.sh: each cheap gate gets a canned bad input (a temp copy of a fixture in
# tools/gate-demos/ with one change applied) and must exit non-zero with its message; every fixture
# first passes unchanged, so a demo cannot fail for the wrong reason. Covers lint-scripts,
# check-quotes, acceptance (thirteen bad changes) and escape-gate (three). Takes a few seconds.
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

fresh quotes
sed -i 's|^//= https|//=https|' "$tmp/quotes/crates/demo/src/lib.rs"
expect_fail "check-quotes: quote without a recognised citation" "not preceded by a recognised" "$root/scripts/check-quotes.sh" "$tmp/quotes/crates"
fresh quotes
sed -i '/^\/\//d' "$tmp/quotes/crates/demo/src/lib.rs"
expect_fail "check-quotes: no citations" "0 citations" "$root/scripts/check-quotes.sh" "$tmp/quotes/crates"

# acceptance (through acceptance.sh, so the cross-count runs too). The fixture's one error fn carries
# its clause; each demo applies one bad change to a fresh copy.
acc() { "$root/scripts/acceptance.sh" --root "$tmp/acceptance" --baseline "$tmp/acceptance/baseline.txt" --old-baseline "$tmp/acceptance/old-baseline.txt"; }
lib=$tmp/acceptance/crates/demo/src/lib.rs
afresh() { fresh acceptance; cp "$tmp/acceptance/baseline.txt" "$tmp/acceptance/old-baseline.txt"; }
# addfn <text>: put <text> before the closing `} // verus!` of the fixture.
addfn() { sed -i 's/^} \/\/ verus!$//' "$lib"; printf '%s\n\n} // verus!\n' "$1" >> "$lib"; }
afresh
expect_pass "acceptance" acc
addfn 'pub fn fresh_err(n: u64) -> (r: Result<(), u64>)
    ensures
        r is Ok ==> n == 0,
{
    if n == 0 { Ok(()) } else { Err(1) }
}'
expect_fail "acceptance: new unannotated fn" "new error-returning fn without an allowed_ ensures clause" acc
echo "demo::fresh_err" >> "$tmp/acceptance/baseline.txt"
expect_fail "acceptance: line appended to the baseline" "baseline line not in the merge-base baseline" acc
afresh
echo "demo::gone" >> "$tmp/acceptance/baseline.txt"
expect_fail "acceptance: stale baseline line" "stale baseline line, no such fn: demo::gone" acc
afresh
echo "demo::demo" >> "$tmp/acceptance/baseline.txt"
expect_fail "acceptance: baseline line for an annotated fn" "now carries the clause" acc
afresh
sed -i 's/    n > 10 \&\& c == 7/    true/' "$lib"
expect_fail "acceptance: allowed_ fn with body true" "vacuous allowed spec fn" acc
afresh
sed -i 's/    n > 10 \&\& c == 7/    match c { 7 => true, _ => true }/' "$lib"
expect_fail "acceptance: allowed_ fn, match with all arms true" "vacuous allowed spec fn" acc
afresh
sed -i 's/    n > 10 \&\& c == 7/    match c { 7 => c > n, _ => true }/' "$lib"
expect_fail "acceptance: allowed_ fn, catch-all arm true" "vacuous allowed spec fn" acc
afresh
sed -i 's/pub open spec fn allowed_demo_err/pub spec(checked) fn allowed_demo_err/; s/    n > 10 \&\& c == 7/    true/' "$lib"
expect_fail "acceptance: spec(checked) allowed_ fn with body true" "vacuous allowed spec fn" acc
# a same-line `ensures .. {` body must not hide the next fn (it used to credit `a` with `hidden`'s clause)
afresh
addfn 'pub fn a(n: u64) -> (r: Result<(), u64>) ensures r is Ok ==> n == 0 {
    if n == 0 { Ok(()) } else { Err(1) }
}

pub fn hidden(n: u64) -> (r: Result<(), u64>)
    ensures
        r is Err ==> allowed_demo_err(n, r->Err_0),
{
    if n > 10 { Err(7) } else { Ok(()) }
}'
expect_fail "acceptance: same-line body brace" "error-returning fn without an allowed_ ensures clause (add the clause; the baseline only shrinks): demo::a" acc
# a field or an unrelated predicate named allowed_* is not the clause
afresh
addfn 'pub fn field_err(n: u64, s: S) -> (r: Result<(), u64>)
    ensures
        r is Err ==> s.allowed_any,
{
    if n == 0 { Ok(()) } else { Err(1) }
}'
expect_fail "acceptance: allowed_ field name is not the clause" "demo::field_err" acc
afresh
addfn 'pub open spec fn ack_only_allowed_spec(n: u64) -> bool { n > 0 }

pub fn other_err(n: u64) -> (r: Result<(), u64>)
    ensures
        r is Err ==> ack_only_allowed_spec(n),
{
    if n == 0 { Ok(()) } else { Err(1) }
}'
expect_fail "acceptance: ack_only_allowed_spec is not the clause" "demo::other_err" acc
# an alias of Result still counts
afresh
addfn 'pub type R<T> = Result<T, u64>;

pub fn alias_err(n: u64) -> (r: R<()>)
    ensures
        r is Ok ==> n == 0,
{
    if n == 0 { Ok(()) } else { Err(1) }
}'
expect_fail "acceptance: fn returning a Result alias" "demo::alias_err" acc
# a signature the parser cannot split is a failure, not a skip
afresh
addfn 'pub fn odd_err(n: u64) -> (r: Result<(), u64>) ensures r is Ok ==> match n { 0 => true, _ => false } {
    Ok(())
}'
expect_fail "acceptance: unsplittable signature" "acceptance: cannot parse" acc
# the independent fn-token count disagrees with the parser (an `fn` and its name on different lines)
afresh
addfn 'pub fn
split_name(n: u64) -> (r: u64)
    ensures
        r == n,
{
    n
}'
expect_fail "acceptance: cross-count mismatch" "independent scan counts" acc

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

fresh escape
mkdir -p "$tmp/escape/crates/crypto/src"
printf '#[verifier::external_body]\npub fn lonely() {}\n' > "$tmp/escape/crates/crypto/src/x.rs"
expect_fail "escape-gate: external_body in crypto without a TRUSTED row" "has no TRUSTED.md row" esc
fresh escape
printf 'assume_specification[ f ](x: u8);\n' >> "$tmp/escape/crates/demo/src/lib.rs"
expect_fail "escape-gate: assume_specification" "unaccounted escape" esc

echo "gate-demos: $n demos, all fail as expected"
