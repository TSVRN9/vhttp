#!/bin/sh
set -eu
set -o pipefail
# gate-demos.sh: each cheap gate gets a canned bad input (a temp copy of a fixture in
# tools/gate-demos/ with one change applied) and must exit non-zero with its message; every fixture
# first passes unchanged, so a demo cannot fail for the wrong reason. Covers lint-scripts,
# check-quotes, the citation gate, the RFC-quantity gate (its git demos in throwaway repos), acceptance (many bad changes, including real-git runs), escape-gate (three), the rlimit gate and the mutant registry (scripts/mutants.sh; its run demos call Verus
# on the fixture crate), the declassify and deps gates, ct-check's report reader (ct-report.sh), ct-binary (against its real build), the test gate, the carryover gate and the requirements status gate (throwaway repos). Takes a few seconds, plus about a minute the first time vstd builds in target/mutants-demo.
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

# lint-scripts: grep read as a verdict (exit 2, a missing file, reads as "no match"); the grep_hits form passes.
fresh lint
printf 'grep -q x /nonexistent %s fail "found"\n' '&&' >> "$tmp/lint/good.sh"
expect_fail "lint-scripts: a verdict by and-list" "uses grep as a verdict" "$root/scripts/lint-scripts.sh" "$tmp/lint"
fresh lint
printf 'if grep -q x /nonexistent; then fail found; fi\n' >> "$tmp/lint/good.sh"
expect_fail "lint-scripts: grep as an if condition" "uses grep as a verdict" "$root/scripts/lint-scripts.sh" "$tmp/lint"
g=gr; g=${g}ep  # the demo's own lines must not trip the rule they test
for form in "! $g -q x /nonexistent" "while $g -q x /nonexistent" "until $g -q x /nonexistent" "$g -q x /nonexistent && { echo bad; exit 1; }"; do
    fresh lint
    printf '%s\n' "$form" >> "$tmp/lint/good.sh"
    expect_fail "lint-scripts: grep verdict form: $form" "uses grep as a verdict" "$root/scripts/lint-scripts.sh" "$tmp/lint"
done
fresh lint
printf 'grep_hits x /nonexistent %s fail "found"\ngrep -q x f || fail "missing"\n# grep x f %s fail\n' '&&' '&&' >> "$tmp/lint/good.sh"
expect_pass "lint-scripts: grep_hits form, grep .. || fail and a comment" "$root/scripts/lint-scripts.sh" "$tmp/lint"

# grep_hits (scripts/ct-lib.sh): 0 on a match, 1 on none, a failure on a missing file or a bad pattern.
gh() { sh -c 'set -eu; fail() { echo "ct-check: $*" >&2; exit 1; }; . "$1"; shift; rc=0; grep_hits "$@" || rc=$?; echo "rc=$rc"' sh "$root/scripts/ct-lib.sh" "$@" ; }
printf 'a\nb\n' > "$tmp/gh.txt"
expect_pass "grep_hits: a match" gh a "$tmp/gh.txt"
rc=0; out=$(gh zzz "$tmp/gh.txt" 2>&1) || rc=$?
{ [ "$rc" -eq 0 ] && [ "$out" = "rc=1" ]; } || die "grep_hits: no match did not return 1 quietly: rc=$rc out=$out"
echo "gate-demos: grep_hits: no match returns 1 (not a failure)"
expect_fail "grep_hits: a missing file" "grep_hits: no $tmp/nonexistent" gh a "$tmp/nonexistent"
expect_fail "grep_hits: a missing file among others" "grep_hits: no $tmp/nonexistent" gh a "$tmp/gh.txt" "$tmp/nonexistent"
expect_fail "grep_hits: an invalid pattern (grep exit 2)" "grep failed (exit 2)" gh '(' "$tmp/gh.txt"
expect_fail "grep_hits: no file argument" "grep_hits: usage" gh a

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
# a `{` in a decreases clause is not the body (9r2 T4: the body was read from `decreases (if .. {`, as allowed_tp_err_from's was)
afresh
sed -i 's/^pub open spec fn allowed_demo_err(n: u64, c: u64) -> bool {$/pub open spec fn allowed_demo_err(n: u64, c: u64) -> bool\n    decreases (if n < 10 { 10 - n } else { 0 }),\n{/; s/    n > 10 \&\& c == 7/    true/' "$lib"
expect_fail "acceptance: allowed_ fn with body true after a decreases clause holding a brace" "vacuous allowed spec fn" acc
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

# N1: a clause line ending in `{` with forall, whose body mentions an allowed_ name, followed by an impl, must not credit the fn.
afresh
addfn 'pub fn probe_err(n: u64) -> (r: Result<(), u64>) ensures forall|i: int| i == 0 ==> r is Ok ==> n == 0 {
    proof { assert(allowed_demo_err(n, 1) || !allowed_demo_err(n, 1)); }
    Ok(())
}
impl S {
    pub fn z(&self) {}
}'
expect_fail "acceptance: body read as clause text" "not indented under the fn" acc
# a defaulted generic in an alias declaration, a `use .. Result as ..` rename, an `ensures_` identifier
afresh
addfn 'pub type D<T = ()> = Result<T, u64>;

pub fn dflt_err(n: u64) -> (r: D)
    ensures
        r is Ok ==> n == 0,
{
    if n == 0 { Ok(()) } else { Err(1) }
}'
expect_fail "acceptance: alias with a defaulted generic" "demo::dflt_err" acc
afresh
sed -i '1i use std::result::Result as Ret;' "$lib"
expect_fail "acceptance: use .. Result as .." "renames an error type" acc
afresh
addfn 'pub fn sub_err(n: u64) -> (r: Result<(), u64>)
    requires
        ensures_ok(n) || allowed_demo_err(n, 1),
{
    if n == 0 { Ok(()) } else { Err(1) }
}'
expect_fail "acceptance: ensures_ok is not the ensures clause" "demo::sub_err" acc
afresh
echo "demo::dup" > "$tmp/acceptance/baseline.txt"; echo "demo::dup" >> "$tmp/acceptance/baseline.txt"; cp "$tmp/acceptance/baseline.txt" "$tmp/acceptance/old-baseline.txt"
expect_fail "acceptance: duplicate baseline line" "duplicate baseline lines" acc

# check-quotes without a spec dir
expect_fail "check-quotes: no spec dir" "check-quotes: no" "$root/scripts/check-quotes.sh" "$tmp/quotes/crates" "$tmp/nonexistent"

# acceptance.sh's real git path, in a throwaway repo: a branch that appends a baseline line; main appending one; no main.
gitrepo() {  # gitrepo <dir>: scripts and tools of the repo plus the acceptance fixture, one commit on main
    rm -rf "${tmp:?}/$1"; mkdir -p "$tmp/$1/tools"
    cp -r "$root/scripts" "$tmp/$1/scripts"; cp "$root/tools/acceptance.py" "$root/tools/ratchet_walk.py" "$tmp/$1/tools/"
    cp -r "$fx/acceptance/crates" "$tmp/$1/crates"; cp "$fx/acceptance/baseline.txt" "$tmp/$1/tools/acceptance-baseline.txt"
    git -C "$tmp/$1" init -q -b main
    git -C "$tmp/$1" add -A
    gitc "$1" commit -qm base
}
gitc() { d=$1; shift; git -C "$tmp/$d" -c user.email=d@d -c user.name=d -c commit.gpgsign=false "$@"; }
gaccept() { "$tmp/$1/scripts/acceptance.sh"; }
gitrepo g1
gitc g1 checkout -qb feat
echo "demo::extra" >> "$tmp/g1/tools/acceptance-baseline.txt"
gitc g1 commit -qam grow
expect_fail "acceptance.sh git: branch appends a baseline line" "not in the merge-base baseline" gaccept g1
gitrepo g2
echo "demo::extra" >> "$tmp/g2/tools/acceptance-baseline.txt"
gitc g2 commit -qam grow
expect_fail "acceptance.sh git: main appends a baseline line (walk)" "ratchet-walk: tools/acceptance-baseline.txt: HEAD is outside the floor" gaccept g2
gitrepo g3
gitc g3 branch -m main trunk
expect_fail "acceptance.sh git: no main" "cannot resolve the merge-base" gaccept g3
gitrepo g4
gitc g4 checkout -qb feat
touch "$tmp/g4/x"; gitc g4 add x; gitc g4 commit -qm noop
expect_pass "acceptance.sh git: unchanged baseline on a branch" gaccept g4

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

# rlimit gate (tools/rl.py --gate): a quic fn at 8,000,001; a FAIL row; empty and rowless logs; a missing log; two JSON objects.
pin=$root/tools/verus-pin.txt
rl() { python3 -I "$root/tools/rl.py" --gate quic --pin "$pin" --max 8000000 "$tmp/rl.json"; }
fresh rlimit; cp "$tmp/rlimit/quic.json" "$tmp/rl.json"
expect_pass "rlimit-gate" rl
sed -i 's/"rlimit": 8000000/"rlimit": 8000001/' "$tmp/rl.json"
expect_fail "rlimit-gate: fn at 8,000,001" "quic::conn::edge at 8000001 is above 8000000" rl
cp "$tmp/rlimit/quic.json" "$tmp/rl.json"; sed -i 's/"rlimit": 120000, "success": true/"rlimit": 120000, "success": false/' "$tmp/rl.json"
expect_fail "rlimit-gate: FAIL row" "FAIL row" rl
cp "$tmp/rlimit/quic.json" "$tmp/rl.json"; sed -i 's/"errors": 0/"errors": 1/' "$tmp/rl.json"
expect_fail "rlimit-gate: errors in the run" "run not clean" rl
: > "$tmp/rl.json"
expect_fail "rlimit-gate: empty log" "0 verification-results objects" rl
echo '{"verification-results": {"success": true}}' > "$tmp/rl.json"
expect_fail "rlimit-gate: truncated results object" "unreadable results" rl
sed 's/"function-breakdown": \[[^]]*\]/"function-breakdown": []/' "$tmp/rlimit/quic.json" > "$tmp/rl.json"
expect_fail "rlimit-gate: no rows" "no per-fn rows" rl
sed 's/quic::conn::small", "rlimit": 120000/tls::big", "rlimit": 11000000/' "$tmp/rlimit/quic.json" > "$tmp/rl.json"
expect_pass "rlimit-gate: a dependency's fn above the cap is not the gated crate's" rl
sed 's/quic::conn/tls::conn/g' "$tmp/rlimit/quic.json" > "$tmp/rl.json"
expect_fail "rlimit-gate: no fns of the gated crate" "no rows for fns of quic" rl
rm -f "$tmp/rl.json"
expect_fail "rlimit-gate: missing log" "cannot read" rl
cat "$tmp/rlimit/quic.json" "$tmp/rlimit/quic.json" > "$tmp/rl.json"
expect_pass "rlimit-gate: two clean result objects (a dependency built in the run)" rl
{ cat "$tmp/rlimit/quic.json"; sed 's/"rlimit": 120000, "success": true/"rlimit": 120000, "success": false/' "$tmp/rlimit/quic.json"; } > "$tmp/rl.json"
expect_fail "rlimit-gate: FAIL row in the second object" "FAIL row" rl

# F5: the log must come from the pinned Verus and a whole-crate run; the pin file must exist and parse.
cp "$tmp/rlimit/quic.json" "$tmp/rl.json"; sed -i 's/"version": "0.2026.10.04.426d8b0"/"version": "0.2026.10.05.0000000"/' "$tmp/rl.json"
expect_fail "rlimit-gate: wrong Verus version" "verus.version is '0.2026.10.05.0000000'" rl
cp "$tmp/rlimit/quic.json" "$tmp/rl.json"; sed -i 's/"commit": "426d8b01/"commit": "000000001/' "$tmp/rl.json"
expect_fail "rlimit-gate: wrong Verus commit" "verus.commit is" rl
cp "$tmp/rlimit/quic.json" "$tmp/rl.json"; sed -i 's/"toolchain": "1.98.1-/"toolchain": "1.98.0-/' "$tmp/rl.json"
expect_fail "rlimit-gate: wrong toolchain" "verus.toolchain is" rl
cp "$tmp/rlimit/quic.json" "$tmp/rl.json"; sed -i 's/"is-verifying-entire-crate": true/"is-verifying-entire-crate": false/' "$tmp/rl.json"
expect_fail "rlimit-gate: partial run" "is-verifying-entire-crate is not true" rl
cp "$tmp/rlimit/quic.json" "$tmp/rl.json"; sed -i 's/"toolchain": "1.98.1-/"toolchain": "1.98.10-/' "$tmp/rl.json"
expect_fail "rlimit-gate: toolchain prefix without the dash" "verus.toolchain is" rl
sed 's/^{"verus": {[^}]*}, /{/' "$tmp/rlimit/quic.json" > "$tmp/rl.json"
expect_fail "rlimit-gate: no verus object" "no verus object" rl
cp "$tmp/rlimit/quic.json" "$tmp/rl.json"; pin=$tmp/no-such-pin
expect_fail "rlimit-gate: missing pin file" "cannot read the pin file" rl
printf 'version 0.2026.10.04.426d8b0\n' > "$tmp/short-pin"; pin=$tmp/short-pin
expect_fail "rlimit-gate: pin file without commit and toolchain" "lacks a version, commit or toolchain" rl
pin=$root/tools/verus-pin.txt
expect_fail "rlimit-gate: no --pin" "no --pin FILE given" python3 -I "$root/tools/rl.py" --gate quic "$tmp/rl.json"

# clean-tree.sh (F5): an untracked file, a modified tracked file and a non-repo dir fail; a clean repo passes.
ct() { "$root/scripts/clean-tree.sh" "$tmp/ctree"; }
rm -rf "${tmp:?}/ctree"; mkdir "$tmp/ctree"; git -C "$tmp/ctree" init -q -b main; echo a > "$tmp/ctree/f"
git -C "$tmp/ctree" add f; gitc ctree commit -qm base
expect_pass "clean-tree" ct
echo b > "$tmp/ctree/new"
expect_fail "clean-tree: untracked file" "clean-tree: tree dirty (1 paths)" ct
rm "$tmp/ctree/new"; echo c >> "$tmp/ctree/f"
expect_fail "clean-tree: modified tracked file" "clean-tree: tree dirty (1 paths)" ct
rm -rf "${tmp:?}/ctree"; mkdir "$tmp/ctree"
expect_fail "clean-tree: not a repo" "clean-tree: git status failed" ct

# clean-tree.sh with a recorded HEAD (verify.sh's end-of-run check): a commit mid-run and an edit mid-run fail.
rm -rf "${tmp:?}/ctree"; mkdir "$tmp/ctree"; git -C "$tmp/ctree" init -q -b main; echo a > "$tmp/ctree/f"
git -C "$tmp/ctree" add f; gitc ctree commit -qm base
h0=$(git -C "$tmp/ctree" rev-parse HEAD)
cth() { "$root/scripts/clean-tree.sh" "$tmp/ctree" "$h0"; }
expect_pass "clean-tree: HEAD unchanged" cth
gitc ctree commit -q --allow-empty -m moved
expect_fail "clean-tree: HEAD moved during the run" "clean-tree: HEAD moved during the run" cth
h0=$(git -C "$tmp/ctree" rev-parse HEAD); echo c >> "$tmp/ctree/f"
expect_fail "clean-tree: tree dirtied during the run" "clean-tree: tree dirty (1 paths)" cth

# verify.sh's first steps (before any Verus step): a dirty tree, a Cargo.lock cargo would rewrite, cargo not on PATH.
vrepo() {  # vrepo <dir>: scripts, the pin and a one-crate workspace with its lock, committed
    rm -rf "${tmp:?}/$1"; mkdir -p "$tmp/$1/tools" "$tmp/$1/src"
    cp -r "$root/scripts" "$tmp/$1/scripts"; cp "$root/tools/verus-pin.txt" "$tmp/$1/tools/"
    printf '[package]\nname = "d"\nversion = "0.1.0"\nedition = "2021"\n' > "$tmp/$1/Cargo.toml"; : > "$tmp/$1/src/lib.rs"
    (cd "$tmp/$1" && cargo metadata --format-version 1 > /dev/null 2>&1) || die "vrepo: cargo metadata failed on the fixture"
    git -C "$tmp/$1" init -q -b main; git -C "$tmp/$1" add -A; gitc "$1" commit -qm base
}
vfy() { "$tmp/$1/scripts/verify.sh"; }
vrepo v1; echo x > "$tmp/v1/untracked"
expect_fail "verify.sh: dirty tree stops the run" "clean-tree: tree dirty (1 paths)" vfy v1
vrepo v2; sed -i 's/version = "0.1.0"/version = "0.2.0"/' "$tmp/v2/Cargo.lock"; gitc v2 commit -qam stale
expect_fail "verify.sh: a Cargo.lock cargo would rewrite" "verify.sh: cargo metadata --locked failed" vfy v2
nocargo=$tmp/nocargo; mkdir -p "$nocargo"; for c in git sh sed dirname wc printf; do ln -sf "$(command -v $c)" "$nocargo/$c"; done
vnc() { env PATH="$nocargo" "$tmp/v2/scripts/verify.sh"; }
expect_fail "verify.sh: cargo not on PATH" "verify.sh: cargo metadata --locked failed" vnc

# rlimit ceilings ratchet (scripts/rlimit-ceilings.sh, in throwaway git repos like the acceptance.sh ones): an unlisted fn above 8M;
# a listed fn above its value; a raised value and a new line against history; a quic line; a stale line; a missing file; server with verus!.
rcrepo() {  # rcrepo <dir>: scripts, rl.py, the ceilings fixture and server src, one commit on main, then branch feat
    rm -rf "${tmp:?}/$1"; mkdir -p "$tmp/$1/tools"
    cp -r "$root/scripts" "$tmp/$1/scripts"; cp "$root/tools/rl.py" "$root/tools/ratchet_walk.py" "$tmp/$1/tools/"
    cp -r "$fx/rlimit/ceilings/crates" "$fx/rlimit/ceilings/logs" "$tmp/$1/"; cp "$fx/rlimit/ceilings/tools/rlimit-ceilings.txt" "$tmp/$1/tools/"
    git -C "$tmp/$1" init -q -b main
    git -C "$tmp/$1" add -A
    gitc "$1" commit -qm base
    gitc "$1" checkout -qb feat
    gitc "$1" commit -q --allow-empty -m feat
}
rceil() { "$tmp/$1/scripts/rlimit-ceilings.sh" "$tmp/$1" "$tmp/$1/logs"; }
rcrepo rc1
expect_pass "rlimit-ceilings" rceil rc1
: > "$tmp/rc1/tools/rlimit-ceilings.txt"
expect_fail "rlimit-ceilings: empty file with a fn above 8M" "is empty but 1 fns are above" rceil rc1
rm "$tmp/rc1/tools/rlimit-ceilings.txt"
expect_fail "rlimit-ceilings: missing file with a fn above 8M" "is missing but 1 fns are above" rceil rc1
rcrepo rc2
sed -i 's/11648578/11648577/' "$tmp/rc2/logs/tls.json"
expect_pass "rlimit-ceilings: fn below its ceiling" rceil rc2
sed -i 's/11648577/11648579/' "$tmp/rc2/logs/tls.json"
expect_fail "rlimit-ceilings: listed fn above its value" "exceeds its ceiling 11648578" rceil rc2
rcrepo rc3
sed -i 's/tls::flight::build_flight", "rlimit": 11648578/tls::flight::other", "rlimit": 8000001/' "$tmp/rc3/logs/tls.json"
expect_fail "rlimit-ceilings: unlisted fn above 8M" "unlisted fn above 8000000: tls::flight::other at 8000001" rceil rc3
rcrepo rc4
sed -i 's/11648578/11648579/' "$tmp/rc4/logs/tls.json" "$tmp/rc4/tools/rlimit-ceilings.txt"
expect_fail "rlimit-ceilings: raised value against the merge-base" "raised from 11648578 to 11648579" rceil rc4
rcrepo rc5
echo "tls tls::flight::extra 9000000" >> "$tmp/rc5/tools/rlimit-ceilings.txt"
sed -i 's/quic::conn::small", "rlimit": 120000/tls::flight::extra", "rlimit": 9000000/' "$tmp/rc5/logs/tls.json"
expect_fail "rlimit-ceilings: new line against the merge-base" "not in the merge-base file" rceil rc5
rcrepo rc6
echo "quic quic::conn::small 9000000" >> "$tmp/rc6/tools/rlimit-ceilings.txt"
sed -i 's/quic::conn::small", "rlimit": 120000/quic::conn::small", "rlimit": 9000000/' "$tmp/rc6/logs/tls.json"
expect_fail "rlimit-ceilings: a quic line" "quic/quictls have a hard 8000000 cap" rceil rc6
rcrepo rc7
sed -i 's/11648578/7999999/' "$tmp/rc7/logs/tls.json"
expect_fail "rlimit-ceilings: stale line (fn dropped below 8M)" "stale ceiling line" rceil rc7
rcrepo rc8
sed -i 's/tls::flight::build_flight/tls::flight::renamed/' "$tmp/rc8/logs/tls.json"
expect_fail "rlimit-ceilings: stale line (fn gone)" "delete the line" rceil rc8
rcrepo rc9
printf 'verus! {\n}\n' >> "$tmp/rc9/crates/server/src/lib.rs"
expect_fail "rlimit-ceilings: server containing verus!" "has proofs" rceil rc9
rcrepo rc12
printf '#[verifier::external_body]\npub fn f() {}\n' >> "$tmp/rc12/crates/server/src/lib.rs"
expect_fail "rlimit-ceilings: server with #[verifier" "has proofs" rceil rc12
rcrepo rc13
printf '#![verifier::loop_isolation(false)]\n' >> "$tmp/rc13/crates/server/src/lib.rs"
expect_fail "rlimit-ceilings: server with #![verifier" "has proofs" rceil rc13
rcrepo rc14
rm -r "$tmp/rc14/crates/server"
expect_fail "rlimit-ceilings: no server src" "crates/server/src is missing" rceil rc14
rcrepo rc15
cp "$tmp/rc15/logs/tls.json" "$tmp/rc15/logs/gone.json"
expect_fail "rlimit-ceilings: log of a crate that is not under crates/" "stale log" rceil rc15
rcrepo rc10
rm "$tmp/rc10/logs/tls.json"
expect_fail "rlimit-ceilings: no logs" "no JSON logs" rceil rc10
rcrepo rc11
gitc rc11 branch -m main trunk
expect_fail "rlimit-ceilings: no main" "cannot resolve the merge-base" rceil rc11

# citation gate (tools/citations.py, C1): the fixture crate has a predicate, a code-mapping spec fn and two close-code fns, each cited
# and (the close fns) named by a mutant row. cite: a predicate, a close-code fn and a mapping fn each with its citation stripped
# (also keeping only a `///` doc line, or a `//=` without a `//#` quote); a blank line between citation and fn; no crates/; no
# codes.rs; no predicate; no close-code fn. closes: a close-code fn with no row; a row naming it only in the origin column;
# an empty or missing tsv.
cfresh() { rm -rf "${tmp:?}/cit"; cp -r "$fx/citations" "$tmp/cit"; }
cit=$tmp/cit/crates/quic/src/conn.rs
cite() { python3 -I "$root/tools/citations.py" cite "$tmp/cit"; }
closes() { python3 -I "$root/tools/citations.py" closes "$tmp/cit" "$tmp/cit/tools/mutants.tsv"; }
cfresh
expect_pass "citations: cite (the uncited echo getter demo_info is not a close-code fn)" cite
expect_pass "citations: closes" closes
# strip_cite <fn-line pattern>: delete the //= and //# lines directly above the matching line (and its doc comment)
strip_cite() { awk -v pat="$1" '{ l[NR] = $0 } END { for (i = 1; i <= NR; i++) if (l[i] ~ pat) { j = i - 1; while (j > 0 && l[j] ~ /^(\/\/[=#]|\/\/\/|#\[)/) { if (l[j] ~ /^\/\/[=#]/) l[j] = "\001"; j-- } } for (i = 1; i <= NR; i++) if (l[i] != "\001") print l[i] }' "$cit" > "$cit.new"; mv "$cit.new" "$cit"; }
strip_cite '^pub open spec fn allowed_demo_err'
expect_fail "citations: predicate without a citation" "allowed_demo_err has no" cite
cfresh; strip_cite '^pub fn demo_close'
expect_fail "citations: close-code fn without a citation" "demo_close has no" cite
cfresh; strip_cite '^spec fn demo_code'
expect_fail "citations: code-mapping spec fn without a citation" "demo_code has no" cite
cfresh; strip_cite '^pub fn demo_map'
expect_fail "citations: a second close-code fn without a citation" "demo_map has no" cite
cfresh; sed -i '/^\/\/# /d' "$cit"
expect_fail "citations: citation lines without a quote" "has no" cite
cfresh; sed -i 's|^/// A parameter the RFC rejects.|\n/// A parameter the RFC rejects.|' "$cit"
expect_fail "citations: a blank line between the citation and the predicate" "allowed_demo_err has no" cite
cfresh; strip_cite '^pub open spec fn allowed_demo_err_from'
expect_fail "citations: an allowed_*err_from predicate without a citation" "allowed_demo_err_from has no" cite
cfresh; sed -i 's/Some((false, TRANSPORT_PARAMETER_ERROR/Some((false, k/' "$cit"; strip_cite '^pub fn demo_close'
expect_fail "citations: close code a name bound outside the fn's parameters, no citation" "demo_close has no" cite
cfresh; sed -i 's/Some((false, TRANSPORT_PARAMETER_ERROR/Some((false, k/' "$cit"; sed -i '/^D1/d' "$tmp/cit/tools/mutants.tsv"
expect_fail "citations: close code a name bound outside the fn's parameters, no row" "close-code fn quic::conn::demo_close has no row" closes
cfresh; sed -i 's/^        r is None ==> c.close_spec() is None,/&\n        r matches Some((a, k, v)) ==> k == 0x0a,/' "$cit"
expect_fail "citations: an echo getter whose code is constrained elsewhere in its ensures, no citation" "demo_info has no" cite
cfresh; sed -i 's/Some((false, TRANSPORT_PARAMETER_ERROR/Some((false, self.code/' "$cit"; strip_cite '^pub fn demo_close'
expect_fail "citations: close code a field expression, fn without a citation" "demo_close has no" cite
cfresh; sed -i 's/(false, demo_code(n)/(false, crate::conn::demo_code(n)/' "$cit"; strip_cite '^spec fn demo_code'
expect_fail "citations: path-qualified code-mapping call, mapping fn without a citation" "demo_code has no" cite
cfresh; sed -i 's|^//= https://|//= http://|' "$cit"
expect_fail "citations: citation with an http URL" "has no" cite
cfresh; sed -i 's|^\(//= https://www.rfc-editor.org/rfc/rfc9000\)#section-7.4|\1|' "$cit"
expect_fail "citations: citation without a section" "has no" cite
cfresh; rm -r "$tmp/cit/crates"
expect_fail "citations: no crates/" "cannot scan crates/" cite
cfresh; rm "$tmp/cit/crates/quic/src/codes.rs"
expect_fail "citations: no codes.rs" "cannot scan crates/" cite
cfresh; sed -i 's/^pub open spec fn allowed_demo_err/pub open spec fn demo_pred/' "$cit"
expect_fail "citations: no allowed predicate" "no allowed_*err spec fn" cite
cfresh; sed -i 's/final(c).close_spec() == Some/final(c).phase_spec() == Some/' "$cit"
expect_fail "citations: no close-code fn" "no close-code fn" cite
cfresh; sed -i '/^D1/d' "$tmp/cit/tools/mutants.tsv"
expect_fail "citations: close-code fn with no mutant row" "close-code fn quic::conn::demo_close has no row" closes
cfresh; sed -i 's/^D1\tquic\tconn\tdemo_close\t/D1\tquic\tconn\tdemo_other\t/; s/gate-demos$/gate-demos demo_close/' "$tmp/cit/tools/mutants.tsv"
expect_fail "citations: close-code fn named only in the origin column" "close-code fn quic::conn::demo_close has no row" closes
cfresh; sed -i 's/^D1\tquic\tconn\tdemo_close\t\(.*\)\tgate-demos$/D1\tquic\tconn\tdemo_other\t\1 demo_close\tgate-demos/' "$tmp/cit/tools/mutants.tsv"
expect_fail "citations: close-code fn named only in the regex column" "close-code fn quic::conn::demo_close has no row" closes
cfresh; : > "$tmp/cit/tools/mutants.tsv"
expect_fail "citations: empty tsv" "has no row" closes
rm "$tmp/cit/tools/mutants.tsv"
expect_fail "citations: no tsv" "cannot read" closes

# RFC-quantity gate (tools/rfc_quantity.py, C8). The fixture mirrors main's three predicates, its allowlist (digest qdig, one
# `root` digest per predicate) and open ratchet; bad/ holds the 9a originals verbatim: T6's recv_allowed_err (rfc_recv's
# running `high`), T4's duplicate rule (the `seen` mask), T3's crypto window (the read offset `s.reassembly().base()`).
# qredig re-pins every root and the allowlist (what a reviewer does after re-reviewing), so a demo can show that a read is
# still caught after the digests are updated; rqn runs with the re-pinned allowlist digest.
qx=$tmp/rfcq/crates/quic/src
qdig=36c9a7087dc8d06981727c66ddad8de36f60bc9e1322636693d8d4f1d21f39cc
rq() { python3 -I "$root/tools/rfc_quantity.py" --root "$tmp/rfcq" --allow-digest "$qdig" "$@"; }
qal=$tmp/rfcq/tools/rfc-quantity-allow.txt
qop=$tmp/rfcq/tools/rfc-quantity-open.txt
qadd() { sed -i '$d' "$qx/$1"; printf '%s\n\n} // verus!\n' "$2" >> "$qx/$1"; }  # qadd <file> <fn>: append a spec fn
qredig() {
    for r in $(awk -F'\t' '$1 == "root" { print $2 }' "$qal"); do
        d=$(rq --print-digest "$r")
        awk -F'\t' -v OFS='\t' -v r="$r" -v d="$d" '$1 == "root" && $2 == r { $3 = d } { print }' "$qal" > "$qal.n"; mv "$qal.n" "$qal"
    done
    qnow=$(rq --print-digest allowlist)
}
rqn() { python3 -I "$root/tools/rfc_quantity.py" --root "$tmp/rfcq" --allow-digest "$qnow" "$@"; }
RR=quic::recv_stream::recv_allowed_err
fresh rfcq
expect_pass "rfc-quantity" rq
fresh rfcq; cp "$tmp/rfcq/bad/t6-recv_stream.rs" "$qx/recv_stream.rs"
expect_fail "rfc-quantity: T6's original recv_allowed_err (8f6b48e) reads the running high" "final_size_trigger (from recv_allowed_err) reads \`s.high\` (a struct field)" rq
fresh rfcq; cp "$tmp/rfcq/bad/t4-tp.rs" "$qx/tp.rs"
expect_fail "rfc-quantity: T4's original duplicate rule (6594f10) reads the seen mask" "allowed_tp_err_from reads \`seen\` (a name used other than" rq
fresh rfcq; cp "$tmp/rfcq/bad/t3-crypto_stream.rs" "$qx/crypto_stream.rs"
expect_fail "rfc-quantity: T3's original crypto window (fcf9ff0^) reads the read offset" "crypto_allowed_err reads \`s.reassembly()\` (a method" rq
# review probes A, B, H: one-token edits that change no list; each changes its root's digest, so the vouches are re-reviewed
fresh rfcq; sed -i 's/                            None => false,/                            None => true,/' "$qx/tp.rs"
expect_fail "rfc-quantity: probe A, allowed_tp_err_from's walk arm None => true (the code's model decides)" "re-review the vouches for quic::tp::allowed_tp_err_from" rq
fresh rfcq; sed -i 's/Some((t2, seen2)) => allowed_tp_err_from(b, s, ids.insert(id), t2, seen2)/Some((t2, len)) => len > 1 || allowed_tp_err_from(b, s, ids.insert(id), t2, len)/' "$qx/tp.rs"
expect_fail "rfc-quantity: probe B, the seen mask rebound as len" "re-review the vouches for quic::tp::allowed_tp_err_from" rq
fresh rfcq; sed -i 's/final_size_trigger(s, off + len, fin)/final_size_trigger(s, conn_room, fin)/' "$qx/recv_stream.rs"
expect_fail "rfc-quantity: probe H, conn_room passed as a callee's vouched end" "re-review the vouches for $RR" rq
fresh rfcq; qadd crypto_stream.rs 'pub open spec fn allowed_win_err(w: nat, offset: u64, len: nat) -> bool { crypto_window_exceeded(w, offset, len) }'
expect_fail "rfc-quantity: probe C, a new predicate inheriting a callee's vouches" "no \`root\` line for quic::crypto_stream::allowed_win_err" rq
# re-review probes: text a vouch rests on outside the walk (pins), callees of unfollowed fns, constants, attributes, aliases
fresh rfcq; sed -i 's/^        let ins = s.ins.push((off, data));$/        let ins = if data.len() > 0 { s.ins.push((off, data)) } else { s.ins };/' "$qx/recv_stream.rs"
expect_fail "rfc-quantity: probe N1b, recv_data (pinned) skips empty frames" "re-review the vouches for $RR" rq
fresh rfcq; sed -i 's/recv_allowed_err(old(self).rfc(), off as nat, /recv_allowed_err(old(self).rfc(), 0, /' "$qx/recv_stream.rs"
expect_fail "rfc-quantity: probe E1, on_data (pinned) passes 0 for the frame's offset" "re-review the vouches for $RR" rq
fresh rfcq; sed -i 's/^        self.ins@$/        self.ins@.skip(1)/' "$qx/crypto_stream.rs"
expect_fail "rfc-quantity: probe N1a, Reassembly::inserted (pinned, called by the unfollowed crypto_contiguous) drops a frame" "re-review the vouches for quic::crypto_stream::crypto_allowed_err" rq
fresh rfcq; sed -i 's/^    1u32 << (id as u32)$/    0u32/' "$qx/tp.rs"
expect_fail "rfc-quantity: probe N3, tp_bit (called by the unfollowed rfc_tp_apply) returns 0" "re-review the vouches for quic::tp::allowed_tp_err_from" rq
fresh rfcq; sed -i 's/^pub const MAX_CRYPTO_BUFFER: u64 = 16384;$/pub const MAX_CRYPTO_BUFFER: u64 = 0;/' "$qx/crypto_stream.rs"
expect_fail "rfc-quantity: probe N2, a constant the predicate names changes" "re-review the vouches for quic::crypto_stream::crypto_allowed_err" rq
fresh rfcq; sed -i 's/^pub open spec fn tp_server_only/#[verifier::external_body]\n&/' "$qx/tp.rs"
expect_fail "rfc-quantity: probe N5, an attribute above a reached fn" "re-review the vouches for quic::tp::allowed_tp_err_from" rq
fresh rfcq; sed -i 's/^use vstd::prelude::\*;$/&\nuse crate::crypto_stream::rfc_contiguous as rfc_vint;/' "$qx/tp.rs"
expect_fail "rfc-quantity: probe N4, a use .. as alias of a name the hashed text calls" "renames a name that the text" rq
fresh rfcq; printf 'pin\t%s\tquic::recv_stream::no_such_fn\n' "$RR" >> "$qal"
expect_fail "rfc-quantity: a pin line naming no fn" "names quic::recv_stream::no_such_fn, which is not a fn" rq
fresh rfcq; sed -i 's/^    ||| end > s.limit$/& || s.high > 0 \/\/ rfc-quantity: s.limit: the largest maximum stream data sent (RFC 9000 §19.10)/' "$qx/recv_stream.rs"
sed -i '/\ts\.limit\t/d' "$qop"; qredig
expect_fail "rfc-quantity: probe I, s.high on a line whose annotation names s.limit (digests re-pinned)" "flow_trigger (from recv_allowed_err) reads \`s.high\`" rqn
fresh rfcq; sed -i 's/||| tp_server_only(id)$/||| tp_server_only(id) || b@.foo > 0/' "$qx/tp.rs"; qredig
expect_fail "rfc-quantity: a field after a view (b@.foo)" "allowed_tp_err_from reads \`b@.foo\` (a struct field)" rqn
fresh rfcq; qadd recv_stream.rs 'impl SpecRecv { pub open spec fn len(&self) -> nat { 0 } }'
expect_fail "rfc-quantity: a spec method named like a vstd method" "a spec method named like a vstd method (len)" rq
fresh rfcq; sed -i 's/^    ||| end > s.limit$/& \/\/ rfc-quantity:/' "$qx/recv_stream.rs"
expect_fail "rfc-quantity: an annotation with an empty reason" "\`// rfc-quantity:\` needs \`READ: <why" rq
fresh rfcq; sed -i 's/^    ||| end > s.limit$/& \/\/ rfc-quantity: s.limit: the largest MAX_STREAM_DATA sent/' "$qx/recv_stream.rs"
expect_fail "rfc-quantity: an annotation citing no RFC section" "\`// rfc-quantity:\` needs \`READ: <why" rq
fresh rfcq; sed -i 's/^    ||| end > s.limit$/& \/\/ rfc-quantity: the largest maximum stream data sent (RFC 9000 §19.10)/' "$qx/recv_stream.rs"
expect_fail "rfc-quantity: an annotation naming no read" "\`// rfc-quantity:\` needs \`READ: <why" rq
fresh rfcq; sed -i 's/^    ||| end > s.limit$/& \/\/ rfc-quantity: s.limit: the largest maximum stream data sent (RFC 9000 §19.10)/' "$qx/recv_stream.rs"
expect_fail "rfc-quantity: an annotation changes its root's digest" "re-review the vouches for $RR" rq
sed -i '/\ts\.limit\t/d' "$qop"; qredig
expect_pass "rfc-quantity: a cited annotation vouches for the read it names (open line deleted, digests re-pinned)" rqn
fresh rfcq; sed -i 's/^    ||| end > s.limit$/& \/\/ rfc-quantity: s.high: the largest received offset (RFC 9000 §19.10)/' "$qx/recv_stream.rs"; qredig
expect_fail "rfc-quantity: an annotation naming a read its line does not make" "\`// rfc-quantity: s.high:\` names no read on its line" rqn
fresh rfcq; printf 'use vstd::prelude::*;\n\nverus! {\n\npub open spec fn other(n: nat) -> bool {\n    n > 0 // rfc-quantity:\n}\n\n} // verus!\n' > "$qx/other.rs"
expect_fail "rfc-quantity: an empty annotation in a file no predicate reaches" "other.rs:6: \`// rfc-quantity:\` needs" rq
fresh rfcq; sed -i 's/final_size_trigger(s, off + len, fin)/crate::recv_stream::final_size_trigger(s, off + len, fin)/' "$qx/recv_stream.rs"; qredig
expect_pass "rfc-quantity: a path-qualified call is followed (digests re-pinned)" rqn
sed -i 's/c == FINAL_SIZE_ERROR \&\& /&crate::recv_stream::peek(s) \&\& /' "$qx/recv_stream.rs"
qadd recv_stream.rs 'pub open spec fn peek(s: SpecRecv) -> bool { s.high > 0 }'; qredig
expect_fail "rfc-quantity: a path-qualified call to a helper reading a field" "peek (from recv_allowed_err) reads \`s.high\`" rqn
fresh rfcq; sed -i 's/c == FINAL_SIZE_ERROR \&\& /crate::tp::peek(s) \&\& /' "$qx/recv_stream.rs"
qadd recv_stream.rs 'pub open spec fn peek(s: SpecRecv) -> bool { true }'
qadd tp.rs 'pub open spec fn peek(s: crate::recv_stream::SpecRecv) -> bool { s.high > 0 }'; qredig
expect_fail "rfc-quantity: a module-qualified call reaches that module's fn, not the caller's namesake" "peek (from recv_allowed_err) reads \`s.high\`" rqn
fresh rfcq; qadd tp.rs 'pub open spec fn peek(s: SpecTp) -> bool { true }'; qadd crypto_stream.rs 'pub open spec fn peek(s: CryptoStream) -> bool { true }'
sed -i 's/c == FINAL_SIZE_ERROR \&\& /peek(s) \&\& /' "$qx/recv_stream.rs"
expect_fail "rfc-quantity: an unqualified call the caller's module does not define, two modules do" "calls peek, which names 2 spec fns" rq
fresh rfcq; sed -i 's/None => largest_received_offset(s.ins),/None => largest_received_offset(SpecRecv { limit: 0, ..s }.ins),/' "$qx/recv_stream.rs"
expect_fail "rfc-quantity: a struct update reads the fields it does not set" "credit_before (from recv_allowed_err) reads \`..s\` (a struct update" rq
fresh rfcq; sed -i 's/c == FINAL_SIZE_ERROR \&\& /s.code_spec() == 0 \&\& \&/' "$qx/recv_stream.rs"
expect_fail "rfc-quantity: a *_spec() accessor" "recv_allowed_err reads \`s.code_spec()\` (a method" rq
fresh rfcq; sed -i 's/c == FINAL_SIZE_ERROR \&\& /vstd::arithmetic::power2::pow2(len) > 0 \&\& &/' "$qx/recv_stream.rs"
expect_fail "rfc-quantity: a call of a fn outside the scanned verus! blocks" "reads \`vstd::arithmetic::power2::pow2(..)\` (a fn that is not" rq
fresh rfcq; qadd recv_stream.rs 'pub open spec fn dup(n: nat) -> bool { n > 0 }'; qadd tp.rs 'pub open spec fn dup(n: nat) -> bool { n > 0 }'
sed -i 's/^    c == CRYPTO_BUFFER_EXCEEDED \&\& /&dup(len) \&\& /' "$qx/crypto_stream.rs"
expect_fail "rfc-quantity: a callee name two modules define" "calls dup, which names 2 spec fns" rq
fresh rfcq; sed -i 's/allowed_/permitted_/g' "$qx"/*.rs
expect_fail "rfc-quantity: no predicate" "no allowed_*err spec fn found" rq
fresh rfcq; rm "$qal"
expect_fail "rfc-quantity: no allowlist" "cannot read the allowlist" rq
fresh rfcq; rm "$qop"
expect_fail "rfc-quantity: no open ratchet" "cannot read the open ratchet" rq
fresh rfcq; rm -r "$tmp/rfcq/crates"
expect_fail "rfc-quantity: no crates/" "cannot scan crates/" rq
fresh rfcq; sed -i '/^root\tquic::tp::allowed_tp_err\t/d' "$qal"
expect_fail "rfc-quantity: a predicate without a root line" "no \`root\` line for quic::tp::allowed_tp_err:" rq
fresh rfcq; printf 'name\t%s\tquic::recv_stream::flow_trigger\tconn_room\tthe connection credit left (RFC 9000 §4.1)\n' "$RR" >> "$qal"
sed -i '/\tconn_room\t/d' "$qop"
expect_fail "rfc-quantity: the allowlist grows without ALLOW_DIGEST" "the allowlist's digest is not ALLOW_DIGEST" rq
fresh rfcq; sed -i '/\tquic::crypto_stream::crypto_allowed_err\tc\t/d' "$qal"; sed -i 's/c == CRYPTO_BUFFER_EXCEEDED \&\& //' "$qx/crypto_stream.rs"
printf 'name\t%s\tquic::recv_stream::flow_trigger\tconn_room\tthe connection credit left (RFC 9000 §4.1)\n' "$RR" >> "$qal"; sed -i '/\tconn_room\t/d' "$qop"
expect_fail "rfc-quantity: the allowlist swaps a stale line for a new one (same count)" "the allowlist's digest is not ALLOW_DIGEST" rq
fresh rfcq; sed -i 's/c == CRYPTO_BUFFER_EXCEEDED \&\& //' "$qx/crypto_stream.rs"; qredig
expect_fail "rfc-quantity: a stale allowlist line" "stale allowlist line, vouches for no read or call: name	quic::crypto_stream::crypto_allowed_err	quic::crypto_stream::crypto_allowed_err	c" rqn
fresh rfcq; sed -i 's/(RFC 9000 §19.8)$/(the frame)/' "$qal"
expect_fail "rfc-quantity: an allowlist reason citing no RFC section" "the reason cites no" rq
fresh rfcq; sed -i 's/credit_before(s) + conn_room/credit_before(s)/' "$qx/recv_stream.rs"; qredig
expect_fail "rfc-quantity: a stale open line" "stale open line, no such read" rqn
fresh rfcq; sed -i 's/\ts\.final_size\t4\t/\ts.final_size\t5\t/' "$qop"
expect_fail "rfc-quantity: an open count that is not the current count" "open line count 5, but" rq
fresh rfcq; sed -i 's/\t9c\t/\tlater\t/' "$qop"
expect_fail "rfc-quantity: an open line without an owner phase" "OWNER-PHASE" rq
fresh rfcq; grep -v $'\tconn_room\t' "$qop" > "$tmp/rfcq/old-open.txt"
expect_fail "rfc-quantity: an open line absent from the merge-base's" "open line not in the merge-base open ratchet" rq --old-open "$tmp/rfcq/old-open.txt"
fresh rfcq; sed 's/\ts\.final_size\t4\t/\ts.final_size\t3\t/' "$qop" > "$tmp/rfcq/old-open.txt"
expect_fail "rfc-quantity: an open count above the merge-base's" "open line count 4 above the merge-base's 3" rq --old-open "$tmp/rfcq/old-open.txt"
# scripts/rfc-quantity.sh's real git path, in a throwaway repo: a branch and main each add a read with its open line; no main.
qrepo() {  # qrepo <dir>: scripts, the two python tools and the fixture, one commit on main
    rm -rf "${tmp:?}/$1"; mkdir -p "$tmp/$1/tools"
    cp -r "$root/scripts" "$tmp/$1/scripts"; cp "$root/tools/acceptance.py" "$root/tools/rfc_quantity.py" "$root/tools/ratchet_walk.py" "$tmp/$1/tools/"
    cp -r "$fx/rfcq/crates" "$tmp/$1/crates"; cp "$fx/rfcq/tools/"*.txt "$tmp/$1/tools/"
    git -C "$tmp/$1" init -q -b main
    git -C "$tmp/$1" add -A
    gitc "$1" commit -qm base
}
qgrow() {  # qgrow <dir>: flow_trigger reads s.high, and the open ratchet lists it
    sed -i 's/^    ||| end > s.limit$/&\n    ||| end > s.high/' "$tmp/$1/crates/quic/src/recv_stream.rs"
    printf 'quic::recv_stream::recv_allowed_err\tquic::recv_stream::flow_trigger\ts.high\t1\t9c\trfc_recv'"'"'s running high (RFC 9000 §19.10)\n' >> "$tmp/$1/tools/rfc-quantity-open.txt"
    gitc "$1" commit -qam grow
}
qgate() { "$tmp/$1/scripts/rfc-quantity.sh" --allow-digest "$qdig"; }
qrepo q1; gitc q1 checkout -qb feat; qgrow q1
expect_fail "rfc-quantity.sh git: a branch adds an open line" "open line not in the merge-base open ratchet" qgate q1
qrepo q2; qgrow q2
expect_fail "rfc-quantity.sh git: main adds an open line (walk)" "ratchet-walk: tools/rfc-quantity-open.txt: HEAD is outside the floor" qgate q2
qrepo q3; gitc q3 branch -m main trunk
expect_fail "rfc-quantity.sh git: no main" "cannot resolve the merge-base" qgate q3
qrepo q4; gitc q4 checkout -qb feat; touch "$tmp/q4/x"; gitc q4 add x; gitc q4 commit -qm noop
expect_pass "rfc-quantity.sh git: unchanged open ratchet on a branch" qgate q4

# the baseline history walk (tools/ratchet_walk.py, R5): growth spread over direct commits on main, for each of the three
# ratchet files, with the last commit not growing it (so the HEAD^1 comparison alone passes).
gitrepo g5
echo "demo::extra" >> "$tmp/g5/tools/acceptance-baseline.txt"; gitc g5 commit -qam grow
touch "$tmp/g5/x"; gitc g5 add x; gitc g5 commit -qm noop
expect_fail "acceptance.sh git: growth over two direct commits on main" "ratchet-walk: tools/acceptance-baseline.txt: HEAD is outside the floor" gaccept g5
rcrepo rc12; gitc rc12 checkout -q main; gitc rc12 merge -q feat
echo "tls tls::flight::extra 9000000" >> "$tmp/rc12/tools/rlimit-ceilings.txt"
sed -i 's/quic::conn::small", "rlimit": 120000/tls::flight::extra", "rlimit": 9000000/' "$tmp/rc12/logs/tls.json"
gitc rc12 commit -qam grow; touch "$tmp/rc12/x"; gitc rc12 add x; gitc rc12 commit -qm noop
expect_fail "rlimit-ceilings.sh git: growth over two direct commits on main" "ratchet-walk: tools/rlimit-ceilings.txt: HEAD is outside the floor" rceil rc12
rcrepo rc13; gitc rc13 checkout -q main; gitc rc13 merge -q feat
sed -i 's/11648578/11648579/' "$tmp/rc13/logs/tls.json" "$tmp/rc13/tools/rlimit-ceilings.txt"; gitc rc13 commit -qam raise
touch "$tmp/rc13/x"; gitc rc13 add x; gitc rc13 commit -qm noop
expect_fail "rlimit-ceilings.sh git: a raised value over two direct commits on main" "above its lowest earlier value 11648578" rceil rc13
qrepo q5; qgrow q5; touch "$tmp/q5/x"; gitc q5 add x; gitc q5 commit -qm noop
expect_fail "rfc-quantity.sh git: growth over two direct commits on main" "ratchet-walk: tools/rfc-quantity-open.txt: HEAD is outside the floor" qgate q5
# the walk itself, on a plain file: a shrink then a re-grow, a legitimate shrink, a deletion then a re-add, a shallow clone.
walk() { python3 -I "$root/tools/ratchet_walk.py" "$tmp/$1" "$2" "$3"; }
wrepo() {  # wrepo <dir> <file> <content>: one commit on main
    rm -rf "${tmp:?}/$1"; mkdir -p "$tmp/$1/$(dirname "$2")"; git -C "$tmp/$1" init -q -b main
    printf '%s\n' "$3" > "$tmp/$1/$2"; git -C "$tmp/$1" add -A; gitc "$1" commit -qm base
}
wrepo w1 f 'a
b'
printf 'a\n' > "$tmp/w1/f"; gitc w1 commit -qam shrink
expect_pass "ratchet-walk: a legitimate shrink" walk w1 f lines
printf 'a\nb\n' > "$tmp/w1/f"; gitc w1 commit -qam regrow
expect_fail "ratchet-walk: a shrink then a re-grow" "HEAD is outside the floor" walk w1 f lines
wrepo w2 f 'c 
c fn 9000000'
printf 'c fn 9000000\n' > "$tmp/w2/f"; gitc w2 commit -qam noop
expect_fail "ratchet-walk: an unreadable ceilings line" "unreadable ceilings line" walk w2 f ceilings
wrepo w3 f 'c fn 9000000'
printf 'c fn 8500000\n' > "$tmp/w3/f"; gitc w3 commit -qam shrink
expect_pass "ratchet-walk: a lowered ceiling" walk w3 f ceilings
git -C "$tmp/w3" rm -q f; gitc w3 commit -qm delete
printf 'c fn 8600000\n' > "$tmp/w3/f"; git -C "$tmp/w3" add f; gitc w3 commit -qm readd
expect_fail "ratchet-walk: a deletion then a re-add above the last copy" "above its lowest earlier value 8500000" walk w3 f ceilings
rm -rf "${tmp:?}/w4"; git clone -q --depth 1 "file://$tmp/w1" "$tmp/w4"
expect_fail "ratchet-walk: a shallow clone" "shallow" walk w4 f lines
wrepo w6 f 'a
b'
printf 'a\n' > "$tmp/w6/f"; gitc w6 commit -qam shrink
printf 'a\nb\n' > "$tmp/w6/f"
expect_fail "ratchet-walk: an uncommitted re-grow after a committed shrink" "the working tree is outside the floor" walk w6 f lines
wrepo w7 f 'c fn 9000000
c fn 8000001'
expect_fail "ratchet-walk: a duplicate ceilings key in a committed copy" "duplicate ceilings line" walk w7 f ceilings
# floor semantics: growth shrunk back before HEAD passes (a fast-forwarded WIP commit); growth beyond the floor fails.
wrepo w8 f 'a
b'
printf 'a\nb\nc\n' > "$tmp/w8/f"; gitc w8 commit -qam wip
printf 'a\n' > "$tmp/w8/f"; gitc w8 commit -qam fix
expect_pass "ratchet-walk: transient growth shrunk back (a fast-forward of a branch)" walk w8 f lines
printf 'a\nb\n' > "$tmp/w8/f"; gitc w8 commit -qam regrow
expect_fail "ratchet-walk: a shrink then a re-grow beyond the shrunk floor" "HEAD is outside the floor" walk w8 f lines
# no reset: a raised ceiling fails, and a commit message that looks like a trailer changes nothing.
wrepo w9 tools/c 'c fn 9000000'
printf 'c fn 9100000\n' > "$tmp/w9/tools/c"; printf 'x\n' > "$tmp/w9/Cargo.lock"; git -C "$tmp/w9" add -A
gitc w9 commit -qm "upgrade" -m "Ratchet-Reset: tools/c: measured values shift"
expect_fail "ratchet-walk: a raised ceiling fails whatever the commit message says" "above its lowest earlier value 9000000" walk w9 tools/c ceilings
wrepo w5 f 'a'
expect_fail "ratchet-walk: a git error (path outside any repo)" "failed" walk w5/nonexistent f lines

# mutant registry (scripts/mutants.sh, C6), in throwaway git repos holding the acceptance fixture crate as crates/demo/src/acc.rs
# and the one-row registry of tools/gate-demos/mutants. check: a patch that no longer applies, a missing patch, an empty or
# missing tsv, a duplicate id, an orphan patch, a patch outside its row's crate, a bad regex, a wildcard fn, a patch
# that applies only at an offset, an allowed_*err predicate with no row or named only in a row's origin. Path-dependency
# patches and the loop-invariant kinds have their own fixture (mutants-dep, below). run (real Verus, seconds:
# MUTANTS_TARGET_DIR keeps vstd built across runs): the killed mutant (with its named test) passes; a mutant that still
# verifies, a named test that does not FAIL, one that fails unmutated, a misspelt test and a missing fn fail; a dirty
# crates/ is refused, and so is a Verus other than the pin's or none at all. The verdict on canned Verus output: rlimit, no
# or two JSON objects, another fn checked, a non-matching error kind, another Verus version or commit, no verus object. The
# main gate (every commit at main's tip): passes after a --no-ff merge or a fast-forward with a fresh run file, and the fresh
# run there reproduces it; fails with none (also detached), crates/ or Cargo.toml changed after the run, a fast-forward
# without a run, main's own crates/ change in the merge, a fail line, a missing or extra id, an edited tsv or patch, a `#`
# line naming another Verus or none, or no main; on the branch, check only. A run file forged from git alone (audit F4)
# passes the gate but fails the fresh run. mutants.py same: equal, differing, missing and empty files.
pin_v=$(sed -n 's/^version //p' "$root/tools/verus-pin.txt"); pin_c=$(sed -n 's/^commit //p' "$root/tools/verus-pin.txt")
[ -n "$pin_v" ] && [ -n "$pin_c" ] || die "tools/verus-pin.txt lacks a version or commit line"
export MUTANTS_TARGET_DIR="${MUTANTS_DEMO_TARGET:-$root/target/mutants-demo}"
mrepo() {  # mrepo <dir>: scripts, tools/mutants.py and the fixture, one commit on main, then branch feat
    rm -rf "${tmp:?}/$1"; mkdir -p "$tmp/$1/tools"
    cp -r "$root/scripts" "$tmp/$1/scripts"; cp "$root/tools/mutants.py" "$root/tools/acceptance.py" "$root/tools/verus-pin.txt" "$tmp/$1/tools/"
    cp -r "$fx/mutants/Cargo.toml" "$fx/mutants/Cargo.lock" "$fx/mutants/crates" "$root/rust-toolchain.toml" "$tmp/$1/"
    cp -r "$fx/mutants/tools/mutants.tsv" "$fx/mutants/tools/mutants" "$tmp/$1/tools/"
    cp "$fx/acceptance/crates/demo/src/lib.rs" "$tmp/$1/crates/demo/src/acc.rs"
    printf '/.worktrees/\n/target/\n' > "$tmp/$1/.gitignore"
    git -C "$tmp/$1" init -q -b main
    git -C "$tmp/$1" add -A
    gitc "$1" commit -qm base
    gitc "$1" checkout -qb feat
}
mut() { d=$1; shift; "$tmp/$d/scripts/mutants.sh" "$@"; }
mrepo m1
expect_pass "mutants check" mut m1 check
sed -i 's/if n > 10 { Err(7) }/if n > 10 { Err(9) }/' "$tmp/m1/crates/demo/src/acc.rs"
expect_fail "mutants check: patch that does not apply" "D-kill.patch does not apply" mut m1 check
mrepo m2
rm "$tmp/m2/tools/mutants/D-kill.patch"
expect_fail "mutants check: missing patch" "cannot read" mut m2 check
mrepo m2
sed -i '/^D-kill/d' "$tmp/m2/tools/mutants.tsv"; rm "$tmp/m2/tools/mutants/D-kill.patch"
expect_fail "mutants check: empty tsv" "has no rows" mut m2 check
rm "$tmp/m2/tools/mutants.tsv"
expect_fail "mutants check: no tsv" "mutants: no " mut m2 check
mrepo m2
sed -i 's/^D-kill.*/&\n&/' "$tmp/m2/tools/mutants.tsv"
expect_fail "mutants check: duplicate id" "duplicate id D-kill" mut m2 check
mrepo m2
cp "$fx/mutants/live.patch" "$tmp/m2/tools/mutants/D-live.patch"
expect_fail "mutants check: patch without a row" "patch without a row: D-live" mut m2 check
mrepo m2
sed -i 's#crates/demo/#crates/wire/#g' "$tmp/m2/tools/mutants/D-kill.patch"
expect_fail "mutants check: patch outside its row's crate" "outside crates/demo/ and its path dependencies (none)" mut m2 check
mrepo m2
sed -i 's/postcondition not satisfied/postcondition (not/' "$tmp/m2/tools/mutants.tsv"
expect_fail "mutants check: regex that does not compile" "regex does not compile" mut m2 check
mrepo m2
sed -i 's/\tacc\tdemo\t/\tacc\tdemo*\t/' "$tmp/m2/tools/mutants.tsv"
expect_fail "mutants check: wildcard fn" "must be a plain path" mut m2 check
mrepo m2
sed -i '1i // one line more' "$tmp/m2/crates/demo/src/acc.rs"
expect_fail "mutants check: patch that applies only at an offset" "applies only with an offset" mut m2 check
mrepo m2
sed -i 's/^verus! {$/verus! {\npub open spec fn other_allowed_err(c: u64) -> bool { c == 9 }/' "$tmp/m2/crates/demo/src/acc.rs"
expect_fail "mutants check: an allowed_*err predicate with no row" "allowed predicate with no mutant row (name it in a row's fn or regex column): other_allowed_err" mut m2 check

mrepo m2
sed -i 's/^verus! {$/verus! {\npub open spec fn other_allowed_err(c: u64) -> bool { c == 9 }/' "$tmp/m2/crates/demo/src/acc.rs"
sed -i 's/^\(D-kill.*\)$/\1 other_allowed_err/' "$tmp/m2/tools/mutants.tsv"
expect_fail "mutants check: an allowed_*err predicate named only in a row's origin" "allowed predicate with no mutant row (name it in a row's fn or regex column): other_allowed_err" mut m2 check

# run, for real: the fixture's mutant is killed (and the run file written); a mutant that still verifies; a dirty tree.
mrepo m3
expect_pass "mutants run: killed mutant" mut m3 run
grep -qx "crates $(git -C "$tmp/m3" rev-parse HEAD:crates)" "$tmp/m3/tools/mutants-last-run.txt" || die "mutants run: run file lacks the crates tree"
[ -z "$(git -C "$tmp/m3" worktree list --porcelain | grep '^worktree .*/mutants-')" ] || die "mutants run: worktree left behind"
[ "$(git -C "$tmp/m3" status --porcelain)" = "?? tools/mutants-last-run.txt" ] || die "mutants run: the caller's tree changed beyond the run file:
$(git -C "$tmp/m3" status --porcelain)"
echo "gate-demos: mutants run: caller's tree unchanged except tools/mutants-last-run.txt"
mrepo m4
cp "$fx/mutants/live.patch" "$tmp/m4/tools/mutants/D-live.patch"
printf 'D-live\tdemo\tacc\tdemo\t-\tpostcondition not satisfied\tgate-demos: n > 11 keeps the clause\n' >> "$tmp/m4/tools/mutants.tsv"
gitc m4 add -A; gitc m4 commit -qm live
expect_fail "mutants run: a mutant that still verifies" "the mutant still verifies acc::demo" mut m4 run D-live
[ -z "$(git -C "$tmp/m4" worktree list --porcelain | grep '^worktree .*/mutants-')" ] || die "mutants run: worktree left behind after a failure"
mkdir -p "$tmp/fakeverus"; printf '#!/bin/sh\necho Verus\necho "  Version: 0.2025.01.01.0000000"\n' > "$tmp/fakeverus/verus"; chmod +x "$tmp/fakeverus/verus"
expect_fail "mutants run: another Verus on VERUS_HOME" "verus --version names 0.2025.01.01.0000000, tools/verus-pin.txt says $pin_v" env VERUS_HOME="$tmp/fakeverus" "$tmp/m4/scripts/mutants.sh" run
expect_fail "mutants run: no Verus at all (VERUS_HOME missing, none on PATH)" "verus --version failed" env VERUS_HOME="$tmp/noverus" PATH=/usr/bin:/bin "$tmp/m4/scripts/mutants.sh" run
mrepo m5
printf '// dirty\n' >> "$tmp/m5/crates/demo/src/acc.rs"
expect_fail "mutants run: uncommitted crates/" "uncommitted changes" mut m5 run
# run's tests branch and fn name: each row edit is committed (run uses HEAD), then one real run.
mrow() {  # mrow <dir> <sed expr on the D-kill row>: a fresh repo whose row is edited and committed
    mrepo "$1"; sed -i "/^D-kill/$2" "$tmp/$1/tools/mutants.tsv"; gitc "$1" commit -qam row
}
mrow m6 's/acc:demo_eleven_is_err7/acc:demo_three_is_ok/'
expect_fail "mutants run: a named test that still passes on the mutant" "test demo/acc:demo_three_is_ok did not print '... FAILED'" mut m6 run D-kill
mrow m6 's/acc:demo_eleven_is_err7/acc:demo_three_is_err/'
expect_fail "mutants run: a named test that fails unmutated" "unmutated: test demo/acc:demo_three_is_err did not print '... ok'" mut m6 run D-kill
mrow m6 's/acc:demo_eleven_is_err7/acc:demo_eleven_is_er7/'
expect_fail "mutants run: a misspelt test name" "test demo/acc:demo_eleven_is_er7 did not print '... ok'" mut m6 run D-kill
mrow m6 's/\tacc\tdemo\t/\tacc\tdemo2\t/'
expect_fail "mutants run: a fn name that is not in the module" "D-kill.clean.json: a VIR error, or not a --verify-function run" mut m6 run D-kill

# a patch in a path dependency, and the loop-invariant kinds (tools/gate-demos/mutants-dep: crate top depends on dep).
# check: a dependency patch passes; a patch outside the row's crate and its path dependencies, and a row crate without a
# Cargo.toml, fail. run: the dependency patch is killed in top only after dep verifies whole on its own, and both loop-
# invariant kinds are kills; a dependency patch that breaks dep's own proof is refused, though top's fn fails on it too.
mdrepo() {  # mdrepo <dir>: as mrepo, with the mutants-dep fixture
    rm -rf "${tmp:?}/$1"; mkdir -p "$tmp/$1/tools"
    cp -r "$root/scripts" "$tmp/$1/scripts"; cp "$root/tools/mutants.py" "$root/tools/acceptance.py" "$root/tools/verus-pin.txt" "$tmp/$1/tools/"
    cp -r "$fx/mutants-dep/Cargo.toml" "$fx/mutants-dep/Cargo.lock" "$fx/mutants-dep/crates" "$root/rust-toolchain.toml" "$tmp/$1/"
    cp -r "$fx/mutants-dep/tools/mutants.tsv" "$fx/mutants-dep/tools/mutants" "$tmp/$1/tools/"
    printf '/.worktrees/\n/target/\n' > "$tmp/$1/.gitignore"
    git -C "$tmp/$1" init -q -b main
    git -C "$tmp/$1" add -A
    gitc "$1" commit -qm base
    gitc "$1" checkout -qb feat
}
mdrepo d1
expect_pass "mutants check: a patch in a path dependency" mut d1 check
expect_pass "mutants run: a dependency patch killed in the dependent crate, and both loop-invariant kinds" mut d1 run
mdrepo d2
sed -i 's/^X-before\ttop\t/X-before\tdep\t/' "$tmp/d2/tools/mutants.tsv"
expect_fail "mutants check: a patch outside the row's crate and its path dependencies" "outside crates/dep/ and its path dependencies (none)" mut d2 check
mdrepo d2
rm "$tmp/d2/crates/top/Cargo.toml"
expect_fail "mutants check: the row's crate has no Cargo.toml" "cannot read" mut d2 check
mdrepo d3
cp "$fx/mutants-dep/depbad.patch" "$tmp/d3/tools/mutants/X-depbad.patch"
printf 'X-depbad\ttop\tm\tquad\t-\tpostcondition not satisfied.*r == 4 \\* n\tgate-demos: double ensures 2n + 1, code unchanged\n' >> "$tmp/d3/tools/mutants.tsv"
gitc d3 add -A; gitc d3 commit -qm depbad
expect_fail "mutants run: a dependency patch that breaks the dependency's own proof" "the patched dependency dep does not verify on its own" mut d3 run X-depbad

# the verdict on canned Verus output (tools/mutants.py killed/clean): a passing kill first.
v=$tmp/verdict
vj() {  # vj <errors> <success> [extra fn]: a one-object Verus JSON with demo::acc::demo checked
    x=; [ -z "${3:-}" ] || x=", {\"function\": \"$3\", \"rlimit\": 5, \"success\": true}"
    printf '{"verus": {"version": "%s", "commit": "%s", "toolchain": "1.98.1-x86_64-unknown-linux-gnu"}, "verification-results": {"encountered-error": false, "encountered-vir-error": false, "verified": %s, "errors": %s, "is-verifying-entire-crate": false}, "times-ms": {"smt": {"smt-run-module-times": [{"function-breakdown": [{"function": "demo::acc::demo", "rlimit": 900, "success": %s}%s]}]}}}\n' \
        "${VJ_VERSION:-$pin_v}" "${VJ_COMMIT:-$pin_c}" "$((1 - $1))" "$1" "$2" "$x" > "$v.json"
}
vlog() { printf 'error: %s\n   --> crates/demo/src/acc.rs:11:9\n    |\n11  |         r is Err ==> allowed_demo_err(n, r->Err_0),\n' "$1" > "$v.log"; }
killed() { python3 -I "$root/tools/mutants.py" killed "$v" demo acc demo 'postcondition not satisfied.*allowed_demo_err'; }
vj 1 false; vlog "postcondition not satisfied"
expect_pass "mutants verdict" killed
printf 'error: function body check: Resource limit (rlimit) exceeded\n' >> "$v.log"
expect_fail "mutants verdict: rlimit is not a kill" "rlimit text" killed
vlog "possible arithmetic underflow/overflow"
expect_fail "mutants verdict: another error kind" "no postcondition/precondition/assertion/invariant block matches" killed
vlog "postcondition not satisfied"; : > "$v.json"
expect_fail "mutants verdict: no JSON (cached build or compile error)" "0 Verus result objects" killed
vj 1 false; cat "$v.json" "$v.json" > "$v.2"; mv "$v.2" "$v.json"
expect_fail "mutants verdict: two JSON objects" "2 Verus result objects" killed
vj 1 false demo::acc::other
expect_fail "mutants verdict: another fn checked too" "want exactly demo::acc::demo" killed
vj 0 true
expect_fail "mutants verdict: still verifies" "the mutant still verifies" killed
VJ_VERSION=0.2025.01.01.0000000 vj 1 false
expect_fail "mutants verdict: another Verus version" "verus.version is '0.2025.01.01.0000000', the pin says '$pin_v'" killed
VJ_COMMIT=0000000000000000000000000000000000000000 vj 1 false
expect_fail "mutants verdict: another Verus commit" "verus.commit is '0000000000000000000000000000000000000000'" killed
vj 1 false; sed -i 's/"verus": {[^}]*}, //' "$v.json"
expect_fail "mutants verdict: no verus object" "no verus object" killed
vj 1 false
expect_fail "mutants verdict: the unmutated fn fails" "unmutated acc::demo" python3 -I "$root/tools/mutants.py" clean "$v" demo acc demo

# the main gate (mutants.sh verify at main's tip, merge or not), on m3's real run file.
mmerge() { gitc "$1" checkout -q main; gitc "$1" reset -q --hard "$mbase"; gitc "$1" merge -q --no-ff feat -m merge; }
mbranch() { gitc "$1" checkout -q feat; gitc "$1" reset -q --hard "$2"; }
mbase=$(git -C "$tmp/m3" rev-parse main)
gitc m3 add tools/mutants-last-run.txt; gitc m3 commit -qm "mutants run"
fresh_run=$(git -C "$tmp/m3" rev-parse HEAD)
expect_pass "mutants verify on the branch (check only, no run file needed there)" mut m3 verify
mmerge m3
expect_pass "mutants verify: merge --no-ff with a fresh run file" mut m3 verify
printf '%s\n' "$out" | grep -qxF "mutants: fresh run at main's tip matches the committed run file (1 mutants)" || die "mutants verify at main's tip: no fresh-run line:
$out"
[ -z "$(git -C "$tmp/m3" status --porcelain)" ] || die "mutants verify at main's tip: the fresh run changed the tree"
echo "gate-demos: mutants verify: the fresh run at main's tip reproduces the honest run file and leaves the tree clean"
expect_fail "mutants verify at main's tip: no Verus (the fresh run cannot run)" "verus --version failed" env VERUS_HOME="$tmp/noverus" PATH=/usr/bin:/bin "$tmp/m3/scripts/mutants.sh" verify
gitc m3 checkout -q main; gitc m3 reset -q --hard "$mbase"; gitc m3 merge -q --ff-only feat
expect_pass "mutants verify: fast-forward to a branch tip with a fresh run file" mut m3 verify
mbranch m3 "$fresh_run"; gitc m3 rm -q tools/mutants-last-run.txt; gitc m3 commit -qm "no run file"; mmerge m3
expect_fail "mutants verify: merge without a run file" "git show HEAD:tools/mutants-last-run.txt failed" mut m3 verify
gitc m3 checkout -q --detach main
expect_fail "mutants verify: the same merge checked out detached (a CI checkout)" "git show HEAD:tools/mutants-last-run.txt failed" mut m3 verify
gitc m3 checkout -q main
mbranch m3 "$fresh_run"; printf '// later\n' >> "$tmp/m3/crates/demo/src/lib.rs"; gitc m3 commit -qam "crates change after the run"
expect_fail "mutants verify on a branch: crates changed after the run (shows before the merge)" "is stale" mut m3 verify
mmerge m3
expect_fail "mutants verify: stale run file (crates changed after the run)" "is stale" mut m3 verify
gitc m3 checkout -q main; gitc m3 reset -q --hard "$mbase"; gitc m3 merge -q --ff-only feat
expect_fail "mutants verify: fast-forward commit on main without a run" "is stale" mut m3 verify
mbranch m3 "$fresh_run"; gitc m3 checkout -q main; gitc m3 reset -q --hard "$mbase"
printf '// main moved\n' >> "$tmp/m3/crates/demo/src/lib.rs"; gitc m3 commit -qam "crates change on main"
gitc m3 merge -q --no-ff feat -m merge
expect_fail "mutants verify: main changed crates/ since the fork (merge tree differs from the run's)" "is stale" mut m3 verify
mbranch m3 "$fresh_run"; printf '# root manifest edit\n' >> "$tmp/m3/Cargo.toml"; gitc m3 commit -qam "Cargo.toml change after the run"; mmerge m3
expect_fail "mutants verify: root Cargo.toml changed after the run" "is stale" mut m3 verify
mbranch m3 "$fresh_run"; sed -i 's/^D-kill pass /D-kill fail /' "$tmp/m3/tools/mutants-last-run.txt"; gitc m3 commit -qam "fail line"; mmerge m3
expect_fail "mutants verify: a fail line" "D-kill did not pass" mut m3 verify
mbranch m3 "$fresh_run"; sed -i '/^D-kill /d' "$tmp/m3/tools/mutants-last-run.txt"; gitc m3 commit -qam "missing id"; mmerge m3
expect_fail "mutants verify: a missing id" "missing D-kill" mut m3 verify
mbranch m3 "$fresh_run"; echo "D-extra pass 0000" >> "$tmp/m3/tools/mutants-last-run.txt"; gitc m3 commit -qam "extra id"; mmerge m3
expect_fail "mutants verify: an extra id in the run file" "extra D-extra" mut m3 verify
mbranch m3 "$fresh_run"; sed -i 's/gate-demos: Err(8)/gate-demos: Err (8)/' "$tmp/m3/tools/mutants.tsv"; gitc m3 commit -qam "tsv edited"; mmerge m3
expect_fail "mutants verify: tsv changed after the run" "was written for another tools/mutants.tsv" mut m3 verify
mbranch m3 "$fresh_run"; sed -i 's/^index .*/index 0000000..1111111 100644/' "$tmp/m3/tools/mutants/D-kill.patch"; gitc m3 commit -qam "patch edited"; mmerge m3
expect_fail "mutants verify: patch edited after the run" "was run with another patch" mut m3 verify
mbranch m3 "$fresh_run"; sed -i 's/ under Verus [^;]*;/ under Verus 0.2025.01.01.0000000;/' "$tmp/m3/tools/mutants-last-run.txt"; gitc m3 commit -qam "other Verus"; mmerge m3
expect_fail "mutants verify: a run file naming another Verus" "names Verus 0.2025.01.01.0000000, the pin says $pin_v" mut m3 verify
mbranch m3 "$fresh_run"; sed -i '/^#/d' "$tmp/m3/tools/mutants-last-run.txt"; gitc m3 commit -qam "no # line"; mmerge m3
expect_fail "mutants verify: a run file naming no Verus" "names Verus none" mut m3 verify
gitc m3 checkout -q feat
gitc m3 branch -m main trunk
expect_fail "mutants verify: no main" "cannot resolve main" mut m3 verify
# audit F4: a run file computed from git alone (no mutant run) for a registry with a live mutant passes the gate; the fresh
# run at main's tip refuses it.
mrepo m7
cp "$fx/mutants/live.patch" "$tmp/m7/tools/mutants/D-live.patch"
printf 'D-live\tdemo\tacc\tdemo\t-\tpostcondition not satisfied\tgate-demos: n > 11 keeps the clause\n' >> "$tmp/m7/tools/mutants.tsv"
gitc m7 add -A; gitc m7 commit -qm live
{
    echo "# tools/mutants-last-run.txt: forged from git on 2026-11-09T00:00Z under Verus $pin_v; verify.sh's main gate reads it"
    echo "crates $(git -C "$tmp/m7" rev-parse HEAD:crates)"
    echo "tree $(python3 -I "$tmp/m7/tools/mutants.py" tree "$tmp/m7" HEAD)"
    echo "tsv $(git -C "$tmp/m7" rev-parse HEAD:tools/mutants.tsv)"
    for i in $(awk -F'\t' '!/^#/ && NF { print $1 }' "$tmp/m7/tools/mutants.tsv"); do
        echo "$i pass $(git -C "$tmp/m7" rev-parse "HEAD:tools/mutants/$i.patch")"
    done
} > "$tmp/m7/tools/mutants-last-run.txt"
gitc m7 add -A; gitc m7 commit -qm "forged run file"
gitc m7 checkout -q main; gitc m7 merge -q --no-ff feat -m merge
expect_pass "mutants gate: a run file forged from git passes the text gate alone" python3 -I "$tmp/m7/tools/mutants.py" gate "$tmp/m7"
expect_fail "mutants verify: a forged run file at main's tip (fresh run)" "the mutant still verifies acc::demo" mut m7 verify
# same: the committed file against a fresh run, `#` lines aside.
sd=$tmp/same; mkdir -p "$sd"
printf '# a\ncrates 1\nD-kill pass 2\n' > "$sd/a"; printf '# b\ncrates 1\nD-kill pass 2\n' > "$sd/b"
expect_pass "mutants same" python3 -I "$root/tools/mutants.py" same "$sd/a" "$sd/b"
printf '# b\ncrates 1\nD-kill fail 2\n' > "$sd/b"
expect_fail "mutants same: a differing line" "+D-kill fail 2" python3 -I "$root/tools/mutants.py" same "$sd/a" "$sd/b"
printf '# only a comment\n' > "$sd/b"
expect_fail "mutants same: a fresh file with no run lines" "$sd/b has no run lines" python3 -I "$root/tools/mutants.py" same "$sd/a" "$sd/b"
expect_fail "mutants same: no fresh file" "cannot read" python3 -I "$root/tools/mutants.py" same "$sd/a" "$sd/none"

# declassify gate (scripts/declassify-gate.sh ROOT REPORT GATEDIR): a report site with no TRUSTED.md row; counts that differ; a source
# line the report lacks; a lost secret label; no report; an empty report; a report without sites.
dg() { "$root/scripts/declassify-gate.sh" "$tmp/dg" "$tmp/dg/report.txt" "$tmp/dg/gate"; }
fresh declassify; rm -rf "$tmp/dg"; mv "$tmp/declassify" "$tmp/dg"
expect_pass "declassify-gate" dg
sed -i 's/a::f#1/a::f#2/' "$tmp/dg/report.txt"
expect_fail "declassify-gate: report site with no TRUSTED.md row" "crypto::a::f#2 has no TRUSTED.md ct-declassify row" dg
fresh declassify; rm -rf "$tmp/dg"; mv "$tmp/declassify" "$tmp/dg"
printf '| ct-declassify: crypto::a::g#1: y | crates/crypto/src/a.rs:9 | demo | never |\n' >> "$tmp/dg/TRUSTED.md"
expect_fail "declassify-gate: extra TRUSTED.md row" "1 report sites but 2 TRUSTED.md ct-declassify rows" dg
sed -i '$d' "$tmp/dg/TRUSTED.md"
printf 'fn h(x: bool) -> bool { crate::ct::declassify(x) }\n' >> "$tmp/dg/crates/crypto/src/a.rs"
expect_fail "declassify-gate: declassify( line the report lacks" "1 report sites but 2 declassify( lines" dg
fresh declassify; rm -rf "$tmp/dg"; mv "$tmp/declassify" "$tmp/dg"
sed -i 's/secret=d,msg,salt/secret=msg,salt/' "$tmp/dg/report.txt"
expect_fail "declassify-gate: lost secret label" "rsa_pss_sign_inner lost its secret labels" dg
fresh declassify; rm -rf "$tmp/dg"; mv "$tmp/declassify" "$tmp/dg"
sed -i 's/a.rs:2 /a.rs:3 /' "$tmp/dg/TRUSTED.md"
expect_fail "declassify-gate: row at another line" "report sites and TRUSTED.md rows differ" dg
rm "$tmp/dg/report.txt"
expect_fail "declassify-gate: no report" "declassify-gate: no $tmp/dg/report.txt" dg
: > "$tmp/dg/report.txt"
expect_fail "declassify-gate: empty report" "is empty" dg
grep -v '^declassify ' "$fx/declassify/report.txt" > "$tmp/dg/report.txt"
expect_fail "declassify-gate: report without sites" "no declassify site in" dg
expect_fail "declassify-gate: no arguments" "usage: declassify-gate.sh" "$root/scripts/declassify-gate.sh"

# deps gate (scripts/deps-gate.sh ROOT TREEDIR): a fake root with crates crypto and wire and one canned `cargo tree` per crate; an extra
# dep in one crate, crypto with a second dep, a crate without a line, a line without a crate, empty and missing trees, a failing cargo.
dpr=$tmp/dp/root; dpt=$tmp/dp/trees
dpg() { "$root/scripts/deps-gate.sh" "$dpr" "$dpt"; }
mkdir -p "$dpr/crates/crypto" "$dpr/crates/wire" "$dpr/tools" "$dpt"
: > "$dpr/crates/crypto/Cargo.toml"; : > "$dpr/crates/wire/Cargo.toml"
printf 'crypto: vstd\nwire: vest_lib vstd\n' > "$dpr/tools/deps-allow.txt"
printf 'crypto v0.1.0 (/x/crates/crypto)\nvstd v0.0.0\n' > "$dpt/crypto.txt"
printf 'wire v0.1.0 (/x/crates/wire)\nvest_lib v0.2.2\nvstd v0.0.0\n' > "$dpt/wire.txt"
expect_pass "deps-gate" dpg
printf 'vstd-extra v0.1.0\n' >> "$dpt/crypto.txt"
expect_fail "deps-gate: crypto with a second dep" "crate crypto: deps" dpg
printf 'crypto v0.1.0 (/x/crates/crypto)\nvstd v0.0.0\n' > "$dpt/crypto.txt"
printf 'libc v0.2.191\n' >> "$dpt/wire.txt"
expect_fail "deps-gate: an extra dep in another crate" "crate wire: deps" dpg
printf 'wire v0.1.0 (/x/crates/wire)\nvest_lib v0.2.2\nvstd v0.0.0\nvstd v0.0.0\n' > "$dpt/wire.txt"
expect_fail "deps-gate: vstd listed twice" "crate wire: deps" dpg
printf 'wire v0.1.0 (/x/crates/wire)\nvstd v0.0.0\n' > "$dpt/wire.txt"
expect_fail "deps-gate: a dep removed" "crate wire: deps" dpg
printf 'wire v0.1.0 (/x/crates/wire)\nvest_lib v0.2.2\nvstd v0.0.0\n' > "$dpt/wire.txt"
printf 'crypto: vstd\n' > "$dpr/tools/deps-allow.txt"
expect_fail "deps-gate: crate without a line" "crate wire has no line" dpg
printf 'crypto: vstd\nwire: vest_lib vstd\ngone: vstd\n' > "$dpr/tools/deps-allow.txt"
expect_fail "deps-gate: line for a removed crate" "lists gone, which is not a crate" dpg
printf 'crypto: vstd\nwire: vest_lib vstd\n' > "$dpr/tools/deps-allow.txt"
: > "$dpt/wire.txt"
expect_fail "deps-gate: empty tree" "empty cargo tree output for wire" dpg
rm "$dpt/wire.txt"
expect_fail "deps-gate: missing tree" "deps-gate: no $dpt/wire.txt" dpg
: > "$dpr/tools/deps-allow.txt"
expect_fail "deps-gate: empty allow-list" "no or empty" dpg
mkdir -p "$tmp/dp/bin"
printf 'crypto: vstd\nwire: vest_lib vstd\n' > "$dpr/tools/deps-allow.txt"
printf '#!/bin/sh\nexit 1\n' > "$tmp/dp/bin/cargo"; chmod +x "$tmp/dp/bin/cargo"
expect_fail "deps-gate: cargo tree fails" "cargo tree failed for crypto" env PATH="$tmp/dp/bin:$PATH" "$root/scripts/deps-gate.sh" "$dpr"

# ct-check's crypto report reader (scripts/ct-report.sh REPORT MANIFEST LABELS OUTDIR): a canned report with a rejected root; a root
# with no verdict; changed labels; a missing and an empty report.
cr() { "$root/scripts/ct-report.sh" "$tmp/cr/report.txt" "$tmp/cr/manifest.txt" "$tmp/cr/labels.txt" "$tmp/cr/out"; }
fresh ctreport; rm -rf "$tmp/cr"; mv "$tmp/ctreport" "$tmp/cr"
expect_pass "ct-report" cr
sed -i 's/^root crypto::a::g ok/reject crypto::a::g SecretSwitch crates\/crypto\/src\/a.rs:1/' "$tmp/cr/report.txt"
expect_fail "ct-report: a rejected root" "crypto: rejects" cr
sed -i '/^reject /d' "$tmp/cr/report.txt"
expect_fail "ct-report: a root with no verdict" "roots with no verdict: crypto::a::g" cr
fresh ctreport; rm -rf "$tmp/cr"; mv "$tmp/ctreport" "$tmp/cr"
sed -i 's/secret=x/secret=/' "$tmp/cr/report.txt"
expect_fail "ct-report: a label lost" "checked lines differ" cr
rm "$tmp/cr/report.txt"
expect_fail "ct-report: no report" "crypto: no report" cr
: > "$tmp/cr/report.txt"
expect_fail "ct-report: empty report" "crypto: empty report" cr
fresh ctreport; rm -rf "$tmp/cr"; mv "$tmp/ctreport" "$tmp/cr"
: > "$tmp/cr/manifest.txt"
expect_fail "ct-report: manifest without roots" "no root in" cr

# ct-binary (scripts/ct-binary.sh --digests FILE: the real build, dump and checks against a canned digest file): one digest byte
# changed; an objdump that lists no function; an objdump that fails; a missing digest file.
cb() { "$root/scripts/ct-binary.sh" --digests "$tmp/cb/digests.txt"; }
mkdir -p "$tmp/cb/bin" "$tmp/cb/bad"
cp "$root/docs/crypto-binary-digests.txt" "$tmp/cb/digests.txt"
expect_pass "ct-binary: the tracked digests as a canned file" cb
l=$(grep -n -m1 '^[0-9a-f]\{64\} ' "$tmp/cb/digests.txt" | cut -d: -f1)
c=$(sed -n "${l}s/^\(.\).*/\1/p" "$tmp/cb/digests.txt")
[ "$c" = 0 ] && r=1 || r=0
sed -i "${l}s/^./$r/" "$tmp/cb/digests.txt"
expect_fail "ct-binary: one digest byte differs" "object code differs from $tmp/cb/digests.txt" cb
printf '#!/bin/sh\n[ "${1-}" = --version ] && echo "GNU objdump fake" || true\n' > "$tmp/cb/bin/objdump"; chmod +x "$tmp/cb/bin/objdump"
expect_fail "ct-binary: objdump lists no function" "no function in the disassembly" env PATH="$tmp/cb/bin:$PATH" "$root/scripts/ct-binary.sh" --digests "$root/docs/crypto-binary-digests.txt"
printf '#!/bin/sh\nexit 1\n' > "$tmp/cb/bin/objdump"
expect_fail "ct-binary: objdump fails" "objdump failed on" env PATH="$tmp/cb/bin:$PATH" "$root/scripts/ct-binary.sh" --digests "$root/docs/crypto-binary-digests.txt"
rm "$tmp/cb/digests.txt"
expect_fail "ct-binary: missing digest file" "ct-binary: no $tmp/cb/digests.txt" cb
expect_fail "ct-binary: --digests without a file" "usage: ct-binary.sh" "$root/scripts/ct-binary.sh" --digests

# test gate (scripts/test-gate.sh DIR LOG): a crate with a failing test; one that does not build; one with no test; a missing dir.
tg() { "$root/scripts/test-gate.sh" "$tmp/tg" "$tmp/tg.log"; }
fresh testgate-pass; rm -rf "$tmp/tg"; mv "$tmp/testgate-pass" "$tmp/tg"
expect_pass "test-gate" tg
fresh testgate-fail; rm -rf "$tmp/tg"; mv "$tmp/testgate-fail" "$tmp/tg"
expect_fail "test-gate: a failing test" "test-gate: cargo test failed" tg
fresh testgate-pass; rm -rf "$tmp/tg"; mv "$tmp/testgate-pass" "$tmp/tg"
printf 'fn broken( {\n' > "$tmp/tg/src/lib.rs"
expect_fail "test-gate: a crate that does not build" "test-gate: cargo test failed" tg
printf 'pub fn f() {}\n' > "$tmp/tg/src/lib.rs"
expect_fail "test-gate: no test runs" "cargo test passed no test" tg
rm -rf "$tmp/tg"
expect_fail "test-gate: missing dir" "no directory" tg
# --workspace runs per member: a member with tests whose tests are all ignored fails although another member passes.
tw() { "$root/scripts/test-gate.sh" "$tmp/tw" "$tmp/tw.log" --workspace; }
rm -rf "${tmp:?}/tw"; mkdir -p "$tmp/tw/crates/a/src" "$tmp/tw/crates/b/src" "$tmp/tw/crates/server/src"
printf '[workspace]\nmembers = ["crates/a", "crates/b", "crates/server"]\nresolver = "2"\n' > "$tmp/tw/Cargo.toml"
for m in a b server; do printf '[package]\nname = "%s"\nversion = "0.0.0"\nedition = "2021"\n' "$m" > "$tmp/tw/crates/$m/Cargo.toml"; done
printf '#[test]\nfn t() {}\n' > "$tmp/tw/crates/a/src/lib.rs"
printf '#[test]\nfn t() {}\n' > "$tmp/tw/crates/b/src/lib.rs"
printf '#[test]\nfn t() {}\n' > "$tmp/tw/crates/server/src/lib.rs"
(cd "$tmp/tw" && cargo generate-lockfile --offline -q) || die "test-gate demo: cannot lock the workspace fixture"
mkdir -p "$tmp/tw/tools"; printf 'a 1\nb 1\nserver 1\n' > "$tmp/tw/tools/test-floor.txt"
expect_pass "test-gate: --workspace, every member passes a test" tw
printf 'a 2\nb 1\nserver 1\n' > "$tmp/tw/tools/test-floor.txt"
expect_fail "test-gate: --workspace, a crate below its floor" "crate a passed 1 tests, below its floor 2" tw
printf 'a 1\nserver 1\n' > "$tmp/tw/tools/test-floor.txt"
expect_fail "test-gate: --workspace, a crate with tests and no floor line" "crate b has tests but no line in tools/test-floor.txt" tw
printf 'a 1\nb 1\nserver 1\nz 1\n' > "$tmp/tw/tools/test-floor.txt"
expect_fail "test-gate: --workspace, a floor line naming no crate" "names z, which is not a crate" tw
: > "$tmp/tw/tools/test-floor.txt"
expect_fail "test-gate: --workspace, an empty floor file" "is missing or empty" tw
rm "$tmp/tw/tools/test-floor.txt"
expect_fail "test-gate: --workspace, no floor file" "is missing or empty" tw
printf 'a 1\nb 1\nserver 1\n' > "$tmp/tw/tools/test-floor.txt"
printf '#[test]\n#[ignore]\nfn t() {}\n' > "$tmp/tw/crates/b/src/lib.rs"
expect_fail "test-gate: --workspace, a member whose tests are all ignored" "crate b has tests but passed no test" tw
# the required crate (server) with no tests at all
rm -rf "${tmp:?}/tw/crates/b"
printf 'pub fn f() {}\n' > "$tmp/tw/crates/server/src/lib.rs"
printf 'a 1\nserver 1\n' > "$tmp/tw/tools/test-floor.txt"
printf '[workspace]\nmembers = ["crates/a", "crates/server"]\nresolver = "2"\n' > "$tmp/tw/Cargo.toml"
(cd "$tmp/tw" && cargo generate-lockfile --offline -q) || die "test-gate demo: cannot lock the workspace fixture"
expect_fail "test-gate: --workspace, the server crate with its tests deleted" "crate server has tests but passed no test" tw
rm -rf "$tmp/tw/crates/server"; printf '[workspace]\nmembers = ["crates/a"]\nresolver = "2"\n' > "$tmp/tw/Cargo.toml"
(cd "$tmp/tw" && cargo generate-lockfile --offline -q) || die "test-gate demo: cannot lock the workspace fixture"
expect_fail "test-gate: --workspace, the server crate missing" "required-tests crate server is missing" tw

# test floor ratchet (scripts/test-floor.sh, throwaway git repos): lowered or removed against the merge-base; growth then a drop on main.
tfrepo() {  # tfrepo <dir> <floor text>: one commit on main with the floor file, then branch feat
    rm -rf "${tmp:?}/$1"; mkdir -p "$tmp/$1/tools"
    cp -r "$root/scripts" "$tmp/$1/scripts"; cp "$root/tools/ratchet_walk.py" "$tmp/$1/tools/"
    printf '%s\n' "$2" > "$tmp/$1/tools/test-floor.txt"
    git -C "$tmp/$1" init -q -b main
    git -C "$tmp/$1" add -A
    gitc "$1" commit -qm base
}
tfloor() { "$tmp/$1/scripts/test-floor.sh" "$tmp/$1"; }
tfrepo tf1 "a 5
b 3"
gitc tf1 checkout -qb feat
gitc tf1 commit -q --allow-empty -m feat
expect_pass "test-floor: unchanged on a branch" tfloor tf1
printf 'a 6\nb 3\n' > "$tmp/tf1/tools/test-floor.txt"
expect_pass "test-floor: a raised value on a branch" tfloor tf1
printf 'a 4\nb 3\n' > "$tmp/tf1/tools/test-floor.txt"
expect_fail "test-floor: a lowered value against the merge-base" "a at 4, below its highest earlier value 5" tfloor tf1
printf 'a 5\n' > "$tmp/tf1/tools/test-floor.txt"
expect_fail "test-floor: a removed line against the merge-base" "b was removed" tfloor tf1
rm "$tmp/tf1/tools/test-floor.txt"
expect_fail "test-floor: a missing file against the merge-base" "cannot read tools/test-floor.txt" tfloor tf1
tfrepo tf2 "a 5"
expect_pass "test-floor: main, one commit" tfloor tf2
printf 'a 6\n' > "$tmp/tf2/tools/test-floor.txt"; gitc tf2 commit -qam grow
expect_pass "test-floor: main, growth" tfloor tf2
printf 'a 4\n' > "$tmp/tf2/tools/test-floor.txt"; gitc tf2 commit -qam drop
expect_fail "test-floor: main, growth then a drop" "a at 4, below its highest earlier value 6" tfloor tf2
tfrepo tf3 "a 5"
rm -rf "$tmp/tf3/.git"
expect_fail "test-floor: not a git checkout" "not a git checkout" tfloor tf3

# interop.sh with a fake curl and a fake cargo on PATH (no network, no client): a present client whose test fails; a cargo that
# ran no test; curl without HTTP3 and no quiche; a present curl that passes; a root with no interop.rs.
ifake=$tmp/ifake; mkdir -p "$ifake/bin" "$ifake/repo/crates/server/tests"
git -C "$ifake/repo" init -q -b main; : > "$ifake/repo/crates/server/tests/interop.rs"
printf '#!/bin/sh\necho "curl 9 HTTP3"\n' > "$ifake/bin/curl"
printf '#!/bin/sh\nfor a; do last=$a; done\ncase $FAKE in ok) echo "test $last ... ok";; fail) echo "test $last ... FAILED"; exit 101;; none) echo "running 0 tests";; esac\n' > "$ifake/bin/cargo"
chmod +x "$ifake/bin/curl" "$ifake/bin/cargo"
iop() { env -u QUICHE_CLIENT PATH="$ifake/bin:$PATH" FAKE=$1 "$root/scripts/interop.sh" "$ifake/repo"; }
expect_pass "interop: a present curl whose tests pass" iop ok
expect_fail "interop: a present curl whose test fails" "curl_fetches failed" iop fail
expect_fail "interop: a present curl whose test printed neither ok nor FAILED" "curl_fetches did not print ok" iop none
printf '#!/bin/sh\necho "curl 9"\n' > "$ifake/bin/curl"
out=$(iop fail 2>&1) || die "interop: curl without HTTP3 failed:
$out"
[ "$out" = "interop: curl skipped (no HTTP3), quiche skipped (no client)" ] || die "interop: unexpected skip line: $out"
echo "gate-demos: interop: no HTTP3 and no quiche passes and says skipped"
rm "$ifake/repo/crates/server/tests/interop.rs"
expect_fail "interop: no interop.rs" "no crates/server/tests/interop.rs" iop ok

# carryovers.sh (C3; F3, F18, F19), on throwaway git repos of tools/gate-demos/carryovers: a bad row, owner, evidence or
# TRUSTED removal cell, an untracked-evidence citation, a deleted row (main across two commits; a branch), missing inputs.
corepo() {  # corepo <dir>: the fixture on main, its MERGESHA placeholders set to the first commit
    rm -rf "${tmp:?}/$1"; cp -r "$fx/carryovers" "$tmp/$1"
    git -C "$tmp/$1" init -q -b main; git -C "$tmp/$1" add -A; gitc "$1" commit -qm base
    sed -i "s/MERGESHA/$(git -C "$tmp/$1" rev-parse --short=12 HEAD)/" "$tmp/$1/docs/roadmap.md"; gitc "$1" commit -qam anchor
}
co() { "$root/scripts/carryovers.sh" "$tmp/$1"; }
cot=docs/carryovers.tsv
corepo co1
expect_pass "carryovers" co co1
sed -i 's/fn:good_fn/fn:no_such_fn/' "$tmp/co1/$cot"
expect_fail "carryovers: a closed row whose fn: does not resolve" 'no `fn no_such_fn` in a tracked .rs file' co co1
corepo co1; sed -i 's/fn:good_fn/fn:good/' "$tmp/co1/$cot"
expect_fail "carryovers: fn: matches a whole name only" 'no `fn good` in a tracked .rs file' co co1
corepo co1; sed -i 's/doc:TRUSTED.md/doc:untracked.md/' "$tmp/co1/$cot"; : > "$tmp/co1/untracked.md"
expect_fail "carryovers: a closed row whose doc: is not tracked" "evidence doc:untracked.md is not a tracked path" co co1
corepo co1; sed -i 's/doc:TRUSTED.md/commit:deadbeef/' "$tmp/co1/$cot"
expect_fail "carryovers: a closed row whose commit: does not exist" "evidence commit:deadbeef is not a commit" co co1
corepo co1; sed -i 's/^a\t2\t/a\t9\t/' "$tmp/co1/$cot"
expect_fail "carryovers: an owner not in the roadmap" "owner 9 is not a phase of docs/roadmap.md" co co1
corepo co1; sed -i 's/| 2 | second | in progress |/| 2 | second | merged |/' "$tmp/co1/docs/roadmap.md"
expect_fail "carryovers: an open row owned by a merged phase" "a is open but its owner 2 is merged" co co1
corepo co1; sed -i 's/^a\t2\topen\t-/a\t2\tclosed\tdoc:TRUSTED.md/' "$tmp/co1/$cot"; sed -i 's/| 2 | second | in progress |/| 2 | second | merged |/' "$tmp/co1/docs/roadmap.md"
expect_fail "carryovers: a TRUSTED row naming a merged phase" "the removal cell names 2, which is merged" co co1
corepo co1; sed -n 2p "$tmp/co1/$cot" >> "$tmp/co1/$cot"
expect_fail "carryovers: a duplicate id" "duplicate id a" co co1
corepo co1; printf 'e\t2\topen\t-\tdemo:5\n' >> "$tmp/co1/$cot"
expect_fail "carryovers: a row with 5 columns" "expected 6 non-empty tab-separated columns, got 5" co co1
corepo co1; sed -i 's/| 2 (the open phase) |/|  |/' "$tmp/co1/TRUSTED.md"
expect_fail "carryovers: a TRUSTED row with an empty removal cell" "the removal cell '' starts with neither roadmap ids nor" co co1
for cell in 'never' 'Phase 2' 'never ()'; do
    corepo co1; sed -i "s/| 2 (the open phase) |/| $cell |/" "$tmp/co1/TRUSTED.md"
    expect_fail "carryovers: a TRUSTED removal cell '$cell'" "the removal cell '$cell' starts with neither" co co1
done
corepo co1; printf -- '- **Evidence:** the run log `.worktrees/vt-x-evidence/log`.\n' >> "$tmp/co1/docs/rca/a.md"
expect_fail "carryovers: an RCA Evidence line citing a worktree evidence log" "docs/rca/a.md:4 cites '.worktrees/', an untracked path" co co1
corepo co1; printf -- '- **Evidence**: see vt-8d-evidence/t2/probe.txt.\n' >> "$tmp/co1/docs/rca/a.md"
expect_fail "carryovers: the other Evidence spelling, a bare evidence dir name" "docs/rca/a.md:4 cites 'vt-8d-evidence'" co co1
corepo co1; printf '/// steps from vt-8d-evidence/t2/core-steps.txt\n' >> "$tmp/co1/crates/a/src/lib.rs"
expect_fail "carryovers: a crates .rs comment citing an evidence dir" "crates/a/src/lib.rs:5 cites 'vt-8d-evidence'" co co1
corepo co1; sed -i '/^a\t/d' "$tmp/co1/$cot"; gitc co1 commit -qam "delete row a"
expect_fail "carryovers: main, a row deleted across two commits" "a was removed" co co1
corepo co1; gitc co1 checkout -qb feat; gitc co1 commit -q --allow-empty -m feat; sed -i '/^a\t/d' "$tmp/co1/$cot"
expect_fail "carryovers: a branch deleting a row of the merge-base" "a was removed (a floor line once present stays) against the merge-base" co co1
corepo co1; sed -i 's/^a\t2\topen\t-/a\t2\tclosed\tdoc:TRUSTED.md/' "$tmp/co1/$cot"; gitc co1 commit -qam "close row a"
expect_pass "carryovers: main, a row closed rather than deleted" co co1
corepo co1; : > "$tmp/co1/$cot"
expect_fail "carryovers: an empty tsv" "the first line must be the header" co co1
corepo co1; sed -i '2,$d' "$tmp/co1/$cot"
expect_fail "carryovers: a tsv with a header only" "docs/carryovers.tsv has no rows" co co1
corepo co1; rm "$tmp/co1/docs/roadmap.md"
expect_fail "carryovers: a missing roadmap file" "cannot read docs/roadmap.md" co co1
corepo co1; sed -i '/^| [12] /d' "$tmp/co1/docs/roadmap.md"
expect_fail "carryovers: a roadmap table with no rows" "the phase table has no rows" co co1
corepo co1; rm "$tmp/co1/TRUSTED.md"
expect_fail "carryovers: a missing TRUSTED.md" "cannot read TRUSTED.md" co co1
corepo co1; rm -rf "$tmp/co1/.git"
expect_fail "carryovers: not a git checkout" "is not a git checkout" co co1
corepo co1; git -C "$tmp/co1" branch -qm main trunk
expect_fail "carryovers: no main branch to compare with" "cannot resolve the merge-base of HEAD and main" co co1
# fix round 1: merged is anchored (I1), evidence only from crates/ and tools/ct-fixtures and test: needs #[test] (I2),
# every leading TRUSTED id (M2), Evidence continuation lines (M9).
corepo co1; sed -i 's/| 1 | first | merged |/| 1 | first | in progress |/' "$tmp/co1/docs/roadmap.md"; gitc co1 commit -qam unmerge
expect_fail "carryovers: main, a merged phase un-merged across two commits" "phase 1 is no longer merged (a phase once merged stays merged)" co co1
corepo co1; gitc co1 checkout -qb feat; gitc co1 commit -q --allow-empty -m feat
sed -i 's/| 1 | first | merged |/| 1 | first | unplanned |/' "$tmp/co1/docs/roadmap.md"
expect_fail "carryovers: a branch un-merging a phase of the merge-base" "phase 1 is no longer merged (a phase once merged stays merged) against the merge-base" co co1
corepo co1; sed -i 's/| first | merged | - | [0-9a-f]* |/| first | merged | - | deadbeef0 |/' "$tmp/co1/docs/roadmap.md"
expect_fail "carryovers: a merged phase naming no commit" "phase 1 is merged but its plan / merge cell names no commit that is an ancestor of HEAD" co co1
corepo co1; gitc co1 checkout -qb side; gitc co1 commit -q --allow-empty -m side; side=$(git -C "$tmp/co1" rev-parse --short=12 HEAD); gitc co1 checkout -q main
sed -i "s/| first | merged | - | [0-9a-f]* |/| first | merged | - | $side |/" "$tmp/co1/docs/roadmap.md"
expect_fail "carryovers: a merged phase naming a commit off HEAD's history" "phase 1 is merged but its plan / merge cell names no commit that is an ancestor of HEAD" co co1
corepo co1; gitc co1 checkout -qb phase-2; gitc co1 commit -q --allow-empty -m two; gitc co1 checkout -q main; gitc co1 merge -q --no-ff -m "Merge phase-2: demo" phase-2
expect_fail "carryovers: a Merge phase-2 commit while 2 is in progress" "merges phase-2, but docs/roadmap.md says 2 is in progress" co co1
corepo co1; gitc co1 checkout -qb phase-zz; gitc co1 commit -q --allow-empty -m zz; gitc co1 checkout -q main; gitc co1 merge -q --no-ff -m "Merge branch 'phase-zz'" phase-zz
expect_fail "carryovers: a merge of a branch that names no phase" "merges phase-zz, which names no phase of docs/roadmap.md" co co1
corepo co1; mkdir -p "$tmp/co1/tools/gate-demos/x"; printf 'fn only_fixture() {}\n' > "$tmp/co1/tools/gate-demos/x/lib.rs"; git -C "$tmp/co1" add -A
sed -i 's/doc:TRUSTED.md/fn:only_fixture/' "$tmp/co1/$cot"
expect_fail "carryovers: fn: evidence found only in a gate-demos fixture" 'no `fn only_fixture` in a tracked .rs file under crates/' co co1
corepo co1; sed -i 's/test:good_test/test:good_fn/' "$tmp/co1/$cot"
expect_fail "carryovers: a non-test fn cited as test:" 'no #[test] `fn good_fn`' co co1
corepo co1; sed -i 's/| 2 (the open phase) |/| 2, 9zz (two ids) |/' "$tmp/co1/TRUSTED.md"
expect_fail "carryovers: a TRUSTED cell whose second id is not a phase" "starts with neither roadmap ids nor" co co1
corepo co1; printf -- '- **Evidence:** the first line,\n  and a continuation naming .worktrees/x/log.\n' >> "$tmp/co1/docs/rca/a.md"
expect_fail "carryovers: an Evidence continuation line citing a worktree" "docs/rca/a.md:5 cites '.worktrees/'" co co1

# requirements.sh (C1; F9), on throwaway git repos of tools/gate-demos/requirements: a ticked row that is not proved:,
# names that do not resolve, a row without a Status, open: ids that are not open phases, a bad false key, missing inputs.
rqrepo() {  # rqrepo <dir>: the fixture as a git repo
    rm -rf "${tmp:?}/$1"; cp -r "$fx/requirements" "$tmp/$1"
    git -C "$tmp/$1" init -q -b main; git -C "$tmp/$1" add -A; gitc "$1" commit -qm base
}
rq() { "$root/scripts/requirements.sh" "$tmp/$1"; }
rqm=docs/requirements.md
rqrepo rq1
expect_pass "requirements" rq rq1
sed -i 's/| ✅ done | proved:good_fn |/| ✅ done | tested:good_test; open:2 |/' "$tmp/rq1/$rqm"
expect_fail "requirements: a ticked row with tested: only" "ticked, but its Status 'tested:good_test; open:2' is not proved: alone" rq rq1
rqrepo rq1; sed -i 's/| ✅ done | proved:good_fn |/| ✅ done | proved:no_such_fn |/' "$tmp/rq1/$rqm"
expect_fail "requirements: a proved: fn that does not exist" 'no `fn no_such_fn` in a tracked .rs file' rq rq1
rqrepo rq1; sed -i 's/| ✅ done | proved:good_fn |/| ✅ done | proved:no_ens |/' "$tmp/rq1/$rqm"
expect_fail "requirements: a proved: fn with no ensures" 'proved no_ens: no fn `no_ens` with an ensures' rq rq1
rqrepo rq1; sed -i 's/| tested:good_test; open:2 |/| tested:good_fn; open:2 |/' "$tmp/rq1/$rqm"
expect_fail "requirements: a tested: name that is not a #[test]" 'no #[test] `fn good_fn`' rq rq1
rqrepo rq1; sed -i 's/| ✅ done | proved:good_fn |/| ✅ done |/' "$tmp/rq1/$rqm"
expect_fail "requirements: a row with no status" "a row without 7 cells and a Status" rq rq1
rqrepo rq1; sed -i 's/| detection proved | proved:good_fn; open:2 |/| detection proved | proved:good_fn; open:9 |/' "$tmp/rq1/$rqm"
expect_fail "requirements: an open: id not in the roadmap" "open:9 is not a phase of docs/roadmap.md" rq rq1
rqrepo rq1; sed -i 's/| detection proved | proved:good_fn; open:2 |/| detection proved | proved:good_fn; open:1 |/' "$tmp/rq1/$rqm"
expect_fail "requirements: an open: id of a merged phase" "open:1 names a merged phase" rq rq1
rqrepo rq1; sed -i 's/| detection proved | proved:good_fn; open:2 |/| detection proved | proved:good_fn; open:3 |/' "$tmp/rq1/$rqm"
expect_fail "requirements: an open: phase with no req- carryover row" "open:3 has no open req-3 row" rq rq1
rqrepo rq1; sed -i 's/| detection proved | proved:good_fn; open:2 |/| detection proved | proved:good_fn; open:3 |/' "$tmp/rq1/$rqm"
printf 'r3\t3\topen\t-\tdocs/requirements.md:1\ta row citing requirements.md that is not req-3\n' >> "$tmp/rq1/docs/carryovers.tsv"
expect_fail "requirements: an open: phase whose only row is not req-" "open:3 has no open req-3 row" rq rq1
rqrepo rq1; sed -i 's/| tested:good_test; open:2 |/| tested:good_test |/' "$tmp/rq1/$rqm"
expect_fail "requirements: tested: without an open: owner" "tested: without open:" rq rq1
rqrepo rq1; sed -i 's/false (t2)/false (req-2)/' "$tmp/rq1/$rqm"
expect_fail "requirements: a false key that is not a TRUSTED.md carryover" "false (req-2): not an open docs/carryovers.tsv row whose source cites TRUSTED.md" rq rq1
rqrepo rq1; sed -i 's/| false (t2); open:2 |/| false (t2) |/' "$tmp/rq1/$rqm"
expect_fail "requirements: a false row without its owner" "false (t2) needs open:2" rq rq1
rqrepo rq1; sed -i 's/| N\/A (client-only) | | n\/a |/| N\/A (client-only) | | open:2 |/' "$tmp/rq1/$rqm"
expect_fail "requirements: an N/A row whose Status is not n/a" "needs Status n/a" rq rq1
rqrepo rq1; sed -i 's/ Notes | Status |/ Notes |/' "$tmp/rq1/$rqm"
expect_fail "requirements: a table without the Status column" "a table header that is not" rq rq1
rqrepo rq1; sed -i '/^|/d; /^## RFC/d' "$tmp/rq1/$rqm"
expect_fail "requirements: no table rows" 'no `| § | ...` table rows' rq rq1
rqrepo rq1; rm "$tmp/rq1/$rqm"
expect_fail "requirements: a missing requirements.md" "cannot read docs/requirements.md" rq rq1
rqrepo rq1; rm "$tmp/rq1/docs/carryovers.tsv"
expect_fail "requirements: a missing carryovers.tsv" "cannot read docs/carryovers.tsv" rq rq1
rqrepo rq1; rm "$tmp/rq1/docs/roadmap.md"
expect_fail "requirements: a missing roadmap" "cannot read docs/roadmap.md" rq rq1
rqrepo rq1; printf '\n| Sec | Topic | #MUST/MUST NOT | Server applies? | Phase | Notes | Status |\n|---|---|---|---|---|---|---|\n| 7 | hidden | 1 | yes | 2 | ✅ done | tested:good_test |\n' >> "$tmp/rq1/$rqm"
expect_fail "requirements: a second table with a | Sec | header and a ticked row" "a table row outside a requirements table carries a tick or a Status item" rq rq1
rqrepo rq1; sed -i 's/^| § | Topic/| Sec | Topic/' "$tmp/rq1/$rqm"
expect_fail "requirements: an RFC table whose header is renamed" "a table header that is not" rq rq1
rqrepo rq1; printf '\n## RFC 2\n\nNo table here.\n' >> "$tmp/rq1/$rqm"
expect_fail "requirements: an RFC section without its table" "'## RFC 2' has 0 tables with the Status header, not 1" rq rq1
rqrepo rq1; rm -rf "$tmp/rq1/.git"
expect_fail "requirements: not a git checkout (git did not run)" "git ls-files -z failed" rq rq1

echo "gate-demos: $n demos, all fail as expected"
