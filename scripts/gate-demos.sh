#!/bin/sh
set -eu
set -o pipefail
# gate-demos.sh: each cheap gate gets a canned bad input (a temp copy of a fixture in
# tools/gate-demos/ with one change applied) and must exit non-zero with its message; every fixture
# first passes unchanged, so a demo cannot fail for the wrong reason. Covers lint-scripts,
# check-quotes, the citation gate, the RFC-quantity gate (its git demos in throwaway repos), acceptance (many bad changes, including real-git runs), escape-gate (three), the rlimit gate and the mutant registry (scripts/mutants.sh; its run demos call Verus
# on the fixture crate). Takes a few seconds, plus about a minute the first time vstd builds in target/mutants-demo.
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
    cp -r "$root/scripts" "$tmp/$1/scripts"; cp "$root/tools/acceptance.py" "$tmp/$1/tools/"
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
expect_fail "acceptance.sh git: main appends a baseline line (compared with HEAD^1)" "not in the merge-base baseline" gaccept g2
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
rl() { python3 -I "$root/tools/rl.py" --gate quic --max 8000000 "$tmp/rl.json"; }
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

# rlimit ceilings ratchet (scripts/rlimit-ceilings.sh, in throwaway git repos like the acceptance.sh ones): an unlisted fn above 8M;
# a listed fn above its value; a raised value and a new line against history; a quic line; a stale line; a missing file; server with verus!.
rcrepo() {  # rcrepo <dir>: scripts, rl.py, the ceilings fixture and server src, one commit on main, then branch feat
    rm -rf "${tmp:?}/$1"; mkdir -p "$tmp/$1/tools"
    cp -r "$root/scripts" "$tmp/$1/scripts"; cp "$root/tools/rl.py" "$tmp/$1/tools/"
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

# RFC-quantity gate (tools/rfc_quantity.py, C8). The fixture mirrors main's three predicates, its allowlist (digest qdig) and
# open ratchet; bad/ holds the 9a originals verbatim: T6's recv_allowed_err (rfc_recv's running `high`), T4's duplicate
# rule (the `seen` mask), T3's crypto window (the read offset `s.reassembly().base()`).
qx=$tmp/rfcq/crates/quic/src
qdig=f8ada6cfb0d3bdc88af71f543b5a14c0c26fa78e2b54a3c8608c1860293e4584
rq() { python3 -I "$root/tools/rfc_quantity.py" --root "$tmp/rfcq" --allow-digest "$qdig" "$@"; }
qal=$tmp/rfcq/tools/rfc-quantity-allow.txt
qop=$tmp/rfcq/tools/rfc-quantity-open.txt
qadd() { sed -i '$d' "$qx/$1"; printf '%s\n\n} // verus!\n' "$2" >> "$qx/$1"; }  # qadd <file> <fn>: append a spec fn
fresh rfcq
expect_pass "rfc-quantity" rq
fresh rfcq; cp "$tmp/rfcq/bad/t6-recv_stream.rs" "$qx/recv_stream.rs"
expect_fail "rfc-quantity: T6's original recv_allowed_err (8f6b48e) reads the running high" "final_size_trigger (from recv_allowed_err) reads \`s.high\` (a struct field)" rq
fresh rfcq; cp "$tmp/rfcq/bad/t4-tp.rs" "$qx/tp.rs"
expect_fail "rfc-quantity: T4's original duplicate rule (6594f10) reads the seen mask" "allowed_tp_err_from reads \`seen\` (a name used other than" rq
fresh rfcq; cp "$tmp/rfcq/bad/t3-crypto_stream.rs" "$qx/crypto_stream.rs"
expect_fail "rfc-quantity: T3's original crypto window (fcf9ff0^) reads the read offset" "crypto_allowed_err reads \`s.reassembly()\` (a method" rq
fresh rfcq; sed -i 's/^    ||| end > s.limit$/& \/\/ rfc-quantity:/' "$qx/recv_stream.rs"
expect_fail "rfc-quantity: an annotation with an empty reason" "\`// rfc-quantity:\` reason cites no" rq
fresh rfcq; sed -i 's/^    ||| end > s.limit$/& \/\/ rfc-quantity: the largest MAX_STREAM_DATA sent/' "$qx/recv_stream.rs"
expect_fail "rfc-quantity: an annotation citing no RFC section" "\`// rfc-quantity:\` reason cites no" rq
fresh rfcq; sed -i 's/^    ||| end > s.limit$/& \/\/ rfc-quantity: the largest maximum stream data sent (RFC 9000 §19.10)/' "$qx/recv_stream.rs"
sed -i '/\ts\.limit\t/d' "$qop"
expect_pass "rfc-quantity: a cited annotation vouches for its line's read (open line deleted)" rq
fresh rfcq; sed -i 's/^pub const FINAL_SIZE_ERROR.*/& \/\/ rfc-quantity: the code (RFC 9000 §20.1)/' "$qx/recv_stream.rs"
expect_fail "rfc-quantity: an annotation on a line with no read" "with no read from an allowed_*err predicate (stale)" rq
fresh rfcq; printf 'use vstd::prelude::*;\n\nverus! {\n\npub open spec fn other(n: nat) -> bool {\n    n > 0 // rfc-quantity:\n}\n\n} // verus!\n' > "$qx/other.rs"
expect_fail "rfc-quantity: an empty annotation in a file no predicate reaches" "other.rs:6: \`// rfc-quantity:\` reason cites no" rq
fresh rfcq; sed -i 's/final_size_trigger(s, off + len, fin)/crate::recv_stream::final_size_trigger(s, off + len, fin)/' "$qx/recv_stream.rs"
expect_pass "rfc-quantity: a path-qualified call is followed" rq
sed -i 's/c == FINAL_SIZE_ERROR \&\& /&crate::recv_stream::peek(s) \&\& /' "$qx/recv_stream.rs"
qadd recv_stream.rs 'pub open spec fn peek(s: SpecRecv) -> bool { s.high > 0 }'
expect_fail "rfc-quantity: a path-qualified call to a helper reading a field" "peek (from recv_allowed_err) reads \`s.high\`" rq
fresh rfcq; sed -i 's/c == FINAL_SIZE_ERROR \&\& /crate::tp::peek(s) \&\& /' "$qx/recv_stream.rs"
qadd recv_stream.rs 'pub open spec fn peek(s: SpecRecv) -> bool { true }'
qadd tp.rs 'pub open spec fn peek(s: crate::recv_stream::SpecRecv) -> bool { s.high > 0 }'
expect_fail "rfc-quantity: a module-qualified call reaches that module's fn, not the caller's namesake" "peek (from recv_allowed_err) reads \`s.high\`" rq
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
fresh rfcq; printf 'name\tquic::recv_stream::flow_trigger\tconn_room\tthe connection credit left (RFC 9000 §4.1)\n' >> "$qal"
sed -i '/\tconn_room\t/d' "$qop"
expect_fail "rfc-quantity: the allowlist grows without ALLOW_DIGEST" "but ALLOW_DIGEST in tools/rfc_quantity.py is $qdig" rq
fresh rfcq; sed -i 's/c == CRYPTO_BUFFER_EXCEEDED \&\& //' "$qx/crypto_stream.rs"; sed -i '/::crypto_allowed_err\tc\t/d' "$qal"
printf 'name\tquic::recv_stream::flow_trigger\tconn_room\tthe connection credit left (RFC 9000 §4.1)\n' >> "$qal"; sed -i '/\tconn_room\t/d' "$qop"
expect_fail "rfc-quantity: the allowlist swaps a stale line for a new one (same count)" "but ALLOW_DIGEST in tools/rfc_quantity.py is $qdig" rq
fresh rfcq; sed -i 's/c == CRYPTO_BUFFER_EXCEEDED \&\& //' "$qx/crypto_stream.rs"
expect_fail "rfc-quantity: a stale allowlist line" "stale allowlist line, vouches for no read or call: name	quic::crypto_stream::crypto_allowed_err	c" rq
fresh rfcq; sed -i 's/(RFC 9000 §19.8)$/(the frame)/' "$qal"
expect_fail "rfc-quantity: an allowlist reason citing no RFC section" "the reason cites no" rq
fresh rfcq; sed -i 's/credit_before(s) + conn_room/credit_before(s)/' "$qx/recv_stream.rs"
expect_fail "rfc-quantity: a stale open line" "stale open line, no such read" rq
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
    cp -r "$root/scripts" "$tmp/$1/scripts"; cp "$root/tools/acceptance.py" "$root/tools/rfc_quantity.py" "$tmp/$1/tools/"
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
expect_fail "rfc-quantity.sh git: main adds an open line (compared with HEAD^1)" "open line not in the merge-base open ratchet" qgate q2
qrepo q3; gitc q3 branch -m main trunk
expect_fail "rfc-quantity.sh git: no main" "cannot resolve the merge-base" qgate q3
qrepo q4; gitc q4 checkout -qb feat; touch "$tmp/q4/x"; gitc q4 add x; gitc q4 commit -qm noop
expect_pass "rfc-quantity.sh git: unchanged open ratchet on a branch" qgate q4

# mutant registry (scripts/mutants.sh, C6), in throwaway git repos holding the acceptance fixture crate as crates/demo/src/acc.rs
# and the one-row registry of tools/gate-demos/mutants. check: a patch that no longer applies, a missing patch, an empty or
# missing tsv, a duplicate id, an orphan patch, a patch outside its row's crate, a bad regex, a wildcard fn, a patch
# that applies only at an offset, an allowed_*err predicate with no row or named only in a row's origin. run (real Verus, seconds:
# MUTANTS_TARGET_DIR keeps vstd built across runs): the killed mutant (with its named test) passes; a mutant that still
# verifies, a named test that does not FAIL, one that fails unmutated, a misspelt test and a missing fn fail; a dirty
# crates/ is refused. The verdict on canned Verus output: rlimit, no or two JSON objects, another fn checked, a non-matching
# error kind. The main gate (every commit at main's tip): passes after a --no-ff merge or a fast-forward with a fresh run file;
# fails with none (also detached), crates/ or Cargo.toml changed after the run, a fast-forward without a run, main's own
# crates/ change in the merge, a fail line, a missing or extra id, an edited tsv or patch, or no main; on the branch, check only.
export MUTANTS_TARGET_DIR="${MUTANTS_DEMO_TARGET:-$root/target/mutants-demo}"
mrepo() {  # mrepo <dir>: scripts, tools/mutants.py and the fixture, one commit on main, then branch feat
    rm -rf "${tmp:?}/$1"; mkdir -p "$tmp/$1/tools"
    cp -r "$root/scripts" "$tmp/$1/scripts"; cp "$root/tools/mutants.py" "$root/tools/acceptance.py" "$tmp/$1/tools/"
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
sed -i 's/^D-kill\tdemo\t/D-kill\twire\t/' "$tmp/m2/tools/mutants.tsv"
expect_fail "mutants check: patch outside its row's crate" "outside crates/wire/" mut m2 check
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

# the verdict on canned Verus output (tools/mutants.py killed/clean): a passing kill first.
v=$tmp/verdict
vj() {  # vj <errors> <success> [extra fn]: a one-object Verus JSON with demo::acc::demo checked
    x=; [ -z "${3:-}" ] || x=", {\"function\": \"$3\", \"rlimit\": 5, \"success\": true}"
    printf '{"verification-results": {"encountered-error": false, "encountered-vir-error": false, "verified": %s, "errors": %s, "is-verifying-entire-crate": false}, "times-ms": {"smt": {"smt-run-module-times": [{"function-breakdown": [{"function": "demo::acc::demo", "rlimit": 900, "success": %s}%s]}]}}}\n' \
        "$((1 - $1))" "$1" "$2" "$x" > "$v.json"
}
vlog() { printf 'error: %s\n   --> crates/demo/src/acc.rs:11:9\n    |\n11  |         r is Err ==> allowed_demo_err(n, r->Err_0),\n' "$1" > "$v.log"; }
killed() { python3 -I "$root/tools/mutants.py" killed "$v" demo acc demo 'postcondition not satisfied.*allowed_demo_err'; }
vj 1 false; vlog "postcondition not satisfied"
expect_pass "mutants verdict" killed
printf 'error: function body check: Resource limit (rlimit) exceeded\n' >> "$v.log"
expect_fail "mutants verdict: rlimit is not a kill" "rlimit text" killed
vlog "possible arithmetic underflow/overflow"
expect_fail "mutants verdict: another error kind" "no postcondition/precondition/assertion block matches" killed
vlog "postcondition not satisfied"; : > "$v.json"
expect_fail "mutants verdict: no JSON (cached build or compile error)" "0 Verus result objects" killed
vj 1 false; cat "$v.json" "$v.json" > "$v.2"; mv "$v.2" "$v.json"
expect_fail "mutants verdict: two JSON objects" "2 Verus result objects" killed
vj 1 false demo::acc::other
expect_fail "mutants verdict: another fn checked too" "want exactly demo::acc::demo" killed
vj 0 true
expect_fail "mutants verdict: still verifies" "the mutant still verifies" killed
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
gitc m3 checkout -q main; gitc m3 reset -q --hard "$mbase"; gitc m3 merge -q --ff-only feat
expect_pass "mutants verify: fast-forward to a branch tip with a fresh run file" mut m3 verify
mbranch m3 "$fresh_run"; gitc m3 rm -q tools/mutants-last-run.txt; gitc m3 commit -qm "no run file"; mmerge m3
expect_fail "mutants verify: merge without a run file" "git show HEAD:tools/mutants-last-run.txt failed" mut m3 verify
gitc m3 checkout -q --detach main
expect_fail "mutants verify: the same merge checked out detached (a CI checkout)" "git show HEAD:tools/mutants-last-run.txt failed" mut m3 verify
gitc m3 checkout -q main
mbranch m3 "$fresh_run"; printf '// later\n' >> "$tmp/m3/crates/demo/src/lib.rs"; gitc m3 commit -qam "crates change after the run"; mmerge m3
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
gitc m3 checkout -q feat
gitc m3 branch -m main trunk
expect_fail "mutants verify: no main" "cannot resolve main" mut m3 verify

echo "gate-demos: $n demos, all fail as expected"
