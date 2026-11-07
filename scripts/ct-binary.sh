#!/bin/sh
# Binary gate on crates/crypto (docs/crypto-binary-audit.md, "Gate"): build the workspace as it
# ships, disassemble the rlib's units per the audit's recipe, normalise each function, and diff a
# sha256 per function against docs/crypto-binary-digests.txt. Also checks that ct_mask stays a
# real call and scalar_in_range stays out of line, and that no other workspace rlib defines a
# crypto:: symbol. It detects change, not leaks: a digest change needs a fresh read of every
# changed symbol before `--update`. Target dir: $root/target/ct-binary, wiped whenever the content
# stamp of the workspace sources changes; the dump and the per-function text stay in its ct-binary/.
set -eu
set -o pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
tracked=docs/crypto-binary-digests.txt
audit=docs/crypto-binary-audit.md
T=$root/target/ct-binary
recipe="per $audit's recipe (\"Gate\", update protocol)"
die() { echo "ct-binary: $*; the gate failed closed, see $audit (\"Gate\") for what to re-read" >&2; exit 1; }
fail() { die "$@"; }
. "$root/scripts/ct-lib.sh"
update=0
# --digests FILE: compare against FILE instead of the tracked file (scripts/gate-demos.sh feeds it a
# canned one); the build, the dump and the structural checks are unchanged, and --update refuses it.
cmp_to=$tracked
case "${1-}" in
    --update) [ $# -eq 1 ] || die "usage: ct-binary.sh [--update | --digests FILE]"; update=1 ;;
    --digests) [ $# -eq 2 ] || die "usage: ct-binary.sh [--update | --digests FILE]"; cmp_to=$2 ;;
    "") ;;
    *) die "usage: ct-binary.sh [--update | --digests FILE]" ;;
esac
for t in cargo ar objdump nm sha256sum awk sed diff find xargs git; do
    command -v "$t" >/dev/null || die "missing tool: $t"
done
# The gate builds the shipped profile only; anything that would change codegen is refused.
bad=$({ env | grep -E '^(RUSTFLAGS|CARGO_ENCODED_RUSTFLAGS|CARGO_BUILD_[A-Z_]*|CARGO_PROFILE_[A-Z_]*|CARGO_TARGET_[A-Z0-9_]*_RUSTFLAGS|CARGO_INCREMENTAL|RUSTC|RUSTC_WRAPPER|RUSTC_WORKSPACE_WRAPPER)=' || [ $? -eq 1 ]; } | cut -d= -f1)
[ -z "$bad" ] || die "refusing to build with" $bad "set: the gate checks the shipped build"

# Content stamp: cargo trusts mtimes for path packages, so a source change that keeps an old
# mtime would leave a stale rlib. Any change to the workspace's non-test sources wipes the dir.
files=$(find crates Cargo.toml Cargo.lock rust-toolchain.toml -path 'crates/*/tests' -prune -o \
    -path 'crates/*/target' -prune -o -type f -print) || die "find failed"
files=$(printf '%s\n' "$files" | LC_ALL=C sort) || die "sort failed"
sums=$(printf '%s\n' "$files" | xargs -d '\n' sha256sum) || die "sha256sum of the sources failed"
stamp=$(printf '%s\n' "$sums" | sha256sum)
[ "$(cat "$T/ct-binary.stamp" 2>/dev/null || true)" = "$stamp" ] || rm -rf "$T"
cargo build --release --locked -q --target-dir "$T" || die "cargo build --release failed"
printf '%s\n' "$stamp" > "$T/ct-binary.stamp"

x=$T/ct-binary
rm -rf "$x"
mkdir -p "$x/fn" "$x/dep"
# members RLIB DIR: extract RLIB's units into DIR and print them; anything but the rmeta files
# and .rcgu.o units fails (an object a build script added would ship unhashed).
members() {
    [ -f "$1" ] || die "no $1"
    l=$(ar t "$1") || die "ar t failed on $1"
    o=$(printf '%s\n' "$l" | { grep -vxE 'lib\.rmeta|lib\.rmeta-link|[^/]+\.rcgu\.o' || [ $? -eq 1 ]; })
    [ -z "$o" ] || die "$1 has members other than lib.rmeta and .rcgu.o units: $o"
    mkdir -p "$2"
    (cd "$2" && ar x "$1") || die "ar x failed on $1"
    printf '%s\n' "$l" | { grep 'rcgu\.o$' || [ $? -eq 1 ]; }
}
rlib=$T/release/libcrypto.rlib
units=$(members "$rlib" "$x") || exit 1
nunits=$(printf '%s\n' "$units" | { grep -c . || [ $? -eq 1 ]; })
[ "$nunits" -gt 0 ] || die "no .rcgu.o member in $rlib"
: > "$x/dump"
for m in $units; do
    objdump -dr --no-show-raw-insn -C "$x/$m" >> "$x/dump" || die "objdump failed on $m"
done
v=$(objdump --version) || die "objdump --version failed"
objver=$(printf '%s\n' "$v" | sed -n 1p)
[ -n "$objver" ] || die "objdump --version printed nothing"

# Normalise: drop file and section headers (they carry paths and mangled crate hashes), each
# line's offset column and objdump's `# ...` comments; strip `.llvm.N` suffixes, the per-unit
# hash in `anon.<hash>.N` and `.Lanon.<hash>.N`, and the function ordinal in `.LCPI<k>_N`;
# squeeze blanks. Opcodes, operands (function-relative jump targets included) and relocations stay.
sed -E 's/\.llvm\.[0-9]+//g; s/(\.L)?anon\.[0-9a-f]{32}\./\1anon./g; s/\.LCPI[0-9]+_/.LCPI_/g' \
    "$x/dump" > "$x/norm" || die "sed failed on $x/dump"
awk -v d="$x/fn" '
    /^[0-9a-f]+ <.*>:$/ { n++; f = d "/" n; s = $0; sub(/^[0-9a-f]+ </, "", s); sub(/>:$/, "", s)
        printf "%s\t%s\n", n, s > (d "/../syms"); printf "" > f; next }
    /file format|^Disassembly of section / { f = ""; next }
    f == "" || /^[ \t]*$/ { next }
    { sub(/^[ \t]+[0-9a-f]+:[ \t]+/, ""); sub(/[ \t]+#.*$/, ""); gsub(/[ \t]+/, " "); print > f }' \
    "$x/norm" || die "awk failed on $x/norm"
[ -s "$x/syms" ] || die "no function in the disassembly of $rlib"
(cd "$x/fn" && sha256sum -- *) > "$x/sums" || die "sha256sum failed"

errs=0
err() { echo "ct-binary: $*" >&2; errs=$((errs + 1)); }
# Dependents: no other workspace rlib may define a crypto:: symbol (crypto code copied into its
# units, which this gate does not hash); their `U crypto::` references are tracked below.
: > "$x/refs"
ndep=0
for r in "$T"/release/lib*.rlib; do
    c=$(basename "$r" .rlib); c=${c#lib}
    [ "$c" != crypto ] || continue
    ndep=$((ndep + 1))
    us=$(members "$r" "$x/dep/$c") || exit 1
    for m in $us; do
        nm -C "$x/dep/$c/$m" > "$x/dep/$c/$m.nm" || die "nm failed on $m"
        awk -v c="$c" '{ sub(/^[0-9a-f]* +/, ""); t = $1; s = substr($0, length(t) + 2) }
            s ~ /(^|[^A-Za-z0-9_])crypto::/ { print (t == "U" ? "U" : "D"), c, s }' \
            "$x/dep/$c/$m.nm" >> "$x/refs" || die "reading nm output of $m failed"
    done
done
if grep_hits '^D ' "$x/refs" > /dev/null; then
    sed -n 's/^D /  /p' "$x/refs" >&2
    err "the symbols above are crypto:: code defined in another crate's units, which the gate does not hash: re-read them where they are $recipe, or make them calls"
fi
# Both below would leave --update writing a digests file with no U block.
[ "$ndep" -gt 0 ] ||
    err "no workspace rlib besides libcrypto.rlib in $T/release: the dependents' calls into crypto are unchecked, re-read tls's callers of crypto $recipe"
grep -q '^U tls ' "$x/refs" ||
    err "tls references no crypto:: symbol (or tls's rlib is missing): every call into crypto became inlined code, re-read tls's callers of crypto $recipe"

{
    echo "# crates/crypto object code, one sha256 per normalised function (scripts/ct-binary.sh)."
    echo "# Rewrite only with --update, after a fresh read $recipe."
    echo "units $nunits"
    echo "objdump $objver"
    awk 'NR == FNR { h[$2] = $1; next } { t = index($0, "\t"); print h[substr($0, 1, t - 1)], substr($0, t + 1) }' \
        "$x/sums" "$x/syms" | LC_ALL=C sort -k2
    { grep '^U ' "$x/refs" || [ $? -eq 1 ]; } | LC_ALL=C sort -u
} > "$x/digests"
fns=$(grep -c '^[0-9a-f]\{64\} ' "$x/digests" || true)
[ "$fns" -eq "$(wc -l < "$x/syms")" ] || die "$(wc -l < "$x/syms") functions but $fns digests"

if [ "$update" -eq 0 ] && [ -f "$cmp_to" ]; then
    grep -qx "units $nunits" "$cmp_to" ||
        err "$nunits units in $rlib, $cmp_to records another count: inlining moved, re-read every function $recipe"
    grep -qxF "objdump $objver" "$cmp_to" ||
        err "objdump is now '$objver', $cmp_to records another: digests may move with no code change; follow update protocol step 7 in $audit (build the commit that last wrote $tracked, cmp its whole .rcgu.o units, relocations included, against this build's in $x; identical: re-digest with --update and record the new objdump line and md5 in Gate records; otherwise re-read every changed symbol $recipe)"
fi
# Structural checks, in every mode. fnfile prints the normalised text's path of a symbol defined once.
fnfile() {
    k=$(awk -F'\t' -v s="$1" '$2 == s { print $1 }' "$x/syms")
    [ "$(printf '%s\n' "$k" | grep -c .)" -eq 1 ] && echo "$x/fn/$k"
}
if f=$(fnfile crypto::bignum::ct_mask); then
    [ "$(awk '{ print $1 }' "$f" | tr '\n' ' ')" = "mov neg ret " ] ||
        err "crypto::bignum::ct_mask's body is not mov/neg/ret: re-read it and its callers $recipe"
else
    err "crypto::bignum::ct_mask is not one out-of-line function: it was inlined, re-read cond_sub, select_n and rsa_pss_sha256_sign $recipe"
fi
fnfile crypto::p256::scalar_in_range >/dev/null ||
    err "crypto::p256::scalar_in_range is not one out-of-line function (F1): re-read p256_public_key, p256_ecdh and p256_ecdsa_sign $recipe"
# Call sites the audit read: caller, callee, the callee's mangled tail (a call to a local symbol
# relocates against its .text section), and the count. ct_mask: 8 exponent-bit sites in the
# signer, 1 each in cond_sub and select_n; scalar_in_range: once per range check (F1).
for c in "crypto::rsa::rsa_pss_sha256_sign crypto::bignum::ct_mask 6bignum7ct_mask 8" \
    "crypto::bignum::cond_sub crypto::bignum::ct_mask 6bignum7ct_mask 1" \
    "crypto::bignum::select_n crypto::bignum::ct_mask 6bignum7ct_mask 1" \
    "crypto::p256::p256_public_key crypto::p256::scalar_in_range 4p25615scalar_in_range 1" \
    "crypto::p256::p256_ecdh crypto::p256::scalar_in_range 4p25615scalar_in_range 1" \
    "crypto::ecdsa::p256_ecdsa_sign crypto::p256::scalar_in_range 4p25615scalar_in_range 2"; do
    set -- $c
    if f=$(fnfile "$1"); then
        got=$(grep -cE "^R_X86_64_PLT32 ($2|\\.text\\.[^ ]*$3)-0x4\$" "$f" || true)
        [ "$got" -ge "$4" ] ||
            err "$1 has $got PLT32 calls to $2, the audit read $4: $2 is inlined there, re-read $1 $recipe"
    else
        err "$1 is not one out-of-line function: re-read it and its callers $recipe"
    fi
done

if [ "$update" -eq 1 ]; then
    [ "$errs" -eq 0 ] || die "structural checks failed; $tracked not written"
    if [ -f "$tracked" ]; then diff "$tracked" "$x/digests" >&2 || true; fi
    cp "$x/digests" "$tracked"
    echo "ct-binary: wrote $tracked ($fns fns). Every changed symbol above needs a fresh read $recipe, recorded in the audit with its date and commit, in the same commit." >&2
    exit 0
fi
[ -f "$cmp_to" ] || die "no $cmp_to (run --update after a fresh read $recipe)"
diff "$cmp_to" "$x/digests" >&2 ||
    err "object code differs from $cmp_to (diff above: < tracked, > built; dump in $x/dump): re-read every changed symbol, and for a removed U line the dependent's caller, $recipe, then run scripts/ct-binary.sh --update"
# A digests change must come with its recorded read: the last commit touching the digests file
# also touches the audit doc, and an uncommitted change to it comes with one to the audit doc.
last=$(git log -1 --format=%H -- "$tracked") || die "git log failed"
if [ -n "$last" ]; then
    git show --name-only --format= "$last" | grep -xF "$audit" >/dev/null ||
        err "commit $last changes $tracked but not $audit: record the read of every changed symbol there $recipe"
fi
git diff --quiet HEAD -- "$tracked" || ! git diff --quiet HEAD -- "$audit" ||
    err "$tracked has uncommitted changes but $audit has none: record the read of every changed symbol there $recipe"
[ "$errs" -eq 0 ] || exit 1
echo "ct-binary: ok ($fns fns)"
