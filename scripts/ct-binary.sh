#!/bin/sh
# Binary gate on crates/crypto (docs/crypto-binary-audit.md, "Gate"): build the workspace as it
# ships, disassemble the rlib's units per the audit's recipe, normalise each function, and diff a
# sha256 per function against docs/crypto-binary-digests.txt. Also checks that ct_mask stays a
# real call and scalar_in_range stays out of line. It detects change, not leaks: a digest change
# needs a fresh read of every changed symbol before `--update`. Target dir: CT_BINARY_TARGET_DIR
# (default $root/target/ct-binary); the dump and the per-function text stay in its ct-binary/.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
tracked=docs/crypto-binary-digests.txt
T=${CT_BINARY_TARGET_DIR:-$root/target/ct-binary}
recipe="per docs/crypto-binary-audit.md's recipe (\"Gate\", update protocol)"
die() { echo "ct-binary: $*; the gate failed closed, see docs/crypto-binary-audit.md (\"Gate\") for what to re-read" >&2; exit 1; }
update=0
case "${1-}" in --update) update=1 ;; "") ;; *) die "usage: ct-binary.sh [--update]" ;; esac
for t in cargo ar objdump sha256sum awk sed diff; do
    command -v "$t" >/dev/null || die "missing tool: $t"
done
# The gate builds the shipped profile only; anything that would change codegen is refused.
bad=$(env | grep -E '^(RUSTFLAGS|CARGO_ENCODED_RUSTFLAGS|CARGO_BUILD_[A-Z_]*|CARGO_PROFILE_[A-Z_]*|CARGO_TARGET_[A-Z0-9_]*_RUSTFLAGS|CARGO_INCREMENTAL|RUSTC|RUSTC_WRAPPER|RUSTC_WORKSPACE_WRAPPER)=' | cut -d= -f1 || true)
[ -z "$bad" ] || die "refusing to build with" $bad "set: the gate checks the shipped build"

cargo build --release --locked -q --target-dir "$T" || die "cargo build --release failed"
rlib=$T/release/libcrypto.rlib
[ -f "$rlib" ] || die "no $rlib"
x=$T/ct-binary
rm -rf "$x"
mkdir -p "$x/fn"
list=$(ar t "$rlib") || die "ar t failed on $rlib"
members=$(printf '%s\n' "$list" | grep 'rcgu\.o$' || true)
units=$(printf '%s\n' "$members" | grep -c . || true)
[ "$units" -gt 0 ] || die "no .rcgu.o member in $rlib"
(cd "$x" && ar x "$rlib") || die "ar x failed on $rlib"
: > "$x/dump"
for m in $members; do
    objdump -dr --no-show-raw-insn -C "$x/$m" >> "$x/dump" || die "objdump failed on $m"
done

# Normalise: drop file and section headers (they carry paths and mangled crate hashes), each
# line's offset column and objdump's `# ...` comments; strip `.llvm.N` suffixes, the per-unit
# hash in `anon.<hash>.N` and the function ordinal in `.LCPI<k>_N`; squeeze blanks. Opcodes,
# operands (function-relative jump targets included) and relocations stay.
sed -E 's/\.llvm\.[0-9]+//g; s/\banon\.[0-9a-f]{32}\./anon./g; s/\.LCPI[0-9]+_/.LCPI_/g' "$x/dump" |
awk -v d="$x/fn" '
    /^[0-9a-f]+ <.*>:$/ { n++; f = d "/" n; s = $0; sub(/^[0-9a-f]+ </, "", s); sub(/>:$/, "", s)
        printf "%s\t%s\n", n, s > (d "/../syms"); printf "" > f; next }
    /file format|^Disassembly of section / { f = ""; next }
    f == "" || /^[ \t]*$/ { next }
    { sub(/^[ \t]+[0-9a-f]+:[ \t]+/, ""); sub(/[ \t]+#.*$/, ""); gsub(/[ \t]+/, " "); print > f }'
[ -s "$x/syms" ] || die "no function in the disassembly of $rlib"
(cd "$x/fn" && sha256sum -- *) > "$x/sums" || die "sha256sum failed"
{
    echo "# crates/crypto object code, one sha256 per normalised function (scripts/ct-binary.sh)."
    echo "# Rewrite only with --update, after a fresh read $recipe."
    echo "units $units"
    awk 'NR == FNR { h[$2] = $1; next } { t = index($0, "\t"); print h[substr($0, 1, t - 1)], substr($0, t + 1) }' \
        "$x/sums" "$x/syms" | LC_ALL=C sort -k2
} > "$x/digests"
fns=$(grep -c '^[0-9a-f]\{64\} ' "$x/digests" || true)
[ "$fns" -eq "$(wc -l < "$x/syms")" ] || die "$(wc -l < "$x/syms") functions but $fns digests"

errs=0
err() { echo "ct-binary: $*" >&2; errs=$((errs + 1)); }
[ "$update" -eq 1 ] || [ ! -f "$tracked" ] || grep -qx "units $units" "$tracked" ||
    err "$units units in $rlib, $tracked records another count: inlining moved, re-read every function $recipe"
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
# The audit's ct_mask call sites: 8 exponent-bit sites in the signer, 1 each in cond_sub and select_n.
for c in "crypto::rsa::rsa_pss_sha256_sign 8" "crypto::bignum::cond_sub 1" "crypto::bignum::select_n 1"; do
    s=${c% *}; want=${c##* }
    if f=$(fnfile "$s"); then
        got=$(grep -c '^R_X86_64_PLT32 crypto::bignum::ct_mask-0x4$' "$f" || true)
        [ "$got" -ge "$want" ] ||
            err "$s has $got PLT32 calls to crypto::bignum::ct_mask, the audit read $want: ct_mask is inlined there, re-read $s $recipe"
    else
        err "$s is not one out-of-line function: re-read it and its callers $recipe"
    fi
done
fnfile crypto::p256::scalar_in_range >/dev/null ||
    err "crypto::p256::scalar_in_range is not one out-of-line function (F1): re-read p256_public_key, p256_ecdh and p256_ecdsa_sign $recipe"

if [ "$update" -eq 1 ]; then
    [ "$errs" -eq 0 ] || die "structural checks failed; $tracked not written"
    if [ -f "$tracked" ]; then diff "$tracked" "$x/digests" >&2 || true; fi
    cp "$x/digests" "$tracked"
    echo "ct-binary: wrote $tracked ($fns fns). Every changed symbol above needs a fresh read $recipe, recorded in the audit with its date and commit." >&2
    exit 0
fi
[ -f "$tracked" ] || die "no $tracked (run --update after a fresh read $recipe)"
diff "$tracked" "$x/digests" >&2 ||
    err "object code differs from $tracked (diff above: < tracked, > built; dump in $x/dump): re-read every changed symbol $recipe, then run scripts/ct-binary.sh --update"
[ "$errs" -eq 0 ] || exit 1
echo "ct-binary: ok ($fns fns)"
