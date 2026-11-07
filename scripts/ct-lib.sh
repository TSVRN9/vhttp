#!/bin/sh
set -eu
set -o pipefail
# ct-lib.sh: the report readers of ct-check.sh (sourced; the sourcer defines fail and CT_OUT).
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
