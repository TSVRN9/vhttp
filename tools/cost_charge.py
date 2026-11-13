"""Cost-charge gate (9b1 D6a). Usage: python3 -I tools/cost_charge.py ROOT
In ROOT/crates/quic/src/avl.rs and ROOT/crates/quic/src/frags.rs, inside `verus!` (comments and strings blanked, fns
found by tools/acceptance.py's parser):
  - every `while` has an `invariant` (or `invariant_except_break`) clause naming `work`, the ghost cost accumulator;
  - every exec fn (not spec/proof) with a fn-level `decreases` or a `while` in its body returns a named result holding a
    `Ghost<nat>` (the whole return, or a top-level tuple element) that its ensures read: `NAME@`, or `NAME.K@` for
    element K;
  - no `loop`, `for .. in` or `exec_allows_no_decreases_clause` (loops and recursion this gate does not see).
Fails naming file:line; fails closed on a missing file, no verus! block, or no looping or recursive fn at all.
Limit: a name check, not a proof that the charge is right (the cost ensures are the proof); recursion is recognised by a
fn-level `decreases`, which Verus requires of every recursive exec fn here (the attribute that waives it is refused)."""
import os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import acceptance as acc  # noqa: E402

FILES = ['crates/quic/src/avl.rs', 'crates/quic/src/frags.rs']
INV = re.compile(r'\b(invariant_except_break|invariant|ensures|decreases)\b')


def split_ty(t):
    """Split a type list at commas outside (), [], {} and <> (`->` is not a bracket)."""
    out, d, cur = [], 0, ''
    for i, ch in enumerate(t):
        if ch in '([{<': d += 1
        elif ch in ')]}' or (ch == '>' and t[i - 1:i] != '-'): d -= 1
        if ch == ',' and d == 0: out.append(cur); cur = ''
        else: cur += ch
    return [x.strip() for x in out + [cur] if x.strip()]


def ghost_reads(ret):
    """The ensures tokens that read the Ghost<nat> parts of a return `(NAME: TYPE)`, or None."""
    m = re.fullmatch(r'\(\s*(\w+)\s*:\s*(.*)\)', ret, re.S)
    if not m: return None
    name, ty = m.group(1), m.group(2).strip()
    if ty == 'Ghost<nat>': return [name + '@']
    if not (ty.startswith('(') and acc.match_paren(ty, 0) == len(ty)): return None
    ks = [k for k, x in enumerate(split_ty(ty[1:-1])) if x == 'Ghost<nat>']
    return ['%s.%d@' % (name, k) for k in ks] or None


def check(root):
    errs, nfn, nwhile = [], 0, 0
    for rel in FILES:
        full = os.path.join(root, rel)
        try:
            raw = open(full, encoding='utf-8').read()
        except OSError as e:
            raise ValueError('cannot read %s: %s' % (rel, e))
        s = acc.strip(raw)
        line = lambda i: '%s:%d' % (rel, s.count('\n', 0, i) + 1)
        if 'exec_allows_no_decreases_clause' in s:
            errs.append('%s: exec_allows_no_decreases_clause (recursion without a decreases)' % line(s.index('exec_allows_no_decreases_clause')))
        blocks = [m for m in re.finditer(r'(?<![A-Za-z0-9_])verus!\s*\{', s)]
        if not blocks: raise ValueError('%s: no verus! block' % rel)
        for m in blocks:
            a = m.end() - 1
            b = acc.match_brace(s, a)
            if b < 0: raise ValueError('%s: unbalanced verus! block' % rel)
            for path, ret, clauses, ex, k in acc.fns(s, a + 1, b - 1, rel):
                if not ex: continue
                nm = re.match(r'fn\s+(\w+)', s[k:]).group(0)
                _, _, end, bodyless = acc.sig_end(s, k, k + len(nm), b - 1, rel, nm[3:].strip())
                if bodyless: continue
                e2 = acc.match_brace(s, end)
                if e2 < 0: raise ValueError('%s: %s: unbalanced body' % (line(k), path))
                body = s[end:e2]
                for bad in re.finditer(r'\bloop\b|\bfor\s+[^{;]*?\bin\b', body):
                    errs.append('%s: `%s` in %s: only `while` loops are checked' % (line(end + bad.start()), bad.group(0).split()[0], path))
                whiles = [w.start() + end for w in re.finditer(r'\bwhile\b', body)]
                rec = re.search(r'\bdecreases\b', clauses) is not None
                for w in whiles:
                    nwhile += 1
                    ls = s.rfind('\n', 0, w) + 1
                    le = s.find('\n', w)
                    if s[w:le].rstrip().endswith('{'):
                        errs.append('%s: while without an invariant naming work' % line(w))
                        continue
                    ind = w - ls
                    lb = re.compile(r'(?m)^[ \t]{%d}\{' % ind).search(s, le, e2)
                    if not lb:
                        errs.append('%s: while whose body brace is not found' % line(w))
                        continue
                    head = s[w:lb.start()]
                    parts = list(INV.finditer(head))
                    inv = [head[p.end():parts[i + 1].start() if i + 1 < len(parts) else len(head)]
                           for i, p in enumerate(parts) if p.group(1).startswith('invariant')]
                    if not any(re.search(r'\bwork\b', x) for x in inv):
                        errs.append('%s: while without an invariant naming work' % line(w))
                if not (rec or whiles): continue
                nfn += 1
                why = 'recurses' if rec else 'loops'
                reads = ghost_reads(ret)
                if reads is None:
                    errs.append('%s: %s %s but returns no named Ghost<nat> cost' % (line(k), path, why))
                    continue
                ens = re.split(r'\bensures\b', clauses, maxsplit=1)
                for r in reads:
                    if len(ens) < 2 or not re.search(r'(?<![\w.])' + re.escape(r), ens[1]):
                        errs.append('%s: %s %s but its ensures do not read its cost %s' % (line(k), path, why, r))
    if errs:
        raise ValueError('\n'.join(errs))
    if nfn == 0 or nwhile == 0:
        raise ValueError('no looping or recursive exec fn (%d) or no while (%d) found: the parser read nothing' % (nfn, nwhile))
    return nfn, nwhile


def main(argv):
    if len(argv) != 1:
        print('usage: cost_charge.py ROOT', file=sys.stderr)
        return 1
    try:
        nfn, nwhile = check(argv[0])
    except ValueError as e:
        print('cost-charge: %s' % e, file=sys.stderr)
        return 1
    print('cost-charge: %d looping or recursive exec fns return a charged Ghost<nat>, %d whiles charge work' % (nfn, nwhile))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
