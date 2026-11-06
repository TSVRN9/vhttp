"""Error-path acceptance ratchet (Phase 9r R4). Run via scripts/acceptance.sh.

Usage: python3 -I tools/acceptance.py [--root DIR] [--baseline FILE]
Lists every exec fn inside a `verus!` block under DIR/crates (default: the repo; crates/crypto/src
excluded) whose return type mentions `Result` or a type in ERROR_TYPES, and whether its ensures
mention an `allowed_` spec name (an identifier with the segment `allowed_`). Fns without the clause
must be listed in the baseline, one `crate::module::[Type::]fn` per line (`#` comments allowed).
Fails if an unannotated fn is not in the baseline, if a baseline line names a fn that now carries
the clause or no longer exists, or if a `spec fn allowed_*` body is literally `true` or a match
whose arms are all `true`. Fails closed: no verus! block, no error-returning fn, or an fn whose
signature this parser cannot split is a failure.

Parser limits (a line-based scan of comment- and string-stripped text, not a Rust parser): the
`verus!` block, `impl`/`trait`/`mod` scopes and fn bodies are found by brace matching; the body
brace of an fn with requires/ensures is the first `{` that starts a line at the fn line's own
indentation (or the first `;` for a bodyless declaration), so unformatted code is rejected rather
than guessed; a fn is named by its crate, file module path, enclosing impl/trait/mod names and its
own name, so two fns with the same path count as one (annotated only if all carry the clause);
macro-generated fns, fns outside `verus!`, and type aliases hiding `Result` are invisible (hence
ERROR_TYPES); the clause check is a name match, not a proof that the clause is meaningful, which
is what the non-vacuity check and 9a's proof-side lemmas are for.
"""
import os, re, sys

ERROR_TYPES = ['Result', 'Error', 'Err']  # substrings of the return type that mark an error-signalling fn
CLAUSE = re.compile(r'\b(requires|ensures|recommends|decreases|opens_invariants|no_unwind|returns)\b')
ALLOWED = re.compile(r'(?<![A-Za-z0-9])(?:[A-Za-z0-9]+_)*allowed_[A-Za-z0-9_]*')


def strip(s):
    """Blank comments, strings and char literals, keeping every offset and newline."""
    out, i, n = [], 0, len(s)
    while i < n:
        c = s[i]
        if s.startswith('//', i):
            j = s.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j
        elif s.startswith('/*', i):
            d, j = 1, i + 2
            while j < n and d:
                if s.startswith('/*', j): d += 1; j += 2
                elif s.startswith('*/', j): d -= 1; j += 2
                else: j += 1
            out.append(re.sub(r'[^\n]', ' ', s[i:j])); i = j
        elif c == '"' or (c == 'r' and re.match(r'r#*"', s[i:i + 8])):
            if c == 'r':
                h = len(re.match(r'r(#*)"', s[i:]).group(1)); end = '"' + '#' * h; j = s.find(end, i + 2 + h)
                j = n if j < 0 else j + len(end)
            else:
                j = i + 1
                while j < n and s[j] != '"':
                    j += 2 if s[j] == '\\' else 1
                j += 1
            out.append(re.sub(r'[^\n]', ' ', s[i:j])); i = j
        elif c == "'" and re.match(r"'(\\.[^']*|[^\\'])'", s[i:i + 12]):
            j = i + len(re.match(r"'(\\.[^']*|[^\\'])'", s[i:i + 12]).group(0))
            out.append(' ' * (j - i)); i = j
        else:
            out.append(c); i += 1
    return ''.join(out)


def match_brace(s, i):
    """Index just past the `}` matching the `{` at i, or -1."""
    d = 0
    for j in range(i, len(s)):
        if s[j] == '{': d += 1
        elif s[j] == '}':
            d -= 1
            if d == 0: return j + 1
    return -1


def match_paren(s, i):
    d = 0
    for j in range(i, len(s)):
        if s[j] in '([': d += 1
        elif s[j] in ')]':
            d -= 1
            if d == 0: return j + 1
    return -1


def top_semi(s, a, b):
    """Index of the first `;` in s[a:b] outside brackets, or -1."""
    d = 0
    for j in range(a, b):
        if s[j] in '([{': d += 1
        elif s[j] in ')]}': d -= 1
        elif s[j] == ';' and d == 0: return j
    return -1


def scopes(s, lo, hi):
    """(start, end, name) of every impl/trait/mod item in s[lo:hi]."""
    out = []
    for m in re.finditer(r'(?<![A-Za-z0-9_])(impl|trait|mod)\b([^{};]*)\{', s[lo:hi]):
        kind, head = m.group(1), m.group(2)
        a = lo + m.end() - 1
        b = match_brace(s, a)
        if kind == 'impl':
            head = re.sub(r'^\s*<[^{}]*?>(?=\s*[A-Za-z(&\[])', '', head, count=1) if head.lstrip().startswith('<') else head
            head = head.split(' where ')[0]
            if ' for ' in head: head = head.split(' for ', 1)[1]
            name = re.sub(r'<.*', '', head.strip()).strip().split('::')[-1] or 'impl'
        else:
            name = re.match(r'\s*(\w+)', head).group(1)
        out.append((a, b, name))
    return out


def fns(s, lo, hi, path):
    """Yield (path, ret, ensures_text, has_clause_bodyless) for exec fns in s[lo:hi]; raise on a split failure."""
    sc = scopes(s, lo, hi)
    pos = lo
    res = []
    while True:
        m = re.compile(r'(?<![A-Za-z0-9_])fn\s+(\w+)').search(s, pos, hi)
        if not m: break
        k = m.start()
        ls = s.rfind('\n', 0, k) + 1
        # modifiers: tokens since the previous item boundary
        b = max(s.rfind(';', lo, k), s.rfind('}', lo, k), s.rfind('{', lo, k), s.rfind(']', lo, k))
        mods = s[b + 1:k].split()
        pos = m.end()
        p = s.find('(', m.end(), hi)
        if p < 0: raise ValueError(f'{path}: fn {m.group(1)}: no parameter list')
        q = match_paren(s, p)
        if q < 0: raise ValueError(f'{path}: fn {m.group(1)}: unbalanced parameter list')
        indent = len(s[ls:]) - len(s[ls:].lstrip(' \t'))
        # signature end
        c = CLAUSE.search(s, q, hi)
        if c and s.find('{', q, c.start()) < 0 and top_semi(s, q, c.start()) < 0:
            end = None
            for lm in re.finditer(r'(?m)^([ \t]*)\{', s[c.start():hi]):
                if len(lm.group(1)) == indent:
                    end = c.start() + lm.start(); end = s.find('{', end); break
            sm = None
            d = 0
            for j in range(c.start(), hi):
                ch = s[j]
                if ch in '{([': d += 1
                elif ch in '})]': d -= 1
                elif ch == ';' and d == 0: sm = j; break
                if end is not None and j >= end: break
            if end is None and sm is None: raise ValueError(f'{path}: fn {m.group(1)}: cannot find the end of the signature')
            if end is None or (sm is not None and sm < end): end, bodyless = sm, True
            else: bodyless = False
            sig_head = s[q:c.start()]
            clauses = s[c.start():end]
        else:
            # no clauses: the first `{` or `;` after the return type
            j = q
            d = 0
            while j < hi and not (s[j] in '{;' and d == 0):
                if s[j] in '(<[': d += 1
                elif s[j] in ')]': d -= 1
                elif s[j] == '>' and s[j - 1] != '-': d -= 1
                j += 1
            if j >= hi: raise ValueError(f'{path}: fn {m.group(1)}: cannot find the end of the signature')
            end, bodyless, sig_head, clauses = j, s[j] == ';', s[q:j], ''
        rm = re.match(r'\s*->\s*(.*)', sig_head, re.S)
        ret = ' '.join(rm.group(1).split()) if rm else ''
        if s[end] == '{':
            bend = match_brace(s, end)
            if bend < 0: raise ValueError(f'{path}: fn {m.group(1)}: unbalanced body')
            pos = bend
        else:
            pos = end + 1
        if 'spec' in mods or 'proof' in mods: continue
        names = [n for a, bb, n in sc if a < k < bb]
        res.append(('::'.join([path] + names + [m.group(1)]), ret, clauses))
    return res


def scan(root):
    """All exec fns: {path: [(ret, ensures)]}, plus the allowed_ spec fns [(path, name, body)]."""
    found, allowed, nblocks = {}, [], 0
    for crate in sorted(os.listdir(os.path.join(root, 'crates'))):
        src = os.path.join(root, 'crates', crate)
        for dp, dn, fs in os.walk(src):
            dn[:] = sorted(d for d in dn if d not in ('target',))
            for f in sorted(fs):
                full = os.path.join(dp, f)
                rel = os.path.relpath(full, src)
                if not f.endswith('.rs') or (crate == 'crypto' and rel.startswith('src' + os.sep)):
                    continue
                parts = rel[:-3].split(os.sep)
                if parts[0] == 'src': parts = parts[1:]
                if parts and parts[-1] in ('lib', 'mod', 'main'): parts = parts[:-1]
                path = '::'.join([crate] + parts)
                s = strip(open(full, encoding='utf-8').read())
                for m in re.finditer(r'(?<![A-Za-z0-9_])verus!\s*\{', s):
                    a = m.end() - 1
                    b = match_brace(s, a)
                    if b < 0: raise ValueError(f'{full}: unbalanced verus! block')
                    nblocks += 1
                    for p, ret, cl in fns(s, a + 1, b - 1, path):
                        found.setdefault(p, []).append((ret, cl))
                    for sm in re.finditer(r'(?<![A-Za-z0-9_])spec\s+fn\s+((?:\w+_)*allowed_\w*)', s[a:b]):
                        i = a + sm.end()
                        j = s.find('{', i)
                        # a spec fn body starts at the first `{` that begins a line or follows `)` after the return type
                        k = match_brace(s, j) if j >= 0 else -1
                        if k < 0: raise ValueError(f'{full}: spec fn {sm.group(1)}: no body')
                        allowed.append((path, sm.group(1), s[j + 1:k - 1]))
    return found, allowed, nblocks


def split_top(t):
    """Split t at commas outside brackets."""
    out, d, cur = [], 0, ''
    for ch in t:
        if ch in '([{': d += 1
        elif ch in ')]}': d -= 1
        if ch == ',' and d == 0: out.append(cur); cur = ''
        else: cur += ch
    return out + [cur]


def vacuous(body):
    b = ' '.join(body.split())
    if b == 'true': return True
    m = re.match(r'^match [^{]*\{(.*)\}$', b)
    if m:
        arms = [x.strip() for x in split_top(m.group(1)) if x.strip()]
        return bool(arms) and all(re.search(r'=>\s*true$', x) for x in arms)
    return False


def main(argv):
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
    base = None
    while argv:
        if argv[0] == '--root': root = argv[1]
        elif argv[0] == '--baseline': base = argv[1]
        else: print(f'acceptance: unknown argument {argv[0]}', file=sys.stderr); return 1
        argv = argv[2:]
    base = base or os.path.join(root, 'tools', 'acceptance-baseline.txt')
    try:
        found, allowed, nblocks = scan(root)
    except (ValueError, OSError) as e:
        print(f'acceptance: cannot parse: {e}', file=sys.stderr); return 1
    if nblocks == 0: print('acceptance: no verus! block under crates/', file=sys.stderr); return 1
    err = {p: v for p, v in found.items() if any(any(t in r for t in ERROR_TYPES) for r, _ in v)}
    if not err: print('acceptance: no error-returning fn found', file=sys.stderr); return 1
    carries = {p for p, v in err.items() if all(ALLOWED.search(cl[cl.find('ensures'):] if 'ensures' in cl else '') for r, cl in v if any(t in r for t in ERROR_TYPES))}
    if not os.path.isfile(base): print(f'acceptance: no baseline {base}', file=sys.stderr); return 1
    bl = [l.strip() for l in open(base, encoding='utf-8') if l.strip() and not l.lstrip().startswith('#')]
    fail = []
    for p in sorted(set(err) - carries - set(bl)): fail.append(f'new error-returning fn without an allowed_ ensures clause (add the clause; the baseline only shrinks): {p}')
    for p in sorted(set(bl)):
        if p not in found: fail.append(f'stale baseline line, no such fn: {p}')
        elif p not in err: fail.append(f'stale baseline line, fn no longer returns an error type: {p}')
        elif p in carries: fail.append(f'stale baseline line, fn now carries the clause (delete the line): {p}')
    if len(bl) != len(set(bl)): fail.append('duplicate baseline lines')
    for path, name, body in allowed:
        if vacuous(body): fail.append(f'vacuous spec fn (body is true, or a match with all arms true): {path}::{name}')
    for f in fail: print(f'acceptance: {f}', file=sys.stderr)
    if fail: return 1
    print(f'acceptance: {len(carries)}/{len(err)} error-returning fns carry allowed_ clauses')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
