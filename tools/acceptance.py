"""Error-path acceptance ratchet (Phase 9r R4). Run via scripts/acceptance.sh.

Usage: python3 -I tools/acceptance.py [--root DIR] [--baseline FILE] [--old-baseline FILE] [--count]
Lists every exec fn inside a `verus!` block under DIR/crates (crates/crypto/src excluded) whose
return type mentions `Result`, `Error`, `Err` or an alias of one (`type R<T> = Result<T, E>;`
anywhere in the scanned crates, matched as a whole word), and whether its ensures call an allowed
spec fn: a `spec fn` (any crate, crypto/src included) named `allowed_*err` or `*_allowed_err`,
written `NAME(`. Fns without the clause must be listed in the baseline, one
`crate::module::[Type[ as Trait]::]fn` per line (`#` comments allowed). Fails if:
  - an unannotated fn is not in the baseline;
  - a baseline line names a fn that now carries the clause, or no longer exists, or is duplicated;
  - the baseline has more than MAX_BASELINE lines (lower the constant in the commit that deletes
    lines), or (--old-baseline FILE, the baseline at the merge-base with main) a line absent from FILE;
  - an allowed spec fn body is literally `true` (parentheses and braces stripped), a match with
    all arms `true`, or a match with a `_` or `Err(..)` arm that is `true`; or has no body;
  - a `use .. as ..` renames Result, an Err/Error name or an alias (not resolved: refused);
  - no verus! block, no error-returning fn, a `verus!(..)`/`verus![..]` block, or an fn whose
    signature this parser cannot split (fail closed).
`--count` prints the number of fn items examined (exec, spec and proof); scripts/acceptance.sh
compares it with an independent awk count.

Parser limits (a line-based scan of comment- and string-stripped text, not a Rust parser): the
`verus!` block, `impl`/`trait`/`mod` scopes and fn bodies are found by brace matching; with
requires/ensures present the body brace is the first `{` that starts a line at the fn line's own
indentation, else (raising if that line is not indented deeper than the fn line, which means the fn body
was read as clause text) the first `{` outside brackets whose line (from the clause keyword) has no
match/if/forall/`=>` and no struct-literal name before it, searched only up to the next fn item;
anything else raises. A fn is named by its crate, file module path, enclosing impl/trait/mod names
(`Type as Trait` for a trait impl) and its own name; two fns with one path count as one (annotated
only if all carry the clause). Out of scope: fns outside `verus!`, macro-generated fns, and error
signals that are not a Result-like return type: `Option`/`None` returns (the wire/h3/quic parsers)
and `close(..)` calls in ()-returning fns. The clause check is a name match, not a proof that the
clause is meaningful (that is 9a's proof-side non-vacuity lemmas).
"""
import os, re, subprocess, sys

MAX_BASELINE = 194  # lower this in the commit that deletes baseline lines
ERR_SUBSTR = ['Result', 'Error', 'Err']
ALLOWED_NAME = re.compile(r'^(?:allowed_\w*err|\w+_allowed_err)$')
CLAUSE = re.compile(r'\b(requires|ensures|recommends|decreases|opens_invariants|no_unwind|returns)\b')
NEXTFN = re.compile(r'(?<![A-Za-z0-9_])fn\s+\w+')


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
            if head.lstrip().startswith('<'):
                head = re.sub(r'^\s*<[^{}]*?>(?=\s*[A-Za-z(&\[])', '', head, count=1)
            head = head.split(' where ')[0]
            def nm(t): return re.sub(r'<.*', '', t.strip()).strip().split('::')[-1] or 'impl'
            if ' for ' in head:
                tr, ty = head.split(' for ', 1)
                name = f'{nm(ty)} as {nm(tr)}'
            else:
                name = nm(head)
        else:
            name = re.match(r'\s*(\w+)', head).group(1)
        out.append((a, b, name))
    return out


def body_brace(s, c0, limit, indent, fn_ls):
    """(index of the body `{` or of the `;` ending a bodyless declaration, bodyless), searching s[c0:limit]."""
    for lm in re.finditer(r'(?m)^([ \t]*)\{', s[c0:limit]):
        if len(lm.group(1)) == indent:
            return s.find('{', c0 + lm.start()), False
    d = bd = 0
    for j in range(c0, limit):
        ch = s[j]
        if ch in '([': d += 1
        elif ch in ')]': d -= 1
        elif ch == ';' and d == 0 and bd == 0: return j, True
        elif ch == '{':
            if d == 0 and bd == 0:
                ls = s.rfind('\n', 0, j) + 1
                before = s[max(ls, c0):j]
                if (not re.search(r'\b(match|if|else|forall|exists|let)\b|(?<!=)=>', before)
                        and not re.match(r'\s*(\w+\s*:(?!:)|\.\.)', s[j + 1:j + 80])
                        and not (re.match(r'\s*\}', s[j + 1:j + 80]) and re.search(r'[A-Z][A-Za-z0-9_]*\s*$', before))):
                    line = s[ls:s.find('\n', j) if s.find('\n', j) >= 0 else len(s)]
                    if ls != fn_ls and len(line) - len(line.lstrip(' \t')) <= indent:
                        raise ValueError('the body brace is on a line not indented under the fn (the fn body was probably read as clause text)')
                    return j, False
            bd += 1
        elif ch == '}': bd -= 1
    return None, False


def fns(s, lo, hi, path):
    """All fn items in s[lo:hi] as (path, ret, clauses, is_exec); raise on a split failure."""
    sc = scopes(s, lo, hi)
    pos = lo
    res = []
    while True:
        m = NEXTFN.search(s, pos, hi)
        if not m: break
        name = re.match(r'fn\s+(\w+)', m.group(0)).group(1)
        k = m.start()
        ls = s.rfind('\n', 0, k) + 1
        b = max(s.rfind(';', lo, k), s.rfind('}', lo, k), s.rfind('{', lo, k), s.rfind(']', lo, k))
        mods = s[b + 1:k].split()
        pos = m.end()
        p = s.find('(', m.end(), hi)
        if p < 0: raise ValueError(f'{path}: fn {name}: no parameter list')
        q = match_paren(s, p)
        if q < 0: raise ValueError(f'{path}: fn {name}: unbalanced parameter list')
        indent = len(s[ls:]) - len(s[ls:].lstrip(' \t'))
        nxt = NEXTFN.search(s, q, hi)
        limit = nxt.start() if nxt else hi
        c = CLAUSE.search(s, q, limit)
        if c and s.find('{', q, c.start()) < 0 and top_semi(s, q, c.start()) < 0:
            try:
                end, bodyless = body_brace(s, c.start(), limit, indent, ls)
            except ValueError as e:
                raise ValueError(f'{path}: fn {name}: {e}')
            if end is None: raise ValueError(f'{path}: fn {name}: cannot find the end of the signature')
            sig_head, clauses = s[q:c.start()], s[c.start():end]
        else:
            j, d = q, 0
            while j < limit and not (s[j] in '{;' and d == 0):
                if s[j] in '(<[': d += 1
                elif s[j] in ')]': d -= 1
                elif s[j] == '>' and s[j - 1] != '-': d -= 1
                j += 1
            if j >= limit: raise ValueError(f'{path}: fn {name}: cannot find the end of the signature')
            end, bodyless, sig_head, clauses = j, s[j] == ';', s[q:j], ''
        if NEXTFN.search(clauses): raise ValueError(f'{path}: fn {name}: the signature scan overran into another fn')
        rm = re.match(r'\s*->\s*(.*)', sig_head, re.S)
        ret = ' '.join(rm.group(1).split()) if rm else ''
        pos = end + 1  # nested fns in a body are examined too
        names = [n for a, bb, n in sc if a < k < bb]
        res.append(('::'.join([path] + names + [name]), ret, clauses, not ('spec' in mods or 'proof' in mods or any(t.startswith('spec(') for t in mods))))
    return res


def rs_files(root):
    for crate in sorted(os.listdir(os.path.join(root, 'crates'))):
        src = os.path.join(root, 'crates', crate)
        for dp, dn, fs in os.walk(src):
            dn[:] = sorted(d for d in dn if d != 'target')
            for f in sorted(fs):
                if f.endswith('.rs'):
                    full = os.path.join(dp, f)
                    yield crate, os.path.relpath(full, src), full


def scan(root):
    """(exec fns {path: [(ret, ensures)]}, allowed spec fns [(path, name, body)], aliases, blocks, examined)."""
    found, allowed, aliases, nblocks, examined = {}, [], {}, 0, 0
    texts = []
    for crate, rel, full in rs_files(root):
        s = strip(open(full, encoding='utf-8').read())
        texts.append((crate, rel, full, s))
        for m in re.finditer(r'(?<![A-Za-z0-9_])type\s+(\w+)', s):
            j = m.end()
            while s[j:j + 1].isspace(): j += 1
            if s[j:j + 1] == '<':
                dd = 0
                while j < len(s):
                    dd += (s[j] == '<') - (s[j] == '>' and s[j - 1] != '-')
                    j += 1
                    if dd == 0: break
            while s[j:j + 1].isspace(): j += 1
            if s[j:j + 1] != '=': continue  # an associated type declaration
            e = s.find(';', j)
            if e < 0: raise ValueError(f'{full}: type {m.group(1)}: no `;`')
            aliases[m.group(1)] = s[j + 1:e]
        for sm in re.finditer(r'(?<![A-Za-z0-9_])spec(?:\(\w+\))?\s+fn\s+(\w+)', s):
            if not ALLOWED_NAME.match(sm.group(1)): continue
            j = sm.end()
            pa = s.find('(', j); qa = match_paren(s, pa) if pa >= 0 else -1
            if qa < 0: raise ValueError(f'{full}: spec fn {sm.group(1)}: no parameter list')
            e = qa
            while e < len(s) and s[e] not in '{;': e += 1
            if e >= len(s) or s[e] == ';': raise ValueError(f'{full}: spec fn {sm.group(1)} has no body')
            k = match_brace(s, e)
            if k < 0: raise ValueError(f'{full}: spec fn {sm.group(1)}: unbalanced body')
            allowed.append((f'{crate}/{rel}', sm.group(1), s[e + 1:k - 1]))
    ere0, _ = error_re(aliases)
    for crate, rel, full, s in texts:
        # a `use .. Result as X;` rename hides an error type: fail closed rather than resolve it
        for u in re.finditer(r'(?<![A-Za-z0-9_])use\b([^;]*);', s):
            for r in re.finditer(r'([A-Za-z0-9_]+)\s+as\s+[A-Za-z0-9_]+', u.group(1)):
                if ere0.search(r.group(1)): raise ValueError(f'{full}: `use {r.group(0)}` renames an error type or alias')
    for crate, rel, full, s in texts:
        if crate == 'crypto' and rel.startswith('src' + os.sep): continue
        if re.search(r'(?<![A-Za-z0-9_])verus!\s*[(\[]', s): raise ValueError(f'{full}: a verus!(..) or verus![..] block is not scanned')
        parts = rel[:-3].split(os.sep)
        if parts[0] == 'src': parts = parts[1:]
        if parts and parts[-1] in ('lib', 'mod', 'main'): parts = parts[:-1]
        path = '::'.join([crate] + parts)
        for m in re.finditer(r'(?<![A-Za-z0-9_])verus!\s*\{', s):
            a = m.end() - 1
            b = match_brace(s, a)
            if b < 0: raise ValueError(f'{full}: unbalanced verus! block')
            nblocks += 1
            for p, ret, cl, ex in fns(s, a + 1, b - 1, path):
                examined += 1
                if ex: found.setdefault(p, []).append((ret, cl))
    return found, allowed, aliases, nblocks, examined


def error_re(aliases):
    names = {n for n, rhs in aliases.items() if any(t in rhs for t in ERR_SUBSTR)}
    while True:  # an alias of an error alias
        more = {n for n, rhs in aliases.items() if n not in names and any(re.search(r'\b%s\b' % re.escape(x), rhs) for x in names)}
        if not more: break
        names |= more
    pat = '|'.join(ERR_SUBSTR + [r'\b%s\b' % re.escape(n) for n in sorted(names)])
    return re.compile(pat), sorted(names)


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
    while True:  # strip enclosing () and {}
        m = re.match(r'^[({]\s*(.*?)\s*[)}]$', b)
        if not m or match_paren(b.replace('{', '(').replace('}', ')'), 0) != len(b): break
        b = m.group(1)
    if b == 'true': return True
    m = re.match(r'^match [^{]*\{(.*)\}$', b)
    if m:
        arms = [x.strip() for x in split_top(m.group(1)) if x.strip()]
        if arms and all(re.search(r'=>\s*true$', x) for x in arms): return True
        # a catch-all or Err arm that is true covers the whole error side
        return any(re.match(r'^(_|Err\s*\(.*\))\s*=>\s*true$', x) for x in arms)
    return False


def main(argv):
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
    base = old = None
    count = False
    while argv:
        if argv[0] == '--root': root = argv[1]; argv = argv[2:]
        elif argv[0] == '--baseline': base = argv[1]; argv = argv[2:]
        elif argv[0] == '--old-baseline': old = argv[1]; argv = argv[2:]
        elif argv[0] == '--count': count = True; argv = argv[1:]
        else: print(f'acceptance: unknown argument {argv[0]}', file=sys.stderr); return 1
    base = base or os.path.join(root, 'tools', 'acceptance-baseline.txt')
    try:
        found, allowed, aliases, nblocks, examined = scan(root)
    except (ValueError, OSError) as e:
        print(f'acceptance: cannot parse: {e}', file=sys.stderr); return 1
    if count: print(examined); return 0
    if nblocks == 0: print('acceptance: no verus! block under crates/', file=sys.stderr); return 1
    ere, anames = error_re(aliases)
    names = {n for _, n, _ in allowed}
    call = re.compile(r'(?<![A-Za-z0-9_.])(?:%s)\s*\(' % '|'.join(map(re.escape, sorted(names)))) if names else None
    err = {p: v for p, v in found.items() if any(ere.search(r) for r, _ in v)}
    if not err: print('acceptance: no error-returning fn found', file=sys.stderr); return 1
    def carries_one(cl):
        e = re.search(r'\bensures\b', cl)
        return bool(call and e and call.search(cl[e.start():]))
    carries = {p for p, v in err.items() if all(carries_one(cl) for r, cl in v if ere.search(r))}
    if not os.path.isfile(base): print(f'acceptance: no baseline {base}', file=sys.stderr); return 1
    bl = [l.strip() for l in open(base, encoding='utf-8') if l.strip() and not l.lstrip().startswith('#')]
    fail = []
    for p in sorted(set(err) - carries - set(bl)): fail.append(f'new error-returning fn without an allowed_ ensures clause (add the clause; the baseline only shrinks): {p}')
    for p in sorted(set(bl)):
        if p not in found: fail.append(f'stale baseline line, no such fn: {p}')
        elif p not in err: fail.append(f'stale baseline line, fn no longer returns an error type: {p}')
        elif p in carries: fail.append(f'stale baseline line, fn now carries the clause (delete the line): {p}')
    if len(bl) != len(set(bl)): fail.append('duplicate baseline lines')
    if len(bl) > MAX_BASELINE: fail.append(f'baseline has {len(bl)} lines, more than MAX_BASELINE = {MAX_BASELINE} (the baseline only shrinks)')
    if old is not None:
        ob = {l.strip() for l in open(old, encoding='utf-8') if l.strip() and not l.lstrip().startswith('#')}
        for p in sorted(set(bl) - ob): fail.append(f'baseline line not in the merge-base baseline (the baseline only shrinks): {p}')
    for path, name, body in allowed:
        if vacuous(body): fail.append(f'vacuous allowed spec fn (body true, a match with all arms true, or a catch-all/Err arm true): {path}::{name}')
    for f in fail: print(f'acceptance: {f}', file=sys.stderr)
    if fail: return 1
    print(f'acceptance: {len(carries)}/{len(err)} error-returning fns carry allowed_ clauses')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
