"""Cost-charge gate (9b1 D6a). Usage: python3 -I tools/cost_charge.py ROOT
In ROOT/crates/quic/src/avl.rs and ROOT/crates/quic/src/frags.rs, inside `verus!` (comments and strings blanked, fns
found by tools/acceptance.py's parser):
  - every `while` has an `invariant` (or `invariant_except_break`) clause naming `work`, the ghost cost accumulator, and
    its body updates `work = work + E` with E not `0`;
  - every exec fn (not spec/proof) with a fn-level `decreases` or a `while` in its body returns a named result holding a
    `Ghost<nat>` (the whole return, or a top-level tuple element) that its ensures read: `NAME@`, or `NAME.K@` for
    element K; a recursive one's body updates `work = work + E` with E not `0`;
  - every assignment to `work` is `work = work + E;`;
  - no callee cost is dropped: a call to an exec fn of these files that returns a `Ghost<nat>` (the costs) is the tail
    of a block (its value passes on), or a `let` whose pattern binds each cost as `Ghost(x)`, and from there to the next
    binding of the same name `x` appears in a `work = work + E` update, in a `Ghost(..)` the fn builds (not a call
    argument), or, in the public wrappers insert, after_insert and take_front only, in an `assert`; any other fn that
    calls one returns a cost itself;
  - no `loop`, `for .. in` or `exec_allows_no_decreases_clause` (loops and recursion this gate does not see).
Fails naming file:line; fails closed on a missing file, no verus! block, or no looping or recursive fn or bound cost.
Limit: a structural check, not a proof that the amount charged is right (the cost ensures are upper bounds, so an
undercharge still verifies; carryover cat-C15-semantic-cost); recursion is recognised by a fn-level `decreases`,
which Verus requires of every recursive exec fn here (the attribute that waives it is refused)."""
import os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import acceptance as acc  # noqa: E402

FILES = ['crates/quic/src/avl.rs', 'crates/quic/src/frags.rs']
INV = re.compile(r'\b(invariant_except_break|invariant|ensures|decreases)\b')
WRAPPERS = {'insert', 'after_insert', 'take_front'}
UPDATE = re.compile(r'\bwork\s*=\s*work\s*\+\s*([^;]*?)\s*;')
ASSIGN = re.compile(r'(?<![\w.])work\s*=(?!=)')


def split_ty(t):
    """Split a type list at commas outside (), [], {} and <> (`->` is not a bracket)."""
    out, d, cur = [], 0, ''
    for i, ch in enumerate(t):
        if ch in '([{<': d += 1
        elif ch in ')]}' or (ch == '>' and t[i - 1:i] != '-'): d -= 1
        if ch == ',' and d == 0: out.append(cur); cur = ''
        else: cur += ch
    return [x.strip() for x in out + [cur] if x.strip()]


def cost_idx(ret):
    """The positions of the Ghost<nat> parts of a return `(NAME: TYPE)`: 'whole', a list of top-level indices, or None."""
    m = re.fullmatch(r'\(\s*(\w+)\s*:\s*(.*)\)', ret, re.S)
    if not m: return None
    ty = m.group(2).strip()
    if ty == 'Ghost<nat>': return 'whole'
    if not (ty.startswith('(') and acc.match_paren(ty, 0) == len(ty)): return None
    return [k for k, x in enumerate(split_ty(ty[1:-1])) if x == 'Ghost<nat>'] or None


def charges(body):
    """The `work = work + E` updates in body with E not `0`."""
    return [u for u in UPDATE.finditer(body) if u.group(1).strip() != '0']


def eq_at(s, a, b):
    """Index of the first `=` in s[a:b] outside brackets that is not part of `==`, `=>`, `<=`, `>=` or `!=`, or -1."""
    d = 0
    for j in range(a, b):
        ch = s[j]
        if ch in '([{': d += 1
        elif ch in ')]}': d -= 1
        elif ch == '=' and d == 0 and s[j - 1] not in '=<>!' and s[j + 1:j + 2] not in ('=', '>'): return j
    return -1


def ghost_reads(ret):
    """The ensures tokens that read the Ghost<nat> parts of a return `(NAME: TYPE)`, or None."""
    m = re.fullmatch(r'\(\s*(\w+)\s*:\s*(.*)\)', ret, re.S)
    if not m: return None
    name, ty = m.group(1), m.group(2).strip()
    if ty == 'Ghost<nat>': return [name + '@']
    if not (ty.startswith('(') and acc.match_paren(ty, 0) == len(ty)): return None
    ks = [k for k, x in enumerate(split_ty(ty[1:-1])) if x == 'Ghost<nat>']
    return ['%s.%d@' % (name, k) for k in ks] or None


def bodies(root):
    """[(rel, s, path, name, ret, clauses, k, body start, body end)] for every exec fn with a body, per file."""
    out = []
    for rel in FILES:
        full = os.path.join(root, rel)
        try:
            raw = open(full, encoding='utf-8').read()
        except OSError as e:
            raise ValueError('cannot read %s: %s' % (rel, e))
        s = acc.strip(raw)
        blocks = [m for m in re.finditer(r'(?<![A-Za-z0-9_])verus!\s*\{', s)]
        if not blocks: raise ValueError('%s: no verus! block' % rel)
        fl = []
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
                if e2 < 0: raise ValueError('%s:%d: %s: unbalanced body' % (rel, s.count('\n', 0, k) + 1, path))
                fl.append((path[len(rel) + 2:], nm[3:].strip(), ret, clauses, k, end, e2))
        out.append((rel, s, fl))
    return out


def check(root):
    errs, nfn, nwhile, nbound = [], 0, 0, 0
    files = bodies(root)
    costs = {}
    for rel, s, fl in files:
        for path, name, ret, clauses, k, end, e2 in fl:
            ci = cost_idx(ret)
            if ci is None: continue
            if name in costs and costs[name] != ci:
                raise ValueError('%s: two exec fns named %s return their cost at different places' % (path, name))
            costs[name] = ci
    call = re.compile(r'(?:(?<=self\.)|(?<![\w.]))(%s)\s*(?:::<[^>]*>\s*)?\(' % '|'.join(map(re.escape, sorted(costs))))
    for rel, s, fl in files:
        line = lambda i: '%s:%d' % (rel, s.count('\n', 0, i) + 1)
        if 'exec_allows_no_decreases_clause' in s:
            errs.append('%s: exec_allows_no_decreases_clause (recursion without a decreases)' % line(s.index('exec_allows_no_decreases_clause')))
        for path, name, ret, clauses, k, end, e2 in fl:
            body = s[end:e2]
            for bad in re.finditer(r'\bloop\b|\bfor\s+[^{;]*?\bin\b', body):
                errs.append('%s: `%s` in %s: only `while` loops are checked' % (line(end + bad.start()), bad.group(0).split()[0], path))
            for w in ASSIGN.finditer(body):
                if not UPDATE.match(body, w.start()):
                    errs.append('%s: %s assigns work other than as `work = work + E;`' % (line(end + w.start()), path))
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
                wb = s.find('{', lb.start())
                if not charges(s[wb:acc.match_brace(s, wb)]):
                    errs.append('%s: while whose body does not charge work (`work = work + E`, E not 0)' % line(w))
            if rec and not charges(body):
                errs.append('%s: %s recurses but its body does not charge work (`work = work + E`, E not 0)' % (line(k), path))
            errs += dropped(s, line, path, name, ret, end, e2, costs, call)
            nbound += len(binds_in(s, end, e2, call))
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
    if nfn == 0 or nwhile == 0 or nbound == 0:
        raise ValueError('no looping or recursive exec fn (%d), no while (%d) or no bound callee cost (%d) found: the parser read nothing' % (nfn, nwhile, nbound))
    return nfn, nwhile, nbound


def binds_in(s, a, b, call):
    """The `let` statements in s[a:b] whose right side calls a cost fn: (let start, pattern, callee names, stmt end)."""
    out = []
    for m in re.finditer(r'\blet\s+', s[a:b]):
        p = a + m.end()
        q = eq_at(s, p, b)
        semi = acc.top_semi(s, p, b)
        if q < 0 or semi < 0 or semi < q: continue
        names = {c.group(1) for c in call.finditer(s, q + 1, semi)}
        if names: out.append((a + m.start(), s[p:q].strip(), names, semi))
    return out


def dropped(s, line, path, name, ret, a, b, costs, call):
    """Errors for callee costs fn `path` (body s[a:b]) drops."""
    errs, ours = [], cost_idx(ret) is not None
    lets = binds_in(s, a, b, call)
    covered = [(l, e) for l, _, _, e in lets]
    for c in call.finditer(s, a, b):
        if any(l < c.start() < e for l, e in covered): continue
        z = acc.match_paren(s, s.index('(', c.end() - 1))
        tail = re.match(r'\s*\}', s[z:b]) is not None
        if not tail:
            errs.append('%s: %s drops the cost %s returns (neither bound by a let nor the tail of a block)' % (line(c.start()), path, c.group(1)))
        elif not ours:
            errs.append('%s: %s passes on the cost %s returns but returns no Ghost<nat> cost' % (line(c.start()), path, c.group(1)))
    for l, pat, names, e in lets:
        idx = {str(costs[n]) for n in names}
        if len(idx) != 1:
            errs.append('%s: %s: one let binds calls returning their cost at different places (%s)' % (line(l), path, ', '.join(sorted(names))))
            continue
        ci = costs[sorted(names)[0]]
        pat = re.sub(r'^(mut|ghost)\s+', '', pat)
        if ci == 'whole':
            els = [pat]
        elif pat.startswith('(') and acc.match_paren(pat, 0) == len(pat):
            els = split_ty(pat[1:-1])
        else:
            els = []
        xs = []
        for kk in ([0] if ci == 'whole' else ci):
            g = re.fullmatch(r'Ghost\(\s*(\w+)\s*\)', els[kk]) if kk < len(els) else None
            if not g:
                errs.append('%s: %s does not bind the cost %s returns as Ghost(x)' % (line(l), path, '/'.join(sorted(names))))
            else:
                xs.append(g.group(1))
        if xs and not ours and name not in WRAPPERS:
            errs.append('%s: %s binds the cost %s returns but returns no Ghost<nat> cost and is not a public wrapper' % (line(l), path, '/'.join(sorted(names))))
            continue
        for x in xs:
            rb = re.compile(r'\bGhost\(\s*%s\s*\)' % re.escape(x))
            nxt = [l2 for l2, p2, _, e2 in lets if l2 > l and rb.search(p2)]
            scope = s[e:nxt[0] if nxt else b]
            if not used(scope, x, name in WRAPPERS):
                errs.append('%s: %s drops the cost %s binds from %s (no `work = work + E` update, built Ghost(..) or wrapper assert names it)' % (line(l), path, x, '/'.join(sorted(names))))
    return errs


def used(scope, x, wrapper):
    """x is read by a charge, by a Ghost(..) built (not a call argument), or, in a wrapper, by an assert."""
    w = re.compile(r'\b%s\b' % re.escape(x))
    if any(w.search(u.group(1)) for u in charges(scope)): return True
    for g in re.finditer(r'\bGhost\(', scope):
        z = acc.match_paren(scope, g.end() - 1)
        if z < 0 or not w.search(scope[g.end():z - 1]): continue
        o, d = g.start() - 1, 0
        while o >= 0:
            if scope[o] in ')]': d += 1
            elif scope[o] in '([':
                if d == 0: break
                d -= 1
            o -= 1
        if o < 0 or scope[o] != '(': return True
        if re.search(r'([\w>]*)\s*$', scope[:o]).group(1) in ('', 'return'): return True  # a tuple, not a call's arguments
    if wrapper:
        for g in re.finditer(r'\bassert\s*\(', scope):
            z = acc.match_paren(scope, g.end() - 1)
            if z > 0 and w.search(scope[g.end():z]): return True
    return False


def main(argv):
    if len(argv) != 1:
        print('usage: cost_charge.py ROOT', file=sys.stderr)
        return 1
    try:
        nfn, nwhile, nbound = check(argv[0])
    except ValueError as e:
        print('cost-charge: %s' % e, file=sys.stderr)
        return 1
    print('cost-charge: %d looping or recursive exec fns return a charged Ghost<nat>, %d whiles charge work, %d callee costs bound and kept' % (nfn, nwhile, nbound))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
