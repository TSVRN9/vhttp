"""RFC-quantity gate (Phase 9r2 R4, class C8). Run via scripts/rfc-quantity.sh.

Usage: python3 -I tools/rfc_quantity.py [--root DIR] [--allow FILE] [--open FILE] [--old-open FILE]
       [--allow-lines N] (the demos' fixture count; the real tree uses ALLOW_LINES)

C8: an allowed_*err predicate written over the code's own bookkeeping (a read-offset window, a
`seen` mask, a running `high`) instead of the RFC's quantities, so the proof checks the code
against itself. This gate reads the body of every `allowed_*err`, `allowed_*err_from` and
`*_allowed_err` spec fn (tools/acceptance.py's scanner and name pattern) and of every spec fn it
calls, transitively (one level is not enough: recv_allowed_err -> flow_trigger -> credit_before),
and reports every read of something that is not vouched for as an RFC quantity:
  - a struct field (`s.high`, `s.final_size->0`), on any receiver;
  - a method that is not a vstd Seq/Set/Map method (`s.reassembly()`, `x.rfc()`, `y.code_spec()`);
  - `self`, a macro call, or a call of a fn that is not a spec fn in a scanned verus! block (vstd's
    `Seq::`/`Set::`/`Map::`/`Multiset::` constructors excepted);
  - a name (a parameter or a pattern-bound local) used other than as a whole argument of a call that
    is followed or allowed: `seen & tp_bit(id)` reads `seen`; `rfc_tp_apply(id, v, true, t, seen)`
    passes it on (the callee's own reads are what count).
A read is vouched for by one of:
  - `// rfc-quantity: <why this is the RFC's quantity, citing RFC N §x>` on its source line;
  - a `name` line of the allowlist (FN, NAME: the name read in FN is the RFC quantity the reason
    says), or a `call` line (CALLER, CALLEE: CALLEE is an RFC spec fn over RFC histories, not
    followed from CALLER); every allowlist reason cites `RFC N §x`. There is no prefix rule: rfc_*
    fns in this tree include models of the code (rfc_recv, rfc_tp_apply) that return bookkeeping;
  - a line of the open ratchet (ROOT, FN, READ, COUNT, OWNER, REASON): a known violation that is
    not an RFC quantity and cannot be fixed by this phase. It only shrinks: a line absent from
    --old-open (the file at the merge-base with main), or with a larger count, fails.
Fails closed: no predicate, a predicate or callee whose body cannot be found, an ambiguous callee
name, a missing or malformed list file, an empty or uncited reason, an allowlist line or annotation
that vouches for nothing (stale), an open line that matches no read (stale) or whose count is not
the current count, or an allowlist whose line count is not ALLOW_LINES (the allowlist is a ratchet:
growth needs this constant raised in the same diff, so it is visible in review).

Limits (a token scan of comment- and string-stripped text, not a Rust parser): pattern bindings are
found in match arms (back from `=>` to the arm start), `let`/`if let` patterns, closure and
quantifier binders and `matches` patterns; a token it cannot place is a read (fails closed). Only
predicate bodies and the spec fns they call are read: what an exec fn's ensures pass as the
predicate's arguments (`recv_allowed_err(old(self).rfc(), ..)`) is the refinement proof's business,
and a `name` line's claim about a parameter holds only if every caller passes what it says (the
reviewer checks the callers, which this gate lists as followed fns).
"""
import importlib.util, os, re, sys

ALLOW_LINES = 30  # the allowlist's line count: raise it in the diff that adds a line (reviewed growth)
VSTD_TYPES = {'Seq', 'Set', 'Map', 'Multiset'}
VSTD_METHODS = {'len', 'skip', 'take', 'subrange', 'push', 'last', 'first', 'drop_last', 'drop_first',
                'contains', 'contains_key', 'insert', 'remove', 'union', 'intersect', 'difference', 'dom',
                'index', 'add', 'update', 'to_multiset', 'is_prefix_of', 'is_empty'}
KEYWORDS = {'if', 'else', 'match', 'let', 'true', 'false', 'as', 'is', 'has', 'matches', 'forall', 'exists',
            'choose', 'in', 'mut', 'ref', 'return', 'int', 'nat', 'bool', 'char', 'str', 'u8', 'u16', 'u32',
            'u64', 'u128', 'usize', 'i8', 'i16', 'i32', 'i64', 'i128', 'isize', '_', 'crate', 'super'}
CITE = re.compile(r'RFC \d+ §\d+(?:\.\d+)*')
ANNOT = re.compile(r'//\s*rfc-quantity:(.*)$')
IDENT = re.compile(r'(?<![A-Za-z0-9_])[A-Za-z_][A-Za-z0-9_]*')


def load_acc():
    sys.dont_write_bytecode = True  # no tools/__pycache__ in the caller's tree
    spec = importlib.util.spec_from_file_location('acceptance', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'acceptance.py'))
    acc = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(acc)
    return acc


class Fail(Exception):
    pass


def back(b, i):
    """Index of the last non-space char before i, or -1."""
    i -= 1
    while i >= 0 and b[i].isspace(): i -= 1
    return i


def fwd(b, i):
    while i < len(b) and b[i].isspace(): i += 1
    return i


def pattern_spans(acc, b):
    """(start, end) spans of b that bind names: match arm patterns, let patterns, binders, matches patterns."""
    out = []
    for m in re.finditer(r'(?<![=<])=>', b):
        j, d = m.start() - 1, 0
        while j >= 0:
            c = b[j]
            if c in ')]': d += 1
            elif c in '([':
                if d == 0: break
                d -= 1
            elif c in ',{};' and d == 0: break
            j -= 1
        a, e = j + 1, m.start()
        g = re.search(r'(?<![A-Za-z0-9_])if(?![A-Za-z0-9_])', b[a:e])  # a guard is read, not bound
        out.append((a, a + g.start() if g else e))
    for m in re.finditer(r'(?<![A-Za-z0-9_])let(?![A-Za-z0-9_])', b):
        j, d = m.end(), 0
        while j < len(b):
            c = b[j]
            if c in '([{': d += 1
            elif c in ')]}': d -= 1
            elif c == '=' and d == 0 and b[j + 1:j + 2] not in ('=', '>') and b[j - 1] not in '=!<>': break
            j += 1
        out.append((m.end(), j))
    for m in re.finditer(r'\|([^|]*)\|', b):
        pre = b[:m.start()].rstrip()
        if re.search(r'(?<![A-Za-z0-9_])(forall|exists|choose)$', pre) or pre.endswith(('(', ',')):
            out.append((m.start(1), m.end(1)))
    for m in re.finditer(r'(?<![A-Za-z0-9_])matches\s+[A-Za-z_][A-Za-z0-9_:]*\s*', b):
        e = m.end()
        if b[e:e + 1] in '({':
            e = (acc.match_paren(b, e) if b[e] == '(' else acc.match_brace(b, e))
            if e < 0: raise Fail('unbalanced `matches` pattern')
        out.append((m.start(), e))
    return out


def chain(b, j):
    """The accessors after index j: [(kind, start, end, name)] with kind field/method/index/num, up to the first
    that is not one; end is past the accessor (past a method's argument list)."""
    res = []
    while True:
        k = fwd(b, j)
        if b.startswith('..', k): break
        if b.startswith('.', k) or b.startswith('->', k):
            a = k + (1 if b[k] == '.' else 2)
            a = fwd(b, a)
            m = re.match(r'[A-Za-z0-9_]+', b[a:])
            if not m: break
            nm, e = m.group(0), a + m.end()
            p = fwd(b, e)
            if b[p:p + 1] == '(' and not nm[0].isdigit():
                q = acc_.match_paren(b, p)
                if q < 0: raise Fail('unbalanced method call')
                res.append(('method', k, q, nm)); j = q
            elif nm[0].isdigit() or (b[k] == '-' and re.match(r'^[A-Z][A-Za-z0-9]*_\d+$', nm)):
                res.append(('num', k, e, nm)); j = e
            else:
                res.append(('field', k, e, nm)); j = e
        elif b.startswith('[', k):
            q = acc_.match_paren(b, k)
            if q < 0: raise Fail('unbalanced index')
            res.append(('index', k, q, '')); j = q
        else:
            break
    return res


def enclosing_call(b, i):
    """For an argument starting at i, the callee token (start, end) of the call paren around it, or None."""
    d, j = 0, i - 1
    while j >= 0:
        c = b[j]
        if c in ')]}': d += 1
        elif c in '([{':
            if d == 0: break
            d -= 1
        j -= 1
    if j < 0 or b[j] != '(': return None
    k = back(b, j)
    m = re.search(r'[A-Za-z_][A-Za-z0-9_]*$', b[:k + 1])
    if not m: return None
    return (m.start(), m.end())


class Gate:
    def __init__(self, acc, root):
        self.acc, self.root = acc, root
        try:
            _, _, _, _, _, sites, apos = acc.scan(root)
        except (ValueError, OSError) as e:
            raise Fail('cannot scan crates/: %s' % e)
        self.sites = [x for x in sites if not x[4]]  # spec and proof fns
        self.apos = apos
        self.text, self.raw = {}, {}
        self.cache = {}

    def src(self, f):
        if f not in self.text:
            r = open(f, encoding='utf-8').read()
            self.raw[f], self.text[f] = r.split('\n'), self.acc.strip(r)
        return self.text[f]

    def line(self, f, off):
        return self.src(f).count('\n', 0, off) + 1

    def site_of_pred(self, f, off, name):
        hit = [x for x in self.sites if x[0] == f and off <= x[1] < off + 200 and x[2].split('::')[-1] == name]
        if len(hit) != 1: raise Fail('%s: spec fn %s is not in a scanned verus! block' % (os.path.relpath(f, self.root), name))
        return hit[0]

    def resolve(self, caller, name, qual):
        crate = caller[2].split('::')[0]
        cand = [x for x in self.sites if x[2].split('::')[-1] == name]
        if qual and qual[-1][0].isupper() and qual[-1] not in VSTD_TYPES:
            cand = [x for x in cand if qual[-1] in x[2].split('::')[:-1]]
        # a fn of the caller's own module shadows a glob import; otherwise one per crate, or one in all crates
        here = [x for x in cand if x[0] == caller[0]]
        same = [x for x in cand if x[2].split('::')[0] == crate]
        cand = here or same or cand
        paths = sorted({x[2] for x in cand})
        if len(paths) > 1: raise Fail('%s calls %s, which names %d spec fns (%s): ambiguous' % (caller[2], name, len(paths), ', '.join(paths)))
        if not cand: return None
        if len({(x[0], x[1]) for x in cand}) > 1: raise Fail('%s: two fns with one path' % paths[0])
        return cand[0]

    def body(self, site):
        f, k, path = site[0], site[1], site[2]
        s = self.src(f)
        m = re.match(r'fn\s+\w+', s[k:])
        try:
            _, _, e, bodyless = self.acc.sig_end(s, k, k + m.end(), len(s), path, path.split('::')[-1])
        except ValueError as ex:
            raise Fail(str(ex))
        if bodyless: raise Fail('%s has no body' % path)
        z = self.acc.match_brace(s, e)
        if z < 0: raise Fail('%s: unbalanced body' % path)
        return e + 1, z - 1

    def analyse(self, site, allow_calls):
        """(reads [(kind, text, file, line)], callees [site]) of one fn's body."""
        key = site[2]
        if key in self.cache: return self.cache[key]
        f = site[0]
        s = self.src(f)
        lo, hi = self.body(site)
        b = s[lo:hi]
        pats = pattern_spans(self.acc, b)
        in_pat = lambda i: any(a <= i < e for a, e in pats)
        reads, callees, done = [], [], set()
        at = lambda i: (f, self.line(f, lo + i))
        # calls first: classify each callee so arguments know whether they pass through
        calls = {}
        for m in IDENT.finditer(b):
            nm, i, e = m.group(0), m.start(), m.end()
            p = fwd(b, e)
            if b[p:p + 1] == '!' and b[p + 1:p + 2] != '=':
                reads.append(('macro', nm + '!', *at(i))); continue
            if b[p:p + 1] != '(' or nm in KEYWORDS: continue
            pb = back(b, i)
            if pb >= 0 and (b[pb] == '.' or b[pb - 1:pb + 1] == '->'): continue  # a method: see the chains
            qual, j = [], i
            while True:
                k = back(b, j)
                if k >= 1 and b[k - 1:k + 1] == '::':
                    mm = re.search(r'([A-Za-z_][A-Za-z0-9_]*)\s*(?:::\s*)?(<[^<>]*>)?\s*$', b[:k - 1])
                    if not mm: break
                    qual.insert(0, mm.group(1)); j = mm.start()
                else:
                    break
            if nm[0].isupper():
                calls[i] = 'ctor'; continue
            if nm == 'self':
                continue
            t = self.resolve(site, nm, qual)
            if t is None:
                if qual and qual[0] in VSTD_TYPES:
                    calls[i] = 'vstd'
                else:
                    calls[i] = 'bad'
                    reads.append(('call', '::'.join(qual + [nm]) + '(..)', *at(i)))
            elif (site[2], t[2]) in allow_calls:
                calls[i] = 'allowed'; allow_calls[(site[2], t[2])] = True
            else:
                calls[i] = 'followed'; callees.append(t)
        for m in IDENT.finditer(b):
            nm, i, e = m.group(0), m.start(), m.end()
            if i in calls: continue
            pb = back(b, i)
            if pb >= 0 and (b[pb] == '.' or b[pb - 1:pb + 1] == '->'): continue
            if pb >= 1 and b[pb - 1:pb + 1] == '::': continue
            p = fwd(b, e)
            if b[p:p + 2] == '::' or (b[p:p + 1] == '!' and b[p + 1:p + 2] != '='): continue  # a path prefix, a macro (reported above)
            if b[p:p + 1] == ':' and b[p + 1:p + 2] != ':': continue  # a struct literal field name or a binder's type
            if nm in KEYWORDS and nm != 'self': continue
            if re.search(r'(?<![A-Za-z0-9_])(as|is)\s*$', b[:i]): continue  # a cast's type, an `is` variant
            if nm == 'self':
                reads.append(('self', 'self', *at(i))); continue
            if nm[0].isupper() or nm[0].isdigit(): continue  # a constant, a type, a variant
            if in_pat(i): continue
            ch = chain(b, e)
            bad = None
            for kind, a, z, mn in ch:
                done.add(a)
                if bad is None and (kind == 'field' or (kind == 'method' and mn not in VSTD_METHODS)):
                    bad = (kind, ' '.join((nm + b[e:z]).split()))
            if bad:
                reads.append(('field' if bad[0] == 'field' else 'method', bad[1], *at(i))); continue
            if not ch:
                c = enclosing_call(b, i)
                whole = b[back(b, i):back(b, i) + 1] in ('(', ',') and b[fwd(b, e):fwd(b, e) + 1] in (',', ')')
                if whole and c and calls.get(c[0]) in ('followed', 'allowed'):
                    continue  # passed on: the callee's own reads count, or the call line vouches for it
            reads.append(('name', nm, *at(i)))
        # accessors on call results and parenthesised expressions
        for m in re.finditer(r'[)\]]', b):
            for kind, a, z, mn in chain(b, m.end()):
                if a in done: break
                done.add(a)
                if kind == 'field' or (kind == 'method' and mn not in VSTD_METHODS):
                    st = m.start()
                    reads.append(('field' if kind == 'field' else 'method', '(..)' + ' '.join(b[m.end():z].split()), *at(st)))
                    break
        self.cache[key] = (reads, callees)
        return self.cache[key]


acc_ = None


def read_list(path, what):
    try:
        lines = open(path, encoding='utf-8').read().split('\n')
    except OSError as e:
        raise Fail('cannot read the %s %s: %s' % (what, path, e))
    return [(n + 1, l) for n, l in enumerate(lines) if l.strip() and not l.lstrip().startswith('#')]


def main(argv):
    global acc_
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
    allow = opn = old = None
    nallow = ALLOW_LINES
    while argv:
        if argv[0] in ('--root', '--allow', '--open', '--old-open', '--allow-lines') and len(argv) > 1:
            v = argv[1]
            if argv[0] == '--root': root = v
            elif argv[0] == '--allow': allow = v
            elif argv[0] == '--open': opn = v
            elif argv[0] == '--allow-lines':
                if not v.isdigit(): print('rfc-quantity: --allow-lines takes a number', file=sys.stderr); return 1
                nallow = int(v)
            else: old = v
            argv = argv[2:]
        else:
            print('rfc-quantity: unknown argument %s' % argv[0], file=sys.stderr); return 1
    allow = allow or os.path.join(root, 'tools', 'rfc-quantity-allow.txt')
    opn = opn or os.path.join(root, 'tools', 'rfc-quantity-open.txt')
    fail = []
    try:
        acc_ = load_acc()
        g = Gate(acc_, root)
        # the lists
        calls, names = {}, {}
        al = read_list(allow, 'allowlist')
        for n, l in al:
            f = l.split('\t')
            if len(f) != 4 or f[0] not in ('call', 'name') or not all(x.strip() for x in f):
                raise Fail('%s:%d: not `call<TAB>CALLER<TAB>CALLEE<TAB>REASON` or `name<TAB>FN<TAB>NAME<TAB>REASON`' % (allow, n))
            if not CITE.search(f[3]): fail.append('%s:%d: the reason cites no `RFC N §x`' % (allow, n))
            d = calls if f[0] == 'call' else names
            if (f[1], f[2]) in d: fail.append('%s:%d: duplicate line' % (allow, n))
            d[(f[1], f[2])] = False
        if len(al) != nallow:
            fail.append('the allowlist has %d lines but ALLOW_LINES in tools/rfc_quantity.py is %d (the allowlist is a ratchet: '
                        'a new line needs the constant raised in the same diff, a deleted line needs it lowered)' % (len(al), nallow))
        ol = read_list(opn, 'open ratchet')
        opens = {}
        for n, l in ol:
            f = l.split('\t')
            if len(f) != 6 or not all(x.strip() for x in f) or not f[3].isdigit() or not re.match(r'^9[a-z0-9]+$', f[4]):
                raise Fail('%s:%d: not `ROOT<TAB>FN<TAB>READ<TAB>COUNT<TAB>OWNER-PHASE<TAB>REASON`' % (opn, n))
            if not CITE.search(f[5]): fail.append('%s:%d: the reason cites no `RFC N §x`' % (opn, n))
            if (f[0], f[1], f[2]) in opens: fail.append('%s:%d: duplicate line' % (opn, n))
            opens[(f[0], f[1], f[2])] = int(f[3])
        if old is not None:
            olds = {}
            for n, l in read_list(old, 'merge-base open ratchet'):
                f = l.split('\t')
                if len(f) >= 4 and f[3].isdigit(): olds[(f[0], f[1], f[2])] = int(f[3])
            for k, c in sorted(opens.items()):
                if k not in olds: fail.append('open line not in the merge-base open ratchet (the open ratchet only shrinks): %s' % '\t'.join(k))
                elif c > olds[k]: fail.append('open line count %d above the merge-base\'s %d (the open ratchet only shrinks): %s' % (c, olds[k], '\t'.join(k)))
        # the predicates and everything they call
        roots = [g.site_of_pred(f, off, name) for f, off, name in g.apos]
        if not roots: raise Fail('no allowed_*err spec fn found under crates/')
        hits = {}  # (root, fn, read) -> [(kind, file, line)]
        used_ann, nfns = set(), set()
        for r in roots:
            seen, work = {r[2]}, [r]
            while work:
                st = work.pop()
                reads, callees = g.analyse(st, calls)
                nfns.add(st[2])
                for kind, text, f, ln in reads:
                    if kind == 'name' and (st[2], text) in names:
                        names[(st[2], text)] = True; continue
                    if ANNOT.search(g.raw[f][ln - 1]):  # an annotation vouches for the line's other reads
                        used_ann.add((f, ln)); continue
                    hits.setdefault((r[2], st[2], text), []).append((kind, f, ln))
                for t in callees:
                    if t[2] not in seen: seen.add(t[2]); work.append(t)
        # annotations: each cites the RFC and vouches for a read
        for f in sorted(g.raw):
            for n, l in enumerate(g.raw[f]):
                a = ANNOT.search(l)
                if not a: continue
                rel = os.path.relpath(f, root)
                if not CITE.search(a.group(1)): fail.append('%s:%d: `// rfc-quantity:` reason cites no `RFC N §x` (an empty reason vouches for nothing)' % (rel, n + 1))
                elif (f, n + 1) not in used_ann: fail.append('%s:%d: `// rfc-quantity:` on a line with no read from an allowed_*err predicate (stale)' % (rel, n + 1))
        for dct, what in ((calls, 'call'), (names, 'name')):
            for k, used in sorted(dct.items()):
                if not used: fail.append('stale allowlist line, vouches for no read or call: %s\t%s\t%s' % (what, k[0], k[1]))
        for k, v in sorted(hits.items()):
            kind, f, ln = v[0]
            what = {'field': 'a struct field', 'method': 'a method that is not a vstd Seq/Set/Map method', 'self': 'self',
                    'macro': 'a macro', 'call': 'a fn that is not a spec fn in a scanned verus! block',
                    'name': 'a name used other than as a whole argument of a followed or allowed call'}[kind]
            if k in opens:
                if opens[k] != len(v): fail.append('open line count %d, but %s reads %s %d times (set the count; it only shrinks): %s' % (opens[k], k[1], k[2], len(v), '\t'.join(k)))
                continue
            via = '' if k[0] == k[1] else ' (from %s)' % k[0].split('::')[-1]
            fail.append('%s:%d: %s%s reads `%s` (%s), which nothing vouches for as an RFC quantity: re-anchor it on the RFC quantity, '
                        'or add `// rfc-quantity: <why, citing RFC N §x>` on the line, or a `name`/`call` line in tools/rfc-quantity-allow.txt; '
                        'a known open item only: a line in tools/rfc-quantity-open.txt'
                        % (os.path.relpath(f, root), ln, k[1].split('::')[-1], via, k[2], what))
        for k in sorted(set(opens) - set(hits)):
            fail.append('stale open line, no such read (delete it: the open ratchet only shrinks): %s' % '\t'.join(k))
    except Fail as e:
        fail.append(str(e))
    for f in fail: print('rfc-quantity: %s' % f, file=sys.stderr)
    if fail: return 1
    nopen = sum(opens.values())
    print('rfc-quantity: ok (%d allowed predicates, %d spec fns read, %d allowlist lines, %d open reads in %d lines)'
          % (len(roots), len(nfns), len(al), nopen, len(opens)))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
