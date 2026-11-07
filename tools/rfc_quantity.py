"""RFC-quantity gate (Phase 9r2 R4, class C8). Run via scripts/rfc-quantity.sh.

Usage: python3 -I tools/rfc_quantity.py [--root DIR] [--allow FILE] [--open FILE] [--old-open FILE]
       [--allow-digest HEX] (the demos' fixture digest; the real tree uses ALLOW_DIGEST)
       [--print-digest ROOT|allowlist] (print a root's digest or the allowlist's, run deliberately after a re-review)

C8: an allowed_*err predicate written over the code's own bookkeeping (a read-offset window, a
`seen` mask, a running `high`) instead of the RFC's quantities, so the proof checks the code
against itself. This gate reads the body of every `allowed_*err`, `allowed_*err_from` and
`*_allowed_err` spec fn (the ROOTs; tools/acceptance.py's scanner and name pattern) and of every
spec fn it calls, transitively (one level is not enough: recv_allowed_err -> flow_trigger ->
credit_before), and reports every read of something that is not vouched for as an RFC quantity:
  - a struct field (`s.high`, `s.final_size->0`, `b@.foo`), on any receiver; a struct update `..s`;
  - a method that is not a vstd Seq/Set/Map method (`s.reassembly()`, `x.rfc()`, `y.code_spec()`); a
    user spec method named like a vstd one is refused outright;
  - `self`, a macro call, or a call of a fn that is not a spec fn in a scanned verus! block (vstd's
    `Seq::`/`Set::`/`Map::`/`Multiset::` constructors excepted);
  - a name (a parameter or a pattern-bound local) used other than as a whole argument of a call that
    is followed or allowed: `seen & tp_bit(id)` reads `seen`; `rfc_tp_apply(id, v, true, t, seen)`
    passes it on (the callee's own reads are what count).
A read is vouched for by one of:
  - `// rfc-quantity: READ: <why READ is the RFC's quantity, citing RFC N §x>` on its source line; it
    vouches only for the read it names (another read on the line is still reported);
  - a `name` line of the allowlist (ROOT, FN, READ: READ, a name or a field read in FN under ROOT, is
    the RFC quantity the reason says), or a `call` line (ROOT, CALLER, CALLEE: CALLEE is an RFC spec fn,
    not followed from CALLER under ROOT); every reason cites `RFC N §x`. There is no prefix rule:
    rfc_* fns in this tree include models of the code (rfc_recv, rfc_tp_apply) that return bookkeeping;
  - a line of the open ratchet (ROOT, FN, READ, COUNT, OWNER, REASON): a known violation that is
    not an RFC quantity and cannot be fixed by this phase. It only shrinks: a line absent from
    --old-open (the file at the merge-base with main), or with a larger count, fails.
Every vouch is keyed by its ROOT, and the ROOT's `root` line pins a sha256 of the source text of the
ROOT, of every fn its walk reaches or calls unfollowed and every fn those call, transitively (methods
resolved by name in the crate; an ambiguous name fails), of the fns its `pin` lines name (text a
reason relies on outside the walk: what the model pushes, an invariant, a wf tie), and of every
`const`/`static` that text names; each fn's text starts after the item before it, so its attributes
and doc comment are in, and comments and annotations are included. A `use .. as` rename of a name
that text uses, in a file holding any of it, is refused (the gate reads names, not what they stand
for). The
vouches' reasons are claims about that text (what a caller passes, how a call's result is used, what
an annotation says), so any edit to it fails ("re-review the vouches for ROOT") until a reviewer
re-reads them and updates the digest with --print-digest; the gate never prints a new digest itself.
Fails closed: no predicate, a predicate without a `root` line or whose digest differs, a stale root
line, a predicate or callee whose body cannot be found, an ambiguous callee name, a missing or
malformed list file, an empty, uncited or read-less annotation, an uncited reason, an allowlist line
or annotation that vouches for nothing (stale), an open line that matches no read (stale) or whose
count is not the current count, or an allowlist whose digest is not ALLOW_DIGEST (the allowlist is a
ratchet: any change to it, growth or a swap, needs this constant changed in the same diff).

Limits (a token scan of comment- and string-stripped text, not a Rust parser): pattern bindings are
found in match arms (back from `=>` to the arm start), `let`/`if let` patterns, closure and
quantifier binders and `matches` patterns; a token it cannot place is a read (fails closed). Only
predicate bodies and the spec fns they call are read: what an exec fn's ensures pass as the
predicate's arguments (`recv_allowed_err(old(self).rfc(), ..)`) is the refinement proof's business.
The scan is the first filter; the root digest is what makes a reviewer re-check the vouches' claims
about the text (a `name` line's claim about what every caller passes, a `call` line's claim about
how its result is used) whenever that text changes. The gate does not check meaning: that a vouch is
true is the reviewer's, and the semantic catches are the proofs, rule 1c's non-vacuity lemmas and
rule 1d's registered re-anchoring mutants (tools/mutants.tsv).
"""
import hashlib, importlib.util, os, re, sys

# sha256 of the allowlist's non-comment lines, sorted and joined by newlines: any change to the vouched-for set (a
# new line, a swap, an edited reason) needs this constant changed in the same diff, so it is reviewed
ALLOW_DIGEST = '09b6e83d6dafe169334fe913b0ba47e974daeaaa97cd43d9d84cfba5eb7d7721'
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
    """The accessors after index j: [(kind, start, end, name)] with kind field/method/index/num/view, up to the first
    that is not one; end is past the accessor (past a method's argument list)."""
    res = []
    while True:
        k = fwd(b, j)
        if b.startswith('..', k): break
        if b.startswith('@', k):  # a view: the accessors after it are still read
            res.append(('view', k, k + 1, '')); j = k + 1; continue
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
        self.allsites = sites  # exec fns too, for `pin` lines
        self.apos = apos
        self.text, self.raw, self.rawstr = {}, {}, {}
        self.cache = {}
        # a user spec method with a vstd method's name would be taken for vstd and not followed: refuse it
        for x in self.sites:
            parts = x[2].split('::')
            if parts[-1] in VSTD_METHODS and any(p[:1].isupper() for p in parts[1:-1]):
                raise Fail('%s: a spec method named like a vstd method (%s) would be read as vstd; rename it' % (x[2], parts[-1]))

    def src(self, f):
        if f not in self.text:
            r = open(f, encoding='utf-8').read()
            self.raw[f], self.text[f], self.rawstr[f] = r.split('\n'), self.acc.strip(r), r
        return self.text[f]

    def line(self, f, off):
        return self.src(f).count('\n', 0, off) + 1

    def site_of_pred(self, f, off, name):
        hit = [x for x in self.sites if x[0] == f and off <= x[1] < off + 200 and x[2].split('::')[-1] == name]
        if len(hit) != 1: raise Fail('%s: spec fn %s is not in a scanned verus! block' % (os.path.relpath(f, self.root), name))
        return hit[0]

    def resolve(self, caller, name, qual):
        """The spec fn site a call of `qual::name` in caller names, None if no scanned fn has that name; raise when
        more than one could be meant. A path keeps the fns whose module path ends with it (`crate` is the caller's
        crate; `self`/`super` are dropped, which only widens the match); an unqualified name is the caller's own
        module's fn (it shadows a glob import), else the one fn of that name in all scanned crates."""
        cand = [x for x in self.sites if x[2].split('::')[-1] == name]
        q = [caller[2].split('::')[0] if x == 'crate' else x for x in qual if x not in ('self', 'super')]
        if q:
            cand = [x for x in cand if x[2].split('::')[:-1][-len(q):] == q]
        else:
            cand = [x for x in cand if x[0] == caller[0]] or cand
        paths = sorted({x[2] for x in cand})
        if len(paths) > 1: raise Fail('%s calls %s, which names %d spec fns (%s): ambiguous' % (caller[2], '::'.join(qual + [name]), len(paths), ', '.join(paths)))
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

    def fn_text(self, site):
        """The raw source of a fn from the end of the item before it (so its doc comment and attributes are in) to its
        body's end, comments and annotations included."""
        lo, hi = self.body(site)
        s, st = self.rawstr[site[0]], self.text[site[0]]
        b = max(st.rfind(';', 0, site[1]), st.rfind('}', 0, site[1]), st.rfind('{', 0, site[1]))
        return s[b + 1:hi + 1]

    def callees_any(self, site):
        """Every scanned spec fn site the body of site calls, free or as a method (a vstd method name excepted, and an
        unresolved name taken for vstd); raise when a name could mean more than one fn."""
        lo, hi = self.body(site)
        b = self.text[site[0]][lo:hi]
        out = []
        for m in IDENT.finditer(b):
            nm, i, e = m.group(0), m.start(), m.end()
            p = fwd(b, e)
            if b[p:p + 1] != '(' or nm in KEYWORDS or nm[0].isupper() or nm == 'self': continue
            pb = back(b, i)
            if pb >= 0 and (b[pb] == '.' or b[pb - 1:pb + 1] == '->'):
                if nm in VSTD_METHODS: continue
                crate = site[2].split('::')[0]
                cand = [x for x in self.sites if x[2].split('::')[-1] == nm and any(q[:1].isupper() for q in x[2].split('::')[1:-1])]
                cand = [x for x in cand if x[2].split('::')[0] == crate] or cand
                paths = sorted({x[2] for x in cand})
                if len(paths) > 1: raise Fail('%s calls the method %s, which names %d spec fns (%s): ambiguous' % (site[2], nm, len(paths), ', '.join(paths)))
                out += cand[:1]
                continue
            qual, j = [], i
            while True:
                k = back(b, j)
                if k >= 1 and b[k - 1:k + 1] == '::':
                    mm = re.search(r'([A-Za-z_][A-Za-z0-9_]*)\s*(?:::\s*)?(<[^<>]*>)?\s*$', b[:k - 1])
                    if not mm: break
                    qual.insert(0, mm.group(1)); j = mm.start()
                else:
                    break
            x = self.resolve(site, nm, qual)
            if x is not None: out.append(x)
        return out

    def consts(self):
        """{NAME: [raw text of each `const`/`static` NAME definition in crates/]}."""
        if not hasattr(self, '_consts'):
            self._consts = {}
            for _, _, f in self.acc.rs_files(self.root):
                st = self.src(f)
                for m in re.finditer(r'(?<![A-Za-z0-9_])(?:const|static)\s+(?:mut\s+)?([A-Z][A-Z0-9_]*)\s*:', st):
                    e = st.find(';', m.end())
                    if e < 0: raise Fail('%s: const %s: no `;`' % (f, m.group(1)))
                    self._consts.setdefault(m.group(1), []).append(self.rawstr[f][m.start():e + 1])
        return self._consts

    def digest(self, rp, walk, allowed, pins):
        """sha256 of the source text a root's vouches rest on: the walk's fns, every fn they or an unfollowed callee call,
        transitively, the pinned fns, and the definition of every constant any of that text names; also refuse a
        `use .. as` rename of a name that text uses, in a file holding any of it."""
        texts, work = {}, list(walk) + list(allowed)
        while work:
            x = work.pop()
            if x[2] in texts: continue
            texts[x[2]] = self.fn_text(x)
            work += self.callees_any(x)
        for x in pins:
            texts.setdefault(x[2], self.fn_text(x))
        files = {x[0] for x in list(walk) + list(allowed) + list(pins)}
        files |= {x[0] for x in self.sites + self.allsites if x[2] in texts}
        toks = {m.group(0) for v in texts.values() for m in IDENT.finditer(v)}
        for f in sorted(files):
            for u in re.finditer(r'(?<![A-Za-z0-9_])use\b([^;]*);', self.text[f]):
                for r in re.finditer(r'([A-Za-z0-9_]+)\s+as\s+([A-Za-z0-9_]+)', u.group(1)):
                    if r.group(2) in toks:
                        raise Fail('%s: `use .. %s` renames a name that the text %s rests on uses: the gate reads and hashes '
                                   'the name, not the item it stands for; refused' % (os.path.relpath(f, self.root), r.group(0), rp))
        cs = self.consts()
        named = sorted(n for n in toks if n in cs)
        body = ''.join('%s\n%s\n' % (p, texts[p]) for p in sorted(texts))
        body += ''.join('const %s\n%s\n' % (n, '\n'.join(cs[n])) for n in named)
        return sha(body)

    def analyse(self, site, allow_calls, rootp):
        """(reads [(kind, text, file, line)], followed callees [site], allowed callees [site]) of one fn's body, under
        root rootp's `call` lines allow_calls {(caller, callee): used}."""
        key = (rootp, site[2])
        if key in self.cache: return self.cache[key]
        f = site[0]
        s = self.src(f)
        lo, hi = self.body(site)
        b = s[lo:hi]
        pats = pattern_spans(self.acc, b)
        in_pat = lambda i: any(a <= i < e for a, e in pats)
        reads, callees, allowed, done = [], [], [], set()
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
                calls[i] = 'allowed'; allow_calls[(site[2], t[2])] = True; allowed.append(t)
            else:
                calls[i] = 'followed'; callees.append(t)
        for m in IDENT.finditer(b):
            nm, i, e = m.group(0), m.start(), m.end()
            if i in calls: continue
            pb = back(b, i)
            if pb >= 1 and b[pb - 1:pb + 1] == '..' and not nm[0].isupper():
                reads.append(('update', '..' + nm, *at(i))); continue  # `S { f: x, ..s }` reads every other field of s
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
        # accessors on call results, parenthesised expressions and struct literals
        for m in re.finditer(r'[)\]}]', b):
            for kind, a, z, mn in chain(b, m.end()):
                if a in done: break
                done.add(a)
                if kind == 'field' or (kind == 'method' and mn not in VSTD_METHODS):
                    st = m.start()
                    reads.append(('field' if kind == 'field' else 'method', '(..)' + ' '.join(b[m.end():z].split()), *at(st)))
                    break
        self.cache[key] = (reads, callees, allowed)
        return self.cache[key]


acc_ = None


def read_list(path, what):
    try:
        lines = open(path, encoding='utf-8').read().split('\n')
    except OSError as e:
        raise Fail('cannot read the %s %s: %s' % (what, path, e))
    return [(n + 1, l) for n, l in enumerate(lines) if l.strip() and not l.lstrip().startswith('#')]


LINE_FORMS = ('`root<TAB>ROOT<TAB>DIGEST`, `pin<TAB>ROOT<TAB>FN`, `call<TAB>ROOT<TAB>CALLER<TAB>CALLEE<TAB>REASON` or '
              '`name<TAB>ROOT<TAB>FN<TAB>READ<TAB>REASON`')
WHAT = {'field': 'a struct field', 'update': 'a struct update, every field it does not set',
        'method': 'a method that is not a vstd Seq/Set/Map method', 'self': 'self', 'macro': 'a macro',
        'call': 'a fn that is not a spec fn in a scanned verus! block',
        'name': 'a name used other than as a whole argument of a followed or allowed call'}


def sha(text):
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def annotation(line):
    """(read, reason) of a `// rfc-quantity: READ: <reason>` on line, ('', '') if malformed, None if there is none."""
    a = ANNOT.search(line)
    if not a: return None
    c = a.group(1).strip()
    k = c.find(': ')
    if k <= 0 or not c[k + 2:].strip(): return ('', '')
    return (c[:k].strip(), c[k + 2:].strip())


def main(argv):
    global acc_
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
    allow = opn = old = pd = None
    nallow = ALLOW_DIGEST
    while argv:
        if argv[0] in ('--root', '--allow', '--open', '--old-open', '--allow-digest', '--print-digest') and len(argv) > 1:
            v = argv[1]
            if argv[0] == '--root': root = v
            elif argv[0] == '--allow': allow = v
            elif argv[0] == '--open': opn = v
            elif argv[0] == '--allow-digest': nallow = v
            elif argv[0] == '--print-digest': pd = v
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
        # the allowlist: every vouch is keyed by its root predicate, whose body text is pinned by the root's line
        rootd, calls, names, pins = {}, {}, {}, {}  # calls/names: root -> {(fn, x): used}; pins: root -> {fn path}
        al = read_list(allow, 'allowlist')
        for n, l in al:
            f = l.split('\t')
            if not (f[0] in ('root', 'pin') and len(f) == 3 or f[0] in ('call', 'name') and len(f) == 5) or not all(x.strip() for x in f):
                raise Fail('%s:%d: not %s' % (allow, n, LINE_FORMS))
            if f[0] == 'root':
                if f[1] in rootd: fail.append('%s:%d: duplicate root line' % (allow, n))
                rootd[f[1]] = f[2]; continue
            if f[0] == 'pin':
                if f[2] in pins.setdefault(f[1], set()): fail.append('%s:%d: duplicate pin line' % (allow, n))
                pins[f[1]].add(f[2]); continue
            if not CITE.search(f[4]): fail.append('%s:%d: the reason cites no `RFC N §x`' % (allow, n))
            d = (calls if f[0] == 'call' else names).setdefault(f[1], {})
            if (f[2], f[3]) in d: fail.append('%s:%d: duplicate line' % (allow, n))
            d[(f[2], f[3])] = False
        adig = sha('\n'.join(sorted(l for _, l in al)))
        if pd == 'allowlist':
            print(adig); return 0
        if adig != nallow:
            fail.append('the allowlist\'s digest is not ALLOW_DIGEST in tools/rfc_quantity.py (the allowlist is a ratchet: any change '
                        'to its lines needs the constant changed in the same diff, for review; compute it with --print-digest allowlist)')
        ol = read_list(opn, 'open ratchet')
        opens = {}
        for n, l in ol:
            f = l.split('\t')
            if len(f) != 6 or not all(x.strip() for x in f) or not f[3].isdigit() or not re.match(r'^9[a-z0-9]+\b', f[4]):
                raise Fail('%s:%d: not `ROOT<TAB>FN<TAB>READ<TAB>COUNT<TAB>OWNER-PHASE ..<TAB>REASON`' % (opn, n))
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
        if pd is not None and pd not in {r[2] for r in roots}: raise Fail('--print-digest: no predicate %s' % pd)
        hits = {}  # (root, fn, read) -> [(kind, file, line)]
        used_ann, nfns = set(), set()
        for r in roots:
            rp = r[2]
            rc, rn = calls.setdefault(rp, {}), names.setdefault(rp, {})
            seen, work, walked, unf = {rp}, [r], [], []
            while work:
                st = work.pop()
                reads, callees, allowed = g.analyse(st, rc, rp)
                nfns.add(st[2])
                walked.append(st); unf += allowed
                for kind, text, f, ln in reads:
                    if kind in ('name', 'field') and (st[2], text) in rn:
                        rn[(st[2], text)] = True; continue
                    a = annotation(g.raw[f][ln - 1])
                    if a and a[0] == text:  # an annotation vouches only for the read it names
                        used_ann.add((f, ln)); continue
                    hits.setdefault((rp, st[2], text), []).append((kind, f, ln))
                for t in callees:
                    if t[2] not in seen: seen.add(t[2]); work.append(t)
            # the root's digest: the source text its vouches rest on, comments included
            ps = []
            for p in sorted(pins.get(rp, {})):
                x = [y for y in g.allsites if y[2] == p]
                if len(x) != 1: fail.append('pin line for %s names %s, which is %s' % (rp, p, 'not a fn in a scanned verus! block' if not x else 'two fns')); continue
                ps.append(x[0])
            d = g.digest(rp, walked, unf, ps)
            if pd == rp:
                print(d); return 0
            if rp not in rootd:
                fail.append('no `root` line for %s: review every read it makes, add its name/call lines, then a `root` line '
                            '(digest from --print-digest %s)' % (rp, rp))
            elif rootd[rp] != d:
                fail.append('%s or a fn it reaches changed since its vouches were reviewed: re-review the vouches for %s; then update '
                            'its digest (--print-digest %s)' % (rp, rp, rp))
        for p in sorted((set(rootd) | set(pins)) - {r[2] for r in roots}):
            fail.append('stale root or pin line, no such predicate: %s' % p)
        # annotations: each names its read, cites the RFC and vouches for that read
        for _, _, f in acc_.rs_files(root):
            g.src(f)
        for f in sorted(g.raw):
            for n, l in enumerate(g.raw[f]):
                a = annotation(l)
                if a is None: continue
                rel = os.path.relpath(f, root)
                if not a[0] or not CITE.search(a[1]):
                    fail.append('%s:%d: `// rfc-quantity:` needs `READ: <why it is the RFC quantity, citing RFC N §x>`' % (rel, n + 1))
                elif (f, n + 1) not in used_ann:
                    fail.append('%s:%d: `// rfc-quantity: %s:` names no read on its line from an allowed_*err predicate (stale)' % (rel, n + 1, a[0]))
        for dct, what in ((calls, 'call'), (names, 'name')):
            for rp, dd in sorted(dct.items()):
                for k, used in sorted(dd.items()):
                    if not used: fail.append('stale allowlist line, vouches for no read or call: %s\t%s\t%s\t%s' % (what, rp, k[0], k[1]))
        for k, v in sorted(hits.items()):
            kind, f, ln = v[0]
            if k in opens:
                if opens[k] != len(v): fail.append('open line count %d, but %s reads %s %d times (set the count; it only shrinks): %s' % (opens[k], k[1], k[2], len(v), '\t'.join(k)))
                continue
            via = '' if k[0] == k[1] else ' (from %s)' % k[0].split('::')[-1]
            fail.append('%s:%d: %s%s reads `%s` (%s), which nothing vouches for as an RFC quantity: re-anchor it on the RFC quantity, '
                        'or add `// rfc-quantity: %s: <why, citing RFC N §x>` on the line, or a `name`/`call` line for this root in '
                        'tools/rfc-quantity-allow.txt; a known open item only: a line in tools/rfc-quantity-open.txt'
                        % (os.path.relpath(f, root), ln, k[1].split('::')[-1], via, k[2], WHAT[kind], k[2]))
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
