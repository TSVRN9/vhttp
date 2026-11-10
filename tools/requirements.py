"""Requirements status gate (C1; audit F9). Usage: python3 -I tools/requirements.py check ROOT
Reads ROOT/docs/requirements.md: every table whose header starts `| § |` must be
`| § | Topic | #MUST/MUST NOT | Server applies? | Phase | Notes | Status |`, and every row has those 7 cells. The Status
cell is one or more `; `-separated items:
  proved:F[,F..]   F is `fn` or `Type::fn`; `fn` resolves as a carryovers `fn:` (tools/carryovers.py) and some fn in a
                   `verus!` block of a tracked crates/ .rs file whose path ends in F has an `ensures`
  tested:T[,T..]   T resolves as a carryovers `test:` (a #[test] fn); needs an open: item too (tested is open work)
  false (ID)       known false today: ID is an open docs/carryovers.tsv row whose source cites TRUSTED.md; needs open:<its owner>
  open:P           P is a roadmap phase that is not merged and owns the open tsv row `req-P`
  n/a, declined    alone; a Phase cell `N/A (..)` needs n/a, `Declined (..)` needs declined
A ticked row (a ✅ in any other cell) must have only proved: items. Each `## RFC` section holds exactly one table with that\nheader (its first table); a row of any other table carrying a ✅ or a Status item fails. A missing file, no table, no row,\nor a git error fails."""
import importlib.util
import os
import re
import sys

HEADER = ['§', 'Topic', '#MUST/MUST NOT', 'Server applies?', 'Phase', 'Notes', 'Status']
STATUS_TOKEN = re.compile(r'(?<![A-Za-z])(?:proved|tested|open):|\bfalse \(|\| *(?:n/a|declined) *\|')
QNAME = re.compile(r'^(?:[A-Za-z_][A-Za-z0-9_]*::)?[A-Za-z_][A-Za-z0-9_]*$')


def load(name, rel):
    sys.dont_write_bytecode = True  # no tools/__pycache__ in the caller's tree
    spec = importlib.util.spec_from_file_location(name, os.path.join(os.path.dirname(os.path.abspath(__file__)), rel))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


co = load('carryovers', 'carryovers.py')
acc = load('acceptance', 'acceptance.py')
Fail = co.Fail


def ensured(root, tracked):
    """Paths (crate::module::[Type::]fn) of every fn in a verus! block of a tracked crates/ .rs file with an ensures."""
    res = set()
    for f in sorted(tracked):
        if not (f.startswith('crates/') and f.endswith('.rs')):
            continue
        s = acc.strip(co.read(root, f))
        for m in re.finditer(r'(?<![A-Za-z0-9_])verus!\s*\{', s):
            b = acc.match_brace(s, m.end() - 1)
            if b < 0:
                raise Fail('%s: unbalanced verus! block' % f)
            try:
                found = acc.fns(s, m.end(), b - 1, f)
            except ValueError as e:
                raise Fail('%s: %s' % (f, e))
            res.update(p for p, _, cl, _, _ in found if re.search(r'\bensures\b', cl))
    if not res:
        raise Fail('no fn with an ensures in any tracked crates/ .rs file')
    return res


def check(root):
    tracked = set(co.git(root, 'ls-files', '-z').split('\0')) - {''}
    if not tracked:
        raise Fail('git ls-files lists nothing in %s' % root)
    phases, _ = co.roadmap(root)
    tsv = {}
    for l in co.read(root, 'docs/carryovers.tsv').split('\n')[1:]:
        f = l.split('\t')
        if len(f) == 6:
            tsv[f[0]] = f
    owners = {f[1] for f in tsv.values() if f[0] == 'req-' + f[1] and f[2] == 'open'}
    rs, ens = None, None
    rows, tables, counts = 0, 0, {}
    head = intable = False
    sec, sec_tables = None, 0  # the current `## RFC` heading and its tables
    lines = co.read(root, 'docs/requirements.md').splitlines()
    for i, l in enumerate(lines + ['## end'], 1):
        if l.startswith('## '):
            if sec is not None and sec_tables != 1:
                raise Fail('docs/requirements.md: %r has %d tables with the Status header, not 1' % (sec, sec_tables))
            sec, sec_tables = (l, 0) if l.startswith('## RFC ') else (None, 0)
        if not l.startswith('|'):
            head = intable = False
            continue
        c = co.cells(l)
        if not intable:  # a table's header line
            intable = True
            if c == HEADER or c[0] == '§' or (sec is not None and sec_tables == 0):
                if c != HEADER:
                    raise Fail('docs/requirements.md:%d: a table header that is not %r' % (i, ' | '.join(HEADER)))
                head, tables = True, tables + 1
                sec_tables += sec is not None
                continue
        if not head:
            if '✅' in l or STATUS_TOKEN.search(l):
                raise Fail('docs/requirements.md:%d: a table row outside a requirements table carries a tick or a Status item' % i)
            continue
        if set(''.join(c)) <= set('-: '):
            continue
        rows += 1
        if len(c) != 7 or not c[6]:
            raise Fail('docs/requirements.md:%d: a row without 7 cells and a Status: %r' % (i, l))
        where = 'docs/requirements.md:%d (§%s)' % (i, c[0])
        items = [x.strip() for x in c[6].split(';')]
        kinds = []
        for it in items:
            m = re.match(r'^(proved|tested|open):(.+)$', it) or re.match(r'^(false) \((.+)\)$', it) or re.match(r'^(n/a|declined)()$', it)
            if not m:
                raise Fail('%s: status item %r is not proved:, tested:, false (..), open:, n/a or declined' % (where, it))
            k, v = m.group(1), m.group(2)
            kinds.append(k)
            if k in ('proved', 'tested'):
                if rs is None:
                    rs, ens = co.rs_text(root, tracked), ensured(root, tracked)
                for n in v.split(','):
                    if not QNAME.match(n) or (k == 'tested' and '::' in n):
                        raise Fail('%s: %s:%s: %r is not a fn name' % (where, k, v, n))
                    if not co.fn_found(rs, 'fn' if k == 'proved' else 'test', n.split('::')[-1]):
                        raise Fail('%s: %s %s: %s' % (where, k, n, co.not_found('fn' if k == 'proved' else 'test', n.split('::')[-1])))
                    if k == 'proved' and not any(p.endswith('::' + n) for p in ens):
                        raise Fail('%s: proved %s: no fn `%s` with an ensures in a verus! block under crates/' % (where, n, n))
            elif k == 'open':
                if v not in phases:
                    raise Fail('%s: open:%s is not a phase of docs/roadmap.md' % (where, v))
                if phases[v] == 'merged':
                    raise Fail('%s: open:%s names a merged phase' % (where, v))
                if v not in owners:
                    raise Fail('%s: open:%s has no open req-%s row (owner %s) in docs/carryovers.tsv' % (where, v, v, v))
            elif k == 'false':
                r = tsv.get(v)
                if r is None or r[2] != 'open' or 'TRUSTED.md' not in r[4]:
                    raise Fail('%s: false (%s): not an open docs/carryovers.tsv row whose source cites TRUSTED.md' % (where, v))
                if 'open:' + r[1] not in items:
                    raise Fail('%s: false (%s) needs open:%s, the owner of %s' % (where, v, r[1], v))
        for k in set(kinds):
            counts[k] = counts.get(k, 0) + 1
        if ('n/a' in kinds or 'declined' in kinds) and len(items) != 1:
            raise Fail('%s: n/a and declined stand alone' % where)
        if 'tested' in kinds and 'open' not in kinds:
            raise Fail('%s: tested: without open: (tested is open work, not done)' % where)
        if c[4].startswith('N/A') and kinds != ['n/a']:
            raise Fail('%s: Phase %r needs Status n/a' % (where, c[4]))
        if c[4].startswith('Declined') and kinds != ['declined']:
            raise Fail('%s: Phase %r needs Status declined' % (where, c[4]))
        if any('✅' in x for x in c[:6]) and set(kinds) != {'proved'}:
            raise Fail('%s: ticked, but its Status %r is not proved: alone' % (where, c[6]))
    if not tables or not rows:
        raise Fail('docs/requirements.md: no `| § | ...` table rows')
    print('requirements: %d rows in %d tables (%s), ok' % (rows, tables, ', '.join('%s %d' % (k, counts.get(k, 0)) for k in ('proved', 'tested', 'false', 'open', 'n/a', 'declined'))))


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] != 'check':
        print('usage: requirements.py check ROOT', file=sys.stderr); sys.exit(1)
    try:
        check(sys.argv[2])
    except Fail as e:
        print('requirements: %s' % e, file=sys.stderr); sys.exit(1)
