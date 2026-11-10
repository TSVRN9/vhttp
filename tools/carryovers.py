"""Carryover gate (C3; audit F3, F18, F19). Usage: python3 -I tools/carryovers.py check ROOT
Reads ROOT/docs/roadmap.md (the table `| id | title | status | order | plan / merge |`), ROOT/docs/carryovers.tsv
(header `#id<TAB>owner<TAB>status<TAB>evidence<TAB>source<TAB>text`) and ROOT/TRUSTED.md, and fails unless:
- every tsv row has exactly the 6 header columns, none empty; ids are unique; every owner is a roadmap id;
- status is open (evidence `-`) or closed, and a closed row's evidence resolves: `test:N`/`fn:N` (`fn N` in a tracked
  .rs file), `doc:PATH` (a tracked path), `commit:SHA` (`git cat-file -e SHA^{commit}`);
- no `merged` phase owns an open row, and no TRUSTED.md row names a merged phase (the phase merged without its work);
- every TRUSTED.md table row has 4 cells and its last cell starts with a roadmap id or is `never (<reason>)`;
- no tracked `docs/rca/*.md` Evidence line, TRUSTED.md, docs/requirements.md or crates/**/*.rs line cites `.worktrees/`,
  `.superpowers/`, `/tmp/` or a `vt-*-evidence` dir (untracked evidence that later disappears).
A missing file, an empty table or tsv, or a git error fails. Row deletion is checked by scripts/carryovers.sh."""
import os, re, subprocess, sys

HEADER = ['#id', 'owner', 'status', 'evidence', 'source', 'text']
STATUSES = {'merged', 'in progress', 'planned', 'unplanned'}
UNTRACKED = re.compile(r'\.worktrees/|\.superpowers/|/tmp/|vt-[^/\s`]*-evidence')
EVIDENCE_LINE = re.compile(r'^\s*- \*\*Evidence(:\*\*|\*\*:)')
NAME = re.compile(r'^[A-Za-z_][A-Za-z0-9_]*$')


class Fail(Exception):
    pass


def git(root, *a):
    p = subprocess.run(['git', '-C', root] + list(a), capture_output=True)
    if p.returncode:
        raise Fail('git %s failed: %s' % (' '.join(a), p.stderr.decode(errors='replace').strip()))
    return p.stdout.decode('utf-8')


def read(root, rel):
    try:
        return open(os.path.join(root, rel), encoding='utf-8').read()
    except OSError as e:
        raise Fail('cannot read %s: %s' % (rel, e))


def cells(line):
    return [c.strip() for c in line.strip().strip('|').split('|')]


def roadmap(root):
    lines = read(root, 'docs/roadmap.md').splitlines()
    start = [i for i, l in enumerate(lines) if cells(l) == ['id', 'title', 'status', 'order', 'plan / merge']]
    if len(start) != 1:
        raise Fail('docs/roadmap.md: expected one table header `| id | title | status | order | plan / merge |`, found %d' % len(start))
    phases = {}
    for l in lines[start[0] + 1:]:
        if not l.startswith('|'):
            break
        c = cells(l)
        if set(''.join(c)) <= set('-: '):
            continue
        if len(c) != 5 or not c[0]:
            raise Fail('docs/roadmap.md: a table row without 5 cells: %r' % l)
        if c[0] in phases:
            raise Fail('docs/roadmap.md: phase %s listed twice' % c[0])
        if c[2] not in STATUSES:
            raise Fail('docs/roadmap.md: phase %s has status %r (one of: %s)' % (c[0], c[2], ', '.join(sorted(STATUSES))))
        phases[c[0]] = c[2]
    if not phases:
        raise Fail('docs/roadmap.md: the phase table has no rows')
    return phases


def check(root):
    tracked = set(git(root, 'ls-files', '-z').split('\0')) - {''}
    if not tracked:
        raise Fail('git ls-files lists nothing in %s' % root)
    phases = roadmap(root)
    rs = [f for f in sorted(tracked) if f.endswith('.rs')]
    fns = None

    rows = read(root, 'docs/carryovers.tsv').split('\n')
    if rows and rows[-1] == '':
        rows.pop()
    if not rows or rows[0].split('\t') != HEADER:
        raise Fail('docs/carryovers.tsv: the first line must be the header %r' % '\t'.join(HEADER))
    if len(rows) == 1:
        raise Fail('docs/carryovers.tsv has no rows')
    ids, n_open = set(), 0
    for i, l in enumerate(rows[1:], 2):
        f = l.split('\t')
        if len(f) != 6 or not all(x.strip() for x in f):
            raise Fail('docs/carryovers.tsv:%d: expected 6 non-empty tab-separated columns, got %d: %r' % (i, len(f), l))
        rid, owner, status, ev = f[:4]
        if rid in ids:
            raise Fail('docs/carryovers.tsv:%d: duplicate id %s' % (i, rid))
        ids.add(rid)
        if owner not in phases:
            raise Fail('docs/carryovers.tsv:%d: %s: owner %s is not a phase of docs/roadmap.md' % (i, rid, owner))
        if status == 'open':
            n_open += 1
            if ev != '-':
                raise Fail('docs/carryovers.tsv:%d: %s is open but names evidence %s' % (i, rid, ev))
            if phases[owner] == 'merged':
                raise Fail('docs/carryovers.tsv:%d: %s is open but its owner %s is merged (close it with evidence or move it to an open phase)' % (i, rid, owner))
            continue
        if status != 'closed':
            raise Fail('docs/carryovers.tsv:%d: %s: status %r is neither open nor closed' % (i, rid, status))
        kind, _, val = ev.partition(':')
        if kind in ('test', 'fn'):
            if not NAME.match(val):
                raise Fail('docs/carryovers.tsv:%d: %s: %s is not a fn name' % (i, rid, ev))
            if fns is None:
                fns = '\n'.join(read(root, p) for p in rs)
            if not re.search(r'\bfn %s\b' % re.escape(val), fns):
                raise Fail('docs/carryovers.tsv:%d: %s: evidence %s: no `fn %s` in a tracked .rs file' % (i, rid, ev, val))
        elif kind == 'doc':
            if val not in tracked:
                raise Fail('docs/carryovers.tsv:%d: %s: evidence %s is not a tracked path' % (i, rid, ev))
        elif kind == 'commit':
            if not re.match(r'^[0-9a-f]{7,40}$', val) or subprocess.run(
                    ['git', '-C', root, 'cat-file', '-e', val + '^{commit}'], capture_output=True).returncode:
                raise Fail('docs/carryovers.tsv:%d: %s: evidence %s is not a commit' % (i, rid, ev))
        else:
            raise Fail('docs/carryovers.tsv:%d: %s: evidence %r is not test:, fn:, doc: or commit:' % (i, rid, ev))

    trows, head = 0, None
    for i, l in enumerate(read(root, 'TRUSTED.md').splitlines(), 1):
        if not l.startswith('|'):
            head = None
            continue
        c = cells(l)
        if c[:1] == ['Item']:
            head = len(c)
            continue
        if head is None or set(''.join(c)) <= set('-: '):
            continue
        if len(c) != 4:
            raise Fail('TRUSTED.md:%d: a trusted-items row with %d cells, not 4' % (i, len(c)))
        trows += 1
        last = c[3]
        if re.match(r'^never \(.*\S.*\)$', last):
            continue
        m = re.match(r'^([0-9A-Za-z-]+)', last)
        if not m or m.group(1) not in phases:
            raise Fail('TRUSTED.md:%d: the removal cell %r starts with neither a roadmap id nor `never (` and a reason' % (i, last))
        if phases[m.group(1)] == 'merged':
            raise Fail('TRUSTED.md:%d: the removal cell names %s, which is merged and did not remove the row' % (i, m.group(1)))
    if not trows:
        raise Fail('TRUSTED.md: no trusted-items table rows (a `| Item | ...` header and rows)')

    scan = [f for f in sorted(tracked) if (f.startswith('docs/rca/') and f.endswith('.md') and '/' not in f[9:])
            or f in ('TRUSTED.md', 'docs/requirements.md') or (f.startswith('crates/') and f.endswith('.rs'))]
    for f in scan:
        rca = f.startswith('docs/rca/')
        for i, l in enumerate(read(root, f).splitlines(), 1):
            if rca and not EVIDENCE_LINE.match(l):
                continue
            m = UNTRACKED.search(l)
            if m:
                raise Fail('%s:%d cites %r, an untracked path: cite a test, a mutant id with `scripts/mutants.sh run`, a gate demo or a commit' % (f, i, m.group(0)))
    print('carryovers: %d rows (%d open), roadmap %d phases, ok' % (len(ids), n_open, len(phases)))


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] != 'check':
        print('usage: carryovers.py check ROOT', file=sys.stderr); sys.exit(1)
    try:
        check(sys.argv[2])
    except Fail as e:
        print('carryovers: %s' % e, file=sys.stderr); sys.exit(1)
