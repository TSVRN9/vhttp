"""Carryover gate (C3; audit F3, F18, F19). Usage: python3 -I tools/carryovers.py check ROOT
Reads ROOT/docs/roadmap.md (the table `| id | title | status | order | plan / merge |`), ROOT/docs/carryovers.tsv
(header `#id<TAB>owner<TAB>status<TAB>evidence<TAB>source<TAB>text`) and ROOT/TRUSTED.md, and fails unless:
- every tsv row has exactly the 6 header columns, none empty; ids are unique; every owner is a roadmap id;
- status is open (evidence `-`) or closed, and a closed row's evidence resolves: `fn:N` (`fn N` in a tracked .rs file under
  crates/ or tools/ct-fixtures/, never a gate-demos fixture), `test:N` (the same, with `#[test]` above the fn), `doc:PATH`
  (a tracked path), `commit:SHA` (`git cat-file -e SHA^{commit}`);
- no `merged` phase owns an open row, and no TRUSTED.md row names a merged phase (the phase merged without its work);
- a `merged` phase's plan / merge cell names a commit that is an ancestor of HEAD, and every first-parent merge commit of
  HEAD whose subject is `Merge phase-<id>` or `Merge branch 'phase-<id>'` names a roadmap phase that is `merged`;
- every TRUSTED.md table row has 4 cells and its last cell is `never (<reason>)` or starts with roadmap ids (every id
  before the first `(`);
- no tracked `docs/rca/*.md` Evidence bullet (its line and indented continuation lines), TRUSTED.md, docs/requirements.md
  or crates/**/*.rs line cites `.worktrees/`, `.superpowers/`, `/tmp/` or a `vt-*-evidence` dir (untracked evidence).
A missing file, an empty table or tsv, or a git error fails. Row deletion and un-merging are checked by scripts/carryovers.sh."""
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
    phases, cell = {}, {}
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
        cell[c[0]] = c[4]
    if not phases:
        raise Fail('docs/roadmap.md: the phase table has no rows')
    return phases, cell


def rs_text(root, tracked):
    """Every tracked .rs file under crates/ or tools/ct-fixtures/, joined: where `fn:` and `test:` names resolve."""
    return '\n'.join(read(root, p) for p in sorted(tracked) if p.endswith('.rs') and p.startswith(('crates/', 'tools/ct-fixtures/')))


def fn_found(text, kind, name):
    """`fn NAME` in text; for kind `test`, with `#[test]` (and other attributes) above it."""
    pat = r'\bfn %s\b' % re.escape(name)
    if kind == 'test':
        pat = r'#\[test\]\s*(?:#\[[^\]\n]*\]\s*)*(?:pub(?:\([^)]*\))?\s+)?' + pat
    return re.search(pat, text) is not None


def not_found(kind, name):
    return 'no %s`fn %s` in a tracked .rs file under crates/ or tools/ct-fixtures/' % ('#[test] ' if kind == 'test' else '', name)


def check(root):
    tracked = set(git(root, 'ls-files', '-z').split('\0')) - {''}
    if not tracked:
        raise Fail('git ls-files lists nothing in %s' % root)
    phases, merge_cell = roadmap(root)
    for pid, st in sorted(phases.items()):
        if st == 'merged' and not any(subprocess.run(['git', '-C', root, 'merge-base', '--is-ancestor', sha, 'HEAD'],
                                                     capture_output=True).returncode == 0
                                      for sha in re.findall(r'\b[0-9a-f]{7,40}\b', merge_cell[pid])):
            raise Fail('docs/roadmap.md: phase %s is merged but its plan / merge cell names no commit that is an ancestor of HEAD' % pid)
    for l in git(root, 'log', '--first-parent', '--merges', '--format=%h %s', 'HEAD').splitlines():
        m = re.match(r"^(\S+) Merge (?:branch ')?phase-([0-9A-Za-z-]+)", l)
        if not m:
            continue
        name = m.group(2)
        pid = name if name in phases else max((p for p in phases if name.startswith(p + '-')), key=len, default=None)
        if pid is None:
            raise Fail('merge %s merges phase-%s, which names no phase of docs/roadmap.md' % (m.group(1), name))
        if phases[pid] != 'merged':
            raise Fail('merge %s merges phase-%s, but docs/roadmap.md says %s is %s' % (m.group(1), name, pid, phases[pid]))
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
                fns = rs_text(root, tracked)
            if not fn_found(fns, kind, val):
                raise Fail('docs/carryovers.tsv:%d: %s: evidence %s: %s' % (i, rid, ev, not_found(kind, val)))
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
        toks = [t for t in re.split(r'[,\s]+', last.split('(')[0]) if t]
        if not toks or any(t not in phases for t in toks):
            raise Fail('TRUSTED.md:%d: the removal cell %r starts with neither roadmap ids nor `never (` and a reason' % (i, last))
        for t in toks:
            if phases[t] == 'merged':
                raise Fail('TRUSTED.md:%d: the removal cell names %s, which is merged and did not remove the row' % (i, t))
    if not trows:
        raise Fail('TRUSTED.md: no trusted-items table rows (a `| Item | ...` header and rows)')

    scan = [f for f in sorted(tracked) if (f.startswith('docs/rca/') and f.endswith('.md') and '/' not in f[9:])
            or f in ('TRUSTED.md', 'docs/requirements.md') or (f.startswith('crates/') and f.endswith('.rs'))]
    for f in scan:
        rca, ev = f.startswith('docs/rca/'), False
        for i, l in enumerate(read(root, f).splitlines(), 1):
            if rca:  # an Evidence bullet and its indented continuation lines
                ev = bool(EVIDENCE_LINE.match(l)) or (ev and l[:1] in (' ', '\t') and bool(l.strip()))
                if not ev:
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
