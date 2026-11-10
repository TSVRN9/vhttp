"""First-parent history walk for the shrink-only ratchet files (Phase 9r2 R5).
Usage: python3 -I tools/ratchet_walk.py ROOT FILE MODE [BASE]   (MODE: lines | open | ceilings | floors | ids | merged)
Walks the first-parent history of HEAD in ROOT from the commit that introduced FILE. The floor is the keys present in
every copy, each at its lowest value (lines: the stripped non-comment lines; open: ROOT<TAB>FN<TAB>READ keyed, COUNT;
ceilings: CRATE FN VALUE, FN keyed, VALUE). HEAD's copy and the working tree must lie within the floor: growth that was
shrunk back passes, growth that persists (or a shrink then a re-grow) fails. floors (test counts that only grow): CRATE COUNT; the floor is each key's highest value over the history, a key once present may
not disappear, and HEAD's copy and the working tree must be at or above it. ids (docs/carryovers.tsv): the key is a line's
first tab-separated field, and a key present in any copy may not disappear (a row is closed, never deleted). merged
(docs/roadmap.md): the keys are the ids of the table rows whose status cell is `merged`; a phase once merged stays merged.
With BASE (floors, ids and merged only), the floor is BASE's copy alone: no value lower, no key removed (the branch check). A commit that deletes the file is not a
reset. Commit messages are ignored (there is no reset). Any git error, and a shallow clone, fail (fail closed)."""
import os, subprocess, sys


class Fail(Exception):
    pass


def git(root, *a):
    p = subprocess.run(['git', '-C', root] + list(a), capture_output=True)
    if p.returncode:
        raise Fail('git %s failed: %s' % (' '.join(a), p.stderr.decode(errors='replace').strip()))
    return p.stdout.decode('utf-8')


def parse(text, mode):
    d = {}
    for l in text.splitlines():
        if not l.strip() or l.lstrip().startswith('#'):
            continue
        if mode == 'lines':
            d[l.strip()] = 0
        elif mode == 'ids':
            d[l.split('\t')[0]] = 0
        elif mode == 'merged':
            c = [x.strip() for x in l.strip().strip('|').split('|')]
            if l.startswith('|') and len(c) >= 3 and c[2] == 'merged':
                d[c[0]] = 0
        elif mode == 'open':
            f = l.split('\t')
            d[tuple(f[:3]) if len(f) >= 4 and f[3].isdigit() else l] = int(f[3]) if len(f) >= 4 and f[3].isdigit() else 0
        elif mode == 'floors':
            f = l.split()
            if len(f) != 2 or not f[1].isdigit():
                raise Fail('unreadable floors line: %r' % l)
            if f[0] in d:
                raise Fail('duplicate floors line for %s' % f[0])
            d[f[0]] = int(f[1])
        else:
            f = l.split()
            if len(f) != 3 or not f[2].isdigit():
                raise Fail('unreadable ceilings line: %r' % l)
            if f[1] in d:
                raise Fail('duplicate ceilings line for %s' % f[1])
            d[f[1]] = int(f[2])
    return d


def floor_of(versions):
    """keys present in every version, each at its minimum value"""
    fl = dict(versions[0])
    for v in versions[1:]:
        fl = {k: min(n, v[k]) for k, n in fl.items() if k in v}
    return fl


def below(cur, fl, mode=None):
    for k, v in sorted(fl.items()):
        if k not in cur:
            if mode == 'merged':
                return 'phase %s is no longer merged (a phase once merged stays merged)' % k
            return '%s was removed (a floor line once present stays)' % k
        if cur[k] < v:
            return '%s at %d, below its highest earlier value %d' % (k, cur[k], v)
    return None


def outside(cur, fl):
    for k, v in sorted(cur.items(), key=str):
        if k not in fl:
            return 'new line %s (not in every earlier copy)' % (k,)
        if v > fl[k]:
            return '%s at %d, above its lowest earlier value %d' % (k, v, fl[k])
    return None


def main(root, path, mode, base=None):
    grows = mode in ('floors', 'ids', 'merged')  # a key once present stays; values only grow
    if mode not in ('lines', 'open', 'ceilings', 'floors', 'ids', 'merged') or (base and not grows):
        raise Fail('unknown mode %s' % mode)
    if git(root, 'rev-parse', '--is-shallow-repository').strip() != 'false':
        raise Fail('the clone is shallow (history missing): %s cannot be walked; fetch the full history' % path)
    if base:
        old = parse(git(root, 'show', '%s:%s' % (base, path)), mode)
        try:
            cur = parse(open(os.path.join(root, path), encoding='utf-8').read(), mode)
        except OSError as e:
            raise Fail('cannot read %s: %s' % (path, e))
        bad = below(cur, old, mode)
        if bad:
            raise Fail('%s: %s against the merge-base %s (the floor only grows)' % (path, bad, base[:12]))
        print('ratchet-walk: %s ok against %s' % (path, base[:12]))
        return
    commits = git(root, 'rev-list', '--first-parent', '--reverse', 'HEAD', '--', path).split()
    versions = []
    for c in commits:
        if not git(root, 'ls-tree', '--name-only', c, '--', path).strip():
            continue  # absent at c: not a reset, the next copy meets the floor of the earlier ones
        try:
            versions.append(parse(git(root, 'show', '%s:%s' % (c, path)), mode))
        except Fail as e:
            raise Fail('%s at %s: %s' % (path, c[:12], e))
    checks = []
    if versions:
        checks.append(('HEAD', versions[-1]))
    try:
        checks.append(('the working tree', parse(open(os.path.join(root, path), encoding='utf-8').read(), mode)))
    except FileNotFoundError:
        pass  # the tool's own check fails a missing file
    except OSError as e:
        raise Fail('cannot read %s: %s' % (path, e))
    if versions:
        if grows:
            fl = {}
            for v in versions:
                for k, n in v.items():
                    fl[k] = max(n, fl.get(k, 0))
        else:
            fl = floor_of(versions)
        for what, cur in checks:
            bad = below(cur, fl, mode) if grows else outside(cur, fl)
            if bad:
                raise Fail('%s: %s is outside the floor of its first-parent history: %s%s' % (
                    path, what, bad, '' if grows else ' (the file only shrinks)'))
    print('ratchet-walk: %s ok (%d commits touch it)' % (path, len(commits)))


if __name__ == '__main__':
    if len(sys.argv) not in (4, 5):
        print('usage: ratchet_walk.py ROOT FILE MODE [BASE]', file=sys.stderr); sys.exit(1)
    try:
        main(*sys.argv[1:])
    except Fail as e:
        print('ratchet-walk: %s' % e, file=sys.stderr); sys.exit(1)
