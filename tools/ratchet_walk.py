"""First-parent history walk for the shrink-only ratchet files (Phase 9r2 R5).
Usage: python3 -I tools/ratchet_walk.py ROOT FILE MODE   (MODE: lines | open | ceilings)
Walks the first-parent history of HEAD in ROOT, from the commit that introduced FILE, and fails if any step
grows it: a new line (lines: the stripped non-comment lines; open: ROOT<TAB>FN<TAB>READ keyed, COUNT may not
rise; ceilings: CRATE FN VALUE, FN keyed, VALUE may not rise). A commit that deletes the file is not a reset: the
next copy is compared with the last one present. Any git error, and a shallow clone, fail (fail closed)."""
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
        elif mode == 'open':
            f = l.split('\t')
            d[tuple(f[:3]) if len(f) >= 4 and f[3].isdigit() else l] = int(f[3]) if len(f) >= 4 and f[3].isdigit() else 0
        else:
            f = l.split()
            if len(f) != 3 or not f[2].isdigit():
                raise Fail('unreadable ceilings line: %r' % l)
            if f[1] in d:
                raise Fail('duplicate ceilings line for %s' % f[1])
            d[f[1]] = int(f[2])
    return d


def main(root, path, mode):
    if mode not in ('lines', 'open', 'ceilings'):
        raise Fail('unknown mode %s' % mode)
    if git(root, 'rev-parse', '--is-shallow-repository').strip() != 'false':
        raise Fail('the clone is shallow (history missing): %s cannot be walked; fetch the full history' % path)
    commits = git(root, 'rev-list', '--first-parent', '--reverse', 'HEAD', '--', path).split()
    prev = None
    steps = [(c, None) for c in commits]
    try:
        wt = open(os.path.join(root, path), encoding='utf-8').read()
    except FileNotFoundError:
        wt = None  # the tool's own check fails a missing file
    except OSError as e:
        raise Fail('cannot read %s: %s' % (path, e))
    if wt is not None:
        steps.append(('the working tree', wt))
    for c, text in steps:
        if text is None:
            if not git(root, 'ls-tree', '--name-only', c, '--', path).strip():
                continue  # deleted at c
            text = git(root, 'show', '%s:%s' % (c, path))
        try:
            cur = parse(text, mode)
        except Fail as e:
            raise Fail('%s at %s: %s' % (path, c[:12], e))
        if prev is not None:
            for k, v in sorted(cur.items(), key=str):
                if k not in prev:
                    raise Fail('%s grew at %s: new line %s (the file only shrinks, across the whole first-parent history and the working tree)' % (path, c[:12], k))
                if v > prev[k]:
                    raise Fail('%s grew at %s: %s raised from %d to %d (the file only shrinks, across the whole first-parent history and the working tree)' % (path, c[:12], k, prev[k], v))
        prev = cur
    print('ratchet-walk: %s ok (%d commits touch it)' % (path, len(commits)))


if __name__ == '__main__':
    if len(sys.argv) != 4:
        print('usage: ratchet_walk.py ROOT FILE MODE', file=sys.stderr); sys.exit(1)
    try:
        main(*sys.argv[1:])
    except Fail as e:
        print('ratchet-walk: %s' % e, file=sys.stderr); sys.exit(1)
