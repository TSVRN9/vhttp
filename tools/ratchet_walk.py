"""First-parent history walk for the shrink-only ratchet files (Phase 9r2 R5).
Usage: python3 -I tools/ratchet_walk.py ROOT FILE MODE   (MODE: lines | open | ceilings)
Walks the first-parent history of HEAD in ROOT from the commit that introduced FILE. The floor is the keys present in
every copy, each at its lowest value (lines: the stripped non-comment lines; open: ROOT<TAB>FN<TAB>READ keyed, COUNT;
ceilings: CRATE FN VALUE, FN keyed, VALUE). HEAD's copy and the working tree must lie within the floor: growth that was
shrunk back passes, growth that persists (or a shrink then a re-grow) fails. A commit that deletes the file is not a
reset. Reset (ceilings only): a commit whose message has `Ratchet-Reset: tools/rlimit-ceilings.txt: REASON` and that
touches rust-toolchain.toml or Cargo.lock restarts the floor; the trailer is refused for the other files. Any git
error, and a shallow clone, fail (fail closed)."""
import os, re, subprocess, sys


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


def resets(root, path, mode):
    """Commits (first-parent, oldest first) whose message carries `Ratchet-Reset: PATH: REASON` for PATH.
    Only the ceilings file may reset, and only in a commit touching rust-toolchain.toml or Cargo.lock."""
    out = []
    log = git(root, 'log', '--first-parent', '--reverse', '--format=%H%x1f%B%x1e', 'HEAD')
    for rec in log.split('\x1e'):
        if not rec.strip():
            continue
        c, _, body = rec.strip().partition('\x1f')
        for l in body.splitlines():
            m = re.match(r'^Ratchet-Reset: (\S+): (\S.*)$', l)
            if not m or m.group(1) != path:
                continue
            if mode != 'ceilings':
                raise Fail('%s: commit %s carries `Ratchet-Reset` for it; only tools/rlimit-ceilings.txt may be reset' % (path, c[:12]))
            files = git(root, 'diff-tree', '-r', '--root', '-m', '--first-parent', '--name-only', '--no-commit-id', c).split()
            if 'rust-toolchain.toml' not in files and 'Cargo.lock' not in files:
                raise Fail('%s: reset commit %s touches neither rust-toolchain.toml nor Cargo.lock' % (path, c[:12]))
            out.append(c)
            break
    return out


def floor_of(versions):
    """keys present in every version, each at its minimum value"""
    fl = dict(versions[0])
    for v in versions[1:]:
        fl = {k: min(n, v[k]) for k, n in fl.items() if k in v}
    return fl


def outside(cur, fl):
    for k, v in sorted(cur.items(), key=str):
        if k not in fl:
            return 'new line %s (not in every earlier copy)' % (k,)
        if v > fl[k]:
            return '%s at %d, above its lowest earlier value %d' % (k, v, fl[k])
    return None


def main(root, path, mode):
    if mode not in ('lines', 'open', 'ceilings'):
        raise Fail('unknown mode %s' % mode)
    if git(root, 'rev-parse', '--is-shallow-repository').strip() != 'false':
        raise Fail('the clone is shallow (history missing): %s cannot be walked; fetch the full history' % path)
    rs = resets(root, path, mode)
    commits = git(root, 'rev-list', '--first-parent', '--reverse', 'HEAD', '--', path).split()
    if rs:
        order = git(root, 'rev-list', '--first-parent', '--reverse', 'HEAD').split()
        pos = {c: i for i, c in enumerate(order)}
        commits = [rs[-1]] + [c for c in commits if pos[c] > pos[rs[-1]]]
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
        fl = floor_of(versions)
        for what, cur in checks:
            bad = outside(cur, fl)
            if bad:
                raise Fail('%s: %s is outside the floor of its first-parent history: %s (the file only shrinks)' % (path, what, bad))
    print('ratchet-walk: %s ok (%d commits touch it%s)' % (path, len(commits), ', reset' if rs else ''))


if __name__ == '__main__':
    if len(sys.argv) != 4:
        print('usage: ratchet_walk.py ROOT FILE MODE', file=sys.stderr); sys.exit(1)
    try:
        main(*sys.argv[1:])
    except Fail as e:
        print('ratchet-walk: %s' % e, file=sys.stderr); sys.exit(1)
