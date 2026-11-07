# mutants.py: the parsing half of scripts/mutants.sh (C6 MUST ONLY TEST-PINNED). Run as python3 -I.
#   rows TSV PATCHDIR        validate the registry, print one tab-separated row per line (id crate module fn tests regex)
#   clean LOG CRATE MOD FN   the unmutated run of FN verified it: N >= 1 verified, 0 errors
#   killed LOG CRATE MOD FN REGEX
#                            the mutant run of FN failed for the stated reason: >= 1 error, REGEX (Python re, DOTALL)
#                            found in a postcondition, precondition or assertion error block, no rlimit text
#   gate ROOT                the merge gate, all read from ROOT's commits: HEAD:tools/mutants-last-run.txt names
#                            HEAD^2:crates, HEAD:tools/mutants.tsv's blob, and every id of that tsv (no other) as
#                            `pass` with the blob of HEAD:tools/mutants/<id>.patch
# Every mode exits 1 with a "mutants: ..." message on failure, and fails closed on a missing or empty input.
import os
import re
import subprocess
import sys

KINDS = ('error: postcondition not satisfied', 'error: precondition not satisfied', 'error: assertion failed')
COLS = ('id', 'crate', 'module', 'fn', 'tests', 'regex', 'origin')


def die(msg):
    print('mutants: ' + msg, file=sys.stderr)
    sys.exit(1)


def read(p):
    try:
        with open(p, encoding='utf-8') as f:
            return f.read()
    except OSError as e:
        die('cannot read %s: %s' % (p, e))


def rows(tsv, pdir):
    out, ids = [], set()
    for n, line in enumerate(read(tsv).split('\n'), 1):
        if not line.strip() or line.startswith('#'):
            continue
        f = line.split('\t')
        if len(f) != len(COLS) or any(not x.strip() for x in f):
            die('%s:%d: want %d non-empty tab-separated fields (%s)' % (tsv, n, len(COLS), ' '.join(COLS)))
        i, crate, mod, fn, tests, rx, _ = f
        if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*', i):
            die('%s:%d: bad id %r' % (tsv, n, i))
        if i in ids:
            die('%s:%d: duplicate id %s' % (tsv, n, i))
        ids.add(i)
        if not re.fullmatch(r'[a-z0-9_]+', crate) or not re.fullmatch(r'[a-z0-9_]+(::[a-z0-9_]+)*', mod):
            die('%s:%d: bad crate or module' % (tsv, n))
        if not re.fullmatch(r'[A-Za-z0-9_]+(::[A-Za-z0-9_]+)*', fn):
            die('%s:%d: fn %r must be a plain path (no wildcard: one fn per row)' % (tsv, n, fn))
        if tests != '-' and not all(re.fullmatch(r'[a-z0-9_]+:[A-Za-z0-9_]+', t) for t in tests.split(',')):
            die('%s:%d: tests must be - or target:name[,target:name..]' % (tsv, n))
        try:
            re.compile(rx, re.S)
        except re.error as e:
            die('%s:%d: regex does not compile: %s' % (tsv, n, e))
        if re.search(rx, 'rlimit', re.S | re.I):
            die('%s:%d: regex matches the word rlimit (an rlimit failure is not a kill)' % (tsv, n))
        p = os.path.join(pdir, i + '.patch')
        text = read(p)
        files = re.findall(r'^(?:---|\+\+\+) (\S+)', text, re.M)
        if not re.search(r'^@@ ', text, re.M) or not files:
            die('%s: no hunk' % p)
        for x in files:
            if x != '/dev/null' and not re.match(r'[ab]/crates/%s/' % re.escape(crate), x):
                die('%s: touches %s, outside crates/%s/ (the row verifies only that crate)' % (p, x, crate))
        out.append((i, crate, mod, fn, tests, rx))
    if not out:
        die('%s has no rows' % tsv)
    have = sorted(x[:-6] for x in os.listdir(pdir) if x.endswith('.patch'))
    orphans = sorted(set(have) - ids)
    if orphans:
        die('patch without a row: %s' % ' '.join(orphans))
    for r in out:
        print('\t'.join(r))


def scan(log, crate, mod, fn):
    text = read(log)
    note = 'note: verifying module %s, function %s::%s::%s (selected functions)' % (mod, crate, mod, fn)
    if note not in text.split('\n'):
        die('%s: no "%s" line (wrong fn, an ambiguous name, or Verus did not run)' % (log, note))
    res = re.findall(r'^verification results:: (\d+) verified, (\d+) errors', text, re.M)
    if len(res) != 1:
        die('%s: %d verification results lines, want 1 (a cached or failed build verifies nothing)' % (log, len(res)))
    if re.search('rlimit', text, re.I):
        die('%s: rlimit text in the log (an rlimit failure is not a kill, and a clean run must not hit it)' % log)
    return text, int(res[0][0]), int(res[0][1])


def clean(log, crate, mod, fn):
    _, ok, bad = scan(log, crate, mod, fn)
    if ok < 1 or bad != 0:
        die('%s: unmutated %s::%s gives %d verified, %d errors (want >= 1, 0)' % (log, mod, fn, ok, bad))


def killed(log, crate, mod, fn, rx):
    text, _, bad = scan(log, crate, mod, fn)
    if bad < 1:
        die('%s: the mutant still verifies %s::%s (0 errors)' % (log, mod, fn))
    blocks = re.split(r'\n(?=error)', text)
    hit = [b for b in blocks if b.split('\n', 1)[0].strip() in KINDS and re.search(rx, b, re.S)]
    if not hit:
        die('%s: %d errors, but no postcondition/precondition/assertion block matches %r' % (log, bad, rx))


def git(root, *args):
    r = subprocess.run(['git', '-C', root] + list(args), capture_output=True, text=True)
    if r.returncode != 0:
        die('git %s failed: %s' % (' '.join(args), r.stderr.strip()))
    return r.stdout


def gate(root):
    crates = git(root, 'rev-parse', 'HEAD^2:crates').strip()
    tsv = git(root, 'show', 'HEAD:tools/mutants.tsv')
    want = [l.split('\t')[0] for l in tsv.split('\n') if l.strip() and not l.startswith('#')]
    if not want:
        die('HEAD:tools/mutants.tsv has no rows')
    run = 'HEAD:tools/mutants-last-run.txt'
    lines = [l for l in git(root, 'show', run).split('\n') if l and not l.startswith('#')]
    head = dict(l.split(' ', 1) for l in lines if l.split(' ', 1)[0] in ('crates', 'tsv'))
    if head.get('crates') != crates:
        die('%s is stale: it names crates tree %s, the merged branch (HEAD^2) has %s; run `scripts/mutants.sh run` '
            'as the branch\'s last step and commit the file' % (run, head.get('crates'), crates))
    if head.get('tsv') != git(root, 'rev-parse', 'HEAD:tools/mutants.tsv').strip():
        die('%s was written for another tools/mutants.tsv (re-run `scripts/mutants.sh run`)' % run)
    got = {}
    for l in lines:
        f = l.split(' ')
        if f[0] in ('crates', 'tsv'):
            continue
        if len(f) != 3 or f[0] in got:
            die('%s: bad or duplicate line %r' % (run, l))
        got[f[0]] = (f[1], f[2])
    if sorted(got) != sorted(want) or len(want) != len(set(want)):
        die('%s ids differ from the registry: missing %s, extra %s' % (
            run, ' '.join(sorted(set(want) - set(got))) or '-', ' '.join(sorted(set(got) - set(want))) or '-'))
    for i in want:
        st, h = got[i]
        if st != 'pass':
            die('%s: %s did not pass (%s)' % (run, i, st))
        if h != git(root, 'rev-parse', 'HEAD:tools/mutants/%s.patch' % i).strip():
            die('%s: %s was run with another patch (re-run `scripts/mutants.sh run`)' % (run, i))
    print('mutants: last run passes: %d mutants on crates tree %s' % (len(want), crates))


def main(a):
    if a[:1] == ['rows'] and len(a) == 3:
        rows(a[1], a[2])
    elif a[:1] == ['clean'] and len(a) == 5:
        clean(*a[1:])
    elif a[:1] == ['killed'] and len(a) == 6:
        killed(*a[1:])
    elif a[:1] == ['gate'] and len(a) == 2:
        gate(a[1])
    else:
        die('usage: see the header of tools/mutants.py')


main(sys.argv[1:])
