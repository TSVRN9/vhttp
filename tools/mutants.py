# mutants.py: the parsing half of scripts/mutants.sh (C6 MUST ONLY TEST-PINNED). Run as python3 -I.
#   rows ROOT TSV PATCHDIR   validate the registry, print one tab-separated row per line (id crate module fn tests deps
#                            regex). A patch touches crates/<crate>/ and may touch crates/<d>/ for a path dependency <d>
#                            of <crate> (its [dependencies] in ROOT/crates/<crate>/Cargo.toml); deps lists those <d> (- if
#                            none), for run to check that each still verifies on its own with the patch
#   clean BASE CRATE MOD FN  BASE.json (Verus --output-json --time-expanded) and BASE.log (its stderr): FN, and only FN,
#                            was checked, and it verified (>= 1 verified, 0 errors), no rlimit text
#   killed BASE CRATE MOD FN REGEX
#                            the mutant run checked only FN and FN failed for the stated reason: >= 1 error, REGEX
#                            (Python re, DOTALL) found in a postcondition, precondition, assertion or loop-invariant
#                            error block of BASE.log (KINDS), no rlimit text
#   depok BASE CRATE         BASE.json/BASE.log of a whole-crate run of CRATE (a patched dependency): one result object,
#                            the entire crate, >= 1 verified, 0 errors, no rlimit text
#   gate ROOT                the main gate, all read from ROOT's HEAD commit: HEAD:tools/mutants-last-run.txt names
#                            `tree` (see tree), HEAD:crates, HEAD:tools/mutants.tsv's blob, and every id of that tsv
#                            (no other) as `pass` with the blob of HEAD:tools/mutants/<id>.patch
#   gate-branch ROOT         on a branch: nothing to demand while crates/, the root Cargo files and the registry equal the
#                            merge-base's, else `gate`
#   tree ROOT REV            sha256 of `git ls-tree REV -- Cargo.lock Cargo.toml crates rust-toolchain.toml` (all four needed)
#   allowed ROOT TSV         every allowed_*err / *_allowed_err spec fn under ROOT/crates is named by a row's fn or regex column
# Every mode exits 1 with a "mutants: ..." message on failure, and fails closed on a missing or empty input.
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import tomllib

# Verus 0.2026.10.04's wording; a failed loop invariant is a named proof obligation like an assertion
KINDS = ('error: postcondition not satisfied', 'error: precondition not satisfied', 'error: assertion failed',
         'error: invariant not satisfied before loop', 'error: invariant not satisfied at end of loop body')
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


def path_deps(root, crate):
    """The crates/<d> dirs that ROOT/crates/<crate>/Cargo.toml names as path [dependencies] (dev-dependencies excluded)."""
    cdir = os.path.join(root, 'crates', crate)
    try:
        man = tomllib.loads(read(os.path.join(cdir, 'Cargo.toml')))
    except tomllib.TOMLDecodeError as e:
        die('%s/Cargo.toml: %s' % (cdir, e))
    out = set()
    for v in man.get('dependencies', {}).values():
        if isinstance(v, dict) and 'path' in v:
            d = os.path.normpath(os.path.join(cdir, v['path']))
            if os.path.dirname(d) == os.path.normpath(os.path.join(root, 'crates')):
                out.add(os.path.basename(d))
    return out


def rows(root, tsv, pdir):
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
        if tests != '-' and not all(re.fullmatch(r'([a-z0-9_]+/)?[a-z0-9_]+:[A-Za-z0-9_]+', t) for t in tests.split(',')):
            die('%s:%d: tests must be - or [package/]target:name[,..] (package defaults to the row\'s crate)' % (tsv, n))
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
        deps, pd = set(), None
        for x in files:
            if x == '/dev/null' or re.match(r'[ab]/crates/%s/' % re.escape(crate), x):
                continue
            m = re.match(r'[ab]/crates/([a-z0-9_]+)/', x)
            pd = path_deps(root, crate) if pd is None else pd
            if not m or m.group(1) not in pd:
                die('%s: touches %s, outside crates/%s/ and its path dependencies (%s): the row verifies only those'
                    % (p, x, crate, ' '.join(sorted(pd)) or 'none'))
            deps.add(m.group(1))
        out.append((i, crate, mod, fn, tests, ','.join(sorted(deps)) or '-', rx))
    if not out:
        die('%s has no rows' % tsv)
    have = sorted(x[:-6] for x in os.listdir(pdir) if x.endswith('.patch'))
    orphans = sorted(set(have) - ids)
    if orphans:
        die('patch without a row: %s' % ' '.join(orphans))
    for r in out:
        print('\t'.join(r))


def results(base):
    """The JSON objects of BASE.json, Verus's --output-json stdout."""
    raw, dec, objs, i = read(base + '.json'), json.JSONDecoder(), [], 0
    while True:
        j = raw.find('{', i)
        if j < 0:
            break
        try:
            o, e = dec.raw_decode(raw[j:])
        except ValueError:
            die('%s.json: unreadable JSON at offset %d' % (base, j))
        objs.append(o)
        i = j + e
    return objs


def scan(base, crate, mod, fn):
    """BASE.json is Verus's --output-json --time-expanded stdout, BASE.log its stderr. Returns (log text, verified,
    errors, success of FN's row); FN must be the only fn Verus spent rlimit on."""
    fqn = '%s::%s::%s' % (crate, mod, fn)
    objs = results(base)
    if len(objs) != 1 or not isinstance(objs[0].get('verification-results'), dict):
        die('%s.json: %d Verus result objects, want 1 (a cached build, a compile error or a crash verifies nothing)'
            % (base, len(objs)))
    vr = objs[0]['verification-results']
    if vr.get('encountered-vir-error') is not False or vr.get('is-verifying-entire-crate') is not False:
        die('%s.json: a VIR error, or not a --verify-function run: %s' % (base, vr))
    rows = [e for m in objs[0].get('times-ms', {}).get('smt', {}).get('smt-run-module-times', [])
            for e in m.get('function-breakdown', [])]
    ran = sorted({e.get('function') for e in rows if e.get('rlimit', 0) > 0 or e.get('success') is not True})
    if ran != [fqn]:
        die('%s.json: Verus checked %s, want exactly %s (wrong or ambiguous fn name)' % (base, ran or 'no fn', fqn))
    text = read(base + '.log')
    if re.search('rlimit', text, re.I):
        die('%s.log: rlimit text (an rlimit failure is not a kill, and the clean run must not hit it)' % base)
    ok = all(e.get('success') is True for e in rows if e.get('function') == fqn)
    return text, vr.get('verified'), vr.get('errors'), ok


def clean(base, crate, mod, fn):
    _, ok, bad, good = scan(base, crate, mod, fn)
    if not isinstance(ok, int) or ok < 1 or bad != 0 or not good:
        die('%s: unmutated %s::%s gives %s verified, %s errors (want >= 1, 0)' % (base, mod, fn, ok, bad))


def killed(base, crate, mod, fn, rx):
    text, _, bad, good = scan(base, crate, mod, fn)
    if not isinstance(bad, int) or bad < 1 or good:
        die('%s: the mutant still verifies %s::%s (%s errors)' % (base, mod, fn, bad))
    blocks = re.split(r'\n(?=error)', text)
    if not any(b.split('\n', 1)[0].strip() in KINDS and re.search(rx, b, re.S) for b in blocks):
        die('%s.log: %d errors, but no postcondition/precondition/assertion/invariant block matches %r' % (base, bad, rx))


def depok(base, crate):
    """A patched dependency still verifies on its own: else a patch breaking its proof would pass as a kill in the
    dependent crate."""
    objs = results(base)
    if len(objs) != 1 or not isinstance(objs[0].get('verification-results'), dict):
        die('%s.json: %d Verus result objects, want 1 (the dependency %s was not verified)' % (base, len(objs), crate))
    vr = objs[0]['verification-results']
    if vr.get('encountered-vir-error') is not False or vr.get('is-verifying-entire-crate') is not True:
        die('%s.json: a VIR error, or not a whole-crate run of %s: %s' % (base, crate, vr))
    if re.search('rlimit', read(base + '.log'), re.I):
        die('%s.log: rlimit text in the patched dependency %s' % (base, crate))
    ok, bad = vr.get('verified'), vr.get('errors')
    if not isinstance(ok, int) or ok < 1 or bad != 0:
        die('the patched dependency %s does not verify on its own (%s verified, %s errors; %s.log)' % (crate, ok, bad, base))


def git(root, *args):
    r = subprocess.run(['git', '-C', root] + list(args), capture_output=True, text=True)
    if r.returncode != 0:
        die('git %s failed: %s' % (' '.join(args), r.stderr.strip()))
    return r.stdout


TREE_PATHS = ('Cargo.lock', 'Cargo.toml', 'crates', 'rust-toolchain.toml')


def tree(root, rev):
    """One hash for what a mutant run depends on: crates/ and the root Cargo.toml, Cargo.lock, rust-toolchain.toml."""
    ls = git(root, 'ls-tree', rev, '--', *TREE_PATHS)
    names = sorted(l.split('\t', 1)[1] for l in ls.split('\n') if l)
    if names != sorted(TREE_PATHS):
        die('%s lacks %s (the run tree hash covers all of them)' % (rev, ' '.join(sorted(set(TREE_PATHS) - set(names)))))
    return hashlib.sha256(ls.encode()).hexdigest()


def gate(root):
    """Every commit at main's tip: the committed run file names this commit's tree."""
    want_tree = tree(root, 'HEAD')
    tsv = git(root, 'show', 'HEAD:tools/mutants.tsv')
    want = [l.split('\t')[0] for l in tsv.split('\n') if l.strip() and not l.startswith('#')]
    if not want:
        die('HEAD:tools/mutants.tsv has no rows')
    run = 'HEAD:tools/mutants-last-run.txt'
    lines = [l for l in git(root, 'show', run).split('\n') if l and not l.startswith('#')]
    keys = ('crates', 'tree', 'tsv')
    head = dict(l.split(' ', 1) for l in lines if l.split(' ', 1)[0] in keys)
    if head.get('tree') != want_tree or head.get('crates') != git(root, 'rev-parse', 'HEAD:crates').strip():
        die('%s is stale: it names tree %s, this commit has %s (crates/ or the root Cargo.toml, Cargo.lock, '
            'rust-toolchain.toml differ from the run). Merge main into the branch, run `scripts/mutants.sh run`, '
            'commit the file, then merge --no-ff' % (run, head.get('tree'), want_tree))
    if head.get('tsv') != git(root, 'rev-parse', 'HEAD:tools/mutants.tsv').strip():
        die('%s was written for another tools/mutants.tsv (re-run `scripts/mutants.sh run`)' % run)
    got = {}
    for l in lines:
        f = l.split(' ')
        if f[0] in keys:
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
    print('mutants: last run passes: %d mutants on tree %s' % (len(want), want_tree))


def gate_branch(root):
    """On a branch: nothing to demand while crates/, the root Cargo files and the registry equal the merge-base's (the
    committed run file still describes them); once any differs, the full gate, so a stale run file shows before the merge."""
    mb = git(root, 'merge-base', 'HEAD', 'main').strip()
    same = tree(root, 'HEAD') == tree(root, mb) and git(root, 'diff', '--name-only', mb, 'HEAD', '--', 'tools/mutants.tsv', 'tools/mutants').strip() == ''
    if same:
        print('mutants: branch tree and registry equal the merge-base\'s: the committed run file still stands')
    else:
        gate(root)


def allowed(root, tsv):
    """Every allowed_*err / *_allowed_err spec fn under ROOT/crates (tools/acceptance.py's scanner) is named, as a whole
    word, in some row's fn or regex column (not origin): a new acceptance predicate needs a mutant."""
    sys.dont_write_bytecode = True  # no tools/__pycache__ in the caller's tree
    spec = importlib.util.spec_from_file_location('acceptance', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'acceptance.py'))
    acc = importlib.util.module_from_spec(spec)
    try:
        spec.loader.exec_module(acc)
        names = sorted({n for _, n, _ in acc.scan(root)[1]})
    except (ValueError, OSError) as e:
        die('cannot scan crates/ for allowed_*err predicates: %s' % e)
    # fn and regex columns only: a name in the free-text origin column is a comment, not a mutant of the predicate
    text = '\n'.join(' '.join(f[3:6:2]) for f in (l.split('\t') for l in read(tsv).split('\n') if l.strip() and not l.startswith('#')))
    bare = [n for n in names if not re.search(r'(?<![A-Za-z0-9_])%s(?![A-Za-z0-9_])' % re.escape(n), text)]
    if bare:
        die('allowed predicate with no mutant row (name it in a row\'s fn or regex column): %s' % ' '.join(bare))
    print('mutants: %d allowed predicates, each named by a row' % len(names))


def main(a):
    if a[:1] == ['rows'] and len(a) == 4:
        rows(a[1], a[2], a[3])
    elif a[:1] == ['depok'] and len(a) == 3:
        depok(a[1], a[2])
    elif a[:1] == ['clean'] and len(a) == 5:
        clean(*a[1:])
    elif a[:1] == ['killed'] and len(a) == 6:
        killed(*a[1:])
    elif a[:1] == ['gate'] and len(a) == 2:
        gate(a[1])
    elif a[:1] == ['gate-branch'] and len(a) == 2:
        gate_branch(a[1])
    elif a[:1] == ['tree'] and len(a) == 3:
        print(tree(a[1], a[2]))
    elif a[:1] == ['allowed'] and len(a) == 3:
        allowed(a[1], a[2])
    else:
        die('usage: see the header of tools/mutants.py')


main(sys.argv[1:])
