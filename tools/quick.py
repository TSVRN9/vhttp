# quick.py: helpers for scripts/quick.sh (the inner loop; not a gate, vouches for no commit).
#   scope META PATHS    META is `cargo metadata --no-deps --format-version 1` output, PATHS a file of NUL-separated paths
#                       (git -z). Prints two lines: the crates the paths touch plus every crate that depends on them (path
#                       dependencies and dev-dependencies, transitively), in dependency order; then the extra gates those
#                       paths trigger (ct binary interop demos), space-separated.
#   check BASE CRATE MOD [FN]  BASE.json is a partial Verus run (--verify-only-module / --verify-function) of the pinned
#                       Verus (tools/verus-pin.txt): every results object has no error, no VIR error and no FAIL row, one
#                       verified >= 1 with a row of CRATE::MOD::FN (or under CRATE::MOD::), and BASE.log no rlimit text.
#   selftest            scope's rules on a fixed workspace.
import json, os, re, sys

WHOLE = ('Cargo.toml', 'Cargo.lock', 'rust-toolchain.toml', 'tools/verus-pin.txt')  # every crate depends on these
CT = {'crypto', 'wire', 'h3', 'quic', 'ctcore', 'ctmir'}  # crates scripts/ct-check.sh dumps or is built from


def die(m):
    print('quick: %s' % m, file=sys.stderr)
    sys.exit(1)


PIN = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'verus-pin.txt')


def graph(meta, kinds=(None,)):
    """{crate: set of its path-dependency crates of KINDS (None normal, 'dev', 'build')} for the workspace members."""
    pk = {p['name']: p for p in meta['packages']}
    return {n: {d['name'] for d in p['dependencies'] if d.get('path') and d.get('kind') in kinds and d['name'] in pk}
            for n, p in pk.items()}


def order(deps):
    out, left = [], dict(deps)
    while left:
        ready = sorted(n for n, ds in left.items() if not ds - set(out))
        if not ready:
            die('dependency cycle among %s' % ' '.join(sorted(left)))
        out += ready
        for n in ready:
            del left[n]
    return out


def scope(deps, paths, up=None):
    """DEPS (normal edges) orders the crates; UP (default DEPS) adds dependents: a crate whose tests use a changed crate
    (a dev-dependency, which may form a cycle) is re-checked too."""
    up = up or deps
    hit = set()
    for p in paths:
        m = re.match(r'crates/([^/]+)/', p)
        if p in WHOLE:
            hit |= set(deps)
        elif m and m.group(1) in deps:
            hit.add(m.group(1))
    grew = True
    while grew:
        more = {n for n, ds in up.items() if ds & hit} - hit
        grew = bool(more)
        hit |= more
    crates = [n for n in order(deps) if n in hit]
    extra = []
    if hit & CT or any(p.startswith(('tools/ct-', 'scripts/ct-')) for p in paths):
        extra.append('ct')
    if 'crypto' in hit or any(p in ('scripts/ct-binary.sh', 'docs/crypto-binary-digests.txt') for p in paths):
        extra.append('binary')
    if 'server' in hit or 'scripts/interop.sh' in paths:
        extra.append('interop')
    if any(p.startswith(('scripts/', 'tools/')) for p in paths):
        extra.append('demos')
    return crates, extra


def check(base, crate, mod, fn=None):
    try:
        raw, log, pin = open(base + '.json').read(), open(base + '.log').read(), open(PIN).read()
        pn = dict(l.split(' ', 1) for l in pin.split('\n') if l)
    except (OSError, ValueError) as e:
        die('cannot read %s or %s: %s' % (base, PIN, e))
    if not all(pn.get(k) for k in ('version', 'commit', 'toolchain')):
        die('%s lacks a version, commit or toolchain line' % PIN)
    objs, dec, i = [], json.JSONDecoder(), 0
    while (j := raw.find('{', i)) >= 0:
        try:
            o, e = dec.raw_decode(raw[j:])
        except ValueError:
            die('%s.json: unreadable JSON at offset %d' % (base, j))
        objs.append(o)
        i = j + e
    objs = [o for o in objs if isinstance(o.get('verification-results'), dict)]
    if not objs:
        die('%s.json: 0 Verus result objects (a compile error verifies nothing)' % base)
    want = '%s::%s::%s' % (crate, mod, fn) if fn else None
    hit = 0
    # a dependency built during the run prints its own object (tools/rl.py): every object must be clean, and the
    # target's rows must be in one that verified something
    for o in objs:
        v, z = o['verification-results'], o.get('verus')
        if not isinstance(z, dict):
            die('%s.json: no verus object (which Verus ran is unknown)' % base)
        for k in ('version', 'commit'):
            if z.get(k) != pn[k]:
                die('%s.json: verus.%s is %r, the pin says %r' % (base, k, z.get(k), pn[k]))
        if not str(z.get('toolchain')).startswith(pn['toolchain'] + '-'):
            die('%s.json: verus.toolchain is %r, the pin says %s-*' % (base, z.get('toolchain'), pn['toolchain']))
        if v.get('encountered-error') is not False or v.get('encountered-vir-error') is not False or v.get('errors') != 0:
            die('%s: %s errors, encountered-error %s, encountered-vir-error %s; see %s.log'
                % (base, v.get('errors'), v.get('encountered-error'), v.get('encountered-vir-error'), base))
        rows = [e for m in o.get('times-ms', {}).get('smt', {}).get('smt-run-module-times', [])
                for e in m.get('function-breakdown', [])]
        bad = [e.get('function') for e in rows if e.get('success') is not True]
        if bad:
            die('%s.json: FAIL rows %s' % (base, ' '.join(map(str, bad))))
        mine = [e for e in rows if (e.get('function') == want if want else str(e.get('function')).startswith('%s::%s::' % (crate, mod)))]
        if mine and isinstance(v.get('verified'), int) and v['verified'] >= 1:
            hit = v['verified']
    if not hit:
        die('%s.json: no results object verified %s (want >= 1 verified, with its row)' % (base, want or '%s::%s::*' % (crate, mod)))
    if re.search('rlimit', log, re.I):
        die('%s.log: rlimit text' % base)
    print('%s verified' % hit)


def selftest():
    deps = {'wire': set(), 'crypto': set(), 'ctcore': set(), 'ctmir': {'ctcore'}, 'h3': {'wire'}, 'tls': {'crypto'},
            'quic': {'crypto', 'h3', 'wire'}, 'quictls': {'crypto', 'h3', 'quic', 'tls'},
            'server': {'h3', 'quic', 'quictls', 'tls'}}
    # dev edges: ctcore's tests use ctmir (a cycle with ctmir's normal edge), tls's tests use wire
    up = {n: ds | {'ctcore': {'ctmir'}, 'tls': {'wire'}}.get(n, set()) for n, ds in deps.items()}
    cases = [
        (['crates/wire/src/varint.rs'], ['wire', 'h3', 'quic', 'quictls', 'server'], ['ct', 'interop']),
        (['crates/quictls/src/server.rs'], ['quictls', 'server'], ['interop']),
        (['crates/ctcore/src/lib.rs'], ['ctcore', 'ctmir'], ['ct']),
        (['crates/crypto/src/sha256.rs'], ['crypto', 'tls', 'quic', 'quictls', 'server'], ['ct', 'binary', 'interop']),
        (['Cargo.lock'], order(deps), ['ct', 'binary', 'interop']),
        (['docs/roadmap.md', 'crates/nosuch/x.rs'], [], []),
        (['scripts/rlimit-gate.sh'], [], ['demos']),
        (['tools/ct-front/src/main.rs'], [], ['ct', 'demos']),
    ]
    dev = [
        (['crates/wire/src/varint.rs'], ['wire', 'h3', 'tls', 'quic', 'quictls', 'server'], ['ct', 'interop']),
        (['crates/ctmir/src/lib.rs'], ['ctcore', 'ctmir'], ['ct']),
    ]
    for paths, want_c, want_x, *u in cases + [(p, c, x, up) for p, c, x in dev]:
        got = scope(deps, paths, *u)
        if got != (want_c, want_x):
            die('selftest: scope %s gave %s, want %s' % (paths, got, (want_c, want_x)))
    print('quick: scope selftest ok (%d cases)' % (len(cases) + len(dev)))


a = sys.argv[1:]
if a[:1] == ['scope'] and len(a) == 3:
    try:
        meta = json.load(open(a[1]))
        paths = [p for p in open(a[2], 'rb').read().decode('utf-8', 'surrogateescape').split('\0') if p]
    except (OSError, ValueError) as e:
        die('cannot read %s or %s: %s' % (a[1], a[2], e))
    c, x = scope(graph(meta), paths, graph(meta, (None, 'dev')))
    print(' '.join(c))
    print(' '.join(x))
elif a[:1] == ['check'] and len(a) in (4, 5):
    check(*a[1:])
elif a == ['selftest']:
    selftest()
else:
    die('usage: quick.py scope META PATHS | check BASE CRATE MOD [FN] | selftest')
