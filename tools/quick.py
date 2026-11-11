# quick.py: helpers for scripts/quick.sh (the inner loop; not a gate, vouches for no commit).
#   scope META PATH..   META is `cargo metadata --no-deps --format-version 1` output. Prints two lines: the crates PATH..
#                       touch plus every crate that depends on them (path dependencies, transitively), in dependency
#                       order; then the extra gates those paths trigger (ct binary interop demos), space-separated.
#   check BASE          BASE.json is a partial Verus run (--verify-only-module / --verify-function): it succeeded,
#                       verified at least one fn, with no error and no rlimit text in BASE.log.
#   selftest            scope's rules on a fixed workspace.
import json, re, sys

WHOLE = ('Cargo.toml', 'Cargo.lock', 'rust-toolchain.toml', 'tools/verus-pin.txt')  # every crate depends on these
CT = {'crypto', 'wire', 'h3', 'quic', 'ctcore', 'ctmir'}  # crates scripts/ct-check.sh dumps or is built from


def die(m):
    print('quick: %s' % m, file=sys.stderr)
    sys.exit(1)


def graph(meta):
    """{crate: set of its path-dependency crates} for the workspace members."""
    pk = {p['name']: p for p in meta['packages']}
    return {n: {d['name'] for d in p['dependencies'] if d.get('path') and d.get('kind') is None and d['name'] in pk}
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


def scope(deps, paths):
    hit = set()
    for p in paths:
        m = re.match(r'crates/([^/]+)/', p)
        if p in WHOLE:
            hit |= set(deps)
        elif m and m.group(1) in deps:
            hit.add(m.group(1))
    grew = True
    while grew:
        more = {n for n, ds in deps.items() if ds & hit} - hit
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


def check(base):
    try:
        raw, log = open(base + '.json').read(), open(base + '.log').read()
    except OSError as e:
        die('cannot read %s: %s' % (base, e))
    objs, dec, i = [], json.JSONDecoder(), 0
    while (j := raw.find('{', i)) >= 0:
        try:
            o, e = dec.raw_decode(raw[j:])
        except ValueError:
            die('%s.json: unreadable JSON at offset %d' % (base, j))
        objs.append(o)
        i = j + e
    vr = [o['verification-results'] for o in objs if isinstance(o.get('verification-results'), dict)]
    if len(vr) != 1:
        die('%s.json: %d Verus result objects, want 1 (a compile error verifies nothing)' % (base, len(vr)))
    v = vr[0]
    if v.get('encountered-error') is not False or v.get('errors') != 0 or not isinstance(v.get('verified'), int) or v['verified'] < 1:
        die('%s: %s verified, %s errors (want >= 1, 0); see %s.log' % (base, v.get('verified'), v.get('errors'), base))
    if re.search('rlimit', log, re.I):
        die('%s.log: rlimit text' % base)
    print('%s verified' % v['verified'])


def selftest():
    deps = {'wire': set(), 'crypto': set(), 'ctcore': set(), 'ctmir': {'ctcore'}, 'h3': {'wire'}, 'tls': {'crypto'},
            'quic': {'crypto', 'h3', 'wire'}, 'quictls': {'crypto', 'h3', 'quic', 'tls'},
            'server': {'h3', 'quic', 'quictls', 'tls'}}
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
    for paths, want_c, want_x in cases:
        got = scope(deps, paths)
        if got != (want_c, want_x):
            die('selftest: scope %s gave %s, want %s' % (paths, got, (want_c, want_x)))
    print('quick: scope selftest ok (%d cases)' % len(cases))


a = sys.argv[1:]
if a[:1] == ['scope'] and len(a) >= 2:
    try:
        meta = json.load(open(a[1]))
    except (OSError, ValueError) as e:
        die('cannot read cargo metadata %s: %s' % (a[1], e))
    c, x = scope(graph(meta), a[2:])
    print(' '.join(c))
    print(' '.join(x))
elif a[:1] == ['check'] and len(a) == 2:
    check(a[1])
elif a == ['selftest']:
    selftest()
else:
    die('usage: quick.py scope META PATH.. | check BASE | selftest')
