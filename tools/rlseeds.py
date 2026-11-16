# rlseeds.py NAME --pin FILE --ceilings FILE [--max N] LOG...: the seed gate (C11 PROOF-BUDGET FRAGILITY, RCA
# docs/rca/2026-11-16-smt-order-fragility.md). Each LOG is one `cargo verus focus -- --rlimit 4 --output-json
# --time-expanded --smt-option smt.random_seed=<i>` run of crate NAME. Fails if a LOG is unreadable or has no results
# object, a run is not clean, a run's verus version/commit/toolchain differs from the pin or is not a whole-crate run,
# any fn has a FAIL row under any seed, every log has the same {fn: rlimit} map (with two or more logs: the seed option
# had no effect), the ceilings FILE has a malformed line for NAME, or a fn of NAME exceeds, under any seed, its line in
# the ceilings FILE (if it has one) or N (default 8,000,000). Prints each fn of NAME above 3,000,000 with its max over seeds and the seed of the max,
# then `rlimit-seeds: NAME <k> seeds ok (max <fn> <n>)`.
import json, sys

def fail(m):
    print('rlimit-seeds: %s' % m, file=sys.stderr)
    sys.exit(1)

a = sys.argv[1:]
if not a:
    fail('usage: rlseeds.py NAME --pin FILE --ceilings FILE [--max N] LOG...')
name = a[0]
a = a[1:]
pin = ceil = None
cap = 8000000
while a and a[0].startswith('--'):
    if len(a) < 2:
        fail('%s needs a value' % a[0])
    k, v = a[0], a[1]
    a = a[2:]
    if k == '--pin':
        pin = v
    elif k == '--ceilings':
        ceil = v
    elif k == '--max':
        cap = int(v)
    else:
        fail('unknown option %s' % k)
if pin is None or ceil is None:
    fail('--pin and --ceilings are required')
if not a:
    fail('no logs given')
try:
    pn = dict(l.split(' ', 1) for l in open(pin).read().splitlines())
except (OSError, ValueError) as e:
    fail('cannot read the pin file %s: %s' % (pin, e))
if not all(pn.get(k) for k in ('version', 'commit', 'toolchain')):
    fail('pin file %s lacks a version, commit or toolchain line' % pin)
lim = {}
try:
    for l in open(ceil).read().splitlines():
        w = l.split()
        if not w or w[0] != name:
            continue
        if len(w) != 3 or not w[2].isdigit() or not w[1].startswith(name + '::'):
            fail('%s: malformed line %r' % (ceil, l))
        lim[w[1]] = int(w[2])
except OSError as e:
    fail('cannot read the ceilings file %s: %s' % (ceil, e))

mx = {}  # fn -> (max rlimit, seed of the max)
maps = []  # per seed: {fn: rlimit}, to check the seed changed the runs
errs = []
for s, lg in enumerate(a):
    try:
        t = open(lg).read()
    except OSError as e:
        fail('seed %d: cannot read %s: %s' % (s, lg, e))
    dec = json.JSONDecoder()
    i = 0
    objs = []
    while True:
        j = t.find('{', i)
        if j < 0:
            break
        try:
            o, e = dec.raw_decode(t[j:])
        except ValueError:
            i = j + 1
            continue
        i = j + e
        if 'verification-results' in o:
            objs.append(o)
    if not objs:
        fail('seed %d: 0 verification-results objects in %s' % (s, lg))
    own = 0
    seen = {}
    maps.append(seen)
    for o in objs:
        try:
            v = o['verification-results']
            vz = o['verus']
            rows = [(f['rlimit'], f['function'], f['success'])
                    for m in o['times-ms']['smt']['smt-run-module-times'] for f in m['function-breakdown']]
            for k in ('version', 'commit'):
                if vz[k] != pn[k]:
                    fail('seed %d: verus.%s is %r, the pin says %r' % (s, k, vz[k], pn[k]))
            if not vz['toolchain'].startswith(pn['toolchain'] + '-'):
                fail('seed %d: verus.toolchain is %r, the pin says %s-*' % (s, vz['toolchain'], pn['toolchain']))
            if v['is-verifying-entire-crate'] is not True:
                fail('seed %d: is-verifying-entire-crate is not true (a partial run)' % s)
            clean = (v['success'] and not v['errors'] and not v['encountered-error'] and not v['encountered-vir-error']
                     and v['verified'])
        except (KeyError, TypeError):
            fail('seed %d: unreadable results object in %s' % (s, lg))
        if not clean:
            errs.append('seed %d: run not clean: %s' % (s, v))
        for r, fn, ok in rows:
            seen[fn] = r
            if not ok:
                errs.append('seed %d: FAIL row %s at %d' % (s, fn, r))
            if fn.startswith(name + '::'):
                own += 1
                if r > mx.get(fn, (-1, 0))[0]:
                    mx[fn] = (r, s)
    if not own:
        fail('seed %d: no rows for fns of %s in %s' % (s, name, lg))
if len(maps) >= 2 and all(m == maps[0] for m in maps[1:]):
    errs.append('all %d seeds gave identical per-fn rlimits: the seed option had no effect' % len(maps))
for fn, (r, s) in sorted(mx.items()):
    l = lim.get(fn, cap)
    if r > l:
        errs.append('%s at %d (seed %d) is above its %s %d' % (fn, r, s, 'ceiling' if fn in lim else 'cap', l))
for fn, (r, s) in sorted(mx.items(), key=lambda x: -x[1][0]):
    if r > 3000000:
        print('rlimit-seeds: %s max %d (seed %d)' % (fn, r, s))
if errs:
    for m in errs:
        print('rlimit-seeds: %s' % m, file=sys.stderr)
    sys.exit(1)
best = max(mx.items(), key=lambda x: x[1][0])
print('rlimit-seeds: %s %d seeds ok (max %s %d)' % (name, len(a), best[0], best[1][0]))
