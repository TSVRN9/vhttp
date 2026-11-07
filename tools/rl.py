# rl.py LOG [FN...]: print per-module verification results and the six highest-rlimit fns from cargo-verus --time-expanded JSON output,
# then the rlimit of each named FN. Run as: python3 -I tools/rl.py LOG [FN...]
# Gate mode: python3 -I tools/rl.py --gate NAME [--max N] LOG  prints `rlimit-gate: NAME max <fn> <n>` and exits 0, or
# exits 1 with the reason when LOG is unreadable, has no verification-results object, no rows, a failed run, a FAIL row, or a fn of NAME above N.
import json,sys
gate=None; mx=None; a=sys.argv[1:]
if a and a[0]=='--gate':
    gate=a[1]; a=a[2:]
    if a and a[0]=='--max': mx=int(a[1]); a=a[2:]
    sys.argv=[sys.argv[0]]+a
try: t=open(sys.argv[1]).read()
except OSError as e:
    if gate is None: raise
    print('rlimit-gate: %s: cannot read the log: %s'%(gate,e),file=sys.stderr); sys.exit(1)
dec=json.JSONDecoder(); i=0; objs=[]
while True:
    j=t.find('{',i)
    if j<0: break
    try:
        o,e=dec.raw_decode(t[j:]); objs.append(o); i=j+e
    except ValueError: i=j+1
want=sys.argv[2:]
def gfail(m): print('rlimit-gate: %s: %s'%(gate,m),file=sys.stderr); sys.exit(1)
if gate is not None:
    # a dependency not yet built is verified inside this crate's run and prints its own object: gate every object
    try: rs=[d for d in objs if 'verification-results' in d]; assert rs
    except AssertionError: gfail('0 verification-results objects in the log')
    best=(0,'')  # over NAME's own fns: a dependency built in this run (quictls builds tls) is gated for FAIL rows but not for the cap
    for d in rs:
        try:
            v=d['verification-results']
            ok=v['success'] and not v['errors'] and not v['encountered-error'] and not v['encountered-vir-error'] and v['verified']
            rows=[(f['rlimit'],f['function'],f['success']) for m in d['times-ms']['smt']['smt-run-module-times'] for f in m['function-breakdown']]
        except (KeyError,TypeError): gfail('unreadable results object')
        if not ok: gfail('run not clean: %s'%v)
        if not rows: gfail('no per-fn rows')
        for r in rows:
            if not r[2]: gfail('FAIL row %s'%(r,))
        own=[r[:2] for r in rows if r[1].startswith(gate+'::')]
        if own: best=max(best,max(own))
    if not best[1]: gfail('no rows for fns of %s'%gate)
    if mx is not None and best[0]>mx: gfail('%s at %d is above %d'%(best[1],best[0],mx))
    print('rlimit-gate: %s max %s %d'%(gate,best[1],best[0])); sys.exit(0)
for d in objs:
    if 'verification-results' not in d: continue
    print(d['verification-results'])
    rows=[]
    for m in d['times-ms']['smt']['smt-run-module-times']:
        for f in m['function-breakdown']:
            rows.append((f['rlimit'],f['function'],f['success']))
    rows.sort(reverse=True)
    for r in rows[:6]: print(' ',r)
    for w in want:
        for r in rows:
            if r[1].endswith('::'+w): print('  W',r)
    for r in rows:
        if not r[2]: print('  FAIL',r)
