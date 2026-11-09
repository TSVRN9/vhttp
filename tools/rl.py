# rl.py LOG [FN...]: print per-module verification results and the six highest-rlimit fns from cargo-verus --time-expanded JSON output,
# then the rlimit of each named FN. Run as: python3 -I tools/rl.py LOG [FN...]
# Gate mode: python3 -I tools/rl.py --gate NAME --pin FILE [--max N] LOG  prints `rlimit-gate: NAME max <fn> <n>` and exits 0, or
# exits 1 with the reason when LOG is unreadable, has no verification-results object, no rows, a failed run, a FAIL row, or a fn of NAME above N, or
# (per results object) a verus.version/commit/toolchain that differs from the pin FILE (tools/verus-pin.txt: version, commit, toolchain lines)
# or is-verifying-entire-crate not true; a missing or malformed pin fails.
# Ceilings mode: python3 -I tools/rl.py --ceilings FILE [--old FILE] LOG...  checks every fn of every LOG against the ceilings ratchet FILE
# (`<crate> <fn> <rlimit>` per fn above 8,000,000 in any crate; quic/quictls may not have lines; see rlimit-ceilings.sh for --old).
import json,sys
if len(sys.argv)>2 and sys.argv[1]=='--ceilings':
    CAP=8000000
    a=sys.argv[2:]; ceil=a[0]; a=a[1:]; old=None
    if a and a[0]=='--old': old=a[1]; a=a[2:]
    errs=[]
    def cfail(m): errs.append(m)
    def load(fn):
        d={}
        try: ls=open(fn).read().splitlines()
        except OSError: return None
        for l in ls:
            w=l.split()
            if len(w)!=3 or not w[2].isdigit() or not w[1].startswith(w[0]+'::'): cfail('%s: malformed line %r'%(fn,l)); continue
            if w[1] in d: cfail('%s: duplicate line for %s'%(fn,w[1]))
            d[w[1]]=(w[0],int(w[2]))
        return d
    cl=load(ceil)
    if not a: cfail('no logs given')
    rows={}
    for lg in a:
        try: t=open(lg).read()
        except OSError as e: cfail('cannot read %s: %s'%(lg,e)); continue
        dec=json.JSONDecoder(); i=0; seen=0
        while True:
            j=t.find('{',i)
            if j<0: break
            try: o,e=dec.raw_decode(t[j:])
            except ValueError: i=j+1; continue
            i=j+e
            if 'verification-results' not in o: continue
            seen+=1
            try:
                for m in o['times-ms']['smt']['smt-run-module-times']:
                    for f in m['function-breakdown']: rows[f['function']]=max(rows.get(f['function'],0),f['rlimit'])
            except (KeyError,TypeError): cfail('%s: unreadable results object'%lg)
        if not seen: cfail('%s: no verification-results object'%lg)
    if not rows: cfail('no per-fn rows in any log')
    over={f:r for f,r in rows.items() if r>CAP}
    if cl is None:
        if over: cfail('%s is missing but %d fns are above %d'%(ceil,len(over),CAP))
        cl={}
    elif not cl and over: cfail('%s is empty but %d fns are above %d'%(ceil,len(over),CAP))
    for f,(c,n) in sorted(cl.items()):
        if c in ('quic','quictls'): cfail('%s may not be listed: quic/quictls have a hard %d cap'%(f,CAP))
        if f not in rows or rows[f]<=CAP: cfail('stale ceiling line, the fn is gone or at or below %d (delete the line): %s %s %d'%(CAP,c,f,n))
    for f,r in sorted(over.items()):
        if f not in cl: cfail('unlisted fn above %d: %s at %d (restructure it; the ceilings file only shrinks)'%(CAP,f,r))
        elif r>cl[f][1]: cfail('%s at %d exceeds its ceiling %d'%(f,r,cl[f][1]))
    if old is not None:
        ol=load(old)
        if ol is None: cfail('cannot read the merge-base ceilings %s'%old); ol={}
        for f,(c,n) in sorted(cl.items()):
            if f not in ol: cfail('ceiling line not in the merge-base file (the file only shrinks): %s %s %d'%(c,f,n))
            elif n>ol[f][1]: cfail('ceiling for %s raised from %d to %d (the file only shrinks)'%(f,ol[f][1],n))
    for e in errs: print('rlimit-gate: ceilings: '+e,file=sys.stderr)
    if errs: sys.exit(1)
    print('rlimit-gate: ceilings ok (%d fns above %d, all listed)'%(len(over),CAP)); sys.exit(0)
gate=None; mx=None; pin=None; a=sys.argv[1:]
if a and a[0]=='--gate':
    gate=a[1]; a=a[2:]
    if a and a[0]=='--pin': pin=a[1]; a=a[2:]
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
    if pin is None: gfail('no --pin FILE given')
    try: pn=dict(l.split(' ',1) for l in open(pin).read().splitlines())
    except (OSError,ValueError) as e: gfail('cannot read the pin file %s: %s'%(pin,e))
    if not all(pn.get(k) for k in ('version','commit','toolchain')): gfail('pin file %s lacks a version, commit or toolchain line'%pin)
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
        try:
            vz=d['verus']
            for k in ('version','commit'):
                if vz[k]!=pn[k]: gfail('verus.%s is %r, the pin says %r'%(k,vz[k],pn[k]))
            if not vz['toolchain'].startswith(pn['toolchain']+'-'): gfail('verus.toolchain is %r, the pin says %s-*'%(vz['toolchain'],pn['toolchain']))
            if d['verification-results']['is-verifying-entire-crate'] is not True: gfail('is-verifying-entire-crate is not true (a partial run)')
        except (KeyError,TypeError): gfail('no verus object or is-verifying-entire-crate in the results object')
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
