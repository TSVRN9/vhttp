# rl.py LOG [FN...]: print per-module verification results and the six highest-rlimit fns from cargo-verus --time-expanded JSON output,
# then the rlimit of each named FN. Run as: python3 -I tools/rl.py LOG [FN...]
import json,sys
t=open(sys.argv[1]).read()
dec=json.JSONDecoder(); i=0; objs=[]
while True:
    j=t.find('{',i)
    if j<0: break
    try:
        o,e=dec.raw_decode(t[j:]); objs.append(o); i=j+e
    except ValueError: i=j+1
want=sys.argv[2:]
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
