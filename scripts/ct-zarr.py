#!/usr/bin/env python3
# Static dump check (8c Task 6 review): no body local (parameters included), ZeroSized constant or
# call destination may have a unit-like type that holds an array ([T; 0], or [Z; n] with unit-like
# Z, at any depth), as ctmir::sem's `ul_arr` decides them (unit_like with clos false or true, plus
# has_arr). ctmir's translator rejects each such site (Unsupported); this scan makes a dump that
# holds one fail loudly instead. Usage: python3 -I scripts/ct-zarr.py <mir-*.json>...; exit 1 on a
# hit, or when it cannot decide: no file given, an instance row without a `body` key, a ZeroSized
# constant without an int `ty`, or an array whose length it cannot read inside a possibly unit-like
# type at one of those sites (counted as a hit). The JSON is walked, not matched as text. Called by
# scripts/ct-dump.sh after each dump and by scripts/ct-check.sh on semconf's.
import json, sys

def die(msg):
    print(f'ct-zarr: {msg}', file=sys.stderr)
    sys.exit(2)

def scan(f):
    d = json.load(open(f))
    byid = {t['id']: t for t in d['tys']}
    cu = {c['id']: c.get('usize') for c in d['consts']}
    adts = {a['ty']: a for a in d['adts']}
    def rig(i): return byid.get(i, {}).get('kind', {}).get('RigidTy')
    def alen(c):
        if 'id' in c and c['id'] in cu and cu[c['id']] is not None: return cu[c['id']]
        v = c.get('kind', {}).get('Value') if isinstance(c.get('kind'), dict) else None
        if v: return int.from_bytes(bytes(v[1]['bytes']), 'little')
        return None
    def fty(fl): return fl if isinstance(fl, int) else fl.get('ty', -1)
    def all3(xs):
        # three-valued and: False wins, then None (unknown), else True
        xs = list(xs)
        return False if False in xs else (None if None in xs else True)
    def ul(i, clos, depth=0):
        # True, False, or None when an array length cannot be read
        if depth > len(byid) + 1: return False
        r = rig(i)
        if not isinstance(r, dict):
            return False
        if 'Tuple' in r: return all3(ul(t, clos, depth + 1) for t in r['Tuple'])
        if 'Adt' in r:
            a = adts.get(i)
            if not (bool(a) and not a['is_box'] and a['kind'] != 'Union' and len(a['variants']) == 1): return False
            return all3(ul(fty(x), clos, depth + 1) for x in a['variants'][0].get('fields', []))
        if 'Array' in r:
            e, c = r['Array']; n = alen(c)
            if n is None: return None
            return True if n == 0 else ul(e, clos, depth + 1)
        if 'FnDef' in r: return True
        if 'Closure' in r: return clos
        return False
    def has_arr(i, depth=0):
        if depth > len(byid) + 1: return False
        r = rig(i)
        if not isinstance(r, dict): return False
        if 'Tuple' in r: return any(has_arr(t, depth + 1) for t in r['Tuple'])
        if 'Adt' in r:
            a = adts.get(i)
            return bool(a) and len(a['variants']) == 1 and any(has_arr(fty(x), depth + 1) for x in a['variants'][0].get('fields', []))
        return 'Array' in r
    def ul_arr(i):
        u = [ul(i, False), ul(i, True)]
        v = True if True in u else (None if None in u else False)
        return v if has_arr(i) else False
    zt = {i for i in byid if ul_arr(i) is not False}
    unknown = {i for i in zt if ul_arr(i) is None}
    def proj_ty(t, e):
        r = rig(t)
        if e == 'Deref': return r['Ref'][1] if isinstance(r, dict) and 'Ref' in r else None
        if isinstance(e, dict) and 'Field' in e: return e['Field'][1]
        if isinstance(e, dict) and ('Index' in e or 'ConstantIndex' in e):
            if isinstance(r, dict) and 'Array' in r: return r['Array'][0]
            if isinstance(r, dict) and 'Slice' in r: return r['Slice']
            return None
        if isinstance(e, dict) and 'Downcast' in e: return t
        return None
    def place_ty(b, p):
        t = b['locals'][p['local']]['ty']
        for e in p['projection']:
            if t is None: return None
            t = proj_ty(t, e)
        return t
    def zero_sized(x, out):
        # every {"kind": "ZeroSized", "ty": <int>} object, at any depth
        if isinstance(x, dict):
            if x.get('kind') == 'ZeroSized':
                if not isinstance(x.get('ty'), int): die(f'{f}: a ZeroSized constant without an int ty: {json.dumps(x)[:100]}')
                out.append(x['ty'])
            for v in x.values(): zero_sized(v, out)
        elif isinstance(x, list):
            for v in x: zero_sized(v, out)
        return out
    locs, zcs, dests = [], [], []
    for inst in d['insts']:
        if 'body' not in inst: die(f'{f}: instance {inst.get("name")} has no body key')
        b = inst['body']
        if b is None: continue
        for k, l in enumerate(b['locals']):
            if l['ty'] in zt: locs.append((inst['name'], k, l['ty'], json.dumps(byid[l['ty']]['kind'])[:80]))
        for t in zero_sized(b, []):
            if t in zt: zcs.append((inst['name'], t))
        for blk in b['blocks']:
            c = blk['terminator']['kind']
            if isinstance(c, dict) and 'Call' in c:
                t = place_ty(b, c['Call']['destination'])
                if t in zt: dests.append((inst['name'], t))
    hits = locs + zcs + dests
    print(f'ct-zarr: {f}: {len(zt)} unit-like array types ({len(unknown)} of unknown length), {len(locs)} locals, {len(zcs)} ZeroSized constants, {len(dests)} call destinations')
    for h in hits[:20]: print('  ', h, '(length unknown)' if h[2 if len(h) > 2 else 1] in unknown else '')
    return len(hits)

if __name__ == '__main__':
    if len(sys.argv) < 2: die('usage: ct-zarr.py <mir-*.json>...')
    sys.exit(1 if sum(scan(f) for f in sys.argv[1:]) else 0)
