"""Untrusted, offline helper: builds the Pratt certificate tree for P-256's p and n with sympy
(not stdlib; `pip install sympy`). Output: node -> [witness, {prime factor of node - 1: exponent}].
Run: python3 scripts/p256_pratt_factor.py > scripts/p256_pratt.json
Nothing here is trusted: scripts/gen_p256_group.py re-checks the data and Verus re-checks every
certificate it emits (crates/crypto/src/p256_group/pratt.rs)."""
# Pratt certificate trees for P-256 p and n (sympy factorint; output: node -> (witness, factorization)).
from sympy import factorint, isprime, primitive_root, n_order
import sys, time, json
p = 2**256 - 2**224 + 2**192 + 2**96 - 1
n = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
SMALL = 1 << 16
cert = {}
def build(q):
    if q < SMALL or q in cert: return
    f = factorint(q - 1)
    a = 2
    while not all(pow(a, (q - 1) // r, q) != 1 for r in f): a += 1
    assert pow(a, q - 1, q) == 1
    cert[q] = (a, f)
    for r in f: build(r)
t = time.time()
for q in (p, n):
    assert isprime(q); build(q)
print(json.dumps({str(q): [a, {str(r): e for r, e in f.items()}] for q, (a, f) in cert.items()}, indent=0))
print('nodes', len(cert), 'time', round(time.time() - t, 1), file=sys.stderr)
