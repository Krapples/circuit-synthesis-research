"""Safety check: the known 25-gate circuit (shard-2 seed + 22-gate cover circuit, canonically ordered after
the seed) must be accepted by cube_search in the seed-pinned, monotone --fast mode."""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))  # sat-search/
import cube_search as cs
EDGES = [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9),
         (6, 7), (6, 10), (7, 9), (8, 9)]
n = 11
SEED = [(1, 6, 9), (1, 7, 10), (0, 11, 12)]
circ = list(SEED); done = set(); terms = []
def add(op, a, b):
    circ.append((op, min(a, b), max(a, b))); return n + len(circ) - 1
for v in (0, 1, 3, 5, 7, 8, 10):
    nb = sorted(u for a, b in EDGES for u in ((b,) if a == v else (a,) if b == v else ()) if (min(u, v), max(u, v)) not in done)
    if not nb: continue
    for u in nb: done.add((min(u, v), max(u, v)))
    t = nb[0]
    for u in nb[1:]: t = add(1, t, u)
    terms.append(add(0, v, t))
o = terms[0]
for t in terms[1:]: o = add(1, o, t)
G = len(circ); first = 3
def swap(c, k):
    a, b = n + k, n + k + 1; ren = lambda i: b if i == a else a if i == b else i
    c = c[:]; c[k], c[k + 1] = c[k + 1], c[k]
    return [(op, min(ren(l), ren(r)), max(ren(l), ren(r))) for op, l, r in c]
changed = True
while changed:
    changed = False
    for k in range(first, G - 2):
        g1, g2 = circ[k], circ[k + 1]
        if n + k in g2[1:]: continue
        if (g1[2], g1[1]) > (g2[2], g2[1]): circ = swap(circ, k); changed = True
masks = [(1 << u) | (1 << v) for u, v in EDGES]
ok = all(cs.evaluate(n, circ, x) == any(x & m == m for m in masks) for x in range(1 << n))
FAST = dict(sens=True, units=True, usens=True, bypass=True, elim=True, elimclosure=True, signeddom=True,
            recursivebounds=True, recdepth=2, notbypass=True, recclosure=True, identifybounds=True,
            fanoutelim=True, pairro=True, colorbounds=True, sharecolor=True, colorbudget=True, nonot=True)
fix = [(k, *circ[k]) for k in range(1, G)]
r = cs.run_cube((n, masks, G, 'maplechrono', circ[0], True, True, {**FAST, 'colex_from': 3, 'fixgates': fix}))
print(f'known circuit: {G} gates, correct on all inputs = {ok}; encoding result with every gate pinned: {r[1]}  {r[4][:50]}')
