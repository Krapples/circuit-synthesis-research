"""Safety check with a known circuit that USES the shard-2 seed: seed (x6|x9, x7|x10, AND), then
h = AND(seed, x6|x7) = x6x7 | x6x10 | x7x9, a cover circuit for the remaining 13 edges, all ORed.
Canonically ordered after the seed; must be accepted with every --fast rule on (monotone, seed pinned)."""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))  # sat-search/
import itertools, cube_search as cs
EDGES = [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9),
         (6, 7), (6, 10), (7, 9), (8, 9)]
n = 11
circ = [(1, 6, 9), (1, 7, 10), (0, 11, 12)]
def add(op, a, b):
    circ.append((op, min(a, b), max(a, b))); return n + len(circ) - 1
g14 = add(1, 6, 7); h = add(0, 13, g14)
rest = [e for e in EDGES if e not in ((6, 7), (6, 10), (7, 9))]
for k in range(1, n + 1):
    T = next((T for T in itertools.combinations(range(n), k) if all(u in T or v in T for u, v in rest)), None)
    if T: break
done = set(); terms = [h]
for v in T:
    nb = sorted(u for a, b in rest for u in ((b,) if a == v else (a,) if b == v else ()) if (min(u, v), max(u, v)) not in done)
    if not nb: continue
    for u in nb: done.add((min(u, v), max(u, v)))
    t = nb[0]
    for u in nb[1:]: t = add(1, t, u)
    terms.append(add(0, v, t))
o = terms[0]
for t in terms[1:]: o = add(1, o, t)
G = len(circ)
def swap(c, k):
    a, b = n + k, n + k + 1; ren = lambda i: b if i == a else a if i == b else i
    c = c[:]; c[k], c[k + 1] = c[k + 1], c[k]
    return [(op, min(ren(l), ren(r)), max(ren(l), ren(r))) for op, l, r in c]
changed = True
while changed:
    changed = False
    for k in range(3, G - 2):
        g1, g2 = circ[k], circ[k + 1]
        if n + k in g2[1:]: continue
        if (g1[2], g1[1]) > (g2[2], g2[1]): circ = swap(circ, k); changed = True
masks = [(1 << u) | (1 << v) for u, v in EDGES]
ok = all(cs.evaluate(n, circ, x) == any(x & m == m for m in masks) for x in range(1 << n))
used = {i for _, l, r in circ for i in (l, r)}
unused = [n + k for k in range(G - 1) if n + k not in used]
FAST = dict(sens=True, units=True, usens=True, bypass=True, elim=True, elimclosure=True, signeddom=True,
            recursivebounds=True, recdepth=2, notbypass=True, recclosure=True, identifybounds=True,
            fanoutelim=True, pairro=True, colorbounds=True, sharecolor=True, colorbudget=True, nonot=True)
fix = [(k, *circ[k]) for k in range(1, G)]
off = cs.run_cube((n, masks, G, 'maplechrono', circ[0], False, False, {'nonot': True, 'colex_from': 3, 'fixgates': fix}))
on = cs.run_cube((n, masks, G, 'maplechrono', circ[0], True, True, {**FAST, 'colex_from': 3, 'fixgates': fix}))
print(f'known circuit: {G} gates, correct = {ok}, unused gates = {unused}; rules OFF: {off[1]}; all --fast rules ON: {on[1]}')
