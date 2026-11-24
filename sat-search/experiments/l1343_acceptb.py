import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))  # sat-search/
import itertools, cube_search as cs, l1343_accept2 as A2
n = 11; E = A2.EDGES; masks = A2.masks
circ = [(1, 6, 9), (1, 7, 10)]
def add(op, a, b):
    circ.append((op, min(a, b), max(a, b))); return n + len(circ) - 1
h1 = add(0, 7, 11); h2 = add(0, 6, 12)        # x6x7|x7x9 and x6x7|x6x10
rest = [e for e in E if e not in ((6, 7), (7, 9), (6, 10))]
for k in range(1, n + 1):
    T = next((T for T in itertools.combinations(range(n), k) if all(u in T or v in T for u, v in rest)), None)
    if T: break
done = set(); terms = [h1, h2]
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
def swap(cc, k):
    a, b = n + k, n + k + 1; rn = lambda i: b if i == a else a if i == b else i
    cc = cc[:]; cc[k], cc[k + 1] = cc[k + 1], cc[k]
    return [(op, min(rn(l), rn(r)), max(rn(l), rn(r))) for op, l, r in cc]
ch = True
while ch:
    ch = False
    for k in range(2, G - 2):
        g1, g2 = circ[k], circ[k + 1]
        if n + k in g2[1:]: continue
        if (g1[2], g1[1]) > (g2[2], g2[1]): circ = swap(circ, k); ch = True
ok = all(cs.evaluate(n, circ, x) == any(x & m == m for m in masks) for x in range(1 << n))
used = {i for _, l, r in circ for i in (l, r)}
r = cs.run_cube((n, masks, G, 'maplechrono', circ[0], True, True, {**A2.FAST, 'colex_from': 2, 'fixgates': [(k, *circ[k]) for k in range(1, G)]}))
print(f'case (b) known circuit: {G} gates, correct={ok}, unused={[n+k for k in range(G-1) if n+k not in used]}, all rules ON: {r[1]}')
