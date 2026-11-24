"""Sanity check for the range-2 scan: every graph has a circuit of exactly E + tau - 1 gates (one AND per
cover vertex over its uncovered neighbours, ORed together), so a search AT the bound must find one.
Usage: python bound_check.py [nmax]"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))  # sat-search/
import json, sys
from multiprocessing import Pool
import cube_search as cs


def find(g):
    n, edges = g['n'], [tuple(e) for e in g['edges']]
    masks = [(1 << u) | (1 << v) for u, v in edges]
    auts = cs.automorphisms(n, edges)
    allc = [(op, l, r) for op in (0, 1) for r in range(n) for l in range(r)] + [(2, i, i) for i in range(n)]
    for c in [c for c in allc if cs.orbit_min(c, auts)]:
        cube, st, circ, dt, _ = cs.run_cube((n, masks, g['bound'], 'maplechrono', c, True, True, dict(sens=True, units=True)))
        if st == 'WITNESS':
            ok = all(cs.evaluate(n, circ, x) == any(x & m == m for m in masks) for x in range(1 << n))
            return g['n'], g['E'], g['bound'], ok
    return g['n'], g['E'], g['bound'], None


if __name__ == '__main__':
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    gs = [g for g in json.load(open('range2_graphs.json')) if g['n'] <= nmax]
    bad = 0
    with Pool(11) as p:
        for n, E, b, ok in p.imap_unordered(find, gs):
            print(f'n={n} E={E} at the bound ({b} gates): '
                  f'{"circuit found and verified" if ok else "NOT FOUND - scanner problem" if ok is None else "FAILED verification"}',
                  flush=True)
            bad += ok is not True
    print(f'BOUND CHECK: {len(gs) - bad}/{len(gs)} graphs OK')
