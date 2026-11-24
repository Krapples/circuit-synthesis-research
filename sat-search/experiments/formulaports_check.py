"""Check the polarity (NOT-aware) formula ports. For every connected graph in the networkx atlas (2..nmax
vertices), compare the standalone ordered-terminal bound with and without --formulaports. Wherever the new
bound is higher, a general search (NOT gates allowed) at new - 1 gates must be UNSAT; a witness there means
the new bound is unsound. Usage: python formulaports_check.py [nmax]"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))
import sys, time
from multiprocessing import Pool
import networkx as nx
import cube_search as cs


def bounds(edges):
    T = cs._anti([(1 << u) | (1 << v) for u, v in edges])
    cs.ORDERED[0] = True
    old = cs.port_binary_lb(T, cs.port_costs(T))
    new = cs.port_binary_lb(T, cs.port_costs(T, formula=True, polarity=True))
    return old, new


def sat_below(job):
    n, edges, G = job
    masks = [(1 << u) | (1 << v) for u, v in edges]
    auts = cs.automorphisms(n, edges)
    allc = [(op, l, r) for op in (0, 1) for r in range(n) for l in range(r)] + [(2, i, i) for i in range(n)]
    for c in [c for c in allc if cs.orbit_min(c, auts)]:
        _, st, circ, _, _ = cs.run_cube((n, masks, G, 'maplechrono', c, True, True, dict(sens=True, units=True)))
        if st == 'WITNESS':
            return n, edges, G, circ
    return n, edges, G, None


if __name__ == '__main__':
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    t0 = time.time()
    graphs = [g for g in nx.graph_atlas_g() if 2 <= g.number_of_nodes() <= nmax and g.number_of_edges()
              and nx.is_connected(g)]
    improved = []
    for g in graphs:
        edges = sorted(tuple(sorted(e)) for e in g.edges())
        old, new = bounds(edges)
        assert new >= old
        if new > old:
            improved.append((g.number_of_nodes(), edges, old, new))
    print(f'{len(graphs)} connected graphs with 2..{nmax} vertices: {len(improved)} improved bounds '
          f'({time.time() - t0:.0f}s)', flush=True)
    for n, edges, old, new in improved:
        print(f'  n={n} edges={edges}: {old} -> {new}', flush=True)
    bad = 0
    with Pool(11) as p:
        for n, edges, G, circ in p.imap_unordered(sat_below, [(n, e, new - 1) for n, e, old, new in improved]):
            if circ is not None:
                bad += 1
                print(f'UNSOUND: n={n} edges={edges} has a circuit with {G} gates: {circ}', flush=True)
    print(f'CHECK: {len(improved) - bad}/{len(improved)} improved bounds confirmed by SAT one below '
          f'({time.time() - t0:.0f}s)')
