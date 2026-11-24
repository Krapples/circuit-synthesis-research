"""Soundness check of the fixed-prefix bounds for prefixes longer than three gates.

The partial ordered bound (cube_search.ordered_prefix_bound) and the forced-repeat bound
(cube_search.partial_repeat_bound) claim: no monotone circuit (AND/OR, fan-in 2, every wire read) whose first
gates are the prefix P has fewer than b gates. Two independent tests on small graphs (4-5 vertices):

 1. Known circuits: find a minimum circuit by SAT, and for random topological orders of its gates take every
    prefix of length 1..6. The bound of each such prefix must be <= the circuit's size.
 2. Random prefixes: draw random monotone prefixes of length 4..6 and, for every exact size G below the
    claimed bound (capped at the graph's minimum + 1), run the plain SAT encoding (nonot, the prefix pinned, no other rules). Every run
    must be UNSAT. At G = bound a witness, if found, is verified and counted as a tight case.

Usage: python experiments/deep_prefix_check.py [graphs] [prefixes_per_graph] [workers] [seed]"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))
import random, sys, time
from multiprocessing import Pool
import networkx as nx
import cube_search as cs

PLAIN = dict(nonot=True)


def sat(n, masks, G, prefix):
    """Plain exact-size monotone search with the prefix pinned as gates 0..k-1."""
    fixed = [(i, *g) for i, g in enumerate(prefix[1:], 1)]
    flags = dict(PLAIN, colex_from=len(prefix), fixgates=fixed)
    _, st, circ, _, _ = cs.run_cube((n, list(masks), G, 'maplechrono', prefix[0], False, False, flags))
    if st == 'WITNESS':
        assert tuple(map(tuple, circ[:len(prefix)])) == tuple(prefix)
        assert all(cs.evaluate(n, circ, x) == any(x & m == m for m in masks) for x in range(1 << n))
    return st, circ


def minimum_circuit(n, masks):
    for G in range(n - 1, 4 * n):
        auts = None
        for op in (0, 1):
            for r in range(n):
                for l in range(r):
                    _, st, circ, _, _ = cs.run_cube((n, list(masks), G, 'maplechrono', (op, l, r), False, False,
                                                     dict(PLAIN)))
                    if st == 'WITNESS':
                        return G, circ
    raise RuntimeError('no circuit')


def topo_orders(n, circ, rng, count):
    """Random topological orders of the gates; returns relabelled circuits (prefix = first gates)."""
    G = len(circ)
    out = []
    for _ in range(count):
        placed, order = set(), []
        while len(order) < G:
            ready = [j for j in range(G) if j not in placed and all(a < n or a - n in placed for a in circ[j][1:])]
            j = rng.choice(ready)
            placed.add(j); order.append(j)
        pos = {n + j: n + k for k, j in enumerate(order)}
        relabel = lambda a: a if a < n else pos[a]
        new = []
        for j in order:
            op, l, r = circ[j]
            l, r = sorted((relabel(l), relabel(r)))
            new.append((op, l, r))
        out.append(new)
    return out


def bounds(n, masks, prefix):
    b = cs.ordered_prefix_bound(n, tuple(masks), tuple(prefix))
    rep = cs.partial_repeat_bound(n, tuple(masks), tuple(prefix[:-1]), prefix[-1]) if len(prefix) > 1 else 0
    return b, rep


def job(args):
    gid, n, edges, nprefix, seed = args
    rng = random.Random(seed)
    masks = tuple((1 << u) | (1 << v) for u, v in edges)
    out = dict(gid=gid, known=0, known_bad=[], random=0, sat_calls=0, unsound=[], tight=0, maxlen=0)
    size, circ = minimum_circuit(n, masks)
    out['min'] = size
    for order in topo_orders(n, [tuple(g) for g in circ], rng, 4):
        for k in range(1, min(len(order), 7)):
            b, rep = bounds(n, masks, order[:k])
            out['known'] += 1
            out['maxlen'] = max(out['maxlen'], k)
            if max(b, rep) > size:
                out['known_bad'].append((order[:k], b, rep, size))
    for _ in range(nprefix):
        k = rng.randint(4, 6)
        prefix = []
        for j in range(k):
            r = rng.randrange(1, n + j)
            l = rng.randrange(r)
            prefix.append((rng.randint(0, 1), l, r))
        b, rep = bounds(n, masks, prefix)
        claim = max(b, rep)
        out['random'] += 1
        cap = min(claim - 1, size + 1) if claim != float('inf') else size + 1
        for G in range(max(k, n - 1), int(cap) + 1):
            st, c = sat(n, masks, G, prefix)
            out['sat_calls'] += 1
            if st == 'WITNESS':
                out['unsound'].append((prefix, G, b, rep, c))
                break
        if claim != float('inf') and claim <= size + 1:
            st, _ = sat(n, masks, int(claim), prefix)
            out['sat_calls'] += 1
            out['tight'] += st == 'WITNESS'
    return out


if __name__ == '__main__':
    ngraphs = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    nprefix = int(sys.argv[2]) if len(sys.argv) > 2 else 15
    workers = int(sys.argv[3]) if len(sys.argv) > 3 else 11
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    rng = random.Random(seed)
    graphs = [g for g in nx.graph_atlas_g() if 4 <= g.number_of_nodes() <= 5 and nx.is_connected(g)
              and g.number_of_edges() >= 3]
    rng.shuffle(graphs)
    jobs = [(i, g.number_of_nodes(), sorted(tuple(sorted(e)) for e in g.edges()), nprefix, seed * 1000 + i)
            for i, g in enumerate(graphs[:ngraphs])]
    t0 = time.time()
    tot = dict(known=0, random=0, sat_calls=0, tight=0, bad=0, unsound=0)
    with Pool(workers) as p:
        for r in p.imap_unordered(job, jobs):
            for k in ('known', 'random', 'sat_calls', 'tight'):
                tot[k] += r[k]
            for item in r['known_bad']:
                tot['bad'] += 1
                print(f'KNOWN-CIRCUIT VIOLATION graph {jobs[r["gid"]][2]}: prefix {item[0]} bound {item[1]} '
                      f'repeat {item[2]} > circuit size {item[3]}', flush=True)
            for item in r['unsound']:
                tot['unsound'] += 1
                print(f'UNSOUND graph {jobs[r["gid"]][2]}: prefix {item[0]} has a size-{item[1]} circuit but '
                      f'bounds {item[2]}/{item[3]}: {item[4]}', flush=True)
    print(f'CHECK: {len(jobs)} graphs; {tot["known"]} known-circuit prefixes, {tot["bad"]} violations; '
          f'{tot["random"]} random 4-6 gate prefixes, {tot["sat_calls"]} SAT calls, {tot["unsound"]} unsound, '
          f'{tot["tight"]} tight at the bound ({time.time() - t0:.0f}s)', flush=True)
