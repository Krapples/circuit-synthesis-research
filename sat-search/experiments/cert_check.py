"""Check the monotone certificate row encoding (flag cert, with nonot). For connected atlas graphs with 3..nmax
vertices, run the monotone search with the --fast rules at the star cost s = |E| + tau - 1 and at s - 1, s - 2,
with and without cert: the verdicts must agree and every witness must verify. Then time size 15 of
L-meta-1343 shard 2 (all 338 pieces) both ways.  Usage: python cert_check.py [nmax] [bench]"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))
import os, sys, time, itertools
from multiprocessing import Pool
import networkx as nx
import cube_search as cs

import os as _rs_os, sys as _rs_sys
_rs_sys.path.insert(0, _rs_os.path.dirname(_rs_os.path.dirname(_rs_os.path.abspath(__file__))))
from rulesets import fast_flags  # canonical --fast rule set (verify/test_rulesets.py)
FAST = fast_flags(monotone=True)


def tau(n, edges):
    for k in range(n + 1):
        for C in itertools.combinations(range(n), k):
            if all(u in C or v in C for u, v in edges):
                return k


def search(job):
    n, edges, G, cert = job
    masks = [(1 << u) | (1 << v) for u, v in edges]
    auts = cs.automorphisms(n, edges)
    allc = [(op, l, r) for op in (0, 1) for r in range(n) for l in range(r)]
    for c in [c for c in allc if cs.orbit_min(c, auts)]:
        _, st, circ, _, _ = cs.run_cube((n, masks, G, 'maplechrono', c, True, True, {**FAST, 'cert': cert}))
        if st == 'WITNESS':
            ok = all(cs.evaluate(n, circ, x) == any(x & m == m for m in masks) for x in range(1 << n))
            return job, 'WITNESS' if ok else 'BAD WITNESS'
    return job, 'UNSAT'


if __name__ == '__main__':
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    t0 = time.time()
    jobs = []
    for g in nx.graph_atlas_g():
        n = g.number_of_nodes()
        if 3 <= n <= nmax and g.number_of_edges() and nx.is_connected(g):
            edges = tuple(sorted(tuple(sorted(e)) for e in g.edges()))
            s = len(edges) + tau(n, edges) - 1
            for G in (s, s - 1, s - 2):
                if G >= n - 1:
                    jobs += [(n, edges, G, False), (n, edges, G, True)]
    with Pool(int(os.environ.get("WORKERS", 22))) as p:
        res = dict(p.imap_unordered(search, jobs))
    bad = 0
    for (n, edges, G, cert), st in res.items():
        if cert:
            other = res[(n, edges, G, False)]
            if st != other or st == 'BAD WITNESS':
                bad += 1
                print(f'MISMATCH n={n} edges={edges} G={G}: cert {st}, plain {other}', flush=True)
    print(f'CHECK: {len(jobs) // 2} (graph, size) cases, {bad} mismatches ({time.time() - t0:.0f}s)', flush=True)
    if len(sys.argv) > 2 and sys.argv[2] == 'bench':
        import l1343_full as lf
        for cert in (False, True):
            tasks = [(c, G, piece, (*args[:7], {**args[7], 'cert': cert})) for c, G, piece, args in lf.tasks_for(15)]
            t1 = time.time()
            with Pool(int(os.environ.get("WORKERS", 22))) as p:
                out = p.map(lf.run, tasks)
            cpu = sum(r[3][3] for r in out)
            sts = {r[3][1] for r in out}
            conf = sum(int(r[3][4].split('conflicts=')[1].split()[0]) for r in out if 'conflicts=' in r[3][4]
                       and r[3][4].split('conflicts=')[1].split()[0].isdigit())
            cl = sum(int(r[3][4].split('clauses=')[1].split()[0]) for r in out if 'clauses=' in r[3][4])
            print(f'L-meta-1343 size 15, cert={cert}: wall {time.time() - t1:.0f}s, CPU {cpu:.0f}s, '
                  f'conflicts {conf}, clauses {cl}, statuses {sts}', flush=True)
