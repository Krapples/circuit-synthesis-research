"""Time cert vs plain monotone rows on the 7-vertex C4-free graphs the analytical bound does not settle
(pieces at star - 1 and star - 2). Usage: WORKERS=4 python cert_bench7.py"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))
import os, time, warnings
warnings.filterwarnings('ignore')
from multiprocessing import Pool
import networkx as nx
import cube_search as cs
import c4free_scan as sc


def run(job):
    n, edges, G, c, cert = job
    masks = [(1 << u) | (1 << v) for u, v in edges]
    _, st, _, dt, stats = cs.run_cube((n, masks, G, 'maplechrono', c, True, True, {**sc.FAST, 'cert': cert}))
    conf = stats.split('conflicts=')[1].split()[0] if 'conflicts=' in stats else '0'
    return cert, st, dt, int(conf) if conf.isdigit() else 0


if __name__ == '__main__':
    L = sc.c4free_graphs(7)
    base = []
    for g in L[7]:
        if nx.is_connected(g):
            e = sorted(tuple(sorted(x)) for x in g.edges())
            s = len(e) + sc.tau(7, e) - 1
            if sc.mono_bound(e) < s:
                auts = cs.automorphisms(7, e)
                for G in (s - 1, s - 2):
                    for c in [(op, l, r) for op in (0, 1) for r in range(7) for l in range(r)]:
                        if cs.orbit_min(c, auts):
                            base.append((7, e, G, c))
    print(len(base), 'pieces', flush=True)
    for cert in (False, True):
        t = time.time()
        with Pool(int(os.environ.get('WORKERS', 22))) as p:
            out = p.map(run, [b + (cert,) for b in base])
        print(f'cert={cert}: wall {time.time() - t:.1f}s, CPU {sum(o[2] for o in out):.1f}s, '
              f'conflicts {sum(o[3] for o in out)}, statuses {sorted({o[1] for o in out})}', flush=True)
