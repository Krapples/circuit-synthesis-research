"""Probe: does extending a surviving pinned prefix by one gate let the analytical bounds reject its children?
For a size-19 L-meta-1343 survivor (results/l1343_size19_survivors.json), enumerate every next gate allowed by
the exact-G model and the colex order (keys (r, l) nondecreasing after colex_from), and compute the forced-
repeat bound (parent projections, cheap) and the ordered prefix bound (one more feature) for each child.
Usage: python experiments/bnb_depth_probe.py [survivor_id] [workers]"""
import json, os, sys, time
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import cube_search as cs
import l1343_full as L

S = json.load(open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'results',
                                'l1343_size19_survivors.json')))


def children(n, prefix, colex_from):
    j = n + len(prefix)
    last = prefix[-1] if len(prefix) > colex_from else None
    out = []
    for r in range(j):
        for l in range(r):
            if last is not None and (r, l) < (last[2], last[1]):
                continue
            for op in (0, 1):
                out.append((op, l, r))
    return out


def bound(args):
    prefix, child = args
    t = time.time()
    rep = cs.partial_repeat_bound(L.n, tuple(L.MASKS), tuple(prefix), child)
    t1 = time.time()
    ordb = cs.ordered_prefix_bound(L.n, tuple(L.MASKS), tuple(prefix) + (child,))
    return child, rep, ordb, round(t1 - t, 2), round(time.time() - t1, 2)


if __name__ == '__main__':
    sid = sys.argv[1] if len(sys.argv) > 1 else 'a:1-0-2'
    workers = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    s = next(x for x in S['survivors'] if x['id'] == sid)
    prefix = [tuple(g) for g in s['prefix']]
    budget = s['budget']
    kids = children(L.n, prefix, s['colex_from'])
    print(f'{sid}: prefix {prefix}, budget {budget}, {len(kids)} children', flush=True)
    t0 = time.time()
    rej_rep = rej_ord = 0
    dist = {}
    with Pool(workers) as p:
        for child, rep, ordb, tr, to in p.imap_unordered(bound, [(prefix, c) for c in kids]):
            b = max(rep, ordb)
            dist[b] = dist.get(b, 0) + 1
            rej_rep += rep > budget
            rej_ord += b > budget
            if b <= budget:
                print(f'  survivor child {child}: repeat {rep}, ordered {ordb}', flush=True)
    print(f'repeat bound rejects {rej_rep}/{len(kids)}; with ordered bound {rej_ord}/{len(kids)}; '
          f'bound distribution {sorted(dist.items())}; {time.time() - t0:.0f}s')
