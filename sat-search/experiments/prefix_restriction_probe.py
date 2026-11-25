"""Does theory/prefix_restriction_bound.py add branch rejections beyond the production prefix bounds?
For children of L-meta-1343 size-19 survivors: production = max(forced-repeat, ordered prefix bound);
new = len(prefix) + prefix_restriction_bound.Bound(cols, P, N, mono=True).lower(U=unread wires, depth=1),
where cols are the input and prefix-wire columns on the boundary rows (edges positive, maximal independent
sets negative) and U marks the wires the suffix must still read. Writes results/prefix_restriction_probe.jsonl.
Usage: python experiments/prefix_restriction_probe.py [workers] [survivor_id ...]"""
import json, os, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))
import cube_search as cs
import l1343_full as L
from prefix_restriction_bound import Bound
from bnb import children


def suffix_bound(n, masks, prefix):
    ones, zeros = cs.boundary_rows(n, masks)
    rows = list(ones) + list(zeros)
    P = (1 << len(ones)) - 1
    N = ((1 << len(rows)) - 1) ^ P
    vals = []
    for r in rows:
        v = [r >> i & 1 for i in range(n)]
        for op, a, b in prefix:
            v.append(v[a] & v[b] if op == 0 else v[a] | v[b])
        vals.append(v)
    width = n + len(prefix)
    cols = tuple(sum(vals[k][w] << k for k in range(len(rows))) for w in range(width))
    read = set()
    for op, a, b in prefix:
        read.update((a, b))
    U = sum(1 << w for w in range(width) if w not in read)
    return len(prefix) + Bound(cols, P, N, mono=True).lower(U=U, depth=1)


def job(args):
    sid, prefix, G = args
    t0 = time.time()
    masks = tuple(L.MASKS)
    rep = cs.partial_repeat_bound(L.n, masks, tuple(prefix[:-1]), prefix[-1])
    ordb = cs.ordered_prefix_bound(L.n, masks, tuple(prefix)) if L.n + len(prefix) <= cs.PARTIAL_FEATURE_LIMIT else 0
    t1 = time.time()
    new = suffix_bound(L.n, masks, prefix)
    return dict(survivor=sid, prefix=prefix, G=G, production=max(rep, ordb), prefix_restriction=new,
                production_seconds=round(t1 - t0, 2), new_seconds=round(time.time() - t1, 2))


if __name__ == '__main__':
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    only = set(sys.argv[2:]) or {'a:1-4-5', 'b:1-4-8', 'a:1-0-2'}
    S = json.load(open(os.path.join(HERE, 'results', 'l1343_size19_survivors.json')))
    jobs = []
    for s in S['survivors']:
        if s['id'] in only:
            pre = [tuple(g) for g in s['prefix']]
            jobs += [(s['id'], pre + [c], s['budget']) for c in children(L.n, pre, s['colex_from'])]
    out = open(os.path.join(HERE, 'results', 'prefix_restriction_probe.jsonl'), 'w', encoding='utf-8')
    tot = dict(children=0, production_rejects=0, new_rejects=0, new_only=0, prod_s=0.0, new_s=0.0)
    with Pool(workers) as p:
        for r in p.imap_unordered(job, jobs):
            out.write(json.dumps(r) + '\n'); out.flush()
            G = r['G']; pr = r['production'] > G; nw = r['prefix_restriction'] > G
            tot['children'] += 1; tot['production_rejects'] += pr; tot['new_rejects'] += nw; tot['new_only'] += nw and not pr
            tot['prod_s'] += r['production_seconds']; tot['new_s'] += r['new_seconds']
    print('SUMMARY', {k: round(v, 1) if isinstance(v, float) else v for k, v in tot.items()}, flush=True)
