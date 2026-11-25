"""Throughput probe for completion-cache key cost on stuck free-NOT excess-5 layout searches.
Runs layout_projection.search_exact(excess 5) for a fixed wall time with ObligationCache(solver=certificate_completion)
under (maxsize, symmetry_limit) configurations, each in its own process; progress = layouts examined (deterministic
search order, so more layouts in the same time = faster). Usage: python experiments/cache_key_probe.py [seconds]"""
import json, os, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))
CASES = ('complete-5', 'hypergraph-09', 'comparator-04')
CONFIGS = ((4096, 32), (1 << 17, 32), (4096, 1), (1 << 17, 1), (1 << 17, 4))


def job(a):
    name, maxsize, sym, seconds = a
    from collections import Counter
    from module_contraction import simplify
    from signed_bound_compare import cases, restrict_essential
    from regional_obligation_cache import ObligationCache
    from regional_certificate_propagation import certificate_completion
    from layout_projection import search_exact
    from regional_deadline import timed
    fr = {nm: (n, f) for nm, _, n, f in cases()}
    n, f, _ = restrict_essential(*fr[name]); m, core, _ = simplify(n, f, True)
    comp = ObligationCache(maxsize=maxsize, solver=certificate_completion, symmetry_limit=sym); st = Counter()
    t0 = time.perf_counter()
    r = timed(seconds, lambda: {'status': 'done', 'w': search_exact(m, core, 5, True, st, completion=comp)}, lambda: {})
    mt = comp.metrics()
    return dict(case=name, maxsize=maxsize, symmetry_limit=sym, status=r['status'], seconds=round(time.perf_counter() - t0, 2),
                layouts=st['layouts'], queries=mt.get('queries', 0), solves=mt.get('cache_misses', 0),
                norm_entries=mt.get('normalization_entries'), norm_hits=mt.get('normalization_hits'))


if __name__ == '__main__':
    seconds = float(sys.argv[1]) if len(sys.argv) > 1 else 30
    jobs = [(c, ms, sy, seconds) for c in CASES for ms, sy in CONFIGS]
    out = open(os.path.join(HERE, 'results', 'cache_key_probe.jsonl'), 'w', encoding='utf-8')
    with Pool(len(jobs), maxtasksperchild=1) as p:
        for r in sorted(p.map(job, jobs), key=lambda r: (r['case'], r['maxsize'], -r['symmetry_limit'])):
            out.write(json.dumps(r) + '\n'); print(r, flush=True)
