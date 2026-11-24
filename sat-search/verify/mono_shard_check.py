"""Differential check of the legacy mono_shard.py encoder (it produced the L-meta-1343 shard-2 exclusions for
sizes 4-13) against reference monotone minima, via its MONO_TEST_GRAPH hook (no seed). Its model is
at-most-G: output on any gate, unused gates allowed, colex order from gate 0, boundary rows only. So the
union over first-gate cubes must be UNSAT at G = M - 1 and SAT at G = M (and M + 1 without exact/distinct),
for every combination of its exact and distinct options. Witnesses are checked on all rows.
Usage: python verify/mono_shard_check.py [--workers 11]"""
import argparse, json, os, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE); sys.path.insert(0, ROOT)
import reference as ref
import differential as dif


def job(args):
    n, terms, G, exact, distinct, expect = args
    edges = [tuple(i for i in range(n) if t >> i & 1) for t in terms]
    os.environ['MONO_TEST_GRAPH'] = f'{n}:' + ','.join(f'{u}-{v}' for u, v in edges)
    import mono_shard as ms
    ms.init(G, 'maplechrono', exact, distinct)
    tt = ref.truth_table(n, terms)
    verdict = 'UNSAT'
    for c in [(op, l, r) for op in (0, 1) for r in range(n) for l in range(r)]:
        _, st, model, _ = ms.run_cube(c)
        if st == 'MODEL':
            circ, out = model
            ok = all(ms.evaluate(circ, out, x) == bool(tt >> x & 1) for x in range(1 << n))
            verdict = 'SAT' if ok else 'BADWITNESS'
            break
    ms._W['s'].delete()
    return dict(n=n, terms=list(terms), G=G, exact=exact, distinct=distinct, expect=expect, verdict=verdict,
                ok=verdict == expect)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--workers', type=int, default=11)
    a = ap.parse_args()
    t0 = time.time()
    cache = dif.load_ref_cache()
    jobs = []
    for kind, n, t in dif.instances(False):
        if kind != 'graph':
            continue
        r = cache.get((n, t, 'monotone'))
        if not r or r['minimum'] is None:
            continue
        M = r['minimum']
        for exact in (False, True):
            for distinct in (False, True):
                jobs.append((n, t, M - 1, exact, distinct, 'UNSAT'))
                jobs.append((n, t, M, exact, distinct, 'SAT'))
                if not exact and not distinct:
                    jobs.append((n, t, M + 1, exact, distinct, 'SAT'))
    out = open(os.path.join(ROOT, 'results', 'differential', 'mono_shard_check.jsonl'), 'w', encoding='utf-8')
    out.write(json.dumps(dict(header=True, version=dif.source_version(), jobs=len(jobs))) + '\n')
    bad = 0
    with Pool(a.workers, maxtasksperchild=1) as p:
        for r in p.imap_unordered(job, jobs):
            out.write(json.dumps(r) + '\n')
            if not r['ok']:
                bad += 1
                print('MISMATCH', r, flush=True)
    print(f'mono_shard: {len(jobs)} jobs on graph instances, {bad} mismatches ({time.time() - t0:.0f}s)')
