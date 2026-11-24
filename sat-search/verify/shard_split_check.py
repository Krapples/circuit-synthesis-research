"""Audit of the L-meta-1343 shard decomposition (l1343_full.tasks_for) on small functions.

The shard 'circuits containing s1 = OR(a, b), s2 = OR(c, d), s3 = AND(s1, s2)' is split into
  case a: s3 used    -> exact size G with s1, s2, s3 pinned as gates 0-2 (colex order from gate 3) and the
                        next gate enumerated as the piece (all (op, l, r), r < n + 3);
  case b: s3 unused  -> dropping it leaves exact size G - 1 with s1, s2 pinned (colex order from gate 2) and
                        the piece at gate 2 (r < n + 2).
l1343_full hard-codes the 11-input target, so this check mirrors its task construction exactly (same pinning,
colex_from and piece enumeration, same rule flags from rulesets) on small graphs with analogous seeds and
compares, for each case, the union over pieces with the reference: exists an exact-size circuit (every wire
read) starting with the pinned seed. Expected: equal verdicts at the reference minimum of each case and one
below it. Usage: python verify/shard_split_check.py [--workers 11]"""
import argparse, json, os, sys, time
from itertools import combinations
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE); sys.path.insert(0, ROOT)
import reference as ref
import differential as dif
import rulesets
import cube_search as cs

CONFIGS = {'plain': (dict(nonot=True), False, False),
           'fast': (rulesets.fast_flags(True), True, True),
           'fast+partial': ({**rulesets.fast_flags(True), 'partialordered': True, 'partialrepeat': True}, True, True)}


def tasks(n, masks, seed, G, case, flags, fanout, readonce):
    (a, b), (c, d) = seed
    out = []
    if case == 'a':
        j = n + 3
        for piece in [(op, l, r) for r in range(j) for l in range(r) for op in (0, 1)]:
            out.append((n, masks, G, 'maplechrono', (1, a, b), fanout, readonce,
                        {**flags, 'colex_from': 3, 'fixgates': [(1, 1, c, d), (2, 0, n, n + 1), (3, *piece)]}))
    else:
        j = n + 2
        for piece in [(op, l, r) for r in range(j) for l in range(r) for op in (0, 1)]:
            out.append((n, masks, G - 1, 'maplechrono', (1, a, b), fanout, readonce,
                        {**flags, 'colex_from': 2, 'fixgates': [(1, 1, c, d), (2, *piece)]}))
    return out


def job(args):
    name, n, terms, seed, case, G, expect = args
    flags, fanout, readonce = CONFIGS[name]
    tt = ref.truth_table(n, terms)
    verdict = 'UNSAT'
    for t in tasks(n, list(terms), seed, G, case, flags, fanout, readonce):
        _, st, circ, _, info = cs.run_cube(t)
        if st == 'WITNESS':
            (a, b), (c, d) = seed
            prefix = ((1, a, b), (1, c, d), (0, n, n + 1)) if case == 'a' else ((1, a, b), (1, c, d))
            ok = ref.check_witness(n, tt, [tuple(g) for g in circ], prefix, True, 'monotone')
            verdict = 'SAT' if ok else 'BADWITNESS'
            break
        if st != 'UNSAT':
            verdict = st
            break
    return dict(config=name, n=n, terms=list(terms), seed=seed, case=case, G=G, expect=expect, verdict=verdict,
                ok=verdict == expect)


def case_minimum(args):
    n, terms, seed, case = args
    tt = ref.truth_table(n, terms)
    (a, b), (c, d) = seed
    P = ((1, a, b), (1, c, d), (0, n, n + 1)) if case == 'a' else ((1, a, b), (1, c, d))
    M = ref.minimum(n, tt, 'monotone', seconds=dif.REF_SECONDS)[0]
    if M in (None, 'undecided'):
        return None
    for size in range(max(len(P), M), M + 5):
        w, info = ref.sat_exists(n, tt, size, 'monotone', P, seconds=dif.REF_SECONDS)
        if info.get('undecided'):
            return None
        if w is not None:
            # case a pins three gates and claims size G; case b claims size G - 1 for shard size G
            return (n, terms, seed, case, size if case == 'a' else size + 1)
    return None


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--workers', type=int, default=11)
    a = ap.parse_args()
    t0 = time.time()
    items = []
    for kind, n, t in dif.instances(False):
        if kind != 'graph' or n < 4:
            continue
        pairs = list(combinations(range(n), 2))
        seeds = [(p, q) for p, q in combinations(pairs, 2) if not set(p) & set(q)][:3]
        for seed in seeds:
            for case in ('a', 'b'):
                items.append((n, t, seed, case))
    with Pool(a.workers) as p:
        mins = [x for x in p.map(case_minimum, items) if x is not None]
    jobs = []
    for n, t, seed, case, G in mins:
        if (case == 'a' and G < 4) or (case == 'b' and G - 1 < 3):
            continue              # the decomposition needs a piece gate after the pinned seed (sizes >= 14 in L-meta-1343)
        for name in CONFIGS:
            jobs.append((name, n, t, seed, case, G, 'SAT'))
            if (case == 'a' and G - 1 >= 4) or (case == 'b' and G - 2 >= 3):
                jobs.append((name, n, t, seed, case, G - 1, 'UNSAT'))
    out = open(os.path.join(dif.RESULTS, 'shard_split_check.jsonl'), 'w', encoding='utf-8')
    out.write(json.dumps(dict(header=True, version=dif.source_version(), jobs=len(jobs))) + '\n')
    bad = 0
    with Pool(a.workers) as p:
        for r in p.imap_unordered(job, jobs):
            out.write(json.dumps(r) + '\n')
            if not r['ok']:
                bad += 1
                print('MISMATCH', r, flush=True)
    print(f'shard split: {len(mins)} (instance, seed, case) minima, {len(jobs)} jobs, {bad} mismatches '
          f'({time.time() - t0:.0f}s)')
