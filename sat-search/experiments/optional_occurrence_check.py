"""Empirical test of the repeated-provider optional-occurrence theorem for regional completion.

Claim (free-NOT): if a regional query is completable when each repeated provider p (allocated c_p >= 2 times) is
used d_p times with 1 <= d_p <= c_p, and every singleton leaf (private input or c_p = 1 provider) is used exactly
once, then it is completable with all c_p occurrences. So exact multiplicities can be relaxed to ranges for
exclusion (an infeasible relaxed query proves the exact query infeasible, and conversely).
Test: random small layouts; the target is built from a random formula over a reduced multiset (so the relaxed
query is feasible by construction); the exact reference solver two_sharing_core.local decides the full query.
Also run in the monotone basis as a contrast. Counterexamples are minimized and printed.
Writes results/optional_occurrence_check.jsonl. Usage: python experiments/optional_occurrence_check.py [trials]"""
import json, os, sys
from collections import Counter
from random import Random
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory'):
    sys.path.insert(0, os.path.join(HERE, d))
from two_sharing_core import local
from regional_padding import columns


def trial(rng, signed):
    m = rng.randrange(3); r = rng.randrange(1, 4)
    c = [rng.randrange(1, 4) for _ in range(r)]
    if max(c) < 2:
        c[rng.randrange(r)] = 2
    d = [x if x == 1 else rng.randrange(1, x + 1) for x in c]
    if d == c:
        i = max(range(r), key=lambda i: c[i]); d[i] -= 1
    if m + sum(d) < 2:
        return None
    full = tuple(i for i in range(r) for _ in range(c[i])); red = tuple(i for i in range(r) for _ in range(d[i]))
    pats = tuple(p for p in range(1 << r) if rng.random() < 0.8) or (0,)
    cs, _, one = columns(m, red, pats, (0,) * len(pats))
    leaves = [cs[i] for i in range(m)] + [cs[m + i] for i in red]
    leaves = [v ^ (one if signed and rng.randrange(2) else 0) for v in leaves]
    while len(leaves) > 1:
        a = leaves.pop(rng.randrange(len(leaves))); b = leaves.pop(rng.randrange(len(leaves)))
        leaves.append(a & b if rng.randrange(2) else a | b)
    f = leaves[0]; w = 1 << m; sm = (1 << w) - 1
    ts = tuple((f >> (k * w)) & sm for k in range(len(pats)))
    assert local(m, red, pats, ts, signed) is not None       # relaxed instance feasible (sanity)
    ok = local(m, full, pats, ts, signed) is not None
    return dict(m=m, c=c, d=d, pats=list(pats), targets=list(ts), signed=signed, full_feasible=ok)


if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    rng = Random(11251); C = Counter(); bad = {True: [], False: []}
    out = open(os.path.join(HERE, 'results', 'optional_occurrence_check.jsonl'), 'w', encoding='utf-8')
    for t in range(N):
        signed = bool(t % 2); r = trial(rng, signed)
        if r is None:
            continue
        C[signed, 'trials'] += 1; C[signed, 'holds'] += r['full_feasible']
        if not r['full_feasible']:
            bad[signed].append(r); out.write(json.dumps(r) + '\n')
    for s in (True, False):
        print('free-NOT' if s else 'monotone', 'trials', C[s, 'trials'], 'restorable', C[s, 'holds'],
              'counterexamples', len(bad[s]), flush=True)
        for r in sorted(bad[s], key=lambda r: (r['m'] + sum(r['c']), len(r['pats'])))[:3]:
            print('   ', r, flush=True)
