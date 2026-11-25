"""Counted-NOT lower bound for partial nonmonotone labels: binary + NOT.

total(P, N) >= partial_first_gate_bound.bound(n, P, N, mono=False)   (binary gates, free-NOT relaxation)
             + partial_inversion.inversion(boundary(inputs, P, N))   (exact minimum NOT count, Markov)
The two parts bound disjoint gate types, so their sum bounds the counted total. Checked against the
independent counted gate-set oracle (theory/module_contraction.brute, basis 'counted'): the bound must not
exceed min over completions of the counted cost. Gains are measured against the binary bound alone (the
production partial bound in the free-NOT/NOT basis has no NOT term).
Writes results/partial_not_bound.jsonl. Usage: python experiments/partial_not_bound.py"""
import json, os, random, sys, time
from collections import Counter
from itertools import product
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, 'theory'))
from module_contraction import brute, vars
from partial_first_gate_bound import bound as partial_bound
from partial_inversion import inversion, boundary


def total_bound(n, P, N):
    b = partial_bound(n, P, N, False, True)
    return b, inversion(boundary(vars(n), P, N))


def run(n, tables, known, out, tag):
    c = Counter()
    ordered = sorted(known.items(), key=lambda q: q[1])
    for P, N in tables:
        if not P or not N or P & N:
            continue
        b, inv = total_bound(n, P, N)
        if b == float('inf'):
            continue
        opt = next((v for f, v in ordered if f & P == P and not f & N), None)
        c['cases'] += 1
        c['not_gain'] += inv > 0
        if opt is not None:
            assert b + inv <= opt, (n, P, N, b, inv, opt)
            c['checked'] += 1
            c['exact'] += b + inv == opt
            c['exact_binary_only'] += b == opt
        out.write(json.dumps(dict(set=tag, n=n, P=P, N=N, binary=b, inversion=inv, oracle=opt)) + '\n')
    return c


if __name__ == '__main__':
    t0 = time.time()
    out = open(os.path.join(HERE, 'results', 'partial_not_bound.jsonl'), 'w', encoding='utf-8')
    k3 = brute(3, 6, 'counted')
    tables3 = [(sum(1 << i for i, v in enumerate(l) if v == 1), sum(1 << i for i, v in enumerate(l) if v == 2))
               for l in product(range(3), repeat=8)]
    print('n=3 all partial tables', dict(run(3, tables3, k3, out, 'all3')), flush=True)
    k4 = brute(4, 5, 'counted')
    rng = random.Random(9)
    tables4 = []
    for _ in range(3000):
        l = [rng.randrange(3) for _ in range(16)]
        tables4.append((sum(1 << i for i, v in enumerate(l) if v == 1), sum(1 << i for i, v in enumerate(l) if v == 2)))
    print('n=4 sampled partial tables', dict(run(4, tables4, k4, out, 'rand4')), flush=True)
    # partial versions of the nonmonotone corpus cases (each row kept with probability 1/2)
    cs = json.load(open(os.path.join(HERE, 'results', 'synthesis_signed_cases.json'), encoding='utf-8'))
    c = Counter()
    for case in cs:
        n, truth = int(case['n']), int(case['truth'])
        if n > 6:
            continue
        for rep in range(20):
            keep = rng.getrandbits(1 << n)
            P, N = truth & keep, ((1 << (1 << n)) - 1) & ~truth & keep
            if not P or not N:
                continue
            b, inv = total_bound(n, P, N)
            c['cases'] += 1; c['not_gain'] += inv > 0
            out.write(json.dumps(dict(set='signed-partial', case=case['name'], n=n, P=P, N=N, binary=b, inversion=inv)) + '\n')
    print('partial nonmonotone corpus labels', dict(c), f'{time.time() - t0:.0f}s', flush=True)
