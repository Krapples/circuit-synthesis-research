"""CPU reference: the encoding of .scratch-sat/search_524.py, for any graph and size.

Usage: python sat_reference.py --n 5 --edges 0-1,1-2,2-3,3-4,0-4 --size 7 [--solver cadical195]
Prints WITNESS (circuit) or UNSAT, with the time taken.
"""
import argparse, sys, time
sys.path.insert(0, r"C:\Users\Carson\Documents\ChatGPT\P=NP\.scratch-sat")
from pysat.formula import IDPool
from pysat.solvers import Solver
from pysat.card import CardEnc


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, required=True)
    ap.add_argument('--edges', required=True)
    ap.add_argument('--size', type=int, required=True)
    ap.add_argument('--solver', default='cadical195')
    a = ap.parse_args()
    n, G = a.n, a.size
    edges = [tuple(map(int, e.split('-'))) for e in a.edges.split(',')]
    masks = [(1 << u) | (1 << v) for u, v in edges]
    target = lambda x: any(x & m == m for m in masks)
    N = 1 << n
    output = n - 1 + G
    pool = IDPool(); clauses = []
    ops = {j: [pool.id((j, op)) for op in ('and', 'or', 'not')] for j in range(n, output + 1)}
    select = {(j, k): [pool.id((j, k, i)) for i in range(j)] for j in ops for k in range(2)}
    one = lambda xs: clauses.extend(CardEnc.equals(xs, 1, vpool=pool).clauses)
    for j, (an, o, no) in ops.items():
        left, right = select[j, 0], select[j, 1]
        one([an, o, no]); one(left); one(right)
        for i in range(j):
            clauses.extend([-left[i], -right[l]] for l in range(i))
            clauses.extend([[-left[i], -right[i], no], [-no, -left[i], right[i]]])
            if i >= n:
                clauses.append([-no, -left[i], -ops[i][2]])
        if j == output:
            continue
        nl, nr = select[j + 1, 0], select[j + 1, 1]
        for i in range(j):
            for l in range(i):
                clauses.append([-right[i], -nr[l]])
            for l in range(i):
                for k in range(l):
                    clauses.append([-right[i], -nr[i], -left[l], -nl[k]])
    for i in range(output):
        clauses.append([select[j, k][i] for j in range(max(n, i + 1), output + 1) for k in range(2)])

    def evaluate(circ, x):
        v = [bool(x >> i & 1) for i in range(n)]
        for op, l, r in circ:
            v.append(v[l] and v[r] if op == 0 else v[l] or v[r] if op == 1 else not v[l])
        return v[-1]

    def row(x):
        val = [pool.id(('val', x, j)) for j in range(output + 1)]
        yield from ([val[i] if x >> i & 1 else -val[i]] for i in range(n))
        for j, (an, o, no) in ops.items():
            l, r = [pool.id(('arg', x, j, k)) for k in range(2)]
            for k, arg in enumerate((l, r)):
                for i, sel in enumerate(select[j, k]):
                    yield [-sel, -arg, val[i]]
                    yield [-sel, arg, -val[i]]
            f = val[j]
            yield from ([-an, -l, -r, f], [-an, l, -f], [-an, r, -f], [-o, l, r, -f], [-o, -l, f],
                        [-o, -r, f], [-no, -l, -f], [-no, l, f])
        yield [val[-1] if target(x) else -val[-1]]

    t0 = time.time()
    with Solver(name=a.solver, bootstrap_with=clauses) as s:
        rows = {0, N - 1, *masks, *(1 << i for i in range(n))}
        rows |= {x for x in range(N) if not target(x)
                 and all(target(x | 1 << i) for i in range(n) if not x >> i & 1)}
        for x in rows:
            s.append_formula(list(row(x)))
        while s.solve():
            m = set(s.get_model())
            circ = [(next(k for k, v in enumerate(ops[j]) if v in m),
                     *(next(i for i, v in enumerate(select[j, k]) if v in m) for k in range(2))) for j in ops]
            bad = [x for x in range(N) if evaluate(circ, x) != target(x)]
            if not bad:
                print(f'WITNESS {circ} ({time.time() - t0:.1f}s)')
                return
            for x in bad:
                s.append_formula(list(row(x)))
            rows.update(bad)
    print(f'UNSAT: no circuit with exactly {G} gates ({time.time() - t0:.1f}s)')


if __name__ == '__main__':
    main()
