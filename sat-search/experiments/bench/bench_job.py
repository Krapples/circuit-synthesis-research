"""One benchmark job: build an instance, shuffle its clauses with a seed, solve it INCREMENTALLY
(the cube goes in as assumptions, as our search scripts do), print one result line.

Usage: python bench_job.py <instance> <solver> <seed>
Instances:
  fano13and / fano13or   L-meta-1023, 13 gates, first gate AND/OR(0,1)            (UNSAT)
  m1343a / m1343b        L-meta-1343 shard 2, exact 13 gates, one cube on gate 14 (UNSAT)
  tiny                   5-cycle monotone, 7 gates (SAT; smoke test)
"""
import os, random, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(os.path.dirname(HERE)))  # sat-search/
sys.path.insert(0, r"C:\Users\Carson\Documents\ChatGPT\P=NP\.scratch-sat")
from pysat.solvers import Solver


def instance(name):
    if name.startswith('fano13'):
        import fano_search as f
        cl, isand, sel, out = f.build(13)
        N = f.N
        assume = [sel[N][0][0], sel[N][1][1], isand[N] if name.endswith('and') else -isand[N]]
        return cl, assume
    if name in ('m1343a', 'm1343b', 'tiny'):
        import mono_shard as m
        if name == 'tiny':
            m.N_IN, m.EDGES, m.SEED = 5, [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)], []
            pool, cl, isand, sel, outv, first = m.build(7, True)
            return cl, []
        pool, cl, isand, sel, outv, first = m.build(13, True)
        op, l, r = (0, 3, 4) if name == 'm1343a' else (1, 1, 4)
        return cl, [sel[first][0][l], sel[first][1][r], isand[first] if op == 0 else -isand[first]]
    raise SystemExit(f'unknown instance {name}')


def main():
    name, solver, seed = sys.argv[1], sys.argv[2], int(sys.argv[3])
    cl, assume = instance(name)
    cl = list(cl)
    random.Random(seed).shuffle(cl)
    t = time.time()
    with Solver(name=solver, bootstrap_with=cl) as s:
        res = s.solve(assumptions=assume)
    print(f'RESULT {name} {solver} {seed} {"SAT" if res else "UNSAT"} {time.time() - t:.1f}', flush=True)


if __name__ == '__main__':
    main()
