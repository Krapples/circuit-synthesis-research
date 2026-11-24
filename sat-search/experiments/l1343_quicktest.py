"""Quick test: L-meta-1343 shard 2 with MapleChrono on the first 11 pieces of size 13 (CaDiCaL
times are in l1343_shard2.log) and of size 14 (where the CaDiCaL run stalled: no piece in 30 min).
One piece per worker, each capped at CAP seconds via the solver's interrupt."""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))  # sat-search/
import sys, threading, time
from multiprocessing import Pool
import mono_shard as m

CAP = 900


def job(args):
    G, cube, distinct = args
    pool, cl, isand, sel, outv, first = m.build(G, True, distinct)
    from pysat.solvers import Solver
    op, l, r = cube
    with Solver(name='maplechrono', bootstrap_with=cl) as s:
        timer = threading.Timer(CAP, s.interrupt); timer.start()
        t = time.time()
        res = s.solve_limited(assumptions=[sel[first][0][l], sel[first][1][r],
                                           isand[first] if op == 0 else -isand[first]], expect_interrupt=True)
        timer.cancel()
        return G, cube, {None: 'CAPPED', False: 'UNSAT', True: 'SAT'}[res], time.time() - t


if __name__ == '__main__':
    j = m.N_IN + len(m.SEED)
    import re
    npieces = int(next((a.split('=')[1] for a in sys.argv if a.startswith('--pieces=')), 11))
    workers = int(next((a.split('=')[1] for a in sys.argv if a.startswith('--workers=')), 11))
    cubes = [(op, l, r) for r in range(j) for l in range(r) for op in (0, 1)][:npieces]
    distinct = '--distinct' in sys.argv
    sizes = [int(a) for a in sys.argv[1:] if a.isdigit()] or [13, 14]
    for G in sizes:
        print(f'{time.strftime("%H:%M:%S")} size {G}: first {len(cubes)} pieces, maplechrono, cap {CAP}s'
              f'{", duplicate-gate ban" if distinct else ""}', flush=True)
        t0 = time.time()
        with Pool(workers) as p:
            for G_, cube, st, dt in p.imap_unordered(job, [(G, c, distinct) for c in cubes]):
                print(f'{time.strftime("%H:%M:%S")} size {G_} cube {cube}: {st} in {dt:.0f}s', flush=True)
        print(f'WALL size {G}: {len(cubes)} pieces with {workers} workers in {time.time() - t0:.0f}s', flush=True)
