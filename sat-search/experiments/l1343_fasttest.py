"""Quick test: L-meta-1343 shard 2 (seed x6|x9, x7|x10, AND) at exactly 14 gates, monotone (no NOT),
same 11 pieces on the first free gate as l1343_quicktest.py, with cube_search --fast rules. Cap by pool kill.
Old result (mono_shard, maplechrono): 3/11 finished within 15 min, fastest 599 s."""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))  # sat-search/
import sys, time
from multiprocessing import Pool
import cube_search as cs
EDGES = [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9),
         (6, 7), (6, 10), (7, 9), (8, 9)]
if __name__ == '__main__':
    cap = float(sys.argv[1]) if len(sys.argv) > 1 else 300
    n, G = 11, 14
    masks = [(1 << u) | (1 << v) for u, v in EDGES]
    FAST = dict(sens=True, units=True, usens=True, bypass=True, elim=True, elimclosure=True, signeddom=True,
                recursivebounds=True, recdepth=2, notbypass=True, recclosure=True, identifybounds=True,
                fanoutelim=True, pairro=True, colorbounds=True, sharecolor=True, colorbudget=True, nonot=True)
    j = n + 3
    pieces = [(op, l, r) for r in range(j) for l in range(r) for op in (0, 1)][:11]
    print(f'{time.strftime("%H:%M:%S")} L-meta-1343 shard 2, exactly {G} gates, monotone, --fast; pieces {pieces}; cap {cap:.0f}s', flush=True)
    p = Pool(11); t0 = time.time()
    res = {c: p.apply_async(cs.run_cube, ((n, masks, G, 'maplechrono', (1, 6, 9), True, True,
                                           {**FAST, 'colex_from': 3, 'fixgates': [(1, 1, 7, 10), (2, 0, 11, 12), (3, *c)]}),)) for c in pieces}
    seen = set()
    while len(seen) < len(pieces) and time.time() - t0 < cap:
        for c, r in res.items():
            if c not in seen and r.ready():
                seen.add(c); cube, st, circ, dt, stats = r.get()
                print(f'{time.strftime("%H:%M:%S")}   piece {c}: {st} in {dt:.0f}s  {stats[:60]}', flush=True)
                if st == 'WITNESS':
                    print('   !!! WITNESS', circ, flush=True)
        time.sleep(0.3)
    p.terminate(); p.join()
    print(f'RESULT: {sum(1 for c in seen)}/{len(pieces)} pieces finished within {cap:.0f}s (wall {time.time() - t0:.0f}s); old method: 0/11 within 5 min, 3/11 within 15 min', flush=True)
