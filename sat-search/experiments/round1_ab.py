"""A/B test of the fan-out rules on real L-meta-519 pieces (11 gates, C7 + leaves on 0 and 1).
Runs the same pieces with and without --fanout, 11 workers, each variant capped by creating STOP.
Usage: python fanout_ab.py [cap_seconds]"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))  # sat-search/
import os, sys, threading, time
from multiprocessing import Pool
import cube_search as cs

N = 9
EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (0, 6), (0, 7), (1, 8)]
MASKS = [(1 << u) | (1 << v) for u, v in EDGES]
PIECES = [(0, 0, 1), (1, 0, 1), (2, 0, 0), (0, 0, 2), (1, 0, 2), (1, 1, 2), (2, 2, 2), (0, 0, 3), (0, 1, 3),
          (1, 0, 3), (1, 1, 3)]   # the hardest remaining pieces
CONFIGS = [('fan-out only', (True, False, {})),
           ('all round-1 rules + minimality', (True, True, dict(sens=True, units=True, minimal=True)))]

if __name__ == '__main__':
    cap = float(sys.argv[1]) if len(sys.argv) > 1 else 600
    for name, (fan, ro, fl) in CONFIGS:
        if os.path.exists(cs.STOP):
            os.remove(cs.STOP)
        timer = threading.Timer(cap, lambda: open(cs.STOP, 'w').close()); timer.start()
        t0 = time.time()
        print(f'{time.strftime("%H:%M:%S")} {name}: {len(PIECES)} pieces, cap {cap:.0f}s', flush=True)
        with Pool(11) as p:
            for cube, st, circ, dt, stats in p.imap_unordered(cs.run_cube, [(N, MASKS, 11, 'maplechrono', c, fan, ro, fl) for c in PIECES]):
                print(f'{time.strftime("%H:%M:%S")}   {cube}: {st} in {dt:.0f}s  {stats}', flush=True)
        timer.cancel()
        if os.path.exists(cs.STOP):
            os.remove(cs.STOP)
        print(f'  wall {time.time() - t0:.0f}s', flush=True)
