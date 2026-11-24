"""Diagnose size-14 splitting: all second-gate parts of ONE first-gate piece, each part timed and logged.
Compare the total with the unsplit solve of that piece (1,0,1): 599 s with maplechrono."""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))  # sat-search/
import sys, time
from multiprocessing import Pool
import l1343_split14 as sp
import mono_shard as m

if __name__ == '__main__':
    c1 = (1, 0, 1)
    distinct = '--plain' not in sys.argv
    j = m.N_IN + len(m.SEED)
    seconds = [(op, l, r) for r in range(j + 1) for l in range(r) for op in (0, 1)]
    log = open('l1343_diag.log', 'a', encoding='utf-8')
    def say(s):
        line = f'{time.strftime("%H:%M:%S")} {s}'; print(line, flush=True); log.write(line + '\n'); log.flush()
    say(f'piece {c1}: {len(seconds)} parts, 11 workers, {"ban" if distinct else "plain"}')
    t0 = time.time(); times = []
    with Pool(11, initializer=sp.init, initargs=(14, distinct)) as p:
        for k, (a, c2, res, dt) in enumerate(p.imap_unordered(sp.part, [(c1, c2) for c2 in seconds]), 1):
            times.append((dt, c2))
            say(f'[{k}/{len(seconds)}] part {c2}: {"SAT!" if res else "UNSAT"} in {dt:.1f}s (wall {time.time() - t0:.0f}s)')
    times.sort(reverse=True); tot = sum(t for t, _ in times)
    say(f'TOTAL core time {tot:.0f}s vs unsplit 599s; wall {time.time() - t0:.0f}s')
    say('slowest parts: ' + ', '.join(f'{c}:{t:.0f}s' for t, c in times[:10]))
    say(f'parts under 1s: {sum(t < 1 for t, _ in times)}; top 10 share of time: {sum(t for t, _ in times[:10]) / tot:.0%}')
