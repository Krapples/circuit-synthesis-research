"""Run the same fixed-budget job several times in parallel; report conflicts per run."""
import sys
from concurrent.futures import ThreadPoolExecutor
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'baselines'))
import first_layer_check as F
tt, k, reps, secs = int(sys.argv[1], 16), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
mode = sys.argv[5] if len(sys.argv) > 5 else 'slack-three-phase-set-lift1-count-const'
def go(i):
    r = F.run(F.PERCY, mode, f'{tt:x}', 4, tt, 0xffff, 'cegar', secs, 2_000_000, budget=k)
    rec = [x for x in r['records'] if 'k' in x][-1]
    return i, r['status'], rec.get('conflicts'), round(rec.get('seconds', 0), 1)
with ThreadPoolExecutor(reps) as p:
    for row in p.map(go, range(reps)):
        print(*row, flush=True)
