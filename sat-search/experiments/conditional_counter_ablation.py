"""Fixed-budget ablation of the conditional restriction counters on the hard proof budgets.

Each job proves (or fails to prove) UNSAT at one budget below the verified minimum, so the known optimum
fixes the budget only; no run uses it to guide a search. Unknown verdicts are recorded as such.

Usage: python conditional_counter_ablation.py OUT.jsonl [--workers 10] [--seconds 300] [--conflicts 2000000]
"""
import argparse
import json
import os
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'baselines'))
import first_layer_check as F  # noqa: E402

TARGETS = (('0116', 8), ('1668', 8), ('1669', 9), ('1686', 8), ('166b', 9))
MODES = ('slack-three-phase-set-lift1-count-const',
         'slack-three-phase-set-lift1-count-const-cond',
         'slack-three-phase-set-lift1-count-const-liveall-ess',
         'slack-three-phase-set-lift1-count-const-liveall-ess-cond')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('out', type=Path)
    p.add_argument('--workers', type=int, default=10)
    p.add_argument('--seconds', type=float, default=300)
    p.add_argument('--conflicts', type=int, default=2_000_000)
    a = p.parse_args()
    jobs = [(m, t, k) for t, k in TARGETS for m in MODES]

    def go(job):
        mode, target, k = job
        return F.run(F.PERCY, mode, f'abl-{target}', 4, int(target, 16), 0xffff, 'cegar', a.seconds,
                     a.conflicts, budget=k)

    with ThreadPoolExecutor(a.workers) as pool, a.out.open('w') as out:
        for r in pool.map(go, jobs):
            out.write(json.dumps(r) + '\n')
            out.flush()
            rec = r['records'][-1] if r.get('records') else {}
            print(r['mode'], r['tt'], r['budget'], r['status'], f"{r['wall_seconds']:.1f}s",
                  'conflicts', rec.get('conflicts'), 'peak', r.get('peak_bytes'), flush=True)


if __name__ == '__main__':
    main()
