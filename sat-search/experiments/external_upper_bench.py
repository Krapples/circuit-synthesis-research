"""Proof-only ladders below an imported constructive upper bound (cofactor two-signal witnesses).

For each target: import and verify the witness (time to upper bound), then run percy_run --upper-witness from
budget 1 with the given proof mode. No witness pass and no known minimum is used: every budget below U is proved
UNSAT or found SAT by the solver. Records time to upper bound, proof time, total time, per-budget conflicts and the
open interval on timeout. Repeats measure the spread.

Usage: python external_upper_bench.py OUT.jsonl [--targets ...] [--modes ...] [--repeats 3] [--tier extended]
"""
import argparse
import json
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from time import perf_counter

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'baselines'))
sys.path.insert(0, str(HERE))
import first_layer_check as F  # noqa: E402
from witness_import import Library  # noqa: E402

TARGETS = ('0116', '1668', '1669', '1686', '166b', '1699', '016a')
MODES = ('slack-three-phase-set-lift1-count-const', 'slack-three-phase-set-lift1-count-const-cond',
         'slack-three-phase-set-lift1-count-const-liveall-ess-cond')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('out', type=Path)
    p.add_argument('--targets', nargs='+', default=TARGETS)
    p.add_argument('--modes', nargs='+', default=MODES)
    p.add_argument('--repeats', type=int, default=3)
    p.add_argument('--tier', default='extended', choices=tuple(F.TIERS))
    p.add_argument('--workers', type=int, default=10)
    a = p.parse_args()
    seconds, conflicts = F.TIERS[a.tier]
    t = perf_counter()
    lib = Library(HERE.parent / 'results/cofactor_witness/npn4_witnesses.json')
    library_seconds = perf_counter() - t
    jobs = [(target, mode, rep) for target in a.targets for mode in a.modes for rep in range(a.repeats)]

    def go(job):
        target, mode, rep = job
        t0 = perf_counter()
        w = lib.chain(int(target, 16))  # transform + independent simulation
        ub_seconds = perf_counter() - t0
        r = F.run(F.PERCY, mode, f'extub-{target}', 4, int(target, 16), 0xffff, 'cegar', seconds, conflicts,
                  start=1, upper_witness=w['spec'])
        budgets = [{'k': x['k'], 'status': x['status'], 'conflicts': x.get('conflicts'),
                    'seconds': round(x.get('seconds', 0), 3)} for x in r.get('records', []) if 'k' in x]
        r.update(repeat=rep, witness_size=w['size'], ub_seconds=ub_seconds, library_seconds=library_seconds,
                 proof_seconds=r['wall_seconds'], total_seconds=ub_seconds + r['wall_seconds'],
                 proof_conflicts=sum(b['conflicts'] or 0 for b in budgets), budgets=budgets)
        return r

    with ThreadPoolExecutor(a.workers) as pool, a.out.open('w') as out:
        for r in pool.map(go, jobs):
            out.write(json.dumps(r) + '\n')
            out.flush()
            hard = [f"k{b['k']}:{b['status'][0]}:{b['conflicts']}" for b in r['budgets'] if (b['conflicts'] or 0) > 1000]
            print(r['tt'], r['mode'].replace('slack-three-phase-set-lift1-count-', ''), r['repeat'], r['status'],
                  'U', r['witness_size'], 'result', r['upper_bound'], 'open', r['open_budget'],
                  f"{r['proof_seconds']:.1f}s", r['proof_conflicts'], ' '.join(hard), flush=True)


if __name__ == '__main__':
    main()
