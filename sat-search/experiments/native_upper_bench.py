"""Proof-only Percy ladders below native cofactor upper bounds on frozen-corpus targets.

For each selected corpus case: synthesize a chain with native/cofactor_synth.exe (re-simulated in C++ and again
here), then run percy_run --upper-witness from k=1. Only budgets below the native size U are solved; a SAT budget
yields a smaller chain, a timeout leaves [k, U-1] open. Known minima are never consulted.
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
import native_cofactor_check as N  # noqa: E402
from synthesis_cases import corpus  # noqa: E402

MODE = 'slack-three-phase-set-lift1'  # restriction counters need 4 inputs; first-layer options need std on partials
PARTIAL = ('base', 'std')  # cegar on partial tables loops at k=1 (242,754 rows, 0 conflicts in 300 s)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('out', type=Path)
    p.add_argument('--n', type=int, nargs='+', default=[5])
    p.add_argument('--names', nargs='*', help='corpus case names (default: every case with the given n)')
    p.add_argument('--exe-args', default='--root-slack 2')
    p.add_argument('--mode', default=MODE)
    p.add_argument('--tier', default='extended', choices=tuple(F.TIERS))
    p.add_argument('--workers', type=int, default=10)
    a = p.parse_args()
    seconds, conflicts = F.TIERS[a.tier]
    N.EXE_ARGS[:] = a.exe_args.split()
    cases = [c for c in corpus() if c.n in a.n and (not a.names or c.name in a.names)]
    t0 = perf_counter()
    recs, table = N.native([(c.n, c.truth, c.known) for c in cases])
    native_seconds = perf_counter() - t0

    def go(job):
        c, w = job
        full = (1 << (1 << c.n)) - 1
        mode, method = (a.mode, 'cegar') if (c.known & full) == full else PARTIAL
        r = F.run(F.PERCY, mode, f'natub-{c.name}', c.n, c.truth, c.known, method, seconds, conflicts,
                  start=1, upper_witness=w['spec'])
        budgets = [{'k': x['k'], 'status': x['status'], 'conflicts': x.get('conflicts'),
                    'seconds': round(x.get('seconds', 0), 3)} for x in r.get('records', []) if 'k' in x]
        r.update(case=c.name, native_size=w['size'], native_seconds=w['seconds'], exe_args=a.exe_args,
                 batch_native_seconds=native_seconds, proof_seconds=r['wall_seconds'],
                 proof_conflicts=sum(b['conflicts'] or 0 for b in budgets), budgets=budgets)
        return r

    with ThreadPoolExecutor(a.workers) as pool, a.out.open('w') as out:
        for r in pool.map(go, zip(cases, recs)):
            out.write(json.dumps(r) + '\n')
            out.flush()
            hard = [f"k{b['k']}:{b['status'][0]}:{b['conflicts']}" for b in r['budgets'] if (b['conflicts'] or 0) > 1000]
            print(r['case'], r['status'], 'U', r['native_size'], 'result', r['upper_bound'], 'open', r['open_budget'],
                  f"{r['proof_seconds']:.1f}s", r['proof_conflicts'], ' '.join(hard), flush=True)


if __name__ == '__main__':
    main()
