"""End-to-end check of percy_run --upper-witness with imported cofactor witnesses.

For every four-input NPN class with a verified minimum (results/baselines/screen_npn4_clean.jsonl), plus random
NPN-transformed members of those classes, run the ladder with the imported witness as the external upper bound.
Expected: SAT at exactly the class minimum. When the witness is minimal, every budget below it must be UNSAT and the
external chain is reported; otherwise the solver must find the smaller chain. The harness re-verifies every
reported chain. Unknown verdicts are listed separately, never counted as agreement.

Usage: python external_upper_check.py OUT.jsonl [--mode M] [--random 100] [--workers 11] [--seconds 60]
"""
import argparse
import json
import os
import random
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'baselines'))
sys.path.insert(0, str(HERE))
import first_layer_check as F  # noqa: E402
from witness_import import Library  # noqa: E402

ROOT = HERE.parent


def minima():
    opt = {}
    for line in (ROOT / 'results/baselines/screen_npn4_clean.jsonl').read_text().splitlines():
        r = json.loads(line)
        if r.get('n') == 4 and r.get('status') == 'OPTIMAL' and r.get('verified'):
            opt.setdefault(int(r['name'].split('-')[1], 16), r['size'])
    return opt


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('out', type=Path)
    p.add_argument('--mode', default='slack-three-phase-set-lift1-count-const-liveall-ess-cond')
    p.add_argument('--random', type=int, default=100)
    p.add_argument('--seed', type=int, default=20261125)
    p.add_argument('--workers', type=int, default=11)
    p.add_argument('--seconds', type=float, default=60)
    a = p.parse_args()
    lib = Library(ROOT / 'results/cofactor_witness/npn4_witnesses.json')
    opt = minima()
    jobs = [(f, opt[f], 'rep') for f in sorted(opt) if f in lib.reps]
    rng = random.Random(a.seed)
    members = [f for f in range(1 << 16) if lib.index[f][0] in opt and f not in lib.reps]
    jobs += [(f, opt[lib.index[f][0]], 'transformed') for f in rng.sample(members, a.random)]

    def go(job):
        f, m, kind = job
        w = lib.chain(f)
        r = F.run(F.PERCY, a.mode, f'ext-{f:04x}', 4, f, 0xffff, 'cegar', a.seconds, 0, start=1,
                  upper_witness=w['spec'])
        r.update(kind=kind, minimum=m, witness_size=w['size'], rep=w['rep'])
        return r

    bad = unknown = external = found_smaller = 0
    with ThreadPoolExecutor(a.workers) as pool, a.out.open('w') as out:
        for r in pool.map(go, jobs):
            out.write(json.dumps(r) + '\n')
            if r['status'] != 'SAT':
                unknown += 1
                print('UNKNOWN', r['tt'], r['status'], r.get('open_budget'), flush=True)
            elif r['upper_bound'] != r['minimum']:
                bad += 1
                print('MISMATCH', r['tt'], r['upper_bound'], r['minimum'], flush=True)
            elif r['upper_bound'] == r['witness_size']:
                external += 1
            else:
                found_smaller += 1
    print(json.dumps({'jobs': len(jobs), 'mismatches': bad, 'unknown': unknown,
                      'proved_witness_minimal': external, 'solver_found_smaller': found_smaller}))


if __name__ == '__main__':
    main()
