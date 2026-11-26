"""Exact-minimum check of the conditional restriction counters on every four-input NPN class.

For each class with a verified minimum s (results/baselines/screen_npn4_clean.jsonl, status OPTIMAL), runs the
given mode at budget s (expected SAT, with the witness checked by the harness) and at s - 1 (expected UNSAT).
A SAT failure at s would mean the conditional clauses excluded every minimum chain; an UNSAT at s - 1 is the
reference verdict. Unknown verdicts are reported as such, never counted as UNSAT.

Usage: python conditional_counter_check.py OUT.jsonl --modes MODE... [--workers 11] [--seconds 60] [--max-size 8]
"""
import argparse
import json
import os
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'baselines'))
import first_layer_check as F  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]


def classes(max_size):
    seen = {}
    for line in (ROOT / 'results/baselines/screen_npn4_clean.jsonl').read_text().splitlines():
        r = json.loads(line)
        if r.get('n') == 4 and r.get('status') == 'OPTIMAL' and r.get('verified') and r['size'] <= max_size:
            seen.setdefault(r['name'], r['size'])
    return sorted(seen.items())


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('out', type=Path)
    p.add_argument('--modes', nargs='+', required=True)
    p.add_argument('--workers', type=int, default=11)
    p.add_argument('--seconds', type=float, default=60)
    p.add_argument('--max-size', type=int, default=8)
    a = p.parse_args()
    jobs = []
    for name, size in classes(a.max_size):
        tt = int(name.split('-')[1], 16)
        for mode in a.modes:
            jobs.append((mode, name, tt, size, 'SAT'))
            if size > 1:
                jobs.append((mode, name, tt, size - 1, 'UNSAT'))

    def go(job):
        mode, name, tt, k, expected = job
        r = F.run(F.PERCY, mode, name, 4, tt, 0xffff, 'cegar', a.seconds, 0, budget=k)
        r['expected'] = expected
        return r

    bad = unknown = 0
    with ThreadPoolExecutor(a.workers) as pool, a.out.open('w') as out:
        for r in pool.map(go, jobs):
            out.write(json.dumps(r) + '\n')
            if r['status'] not in ('SAT', 'UNSAT'):
                unknown += 1
            elif r['status'] != r['expected']:
                bad += 1
                print('MISMATCH', r['mode'], r['name'], r['budget'], r['status'], r['expected'], flush=True)
    print(json.dumps({'jobs': len(jobs), 'classes': len(classes(a.max_size)), 'mismatches': bad, 'unknown': unknown}))


if __name__ == '__main__':
    main()
