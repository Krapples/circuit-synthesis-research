"""Capture Percy CEGAR candidate models on hard fixed budgets, with restriction certificates traced
(same trajectory as plain Percy) or learned (cut/all), for offline replay.

Each job runs percy_run --budget K with --capture-models and writes the budget record and the
models under the output directory. Wall and conflict limits are explicit; a TIMEOUT budget keeps
its reason and is never read as UNSAT.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PERCY = ROOT / 'external' / 'percy-build' / 'percy_run.exe'
TARGETS = ('016a', '1699', '0116', '6996', '0196', '16a9', '1668', '1686', '1669', '166b')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='new directory')
    parser.add_argument('--percy', type=Path, default=PERCY)
    parser.add_argument('--budgets', type=int, nargs='+', default=[8, 9])
    parser.add_argument('--targets', nargs='+', default=TARGETS)
    parser.add_argument('--modes', nargs='+', default=['trace'], choices=('trace', 'cut', 'all', 'rows'))
    parser.add_argument('--seconds', type=float, default=60)
    parser.add_argument('--conflicts', type=int, default=200000)
    parser.add_argument('--workers', type=int, default=11)
    args = parser.parse_args()
    args.output.mkdir(parents=True)
    jobs = [(mode, target, k) for mode in args.modes for target in args.targets for k in args.budgets]

    def execute(job):
        mode, target, k = job
        stem = args.output / f'{mode}_{target}_{k}'
        models = stem.with_suffix('.models.jsonl')
        command = [str(args.percy), '--n', '4', '--tt', target, '--method', 'cegar', '--solver', 'satoko',
                   '--budget', str(k), '--conflicts', str(args.conflicts), '--seconds', str(args.seconds),
                   '--restriction-cuts', mode, '--capture-models', str(models)]
        done = subprocess.run(command, capture_output=True, text=True)
        if done.returncode != 0:
            raise RuntimeError(f'{job}: exit {done.returncode}: {done.stderr[-500:]}')
        lines = [json.loads(line) for line in done.stdout.splitlines() if line.startswith('{')]
        record = next(r for r in lines if 'k' in r)
        row = dict(record, target=target, mode=mode, command=command[1:])
        print(f"{mode} {target} k={k} {record['status']} {record['reason']} rows={record['cegar_rows']} "
              f"models={record['restriction_models']} rejects={record['restriction_rejects']} "
              f"{record['seconds']:.1f}s", flush=True)
        return row

    with (args.output / 'records.jsonl').open('x', encoding='utf-8') as out, \
            ThreadPoolExecutor(args.workers) as pool:
        for row in pool.map(execute, jobs):
            out.write(json.dumps(row) + '\n')


if __name__ == '__main__':
    main()
