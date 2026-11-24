"""Probe the lowest unresolved monotone budgets in an existing synthesis sweep."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path

from synthesis_bench import interval, isolated
from synthesis_cases import Case, Witness


def load_cases(path):
    values = json.loads(path.read_text(encoding='utf-8'))
    return {r['name']: Case(r['name'], r['family'], r['n'], r['known'], r['truth'],
                           Witness(tuple(map(tuple, r['witness']['gates'])), r['witness']['output']))
            for r in values}


def read_rows(path):
    return [json.loads(line) for line in path.read_text(encoding='utf-8').splitlines()]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def endpoint_order(rows):
    tried = {(r['case'], r['budget']) for r in rows if r['kind'] == 'job' and r['basis'] == 'mono'}
    open_intervals = [r for r in rows if r['kind'] == 'interval' and r['basis'] == 'mono'
                      and r['final']['minimum'] is None]
    return sorted(open_intervals, key=lambda r: ((r['case'], r['final']['lower']) in tried, r['case']))


def probe(case, frame, seconds, rounds):
    previous = frame['final']
    current = previous
    records = []
    for _ in range(rounds):
        if current['minimum'] is not None:
            break
        budget = current['lower']
        evidence = []
        for config in ('SAT', 'B', 'D', 'E'):
            result = isolated(case, config, 'mono', budget, {}, seconds)
            records.append(dict(kind='job', case=case.name, family=case.family, n=case.n, basis='mono',
                                configuration=config, budget=budget, **result))
            evidence.append((budget, result))
        narrowed = interval(evidence, current['lower'], current['upper'])
        if narrowed == current:
            break
        current = narrowed
    records.append(dict(kind='interval', case=case.name, family=case.family, n=case.n, basis='mono',
                        previous=previous, final=current))
    return records


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline', type=Path, required=True)
    ap.add_argument('--manifest', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--seconds', type=float, default=1.0)
    ap.add_argument('--rounds', type=int, default=2)
    ap.add_argument('--workers', type=int, default=1)
    args = ap.parse_args()
    if not args.seconds > 0 or args.rounds < 1 or args.workers < 1:
        ap.error('seconds, rounds, and workers must be positive')
    cases = load_cases(args.manifest)
    selected = endpoint_order(read_rows(args.baseline))
    with args.output.open('x', encoding='utf-8') as output, ThreadPoolExecutor(max_workers=args.workers) as workers:
        def write(row):
            output.write(json.dumps(row, sort_keys=True) + '\n')
            output.flush()

        write(dict(kind='meta', baseline_sha256=digest(args.baseline), targets_sha256=digest(args.manifest),
                   seconds=args.seconds, rounds=args.rounds, workers=args.workers, cases=[r['case'] for r in selected]))
        batches = workers.map(lambda r: probe(cases[r['case']], r, args.seconds, args.rounds), selected)
        for i, records in enumerate(batches, 1):
            for row in records:
                write(row)
            print(f"[{i}/{len(selected)}] {records[-1]['case']} {records[-1]['final']}", flush=True)


if __name__ == '__main__':
    main()
