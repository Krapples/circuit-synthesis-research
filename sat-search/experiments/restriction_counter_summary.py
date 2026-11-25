"""Per-mode totals for restriction-counter runs (first_layer_check / tier_bench jsonl records).

For each mode: jobs, verified minima, highest excluded budget per target, wall time, and per-budget
search work summed over budget records (conflicts, decisions, propagations, CEGAR rows, SAT calls)
with the counter CNF overhead (variables, clauses, encoding seconds).
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path

KEYS = ('conflicts', 'decisions', 'propagations', 'cegar_rows', 'sat_calls', 'counter_vars', 'counter_clauses',
        'counter_seconds', 'encoding_seconds', 'extra_clauses')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('inputs', nargs='+', type=Path)
    parser.add_argument('--budget', type=int, help='only budget records with this k (bounded comparisons)')
    args = parser.parse_args()
    stats = defaultdict(lambda: defaultdict(float))
    excluded = defaultdict(dict)
    order = []
    for path in args.inputs:
        for line in path.open(encoding='utf-8'):
            if not line.strip():
                continue
            row = json.loads(line)
            key = (row['wall_limit'], row['conflicts_limit'], row['mode'])
            if key not in order:
                order.append(key)
            s = stats[key]
            s['jobs'] += 1
            s['wall'] += row['wall_seconds']
            s['minima'] += row['status'] == 'SAT'
            top = None
            for record in row['records']:
                if 'k' not in record or (args.budget is not None and record['k'] != args.budget):
                    continue
                if record['status'] == 'UNSAT':
                    top = record['k'] if top is None else max(top, record['k'])
                s['budgets'] += 1
                for name in KEYS:
                    s[name] += record.get(name, 0)
            excluded[key][row['name']] = top
    for key in order:
        s = stats[key]
        tops = excluded[key]
        print(json.dumps({'wall_limit': key[0], 'conflicts_limit': key[1], 'mode': key[2],
                          **{name: round(value, 3) for name, value in s.items()},
                          'excluded': dict(sorted(tops.items()))}))


if __name__ == '__main__':
    main()
