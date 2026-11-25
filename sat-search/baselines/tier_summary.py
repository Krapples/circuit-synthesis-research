"""Summarize tier_bench records: verdicts, minima, termination reasons, and a caps cross-check."""

import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
CAPS = HERE.parent / 'results' / 'baselines' / 'caps_hard_npn4.jsonl'


def known_optima():
    optima = {}
    for line in CAPS.open(encoding='utf-8'):
        row = json.loads(line)
        if row.get('status') == 'OPTIMAL':
            assert optima.setdefault(row['name'], row['size']) == row['size'], row['name']
    return optima


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('inputs', nargs='+', type=Path)
    args = parser.parse_args()
    optima = known_optima()
    rows = [json.loads(line) for path in args.inputs for line in path.open(encoding='utf-8') if line.strip()]
    stats = defaultdict(lambda: defaultdict(float))
    reasons = defaultdict(Counter)
    best = defaultdict(dict)  # (label, mode) -> target -> highest excluded budget
    order = []
    for row in rows:
        label = (row['wall_limit'], row['conflicts_limit'], row.get('conflict_scope', 'call'))
        key = (*label, row['mode'])
        if key not in order:
            order.append(key)
        s = stats[key]
        s['jobs'] += 1
        s['wall'] += row['wall_seconds']
        s['peak'] = max(s['peak'], row['peak_bytes'] / 2 ** 20)
        opt = optima.get(row['name'])
        top = None
        for record in row['records']:
            if 'k' not in record:
                continue
            s['conflicts'] += record.get('conflicts', 0)
            if record['status'] == 'UNSAT':
                top = record['k']
                assert opt is None or record['k'] < opt, ('UNSAT at or above the optimum', row['name'], record)
            elif record['status'] == 'SAT':
                assert opt is None or record['k'] == opt, ('SAT below the optimum', row['name'], record)
            for cause, name in ((record.get('two_unknown_cause'), 'two'), (record.get('three_unknown_cause'), 'three')):
                for index, count in enumerate(cause or ()):
                    s[f'{name}_unknown_{("deadline", "work", "capacity")[index]}'] += count
        best[key][row['name']] = top
        if row['status'] == 'SAT':
            s['minima'] += 1
        reasons[key][row['reason']] += 1
        if row['status'] != 'SAT' and top is not None and top >= 7:
            s['excl_ge7'] += 1
        pending = next((r for r in row['records'] if r.get('status') == 'TIMEOUT'), None)
        if pending:
            s['open_conflicts'] += pending.get('conflicts', 0)
            s['open_seconds'] += pending.get('seconds', 0)
    print('| Wall s | Conflicts | Scope | Mode | Minima | Size-8 excl | Excl budgets k>=7 | Wall s total |'
          ' Conflicts | Reasons | Peak MiB |')
    print('| ---: | ---: | --- | --- | ---: | ---: | ---: | ---: | ---: | --- | ---: |')
    for key in order:
        s = stats[key]
        excl8 = sum(1 for top in best[key].values() if top is not None and top >= 8)
        excluded = sum(max(0, (top or 0) - 6) for top in best[key].values())
        reason = ', '.join(f'{name} {count}' for name, count in sorted(reasons[key].items()))
        print(f"| {key[0]:g} | {key[1]:,} | {key[2]} | {key[3]} | {s['minima']:.0f} | {excl8} | {excluded} | "
              f"{s['wall']:.1f} | {s['conflicts']:,.0f} | {reason} | {s['peak']:.1f} |")
    print()
    print('Highest excluded budget per target (S = minimum found):')
    targets = sorted({row['name'] for row in rows})
    print('| Limits | Mode | ' + ' | '.join(t.removeprefix('npn4-') for t in targets) + ' |')
    print('| --- | --- | ' + ' | '.join('---:' for _ in targets) + ' |')
    found = defaultdict(dict)
    for row in rows:
        if row['status'] == 'SAT':
            label = (row['wall_limit'], row['conflicts_limit'], row.get('conflict_scope', 'call'), row['mode'])
            found[label][row['name']] = next(r['steps'] for r in row['records'] if 'final' in r)
    for key in order:
        cells = [f"S{found[key][t]}" if t in found[key] else str(best[key].get(t, '')) for t in targets]
        print(f"| {key[0]:g}/{key[1]:,}/{key[2]} | {key[3]} | " + ' | '.join(cells) + ' |')
    print()
    print('Inner residual unknowns (deadline / work / capacity):')
    for key in order:
        s = stats[key]
        two = [s[f'two_unknown_{c}'] for c in ('deadline', 'work', 'capacity')]
        three = [s[f'three_unknown_{c}'] for c in ('deadline', 'work', 'capacity')]
        if any(two) or any(three):
            print(f"  {key}: slack-two {two[0]:.0f}/{two[1]:.0f}/{two[2]:.0f}, "
                  f"slack-three {three[0]:.0f}/{three[1]:.0f}/{three[2]:.0f}")
    print(f'Caps cross-check passed against {len(optima)} known optima.')


if __name__ == '__main__':
    main()
