"""Summarize a time-capped synthesis benchmark from its JSONL certificates."""

import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
from statistics import median


def summarize(path):
    rows = [json.loads(line) for line in path.read_text(encoding='utf-8').splitlines()]
    meta = rows[0]
    intervals = {(r['case'], r['basis']): r for r in rows if r['kind'] == 'interval'}
    jobs = {(r['case'], r['basis'], r['configuration'], r['budget']): r for r in rows if r['kind'] == 'job'}
    analytical = {r['case']: r for r in rows if r['kind'] == 'analytical'}
    complete = [name for name in meta['cases'] if all((name, basis) in intervals for basis in ('mono', 'not'))]
    print(f"{len(complete)}/{len(meta['cases'])} cases, {meta['seconds']} s cap, {meta['workers']} concurrent cases")
    print()
    print('| Family | Cases | Reference exact mono / NOT | Final exact mono / NOT | Tight raises support |')
    print('| --- | ---: | ---: | ---: | ---: |')
    families = defaultdict(list)
    for name in complete:
        families[analytical[name]['family']].append(name)
    for group, names in families.items():
        counts = {(stage, basis): sum(intervals[name, basis][stage]['minimum'] is not None for name in names)
                  for stage in ('reference', 'final') for basis in ('mono', 'not')}
        tight = sum((b := analytical[name]['bounds']).get('tight', b['support']) > b['support'] for name in names)
        print(f"| {group} | {len(names)} | {counts['reference', 'mono']} / {counts['reference', 'not']} | "
              f"{counts['final', 'mono']} / {counts['final', 'not']} | {tight} |")
    print()
    print('| Basis and config | SAT | UNSAT | Timeout | Median peak MiB | Formula queries reaching enumeration |')
    print('| --- | ---: | ---: | ---: | ---: | ---: |')
    configs = defaultdict(list)
    for (name, basis), result in intervals.items():
        if name in complete:
            for config in result['applicable']:
                configs[basis, config].extend(jobs[name, basis, config, b] for b in result['budgets'])
    for (basis, config), measurements in configs.items():
        counts = Counter(m['status'] for m in measurements)
        peaks = [m['peak_bytes'] / 2**20 for m in measurements if m.get('peak_bytes') is not None]
        formulas = sum(m.get('stats', {}).get('distinct_formula_enumerations', 0) for m in measurements)
        memory = f'{median(peaks):.1f}' if peaks else '—'
        print(f"| {basis} {config} | {counts['SAT']} | {counts['UNSAT']} | {counts['TIMEOUT']} | {memory} | {formulas} |")
    print()
    for before, after in zip('SABCDE', 'ABCDEF'):
        before = 'SAT' if before == 'S' else before
        pairs = []
        for m in configs.get(('mono', after), ()):
            earlier = jobs.get((m['case'], 'mono', before, m['budget']))
            if earlier is not None and earlier['status'] == m['status'] and m['status'] in ('SAT', 'UNSAT'):
                pairs.append(earlier['seconds'] / m['seconds'])
        if pairs:
            print(f'{before} → {after}, {len(pairs)} solved pairs, median wall ratio {median(pairs):.2f}x')
    print()
    for basis in ('mono', 'not'):
        gains = []
        for name in complete:
            row = intervals[name, basis]
            support = analytical[name]['bounds']['support']
            sat_only = max([support, *(b + 1 for (c, mode, config, b), job in jobs.items()
                                       if c == name and mode == basis and config == 'SAT' and job['status'] == 'UNSAT')])
            if row['final']['lower'] > sat_only:
                gains.append((name, sat_only, row['final']['lower']))
        print(f'{basis} lower certificates beyond all direct SAT jobs ({len(gains)}) {gains}')
    separation = [name for name in complete if intervals[name, 'not']['final']['upper'] < intervals[name, 'mono']['final']['lower']]
    print(f'Certified NOT advantage ({len(separation)}) {separation}')
    negations = [m for m in jobs.values() if m['basis'] == 'not' and m.get('not_gates')]
    print(f'Verified NOT witnesses using NOT ({len(negations)}) on {len({m["case"] for m in negations})} cases')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('results', type=Path)
    summarize(parser.parse_args().results)
