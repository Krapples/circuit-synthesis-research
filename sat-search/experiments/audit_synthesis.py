"""Verify saved witnesses against targets and archive a reproducible benchmark baseline."""

import argparse
from collections import Counter, defaultdict
from importlib.metadata import version
import json
from pathlib import Path
import platform
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo

from synthesis_bench import interval
from synthesis_cases import Witness, essential, truth_table
from synthesis_followup import digest, endpoint_order, load_cases, read_rows


def audit(rows, cases):
    observed = defaultdict(list)
    bounds = {r['case']: r['bounds'] for r in rows if r['kind'] == 'analytical'}
    intervals = {(r['case'], r['basis']): r for r in rows if r['kind'] == 'interval'}
    selected = set(rows[0]['cases'])
    if set(bounds) != selected or set(intervals) != {(name, basis) for name in selected for basis in ('mono', 'not')}:
        raise ValueError('missing analytical records or intervals')
    jobs = {}
    for r in rows:
        if r['kind'] != 'job':
            continue
        case = cases[r['case']]
        key = case.name, r['basis'], r['configuration'], r['budget']
        if key in jobs:
            raise ValueError(f'duplicate job {key}')
        if (case.name, r['basis']) not in intervals or r['status'] not in ('SAT', 'UNSAT', 'TIMEOUT'):
            raise ValueError(f'unexpected job {key}')
        jobs[key] = r
        if r['status'] == 'SAT':
            wire = r['witness']
            witness = Witness(tuple(map(tuple, wire['gates'])), wire['output'])
            if (len(witness.gates) != r['gates'] or r['gates'] > r['budget']
                    or truth_table(case.n, witness) & case.known != case.truth
                    or r['basis'] == 'mono' and any(op == 2 for op, _, _ in witness.gates)):
                raise ValueError(f'invalid witness {key}')
        observed[case.name, r['basis']].append((r['budget'], r))

    for (name, basis), row in intervals.items():
        case = cases[name]
        support = max(0, essential(case.n, case.labels()) - 1)
        upper = len(case.witness.gates) if basis == 'mono' else intervals[name, 'mono']['final']['upper']
        if row['initial_upper'] != upper or truth_table(case.n, case.witness) & case.known != case.truth:
            raise ValueError(f'invalid baseline for {name}')
        if interval(observed[name, basis], support, upper) != row['final']:
            raise ValueError(f'inconsistent interval {name} {basis}')
        reference = [(b, r) for b, r in observed[name, basis] if r['phase'] == 'reference']
        if interval(reference, support, upper) != row['reference']:
            raise ValueError(f'inconsistent reference {name} {basis}')
        for config in row['applicable']:
            if not all((name, basis, config, budget) in jobs for budget in row['budgets']):
                raise ValueError(f'incomplete comparison {name} {basis} {config}')
        if basis == 'not' and row['final']['lower'] > intervals[name, 'mono']['final']['upper']:
            raise ValueError(f'inconsistent cross-basis intervals {name}')

    shared = [(name, budget) for (name, basis), row in intervals.items() if basis == 'mono'
              for budget in row['budgets']]
    hard = [(name, budget) for name, budget in shared if budget > bounds[name]['support']]

    def comparison(group):
        result = {}
        for config in ('SAT', 'A', 'B', 'C', 'D', 'E'):
            measurements = [jobs[name, 'mono', config, budget] for name, budget in group]
            result[config] = dict(Counter(r['status'] for r in measurements),
                                  seconds=sum(r['seconds'] for r in measurements))
        return result

    tried = {(name, budget) for name, basis, _, budget in jobs if basis == 'mono'}
    mono_gains = sum(row['final']['lower'] > max(bounds[name]['support'], max(
        (budget + 1 for budget, r in observed[name, basis] if r['configuration'] == 'SAT' and r['status'] == 'UNSAT'),
        default=0)) for (name, basis), row in intervals.items() if basis == 'mono')
    return dict(records=len(rows), instances=len(intervals) // 2, jobs=len(jobs),
                verdicts=dict(Counter(r['status'] for r in jobs.values())),
                exact_mono=sum(r['final']['minimum'] is not None for (_, b), r in intervals.items() if b == 'mono'),
                lower_gains_over_direct_sat=mono_gains,
                tight_improvements=sum(b.get('tight', b['support']) > b['support'] for b in bounds.values()),
                unresolved=len(endpoint_order(rows)), untested_endpoints=sum((r['case'], r['final']['lower']) not in tried
                                                                           for r in endpoint_order(rows)),
                shared_budgets=len(shared), harder_budgets=len(hard), all_jobs=comparison(shared), harder_jobs=comparison(hard))


SOURCES = (
    'cube_search.py', 'monotone_interface.py', 'partial_ordered.py',
    'experiments/antichain_search.py', 'experiments/regional_search.py', 'experiments/regional_synthesis.py',
    'experiments/subtree_formulas.py', 'experiments/synthesis_cases.py', 'experiments/synthesis_bench.py',
)


def freeze(path, baseline, targets):
    root = Path(__file__).resolve().parents[1]
    manifest = dict(python=platform.python_version(), platform=platform.platform(), pysat=version('python-sat'),
                    solver='maplechrono', results={v.name: digest(v) for v in (baseline, targets)},
                    sources={f'sat-search/{rel}': digest(root / rel) for rel in SOURCES})
    with ZipFile(path, 'x') as archive:
        for rel in SOURCES:
            archive.writestr(ZipInfo(f'sat-search/{rel}'), (root / rel).read_bytes(), ZIP_DEFLATED)
        archive.writestr(ZipInfo('BASELINE.json'), json.dumps(manifest, indent=2) + '\n', ZIP_DEFLATED)
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', required=True, type=Path)
    parser.add_argument('--manifest', required=True, type=Path)
    parser.add_argument('--freeze', type=Path)
    args = parser.parse_args()
    result = audit(read_rows(args.baseline), load_cases(args.manifest))
    if args.freeze:
        result['archive'] = freeze(args.freeze, args.baseline, args.manifest)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
