"""Coverage checks and matched higher-excess jobs for provider-first layouts."""

import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
from random import Random
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'theory'))
sys.path.insert(0, str(ROOT / 'verify'))

from complete_frontier_check import programs
from layout_projection import Projection, port_patterns, search_exact
from module_contraction import essential, simplify, vars as truth_variables
from ordered_quotient_core import materialize3, reconstruct, solve3
from port_certificates_check import bounded
from reference import check_witness
from signed_bound_compare import cases, restrict_essential
from two_sharing_core import solve as solve2


class LayoutProjectionChecks(unittest.TestCase):
    def test_provider_connectivity_enumeration(self):
        for repeated, internal, excess in ((3, 0, 4), (2, 1, 4), (1, 2, 4), (1, 3, 4), (2, 2, 5)):
            count = repeated + internal
            expected = set()
            for degrees in product(range(2, excess + 2), repeat=count):
                if sum(degree - 1 for degree in degrees) != excess:
                    continue
                destinations = [list(product(range(max(0, p-repeated+1), internal+1), repeat=degree))
                                for p, degree in enumerate(degrees)]
                for choices in product(*destinations):
                    ports = tuple(tuple(p for p, recipients in enumerate(choices) for j in recipients if j == r)
                                  for r in range(internal+1))
                    if all(ports):
                        expected.add(ports)
            actual = tuple(port_patterns(repeated, internal, excess))
            self.assertEqual(len(actual), len(set(actual)))
            self.assertEqual(set(actual), expected)

    def test_projection_on_concrete_recipient_layouts(self):
        rng = Random(78319)
        checked = 0
        for trial in range(850):
            n, repeated_count, internal = 6, (1 if trial % 2 else 2), 2
            repeated = tuple(sorted(rng.sample(range(n), repeated_count)))
            ports = rng.choice(tuple(port_patterns(repeated_count, internal, 4)))
            groups = [[] for _ in ports]
            for i in range(n):
                if i not in repeated:
                    groups[rng.randrange(len(groups))].append(i)
            if any(len(p) + len(g) < 2 for p, g in zip(ports, groups)):
                continue
            signed = bool(trial % 3)
            variables = truth_variables(n)
            one = (1 << (1 << n)) - 1
            available = [variables[i] for i in repeated]
            supports = [1 << i for i in repeated]
            for group, row in zip(groups, ports):
                values = [variables[i] for i in group] + [available[i] for i in row]
                if signed:
                    values = [v ^ (one if rng.randrange(2) else 0) for v in values]
                while len(values) > 1:
                    a = values.pop(rng.randrange(len(values)))
                    b = values.pop(rng.randrange(len(values)))
                    values.append(a | b if rng.randrange(2) else a & b)
                available.append(values[0])
                support = sum(1 << i for i in group)
                for i in row:
                    support |= supports[i]
                supports.append(support)
            target = available[-1]
            if not essential(n, target):
                continue
            cut = Projection(n, target, repeated, signed)
            processed = repeated
            for j, (group, row) in enumerate(zip(groups, ports)):
                live = {p for later in ports[j:] for p in later if p < repeated_count+j}

                def signals(pool):
                    return tuple(repeated[i] for i in sorted(pool) if i < repeated_count), sum(i >= repeated_count for i in pool)

                self.assertTrue(cut.cut(processed, *signals(live)))
                self.assertTrue(cut.support_cut(processed, tuple(supports[i] for i in sorted(live))))
                self.assertTrue(cut.step(processed, tuple(group), *signals(set(row)), j == internal))
                processed = tuple(sorted((*processed, *group)))
            checked += 1
        self.assertGreater(checked, 50)
        print(f'{checked} concrete layouts satisfy all projection tests')

    def test_small_monotone_minima_against_independent_programs(self):
        oracle = programs(4, 5, False)
        count = 0
        for target, budget in oracle.items():
            if not essential(4, target) or simplify(4, target, False)[0] != 4:
                continue
            excess = budget - 3
            result = search_exact(4, target, excess, support_filter=True)
            self.assertIsNotNone(result, (hex(target), excess))
            gates, _ = reconstruct(4, target, *result, excess)
            self.assertEqual(len(gates), budget)
            count += 1
        self.assertGreater(count, 0)


def production_sat(n, target, budget):
    import cube_search as cs
    terms = tuple(a for a in range(1 << n) if target >> a & 1
                  and not any(target >> (a ^ (1 << i)) & 1 for i in range(n) if a >> i & 1))
    stats = Counter()
    for right in range(n):
        for left in range(right):
            for op in (0, 1):
                _, status, witness, _, _ = cs.run_cube((n, terms, budget, 'maplechrono', (op, left, right),
                                                        False, False, dict(nonot=True, cert=True, reuse=True)))
                stats[status] += 1
                if status == 'WITNESS':
                    if not check_witness(n, target, witness):
                        raise RuntimeError('invalid production witness')
                    return dict(status='SAT', gates=witness, stats=stats)
                if status != 'UNSAT':
                    return dict(status='UNKNOWN', stats=stats)
    return dict(status='UNSAT_EXACT', stats=stats)


def layout_job(n, target, excess, mode):
    stats = Counter()
    if mode == 'sat':
        return production_sat(n, target, n-1+excess)
    if mode == 'quotient3':
        result = solve3(n, target, False, stats)
        if result is None:
            return dict(status='QUOTIENT3_EXCLUDED', stats=stats)
        gates, output = materialize3(n, target, result)
    else:
        result = search_exact(n, target, excess, stats=stats, projection=mode != 'unfiltered',
                              restrictions=mode not in ('unfiltered', 'projection-only'),
                              support_filter=mode == 'support', internal_first=mode == 'internal-first')
        if result is None:
            status = 'ANALYTICAL_FIRST_GATE' if stats['analytical_first_gate'] else 'LAYOUT_EXCLUDED'
            return dict(status=status, stats=stats)
        gates, output = reconstruct(n, target, *result, excess)
    if any(sign for _, a, b in gates for _, sign in (a, b)) or output[1]:
        raise RuntimeError('unexpected negation in a monotone witness')
    materialized = tuple((0 if op == '&' else 1, *sorted((a[0], b[0]))) for op, a, b in gates)
    if output[0] != n + len(gates) - 1 or not check_witness(n, target, materialized):
        raise RuntimeError('invalid reconstructed layout witness')
    return dict(status='SAT', gates=materialized, stats=stats)


HIGHER = (('graph-01', 4), ('hypergraph-08', 4), ('hypergraph-12', 4), ('hypergraph-21', 4),
          ('hypergraph-03', 4), ('comparator-02', 4), ('comparator-02', 5), ('comparator-04', 5),
          ('threshold-5-3', 5), ('random-monotone-10', 4))


def matched_three():
    """The monotone half of the supplied matched workload."""
    rng = Random(811)
    selected = []
    n = 5
    variables = truth_variables(n)
    while len(selected) < 10:
        target = 0
        for _ in range(rng.randint(3, 7)):
            term = (1 << (1 << n)) - 1
            for i in rng.sample(range(n), rng.choice((2, 3))):
                term &= variables[i]
            target |= term
        if essential(n, target) and simplify(n, target, False)[0] == n and target not in selected:
            selected.append(target)
    return [target for target in selected if solve2(n, target, False) is None]


def benchmark(args):
    if args.matched:
        jobs = [(hex(target), 5, target, 3, 0) for target in matched_three()]
        modes = ('quotient3', 'unfiltered', 'projection-only', 'combined')
    else:
        data = {name: (n, target) for name, _, n, target in cases()}
        chosen = HIGHER if args.job is None else tuple((key, int(e)) for key, e in args.job)
        jobs = []
        for name, excess in chosen:
            n, target = data[name]
            n, target, _ = restrict_essential(n, target)
            n, target, trace = simplify(n, target, False)
            jobs.append((name, n, target, excess, len(trace)))
        modes = ('combined', 'sat') if args.mode is None else tuple(args.mode)
    with args.output.open('x', encoding='utf-8') as out:
        for name, n, target, excess, contraction in jobs:
            for mode in modes:
                result = bounded(layout_job, (n, target, excess, mode), args.seconds)
                record = dict(case=name, n=n, target=hex(target), excess=excess, contraction=contraction,
                              mode=mode, **result)
                out.write(json.dumps(record, sort_keys=True) + '\n')
                out.flush()
                print(name, excess, mode, result['status'], round(result['seconds'], 3), flush=True)


if __name__ == '__main__':
    if '--output' in sys.argv:
        parser = argparse.ArgumentParser(description=__doc__)
        parser.add_argument('--output', type=Path, required=True)
        parser.add_argument('--seconds', type=float, default=4)
        parser.add_argument('--matched', action='store_true')
        parser.add_argument('--job', nargs=2, action='append')
        parser.add_argument('--mode', nargs='+', choices=('combined', 'sat', 'projection-only', 'unfiltered',
                                                          'support', 'internal-first', 'quotient3'))
        args = parser.parse_args()
        if args.seconds <= 0:
            parser.error('--seconds must be positive')
        benchmark(args)
    else:
        unittest.main()
