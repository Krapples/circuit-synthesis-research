"""Independent checks and frozen-corpus ablations for global provider capacity."""

import argparse
from collections import Counter, defaultdict
from itertools import product
import json
from pathlib import Path
from random import Random
import sys
from time import perf_counter
import unittest

from certificate_decomposition import LazyTopology, _capacity_owner_cut, _capacity_prefix_clauses, complete_status
from certificate_rank_check import complete_certificates, graph_certificates
from certify_synthesis import encode as encode_direct
from port_certificates import minimal_zero_certificates
from port_certificates_check import MANIFEST, bounded, check_with_minisat, flatten_witness, lazy_job
from provider_capacity import (CAPACITY_LEVELS, CapacityLayout, CapacityRegion, capacity_obstruction,
                               global_rectangle_allocation, prepare_capacity_layout)
from provider_certificates import incompatibility_cliques
from provider_certificates_check import monotone_tables
from synthesis_cases import Witness, full_rows, trim, truth_table
from synthesis_followup import digest, load_cases
from pysat.solvers import Solver


def reference_layout(positives, zeros, groups, capacities):
    """Enumerate concrete monotone provider tables before global rectangle cover."""
    tests = []
    for region, primary in enumerate(groups):
        rows = tuple(i for i, a in enumerate(positives) if a & primary or region == len(groups) - 1)
        columns = tuple(j for j, b in enumerate(zeros) if b & primary or region == len(groups) - 1)
        for i, j in product(rows, columns):
            common = (positives[i] & zeros[j] & primary).bit_count()
            if common > 1:
                return False
            if not common:
                tests.append((region, i, j))
    required = frozenset(tests)
    support = 0
    choices = []
    for source, primary in enumerate(groups[:-1]):
        support |= primary
        bits = [1 << i for i in range(support.bit_length()) if support >> i & 1]

        def project(mask):
            return sum(1 << i for i, bit in enumerate(bits) if mask & bit)

        high = tuple(project(a) for a in positives)
        low = tuple(project(~b) for b in zeros)
        available = set()
        for table in monotone_tables(len(bits)):
            if (any(a & primary and not table >> x & 1 for a, x in zip(positives, high))
                    or any(b & primary and table >> x & 1 for b, x in zip(zeros, low))):
                continue
            available.add(frozenset((r, i, j) for r, i, j in tests
                                    if source < r and table >> high[i] & 1 and not table >> low[j] & 1))
        if not available:
            return False
        choices.append(available)
    for selected in product(*choices):
        if not required <= frozenset().union(*selected):
            continue
        rectangles = []
        for source, available in enumerate(selected):
            for region in range(source + 1, len(groups)):
                rows = sorted({i for r, i, _ in available if r == region})
                cols = sorted({j for r, _, j in available if r == region})
                for rs, cs in product(range(1, 1 << len(rows)), range(1, 1 << len(cols))):
                    rectangle = frozenset((region, rows[i], cols[j]) for i, j in product(range(len(rows)),
                                                                                       range(len(cols)))
                                          if rs >> i & 1 and cs >> j & 1)
                    if rectangle <= available:
                        rectangles.append((source, rectangle))

        def cover(remaining, caps):
            if not remaining:
                return True
            first = min(remaining)
            return any(cover(remaining - rect, (*caps[:j], caps[j] - 1, *caps[j + 1:]))
                       for j, rect in rectangles if caps[j] and first in rect and rect <= remaining)

        if cover(required, capacities):
            return True
    return False


class GlobalCapacityChecks(unittest.TestCase):
    def test_requested_regression(self):
        positives, zeros = (7, 10, 12), (6, 9, 10, 12)
        groups, caps = (8, 3, 4), (2, 3)
        layout, initial = prepare_capacity_layout(positives, zeros, groups, caps)
        self.assertIsNone(initial)
        self.assertTrue(all(global_rectangle_allocation(layout, regions=(region,)) for region in layout.regions))
        self.assertFalse(global_rectangle_allocation(layout))
        self.assertFalse(reference_layout(positives, zeros, groups, caps))
        failure = capacity_obstruction(layout, 'singletons')
        self.assertEqual((failure.subset, failure.required, failure.capacity), (1, 3, 2))
        self.assertEqual(tuple(map(len, failure.cliques)), (0, 1, 2))
        self.assertEqual(prepare_capacity_layout((7, 7, 10, 12), zeros, groups, caps), (layout, None))
        # The output cell (cd, ad) distinguishes on the second provider's
        # ancestor d, but cd conflicts with its mandatory zero certificate bc.
        self.assertTrue(12 & 9 & 11)
        self.assertEqual(layout.regions[-1].eligibility[2][1], 1)

        owners = tuple(tuple(range(10 + 3*i, 13 + 3*i)) for i in range(4))
        topology = LazyTopology(owners, (1, 2, 4, 8), (), ())
        stats = Counter()
        clause = _capacity_owner_cut(topology, (3, 2), (positives, zeros), (1, 1, 0, 2),
                                     'subsets', stats, 'static')
        self.assertEqual(clause, (-11, -14, -16, -21))
        self.assertEqual(stats['capacity_static_capacity'], 1)
        prescreened = _capacity_prefix_clauses(topology, (3, 2), (positives, zeros), 'subsets', stats, limit=1000)
        self.assertIn(clause, prescreened)
        prefix, failure = prepare_capacity_layout(positives, zeros, groups[:2], caps, output=False)
        self.assertIsNone(failure)
        self.assertIsNone(capacity_obstruction(prefix))

    def test_subset_cliques_keep_optional_cross_corners(self):
        self.assertEqual(max(map(len, incompatibility_cliques(((1, 3), (3, 1)), 1))), 1)
        diagonal = CapacityRegion((0, 1), (0, 1), ((3, 0), (0, 3)))
        layout = CapacityLayout((1, 2), ((3, 3), (3, 3)), ((0, 0), (0, 0)), (diagonal, diagonal))
        self.assertIsNone(capacity_obstruction(layout, 'singletons'))
        failure = capacity_obstruction(layout, 'subsets')
        self.assertEqual((failure.subset, failure.required, failure.capacity), (3, 4, 3))

    def test_regression_target_also_has_an_independent_five_gate_minimum(self):
        p, z = (7, 10, 12), (6, 9, 10, 12)
        labels = {x: any(a & x == a for a in p) for x in range(16)}
        variables, clauses = encode_direct(4, labels, 4)
        with Solver(name='g4', bootstrap_with=clauses, with_proof=True) as sat:
            self.assertFalse(sat.solve())
            self.assertGreater(check_with_minisat(variables, clauses, [*(sat.get_proof() or ()), '0']), 1)
        stats, witnesses = Counter(), []
        self.assertEqual(complete_status(p, z, 2, backend='lazy-certificates', local_intersection=True,
                                         provider_capacity='subsets', conflicts=None, stats=stats,
                                         on_sat=lambda _, w: witnesses.append(flatten_witness(4, w))), 'SAT')
        self.assertGreater(stats['capacity_static_capacity'], 0)
        self.assertEqual(len(witnesses[0].gates), 5)
        self.assertEqual(truth_table(4, witnesses[0]), sum(1 << x for x, high in labels.items() if high))

    def test_exact_allocation_checks_cross_region_provider_consistency(self):
        first = CapacityRegion((0,), (0,), ((1,),))
        second = CapacityRegion((1,), (1,), ((1,),))
        layout = CapacityLayout((2,), ((1, 2),), ((0, 0),), (first, second))
        self.assertTrue(global_rectangle_allocation(layout, regions=(first,)))
        self.assertTrue(global_rectangle_allocation(layout, regions=(second,)))
        self.assertIsNone(capacity_obstruction(layout))
        self.assertIsNone(global_rectangle_allocation(layout, max_states=0))
        self.assertEqual(capacity_obstruction(layout, 'exact').kind, 'allocation')

    def test_small_complete_layouts_against_independent_provider_tables(self):
        rng = Random(18381)
        counts = Counter()
        for _ in range(440):
            w = rng.randrange(3, 5)
            raw = rng.sample(range(1, 1 << w), rng.randrange(1, 7))
            p = tuple(sorted(a for a in raw if not any(a != b and a & b == b for b in raw)))
            z = minimal_zero_certificates(p)
            groups = [0, 0, 1 << (w-1)]
            for i in range(w-1):
                groups[rng.randrange(3)] |= 1 << i
            caps = tuple(rng.randrange(1, 4) for _ in range(2))
            expected = reference_layout(p, z, groups, caps)
            layout, obstruction = prepare_capacity_layout(p, z, groups, caps)
            exact = False if obstruction is not None else global_rectangle_allocation(layout)
            self.assertIs(exact, expected, (p, z, groups, caps))
            if expected:
                self.assertIsNone(capacity_obstruction(layout))
            counts['feasible' if expected else 'excluded'] += 1
        self.assertGreater(counts['feasible'], 30)
        self.assertGreater(counts['excluded'], 30)
        print(f'global oracle compared {dict(counts)}')

    def test_concrete_circuit_capacities_and_supports(self):
        rng = Random(323122)
        checked = Counter()
        for _ in range(1300):
            n = rng.randrange(3, 7)
            gates = tuple((rng.randrange(2), *sorted(rng.sample(range(wire), 2)))
                          for wire in range(n, n + rng.randrange(3, 14)))
            circuit = trim(n, Witness(gates, n + len(gates) - 1))
            p, z = complete_certificates(n, truth_table(n, circuit))
            if any(not any(a >> i & 1 for a in p) for i in range(n)):
                continue
            parents = defaultdict(list)
            supports = [1 << i for i in range(n)]
            for wire, (_, a, b) in enumerate(circuit.gates, n):
                supports.append(supports[a] | supports[b])
                for operand in (a, b):
                    parents[operand].append(wire)
            repeated = tuple(sorted(w for w, readers in parents.items() if len(readers) > 1))
            terminals = (*repeated, circuit.output)
            groups = dict.fromkeys(terminals, 0)
            for i in range(n):
                root = i
                while root not in groups:
                    root = parents[root][0]
                groups[root] |= 1 << i
            caps = tuple(len(parents[wire]) for wire in repeated)
            for end in range(1, len(caps) + 1):
                prefix, obstruction = prepare_capacity_layout(p, z, tuple(groups.values())[:end], caps[:end],
                                                               output=False)
                self.assertIsNone(obstruction)
                self.assertIsNone(capacity_obstruction(prefix))
                checked['prefixes'] += 1
            for upper in (None, tuple(supports[wire] for wire in repeated)):
                layout, obstruction = prepare_capacity_layout(p, z, tuple(groups.values()), caps, supports=upper)
                self.assertIsNone(obstruction)
                self.assertIsNone(capacity_obstruction(layout))
                result = global_rectangle_allocation(layout)
                self.assertIsNot(result, False)
                checked['exact' if result else 'capped'] += 1
            checked['circuits'] += 1
            checked['shared'] += bool(repeated)
        self.assertGreater(checked['shared'], 50)
        print(f'concrete capacity checks {dict(checked)}')

    def test_lazy_known_minima_and_proofs(self):
        p, z = graph_certificates(5, tuple((i, (i + 1) % 5) for i in range(5)))
        for local, level in product((False, True), CAPACITY_LEVELS):
            for budget in (6, 7):
                checked, witnesses, stats = [], [], Counter()

                def verify(_, variables, clauses, proof):
                    checked.append(check_with_minisat(variables, clauses, [*(proof or ()), '0']))

                status = complete_status(p, z, budget - 4, backend='lazy-certificates', conflicts=None,
                                         local_intersection=local, provider_capacity=level, stats=stats,
                                         verify_unsat=verify, on_sat=lambda _, w: witnesses.append(w))
                self.assertEqual(status, 'SAT' if budget == 7 else 'UNSAT')
                if status == 'UNSAT':
                    self.assertTrue(checked)
                else:
                    circuit = flatten_witness(5, witnesses[0])
                    self.assertEqual(len(circuit.gates), 7)
                    self.assertEqual(truth_table(5, circuit), sum(1 << x for x in range(32)
                                                                if any(a & x == a for a in p)))
                    self.assertGreater(sum(stats[key] for key in ('capacity_static_layouts', 'capacity_lazy_layouts',
                                                                   'capacity_prefix_layouts')), 0)
        with self.assertRaisesRegex(ValueError, 'complete monotone'):
            complete_status(p, z[:-1], 2, backend='lazy-certificates', provider_capacity='subsets')


JOBS = (('cycle-5', 6), ('cycle-5', 7), ('threshold-4-3', 6), ('threshold-4-3', 7),
        ('hypergraph-19', 9), ('hypergraph-19', 10), ('comparator-02', 8), ('comparator-02', 9),
        ('hypergraph-05', 13), ('random-monotone-05', 13))


def profile_layouts(level):
    rng = Random(503612)
    counts = Counter()
    for case in load_cases(MANIFEST).values():
        if case.n < 2 or case.known != full_rows(case.n):
            continue
        p, z = complete_certificates(case.n, case.truth)
        for _ in range(20):
            count = rng.randrange(2, min(5, case.n) + 1)
            groups = [0] * count
            for i in range(case.n):
                groups[rng.randrange(count)] |= 1 << i
            caps = tuple(rng.randrange(2, 5) for _ in groups[:-1])
            layout, obstruction = prepare_capacity_layout(p, z, groups, caps)
            if layout is not None:
                obstruction = capacity_obstruction(layout, level)
            if obstruction is None:
                counts['survives'] += 1
            elif obstruction.kind == 'capacity':
                counts[f'capacity_{obstruction.subset.bit_count()}'] += 1
            else:
                counts[obstruction.kind] += 1
    return dict(status='OK', counts=counts)


def profile_four_input_layouts(level):
    counts = Counter()
    for truth in monotone_tables(4):
        p, z = complete_certificates(4, truth)
        if not all(any(a >> i & 1 for a in p) for i in range(4)):
            continue
        for assignments in product(range(3), repeat=4):
            if len(set(assignments)) != 3:
                continue
            groups = tuple(sum(1 << i for i, r in enumerate(assignments) if r == region) for region in range(3))
            for caps in product((2, 3), repeat=2):
                layout, obstruction = prepare_capacity_layout(p, z, groups, caps)
                if layout is not None:
                    obstruction = capacity_obstruction(layout, level)
                if obstruction is None:
                    counts['survives'] += 1
                elif obstruction.kind == 'capacity':
                    counts[f'capacity_{obstruction.subset.bit_count()}'] += 1
                else:
                    counts[obstruction.kind] += 1
    return dict(status='OK', counts=counts)


def benchmark(args):
    jobs = JOBS if args.job is None else tuple((name, int(budget)) for name, budget in args.job)
    levels = ('subsets', 'exact') if args.exact else (None, 'singletons', 'subsets')
    local = not args.without_local_intersection
    with args.benchmark.open('x', encoding='utf-8') as out:
        def record(row):
            out.write(json.dumps(row, sort_keys=True) + '\n')
            out.flush()
            print(json.dumps({k: v for k, v in row.items() if k not in ('stats', 'witnesses')}), flush=True)

        record(dict(kind='meta', manifest_sha256=digest(MANIFEST), jobs=jobs, local=local,
                    seconds=args.seconds, conflicts=args.conflicts, levels=levels, proof=args.proof,
                    layouts='four-input' if args.all_four_inputs else 'frozen-sample' if args.layouts else None))
        if args.layouts or args.all_four_inputs:
            profile = profile_four_input_layouts if args.all_four_inputs else profile_layouts
            for level in levels:
                if level is not None:
                    record(dict(kind='layouts', level=level, **bounded(profile, (level,), 15)))
            return
        for name, budget in jobs:
            for level in levels:
                result = bounded(lazy_job, (name, budget, None, args.conflicts, args.proof, local, None, None, level),
                                 args.seconds)
                record(dict(kind='lazy', name=name, budget=budget, level=level, **result))


if __name__ == '__main__':
    if '--benchmark' in sys.argv:
        parser = argparse.ArgumentParser(description=__doc__)
        parser.add_argument('--benchmark', type=Path, required=True)
        parser.add_argument('--seconds', type=float, default=1.25)
        parser.add_argument('--conflicts', type=int, default=1800)
        parser.add_argument('--job', nargs=2, action='append', metavar=('CASE', 'BUDGET'))
        parser.add_argument('--exact', action='store_true')
        profiles = parser.add_mutually_exclusive_group()
        profiles.add_argument('--layouts', action='store_true')
        profiles.add_argument('--all-four-inputs', action='store_true')
        parser.add_argument('--without-local-intersection', action='store_true')
        parser.add_argument('--proof', action='store_true')
        args = parser.parse_args()
        if args.seconds <= 0 or args.conflicts < 1:
            parser.error('seconds and conflicts must be positive')
        benchmark(args)
    else:
        unittest.main()
