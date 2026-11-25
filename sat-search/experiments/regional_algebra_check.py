"""Independent checks and matched profiles for regional algebraic bounds."""

from collections import Counter
from itertools import product
import json
from random import Random
import sys
from time import perf_counter
import unittest

from affine_completion import complete_affine, direction, is_exact_certificate, rational_affine_basis
from certificate_decomposition import complete_status
from certificate_rank_check import complete_certificates, graph_certificates
from cube_search import ordered_port_lb, ordered_type_bounds, port_costs, rterms_support
from port_certificates import certificate_type_costs, incoming_port_bound
from port_certificates_check import MANIFEST, bounded, check_with_minisat, flatten_witness, lazy_job
from provider_capacity import (ALLOCATION_LEVELS, allocation_excess, compulsory_demands,
                               ordered_allocation_excess, prepare_capacity_layout)
from regional_synthesis import _formulas
from synthesis_cases import Witness, full_rows, trim, truth_table
from synthesis_followup import load_cases


def type_counts(tree):
    if isinstance(tree, int):
        return 0, 0
    op, a, b = tree
    x, y = type_counts(a)
    z, w = type_counts(b)
    return x + z + (op == 0), y + w + (op == 1)


class RegionalAlgebraChecks(unittest.TestCase):
    def test_capacity_budget_and_exact_allocation_reference(self):
        p, z = (7, 10, 12), (6, 9, 10, 12)
        groups = (8, 3, 4)
        layout, failure = prepare_capacity_layout(p, z, groups, (2, 2))
        self.assertIsNone(failure)
        unrestricted = [incoming_port_bound(p, z, group, output=i == 2) for i, group in enumerate(groups)]
        self.assertEqual(max(2, sum(unrestricted) - 2), 2)
        self.assertEqual(compulsory_demands(layout), (0, 3, 2, 5))
        for level in ALLOCATION_LEVELS:
            self.assertEqual(allocation_excess(compulsory_demands(layout), 2, level), 3)
        # Pair constraints sharing providers separate packing from integer allocation.
        demands = (0, 0, 0, 5, 0, 5, 5, 0)
        self.assertEqual(tuple(allocation_excess(demands, 6, level) for level in ALLOCATION_LEVELS), (4, 4, 5))
        self.assertEqual(allocation_excess((0, 3, 3, 0), 5, 'packing'), 4)
        rng = Random(2751)
        for _ in range(200):
            r = rng.randrange(1, 5)
            budget = r + rng.randrange(6)
            demands = (0, *(rng.randrange(9) for _ in range((1 << r) - 1)))
            exact_best = min((r + sum(extra) for extra in product(range(budget-r+1), repeat=r)
                              if sum(extra) <= budget-r and all(
                                  sum(2+extra[i] for i in range(r) if subset >> i & 1) >= demand
                                  for subset, demand in enumerate(demands))), default=budget + 1)
            got = allocation_excess(demands, budget, 'exact')
            self.assertEqual(min(got, budget+1), exact_best)
            self.assertLessEqual(allocation_excess(demands, 30, 'deficit'),
                                 allocation_excess(demands, 30, 'packing'))

    def test_typed_rank_against_concrete_dags_and_capacity_occurrences(self):
        rng = Random(6654)
        count = 0
        for _ in range(1100):
            n = rng.randrange(3, 7)
            gates = tuple((rng.randrange(2), *sorted(rng.sample(range(i), 2)))
                          for i in range(n, n + rng.randrange(3, 13)))
            circuit = trim(n, Witness(gates, n + len(gates) - 1))
            p, z = (tuple(axis) for axis in complete_certificates(n, truth_table(n, circuit)))
            if rterms_support(p) != (1 << n) - 1:
                continue
            parents = {}
            for gate, (_, a, b) in enumerate(circuit.gates, n):
                for wire in (a, b):
                    parents.setdefault(wire, []).append(gate)
            repeated = tuple(sorted(wire for wire, readers in parents.items() if len(readers) > 1))
            regions = dict.fromkeys((*repeated, circuit.output), 0)

            def owner(wire):
                while wire not in regions:
                    wire = parents[wire][0]
                return wire

            for i in range(n):
                regions[owner(i)] |= 1 << i
            types = Counter((owner(i), op) for i, (op, _, _) in enumerate(circuit.gates, n))
            for wire, primary in regions.items():
                typed = certificate_type_costs(p, z, primary, output=wire == circuit.output)
                for op, bound in enumerate(typed):
                    self.assertLessEqual(bound, types[wire, op])
            costs = port_costs(p, mono=True, certificate_level='exact', certificate_output=True,
                               provider_eligibility=True, type_rank=True)
            typed = ordered_type_bounds(p, costs)
            self.assertTrue(all(typed[i] <= sum(op == i for op, _, _ in circuit.gates) for i in (0, 1)))
            self.assertLessEqual(typed[2], len(circuit.gates))
            if len(repeated) <= 6:
                layout, failure = prepare_capacity_layout(p, z, tuple(regions.values()), (2,) * len(repeated))
                self.assertIsNone(failure)
                excess = len(circuit.gates) - n + 1
                self.assertLessEqual(allocation_excess(compulsory_demands(layout), excess, 'exact'), excess)
            count += 1
        self.assertGreater(count, 90)
        print(f'concrete typed/capacity checks on {count} circuits')

    def test_affine_completion_and_rational_compression_against_cographs(self):
        rng = Random(61124)
        checked, compressed, zero = 0, 0, 0
        for n in (4, 5, 6):
            leaves = (1 << n) - 1
            reference = tuple(tuple(frozenset(axis) for axis in complete_certificates(n, truth))
                              for truth in _formulas(n, leaves))
            for _ in range(250):
                p, z = rng.choice(reference)
                if checked % 3 == 0:
                    _, z = rng.choice(reference)
                pos = tuple(rng.sample(sorted(p), rng.randrange(1, min(4, len(p)) + 1)))
                neg = tuple(rng.sample(sorted(z), rng.randrange(1, min(4, len(z)) + 1)))
                expected = any(set(pos) <= a and set(neg) <= b for a, b in reference)
                tree, deficit, _ = complete_affine(leaves, pos, neg, max_deficit=5)
                self.assertEqual(tree is not None, expected)
                basis_p, basis_n = rational_affine_basis(pos), rational_affine_basis(neg)
                self.assertEqual(any(set(basis_p) <= a and set(basis_n) <= b for a, b in reference), expected)
                compressed += len(basis_p) + len(basis_n) < len(pos) + len(neg)
                if tree is not None:
                    self.assertTrue(all(is_exact_certificate(tree, x, high)
                                        for high, axis in ((True, pos), (False, neg)) for x in axis))
                    zero += deficit == 0
                checked += 1
            for table, known in list(_formulas(n, leaves).items())[:80]:
                p, z = complete_certificates(n, table)
                tree, deficit, _ = complete_affine(leaves, p, z, max_deficit=0)
                self.assertIsNotNone(tree)
                self.assertEqual(deficit, 0)
                self.assertEqual(certificate_type_costs(p, z, leaves, output=True), type_counts(known))
        # A mod-2 basis would drop 111 from the affine span of three singleton rows.
        self.assertEqual(direction((1, 2, 4)), direction((1, 2, 4, 7)))
        self.assertEqual(len(rational_affine_basis((1, 2, 4, 7))), 4)
        self.assertGreater(compressed, 0)
        print(f'{checked} exact partial-family checks, {zero} zero-deficit completions, {compressed} rational reductions')

    def test_affine_lazy_matches_checked_known_answer(self):
        p, z = graph_certificates(5, tuple((i, (i+1) % 5) for i in range(5)))
        for cap in (None, 0, 3):
            for budget in (6, 7):
                stats, proofs, witnesses = Counter(), [], []

                def verify(_, variables, clauses, trace):
                    proofs.append(check_with_minisat(variables, clauses, [*(trace or ()), '0']))

                answer = complete_status(p, z, budget-4, backend='lazy-certificates', local_intersection=True,
                                         conflicts=None, affine_completion=cap, verify_unsat=verify, stats=stats,
                                         on_sat=lambda _, w: witnesses.append(flatten_witness(5, w)))
                self.assertEqual(answer, 'UNSAT' if budget == 6 else 'SAT')
                if answer == 'UNSAT':
                    self.assertTrue(proofs)
                else:
                    self.assertEqual(len(witnesses[0].gates), 7)
                    self.assertEqual(truth_table(5, witnesses[0]), sum(1 << row for row in range(32)
                                                                      if any(p & row == p for p in p)))


def ordered_profile(level):
    records = []
    for case in load_cases(MANIFEST).values():
        if case.known != full_rows(case.n) or case.n > 6:
            continue
        p, z = (tuple(axis) for axis in complete_certificates(case.n, case.truth))
        support = rterms_support(p)
        begin = perf_counter()
        costs = port_costs(p, mono=True, separation=True, profile=True, formula=True, output=True,
                           certificate_level='exact', certificate_output=True, provider_eligibility=True,
                           type_rank=level == 'typed')
        lower = ordered_port_lb(p, costs)
        stats = Counter()
        if level == 'typed':
            typed = ordered_type_bounds(p, costs)
            lower = max(lower, typed[2])
            stats['local_nonzero'] = sum(any(certificate_type_costs(p, z, group)) for group in costs)
            stats['and'], stats['or'] = typed[:2]
        elif level == 'layout' or level in ALLOCATION_LEVELS:
            base = support.bit_count()-1
            lower = base + ordered_allocation_excess(p, z, costs, costs.pout or {}, support,
                                                    lower-base, lower-base,
                                                    None if level == 'layout' else level,
                                                    max_layouts=900, stats=stats)
        records.append(dict(name=case.name, lower=lower, seconds=perf_counter()-begin, stats=stats,
                            costs=costs, output=costs.pout))
    return dict(status='OK', cases=records)


def profile():
    for level in ('reference', 'layout', 'deficit', 'packing', 'exact', 'typed'):
        record = bounded(ordered_profile, (level,), 35)
        print(json.dumps(dict(kind='ordered', level=level, **record)), flush=True)
    jobs = (('cycle-5', 6), ('cycle-5', 7), ('hypergraph-19', 9), ('hypergraph-19', 10),
            ('threshold-5-3', 9), ('threshold-5-3', 10), ('hypergraph-05', 13))
    for name, budget in jobs:
        for cap in (None, 0, 3):
            record = bounded(lazy_job, (name, budget, None, 1800, False, True, None, None, None, cap), 1.25)
            print(json.dumps(dict(kind='lazy', name=name, budget=budget, cap=cap, **record)), flush=True)


if __name__ == '__main__':
    if '--profile' in sys.argv:
        profile()
    else:
        unittest.main()
