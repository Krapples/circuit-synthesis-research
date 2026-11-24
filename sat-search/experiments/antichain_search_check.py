"""Cross-check exact antichain search and its formula and regional completions."""

from collections import Counter
from itertools import combinations, product
from random import Random
import unittest
from unittest.mock import patch

import antichain_search as search
from cube_search import boundary_rows
from regional_search import known_formulas, pareto
from subtree_formulas import constrained_formulas, forced_by_outside


def brute(n, labels, budget):
    target = sum(1 << j for j, value in enumerate(labels.values()) if value)
    init = frozenset(sum(1 << j for j, row in enumerate(labels) if row >> i & 1) for i in range(n))
    states = {init}
    for step in range(budget + 1):
        if any(target in state for state in states):
            return True
        if step < budget:
            states = {state | {gate} for state in states for a, b in combinations(state, 2)
                      for gate in (a & b, a | b)}
    return False


def graph(n, cyclic=False):
    masks = tuple((1 << i) | (1 << (i + 1)) for i in range(n - 1))
    if cyclic:
        masks += (1 | (1 << (n - 1)),)
    positive, negative = boundary_rows(n, masks)
    return masks, {**dict.fromkeys(positive, True), **dict.fromkeys(negative, False)}


class AntichainSearchChecks(unittest.TestCase):
    def test_local_subtree_frontiers_match_unconstrained_enumeration(self):
        rng = Random(769)
        for _ in range(150):
            columns = tuple(rng.randrange(256) for _ in range(rng.randint(1, 5)))
            negative = rng.randrange(256)
            positive = 255 ^ negative
            required_p, required_n = forced_by_outside(tuple(rng.randrange(256) for _ in range(2)),
                                                       positive, negative)
            baseline = known_formulas(columns, negative, prune=False)
            expected = pareto({t: f for t, f in baseline.items() if t & required_p == required_p and not t & required_n},
                              negative)
            tables, rejected = constrained_formulas(columns, required_p, required_n, negative)
            self.assertEqual(tables.keys(), expected.keys())
            if rejected:
                self.assertFalse(expected)

    def test_structural_admissibility_can_pass_without_a_formula(self):
        pos = (3, 14, 20, 24, 27, 29, 30)
        neg = (4, 5, 9, 17, 18)
        self.assertTrue({1, 2, 4, 8, 16} <= {a & ~b for a in pos for b in neg})
        positive = sum(1 << r for r in pos)
        negative = sum(1 << r for r in neg)
        columns = tuple(sum(1 << r for r in pos + neg if r >> i & 1) for i in range(5))
        tables, rejected = constrained_formulas(columns, positive, negative, negative)
        self.assertFalse(rejected)
        self.assertEqual(tables, {})
        self.assertNotIn(positive, known_formulas(columns, negative, prune=False))

    def test_excluded_tight_frontiers_need_no_boolean_enumeration(self):
        for n, cyclic, budget, expected in ((5, True, 6, 21), (6, False, 6, 5), (6, True, 7, 31)):
            _, labels = graph(n, cyclic)
            stats = Counter()
            self.assertIsNone(search.solve_partial(n, labels, budget, stats=stats))
            self.assertEqual(stats['distinct_formula_tests'], expected)
            self.assertEqual(stats['distinct_structural_rejections'], expected)
            self.assertEqual(stats['distinct_formula_enumerations'], 0)

    def test_exact_hitting_number(self):
        rng = Random(153)
        for _ in range(100):
            width = rng.randint(1, 7)
            demands = [rng.randrange(1 << width) for _ in range(rng.randint(0, 12))]
            reference = min((mask.bit_count() for mask in range(1 << width)
                             if all(mask & d for d in demands)), default=float('inf'))
            self.assertEqual(search.hitting_number(search.minimal_demands(demands)), reference)

    def test_noninjective_coverage(self):
        self.assertTrue(search.state_dominates((3,), (1, 2), 0))
        self.assertFalse(search.state_dominates((1, 2), (3,), 0))

    def test_at_most_verdicts_match_brute_force(self):
        rng = Random(871)
        cases = [{row: bool(table >> row & 1) for row in range(8)} for table in range(256)]
        cases += [{row: bool(rng.randrange(2)) for row in rng.sample(range(8), rng.randrange(9))}
                  for _ in range(80)]
        for labels in cases:
            for budget in range(4):
                expected = brute(3, labels, budget)
                for options in ({'hitting': False, 'nondegenerate': False}, {'tight': False}, {},
                                {'sharing': 1, 'dominance_memo': True}, {'sharing': 2, 'sharing_order': True}):
                    witness = search.solve_partial(3, labels, budget, **options)
                    self.assertEqual(witness is not None, expected, (labels, budget, options))
                    if witness is not None:
                        self.assertLessEqual(len(witness.gates), budget)
                        self.assertTrue(all(witness.evaluate(row) == value for row, value in labels.items()))

    def test_tight_width_limit_falls_back_to_gate_search(self):
        labels = {row: row == 7 for row in range(8)}
        stats = Counter()
        with patch.object(search, 'MAX_KNOWN_LEAVES', 2):
            circuit = search.solve_partial(3, labels, 2, stats=stats)
        self.assertIsNotNone(circuit)
        self.assertGreater(stats['states'], 1)
        self.assertTrue(all(circuit.evaluate(row) == target for row, target in labels.items()))

    def test_joint_completion_matches_small_at_most_search(self):
        rng = Random(1529)
        total = 0
        for _ in range(36):
            width = rng.randint(3, 4)
            rows = rng.sample(range(1 << width), 6)
            terms = rng.sample(range(1, 1 << width), 3)
            labels = {row: any(row & term == term for term in terms) for row in rows}
            for budget in range(4):
                stats = Counter()
                result = search.solve_partial(width, labels, budget, antichain=False, nondegenerate=False,
                                              jointcompletion=True, sharing=3, stats=stats)
                self.assertEqual(result is not None, brute(width, labels, budget), (labels, budget))
                if result is not None:
                    self.assertLessEqual(len(result.gates), budget)
                    self.assertTrue(all(result.evaluate(row) == high for row, high in labels.items()))
                total += stats['joint_completion_patterns']
        self.assertGreater(total, 0)

    def test_one_unit_of_sharing_uses_direct_completion(self):
        masks, labels = graph(4)
        for twocolorcompletion in (False, True):
            with self.subTest(twocolorcompletion=twocolorcompletion):
                stats = Counter()
                circuit = search.solve_partial(4, labels, 4, sharing=1, stats=stats,
                                               twocolorcompletion=twocolorcompletion)
                self.assertIsNotNone(circuit)
                self.assertGreater(stats['one_sharing_sets'], 0)
                self.assertEqual(stats['regional_tests'], 0)
                self.assertEqual(stats['states'], 1)
                self.assertTrue(all(circuit.evaluate(row) == any(row & edge == edge for edge in masks)
                                    for row in range(16)))

    def test_two_units_of_sharing_complete_the_triangle(self):
        labels = {row: row.bit_count() >= 2 for row in range(8)}
        self.assertIsNone(search.solve_partial(3, labels, 3, sharing=2))
        stats = Counter()
        circuit = search.solve_partial(3, labels, 4, sharing=2, stats=stats)
        self.assertIsNotNone(circuit)
        self.assertEqual((len(circuit.gates), stats['states'], stats['regional_tests']), (4, 1, 0))
        self.assertGreater(stats['two_sharing_sets'], 0)
        self.assertTrue(all(circuit.evaluate(row) == value for row, value in labels.items()))

    def test_direct_two_sharing_matches_gate_search_on_four_input_targets(self):
        rng = Random(159)
        edges = tuple((1 << a) | (1 << b) for a, b in combinations(range(4), 2))
        masks = [edges, *(tuple(rng.sample(edges, rng.randint(2, 6))) for _ in range(20))]
        columns = tuple(sum(1 << row for row in range(16) if row >> bit & 1) for bit in range(4))
        for terms in masks:
            if any(not any(term >> bit & 1 for term in terms) for bit in range(4)):
                continue
            labels = {row: any(row & term == term for term in terms) for row in range(16)}
            positive = sum(1 << row for row, high in labels.items() if high)
            gate_search = search.solve_partial(4, labels, 5, tight=False)
            plan, complete = search._direct_completion(columns, 2, positive, 65535 ^ positive, Counter())
            self.assertTrue(complete)
            self.assertEqual(plan is not None, gate_search is not None, terms)
            if plan is not None:
                witness = search._reconstruct(columns, plan, positive)
                self.assertLessEqual(len(witness.gates), 5)
                self.assertTrue(all(witness.evaluate(row) == high for row, high in labels.items()))

    def test_homogeneous_partial_labels_do_not_assume_constant_wires(self):
        for target in (True, False):
            labels = {1: target, 2: target}
            self.assertIsNone(search.solve_partial(2, labels, 0))
            witness = search.solve_partial(2, labels, 1)
            self.assertIsNotNone(witness)
            self.assertTrue(all(witness.evaluate(row) == target for row in labels))

    def test_sharing_classifier_matches_exact_hitting_recomputation(self):
        rng = Random(510)
        positive, negative = 0b000111, 0b111000
        pairs = tuple(product(search._bits(positive), search._bits(negative)))
        checked = 0
        for _ in range(160):
            columns = tuple(sorted({rng.randrange(64) for _ in range(rng.randrange(2, 8))}))
            demands = search.frontier_demands(columns, positive, negative)
            required = search.hitting_number(demands)
            if required == float('inf'):
                continue
            candidates = {table: (op, a, b, table) for a, b in combinations(columns, 2)
                          for op, table in ((0, a & b), (1, a | b)) if table not in columns}
            classified = search.preserving_gates(columns, demands, required, candidates, pairs)
            for table in candidates:
                updated = (*columns, table)
                updated = tuple(g for g in updated if search.useful_signal(g, positive, negative)
                                and not any(g != h and search.dominates(h, g, negative) for h in updated))
                following = search.hitting_number(search.frontier_demands(updated, positive, negative))
                self.assertIn(following, (required, required - 1))
                self.assertEqual(table in classified, following == required - 1)
                checked += 1
        self.assertGreater(checked, 100)

    def test_cycle_minima_and_reconstructed_witnesses(self):
        for n, minimum in ((5, 7), (6, 8)):
            masks, labels = graph(n, cyclic=True)
            for sharing in (None, 1, 2):
                self.assertIsNone(search.solve_partial(n, labels, minimum - 1, sharing=sharing))
                circuit = search.solve_partial(n, labels, minimum, sharing=sharing)
                self.assertIsNotNone(circuit)
                self.assertEqual(len(circuit.gates), minimum)
                self.assertTrue(all(circuit.evaluate(row) == any(row & edge == edge for edge in masks)
                                    for row in range(1 << n)))


if __name__ == '__main__':
    unittest.main()
