"""Small exact minima and hierarchy checks for regional synthesis."""

from itertools import product
from random import Random
import unittest

from consistent_network_test import random_circuit, random_groups
from regional_search import canonical_layouts
from regional_synthesis import one_port_feasible, synthesize_regions
import cube_search as cs


def find_with_budget(n, labels, gates):
    """Enumerate the regional decompositions of an all-wires-used monotone circuit."""
    for groups, ports in canonical_layouts(n, gates):
        solution = synthesize_regions(groups, ports, labels, reader_limits=((2, None),) * (len(groups) - 1))
        if solution is not None:
            return solution
    return None


class RegionalSynthesisChecks(unittest.TestCase):
    def test_one_port_path_obstruction_and_two_occurrence_witness(self):
        # x0*x1 OR x0*x3 OR x1*x2, with x1 supplied by the earlier terminal.
        group, earlier = 13, 2
        labels = {row: any(row & mask == mask for mask in (3, 9, 6)) for row in range(16)}
        pos = [r for r, v in labels.items() if v]
        neg = [r for r, v in labels.items() if not v]
        self.assertFalse(one_port_feasible(group, earlier, pos, neg))
        self.assertIsNone(synthesize_regions((earlier, group), (0, 1), labels))
        solution = synthesize_regions((earlier, group), (0, 2), labels, reader_limits=((2, 2),))
        self.assertIsNotNone(solution)
        self.assertEqual(solution.providers, ((), (0, 0)))
        self.assertTrue(all(solution.evaluate(row) == target for row, target in labels.items()))

    def test_one_port_checker_against_direct_partial_truth_tables(self):
        def combine(a, b, op):
            return a | b if op else a & b

        tables = set()
        for signal in (0, 255, 240):  # the monotone functions of the earlier variable x2
            leaves = (170, 204, signal)
            for i in range(3):
                a, b, c = leaves[i], leaves[(i + 1) % 3], leaves[(i + 2) % 3]
                tables.update(combine(a, combine(b, c, inner), outer)
                              for inner, outer in product((0, 1), repeat=2))
        for values in product((-1, 0, 1), repeat=8):
            pos = sum(1 << r for r, value in enumerate(values) if value == 1)
            neg = sum(1 << r for r, value in enumerate(values) if value == 0)
            expected = any(table & pos == pos and not table & neg for table in tables)
            self.assertEqual(one_port_feasible(3, 4, [r for r in range(8) if pos >> r & 1],
                                               [r for r in range(8) if neg >> r & 1]), expected)

        labels = {row: bool(row & 1 and row & 6) for row in range(8)}
        self.assertIsNotNone(synthesize_regions((4, 3), (0, 1), labels, mode='consistent'))

    def test_context_consistency_and_reader_capacity_strengthen_the_model(self):
        majority = {row: row.bit_count() >= 2 for row in range(8)}
        self.assertIsNotNone(synthesize_regions((1, 6), (0, 1), majority, mode='free'))
        self.assertIsNone(synthesize_regions((1, 6), (0, 1), majority, mode='consistent'))

        path = {row: any(row & mask == mask for mask in (3, 9, 6)) for row in range(16)}
        self.assertIsNotNone(synthesize_regions((2, 13), (0, 2), path, mode='consistent'))
        self.assertIsNone(synthesize_regions((2, 13), (0, 2), path, reader_limits=((0, 1),)))

    def test_known_monotone_minima_from_boundary_rows(self):
        cases = (('edge', 2, (3,), 1), ('three-vertex path', 3, (3, 6), 2),
                 ('matching', 4, (3, 12), 3), ('triangle', 3, (3, 5, 6), 4),
                 ('four-vertex path', 4, (3, 6, 12), 4))
        for name, n, masks, minimum in cases:
            with self.subTest(graph=name):
                pos, neg = cs.boundary_rows(n, masks)
                labels = {**dict.fromkeys(pos, True), **dict.fromkeys(neg, False)}
                self.assertIsNone(find_with_budget(n, labels, minimum - 1))
                solution = find_with_budget(n, labels, minimum)
                self.assertIsNotNone(solution)
                self.assertTrue(all(solution.evaluate(row) == any(row & edge == edge for edge in masks)
                                    for row in range(1 << n)))

    def test_existing_regional_circuits_survive_from_boundary_rows(self):
        rng = Random(71)
        for _ in range(30):
            n = rng.randint(3, 4)
            groups = random_groups(n, 2, rng)
            table, ports = random_circuit(n, groups, rng)
            labels = {row: bool(table >> row & 1) for row in range(1 << n)}
            boundary = {row: high for row, high in labels.items()
                        if all(labels[row ^ (1 << i)] != high for i in range(n) if bool(row >> i & 1) == high)}
            solution = synthesize_regions(groups, ports, boundary, reader_limits=((2, 2),))
            self.assertIsNotNone(solution)
            self.assertTrue(all(solution.evaluate(row) == target for row, target in labels.items()))


if __name__ == '__main__':
    unittest.main()
