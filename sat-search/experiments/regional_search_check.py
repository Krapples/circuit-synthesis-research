"""Dominance, reader-capacity, and exact-minimum regression tests."""

from itertools import combinations
from random import Random
import unittest
from unittest.mock import patch

import regional_search as rs
from regional_synthesis import synthesize_regions
import cube_search as cs
import l1343_full as shard


class RegionalSearchChecks(unittest.TestCase):
    def test_recursive_frontier_equals_posthoc_pruning(self):
        rng = Random(718)
        for width in range(2, 7):
            for _ in range(12):
                columns = tuple(rng.getrandbits(13) for _ in range(width))
                negative = rng.getrandbits(13)
                full = rs.known_formulas(columns, negative, prune=False)
                frontier = rs.known_formulas(columns, negative)
                self.assertEqual(frontier.keys(), rs.pareto(full, negative).keys())

    def test_shard_boundary_sample(self):
        seed = ((1, 6, 9), (1, 7, 10), (0, 11, 12))
        _, pos, neg = cs.prefix_boundary(shard.n, tuple(shard.MASKS), seed)
        rows = pos + neg
        negative = ((1 << len(rows)) - 1) ^ ((1 << len(pos)) - 1)
        columns = tuple(sum(1 << i for i, row in enumerate(rows) if row >> feature & 1)
                        for feature in range(shard.n + len(seed)))
        rng = Random(20261124)
        for width, expected in ((4, (3713, 1569)), (5, (20226, 3658)), (6, (99964, 7047))):
            raw = kept = 0
            for leaves in rng.sample(list(combinations(range(len(columns)), width)), 100):
                selected = tuple(columns[i] for i in leaves)
                full = rs.known_formulas(selected, negative, prune=False)
                frontier = rs.known_formulas(selected, negative)
                self.assertEqual(frontier.keys(), rs.pareto(full, negative).keys())
                raw += len(full)
                kept += len(frontier)
            self.assertEqual((raw, kept), expected)

    def test_matching_observes_reader_minimum_and_capacity(self):
        weaker = ((1, 1, 1), (2, 0, 2))
        self.assertTrue(rs.covers_state(((3, 0, 2), (1, 1, 1)), weaker, 0))
        self.assertFalse(rs.covers_state(((3, 1, 2), (1, 1, 1)), weaker, 0))
        self.assertFalse(rs.covers_state(((3, 0, 1), (1, 1, 1)), weaker, 0))
        self.assertTrue(rs.dominates(1, 3, 2))
        self.assertFalse(rs.dominates(3, 1, 2))

    def test_forward_modes_agree_with_symbolic_linking_on_partial_rows(self):
        rng = Random(117)
        for _ in range(32):
            n = 4
            assign = rng.sample(range(n), n)
            groups = ((1 << assign[0]) | (1 << assign[1]), 1 << assign[2], 1 << assign[3])
            ports = (0, rng.randint(0, 2), rng.randint(1, 3))
            limits = tuple((rng.randint(0, 1), rng.randint(1, 3)) for _ in range(2))
            masks = rng.sample(tuple(a | b for a, b in combinations((1, 2, 4, 8), 2)), rng.randint(1, 5))
            labels = {row: any(row & mask == mask for mask in masks) for row in rng.sample(range(16), 9)}
            expected = synthesize_regions(groups, ports, labels, reader_limits=limits) is not None
            for prune, matching in ((False, False), (True, False), (True, True)):
                solution = rs.synthesize_forward(groups, ports, labels, reader_limits=limits,
                                                 prune=prune, state_dominance=matching)
                self.assertEqual(solution is not None, expected, (groups, ports, limits, labels))
                if solution is not None:
                    self.assertTrue(all(solution.evaluate(row) == target for row, target in labels.items()))

    def test_minimum_modes_and_gate_usefulness(self):
        self.assertTrue(rs.useful_gate(0, 1, 2, 0, 3))
        self.assertFalse(rs.useful_gate(0, 1, 3, 0, 3))
        self.assertTrue(rs.useful_gate(1, 1, 2, 3, 0))
        self.assertFalse(rs.useful_gate(1, 1, 3, 3, 0))
        masks = (3, 6, 12, 24)
        pos, neg = cs.boundary_rows(5, masks)
        labels = {**dict.fromkeys(pos, True), **dict.fromkeys(neg, False)}
        for useful in (False, True):
            size, solution = rs.find_minimum(5, labels, 5, useful=useful)
            self.assertEqual(size, 5)
            self.assertTrue(all(solution.evaluate(row) == any(row & mask == mask for mask in masks)
                                for row in range(32)))

    def test_unsupported_width_is_inconclusive(self):
        labels = {row: row == 7 for row in range(8)}
        with patch.object(rs, 'MAX_KNOWN_LEAVES', 2):
            with self.assertRaises(NotImplementedError):
                rs.find_minimum(3, labels, 2)


if __name__ == '__main__':
    unittest.main()
