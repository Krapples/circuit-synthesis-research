"""Regression checks for the monotone partial-prefix bound and its integration."""

from collections import Counter
from itertools import combinations
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import cube_search as cs
import l1343_full as shard
from partial_ordered import forced_empty_regions, minimum_ordered_groups, monotone_closure, projected_suffix_bounds
from partial_ordered import suffix_projections


SEED = ((1, 6, 9), (1, 7, 10), (0, 11, 12))


class PartialOrderedChecks(unittest.TestCase):
    def test_monotone_closure_and_conflict(self):
        ones, zeros = monotone_closure(3, (1,), (2,))
        self.assertEqual(ones, sum(1 << x for x in (1, 3, 5, 7)))
        self.assertEqual(zeros, sum(1 << x for x in (0, 2)))
        self.assertIsNone(minimum_ordered_groups(3, (1,), (3,)))

    def test_shard_seed_projections(self):
        expected = [(6992, [(13, 18)]), (13709, [(12, 19), (13, 19), (13, 19), (14, 20)])]
        for length, (closure_count, bounds) in enumerate(expected, 2):
            mandatory, positives, negatives = cs.prefix_boundary(shard.n, tuple(shard.MASKS), SEED[:length])
            width = shard.n + length
            ones, zeros = monotone_closure(width, positives, negatives)
            self.assertFalse(ones & zeros)
            self.assertEqual((ones | zeros).bit_count(), closure_count)
            cases = list(projected_suffix_bounds(width, mandatory, positives, negatives))
            self.assertEqual([(used.bit_count(), length + bound) for used, bound in cases], bounds)
            for used, _ in cases:
                self.assertEqual(used & ((1 << shard.n) - 1), (1 << shard.n) - 1)

    def test_forced_repeat_distribution(self):
        projections = cs.repeat_prefix_projections(shard.n, tuple(shard.MASKS), SEED)
        projection = next(p for p in projections if len(p.bits) == 12)
        features = [bit.bit_length() - 1 for bit in projection.bits]
        repeats, bounds = Counter(), Counter()
        for left, right in combinations(features, 2):
            for op in (0, 1):
                forced = projection.forced_repeats((op, left, right))
                repeats[forced.bit_count()] += 1
                bounds[len(SEED) + projection.binary_bound(forced)] += 1
        self.assertEqual(repeats, {0: 5, 1: 18, 2: 109})
        self.assertEqual(bounds, {19: 74, 20: 53, 21: 5})

    def test_reader_multiplicity_distribution(self):
        width = shard.n + len(SEED)
        projections = cs.repeat_prefix_projections(shard.n, tuple(shard.MASKS), SEED)
        projection = next(p for p in projections if len(p.bits) == 12)
        features = [bit.bit_length() - 1 for bit in projection.bits] + [width]
        singleton, multiple, gains = Counter(), Counter(), Counter()
        for left, right in combinations(features, 2):
            if (right, left) <= (2, 0):
                continue
            for op in (0, 1):
                gates = ((1, 0, 2), (op, left, right))
                _, readers = projection.pinned_readers(width, gates)
                repeated = sum(1 << i for i, count in enumerate(readers[:12]) if count >= 2)
                old = len(SEED) + projection.binary_bound(repeated)
                new = len(SEED) + projection.multiplicity_bound(width, gates)
                singleton[old] += 1
                multiple[new] += 1
                gains[new - old] += 1
        self.assertEqual(singleton, {19: 56, 20: 79, 21: 17})
        self.assertEqual(multiple, {19: 42, 20: 78, 21: 32})
        self.assertEqual(gains, {0: 123, 1: 29})

    def test_after_projection_forces_third_internal_reader_and_empty_region(self):
        gates = ((1, 0, 1), (0, 0, 2), (0, 1, 3), (1, 3, 4))
        circuit = gates + ((1, 3, 5), (1, 6, 7))
        positives = tuple(x for x in range(8) if cs.evaluate(3, circuit, x))
        negatives = tuple(x for x in range(8) if x not in positives)
        projection, = suffix_projections(3, 7, positives, negatives)
        after = (1 << 3) | (1 << 5) | (1 << 6)
        dense, readers = projection.pinned_readers(3, gates, after)
        self.assertEqual(readers, [2, 2, 1, 3, 1, 1, 1])
        self.assertEqual(forced_empty_regions(3, dense, readers), 1)
        self.assertEqual(projection.multiplicity_bound(3, gates, empty=True), 5)
        self.assertEqual(projection.multiplicity_bound(3, gates, after, empty=True), 6)

    def test_size_19_repeat_bound_across_all_projections(self):
        counts, rejected = Counter(), set()
        for case, _, gate, args in shard.tasks_for(19):
            prefix = SEED if case == 'a' else SEED[:2]
            bound = cs.partial_repeat_bound(shard.n, tuple(shard.MASKS), prefix, gate)
            counts[case, bound] += 1
            if bound > args[2] and case not in rejected:
                _, status, _, _, stats = cs.run_cube((*args[:7], {**args[7], 'partialrepeat': True}))
                self.assertEqual(status, 'UNSAT')
                self.assertIn('analytical: partial repeat', stats)
                rejected.add(case)
        self.assertEqual(rejected, {'a', 'b'})
        self.assertEqual(counts, {('a', 19): 104, ('a', 20): 73, ('a', 21): 5,
                                  ('b', 18): 72, ('b', 19): 75, ('b', 20): 9})

    def test_extended_bound_runs_after_repeat_bound(self):
        gate = (0, 0, 1)
        self.assertEqual(cs.partial_repeat_bound(shard.n, tuple(shard.MASKS), SEED, gate), 19)
        args = next(args for case, _, piece, args in shard.tasks_for(19) if case == 'a' and piece == gate)
        flags = {**args[7], 'partialrepeat': True, 'partialordered': True}
        _, status, _, _, stats = cs.run_cube((*args[:7], flags))
        self.assertEqual(status, 'UNSAT')
        self.assertIn('analytical: partial ordered', stats)

    def test_size_18_driver_pieces(self):
        tasks = shard.tasks_for(18)
        self.assertEqual(len(tasks), 338)
        for case, _, piece, args in tasks:
            _, status, _, _, stats = cs.run_cube((*args[:7], {**args[7], 'partialordered': True}))
            with self.subTest(case=case, piece=piece):
                self.assertEqual(status, 'UNSAT')
                self.assertIn('analytical: partial ordered', stats)

    def test_known_circuit_prefixes_survive(self):
        masks = (3, 6, 12)
        circuit = ((0, 0, 1), (1, 1, 3), (0, 2, 5), (1, 4, 6))
        for length in range(1, len(circuit)):
            fixed = [(i, *circuit[i]) for i in range(1, length)]
            flags = dict(nonot=True, partialordered=True, partialrepeat=True, partialmultiplicity=True,
                         partialempty=True, coupledprojections=True, frontier=True, cert=True,
                         reuse=True, colex_from=length, fixgates=fixed)
            _, status, witness, _, _ = cs.run_cube((4, masks, 4, 'maplechrono', circuit[0], False, False, flags))
            self.assertEqual(status, 'WITNESS')
            self.assertEqual(tuple(witness[:length]), circuit[:length])
            for row in range(16):
                self.assertEqual(cs.evaluate(4, witness, row), any(row & m == m for m in masks))

    def test_cache_keys_include_live_costs_and_metadata(self):
        masks = (3, 6, 12)
        cs._SCACHE.clear()
        try:
            for costs in (cs.PortCosts({1: 0}), cs.PortCosts({1: 0}, mono=True),
                          cs.PortCosts({1: 0}, mono=True, pout={1: 0})):
                flags = dict(nonot=True, reuse=True, portcosts=costs)
                args = (4, masks, 4, 'maplechrono', (0, 0, 1), False, False, flags)
                self.assertEqual(cs.run_cube(args)[1], 'WITNESS')
            self.assertEqual(len(cs._SCACHE), 3)
            costs[1] = 1
            self.assertEqual(cs.run_cube(args)[1], 'WITNESS')
            self.assertEqual(len(cs._SCACHE), 4)
        finally:
            cs._SCACHE.clear()

    def test_ordered_lookup_distinguishes_output_costs(self):
        costs = cs.PortCosts({1: 0}, mono=True, pout={1: 0})
        with patch.object(cs, 'ORDERED', [True]), patch.object(cs, '_ord_cache', {}), \
                patch.object(cs, '_port_binary_lb_unordered', return_value=0), \
                patch.object(cs, 'ordered_port_lb', side_effect=lambda terms, table, h: table.pout[1]) as ordered:
            self.assertEqual(cs.port_binary_lb((1,), costs), 0)
            equal = cs.PortCosts({1: 0}, mono=True, pout={1: 0})
            self.assertEqual(cs.port_binary_lb((1,), equal), 0)
            self.assertEqual(ordered.call_count, 1)
            costs.pout[1] = 1
            self.assertEqual(cs.port_binary_lb((1,), costs), 1)
            self.assertEqual(ordered.call_count, 2)


if __name__ == '__main__':
    unittest.main()
