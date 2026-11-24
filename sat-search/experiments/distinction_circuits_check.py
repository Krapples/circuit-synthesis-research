"""Independent small-circuit and relocation checks for the distinction-grid reduction."""

from collections import Counter
from functools import reduce
from itertools import combinations
from operator import or_
from random import Random
import unittest

import antichain_search as ac
from distinction_circuits import (_core_input_sets, _cover_size, _fringe_patterns, _match_requests, _request_candidates,
                                  certificate_requirements, minimum_partial_circuit)
from distinction_rectangles import _matching_endpoints, _rectangles, minimum_partial_formula
from regional_synthesis import _bits


def signal_tables(width):
    return tuple(sum(1 << row for row in range(1 << width) if row >> i & 1) for i in range(width))


def exact_by_gate_sets(columns, target, upper):
    states = {frozenset(columns)}
    for cost in range(upper + 1):
        if any(target in state for state in states):
            return cost
        if cost < upper:
            states = {state | {gate} for state in states for a, b in combinations(state, 2)
                      for gate in (a & b, a | b) if gate not in state}
    return None


class DistinctionCircuitChecks(unittest.TestCase):
    def test_certificate_intersections_on_random_circuits(self):
        rng = Random(31415)
        counts = Counter()
        for _ in range(300):
            width = rng.randint(2, 6)
            gates = tuple((rng.randrange(2), *rng.sample(range(index), 2))
                          for index in range(width, width + rng.randint(1, 11)))
            circuit = ac.Circuit(width, gates, width + len(gates) - 1)
            cone = {circuit.output}
            for index in range(circuit.output, width - 1, -1):
                if index in cone:
                    cone.update(gates[index - width][1:])
            excess = sum(index >= width for index in cone) - sum(index < width for index in cone) + 1
            p = sum(1 << row for row in range(1 << width) if circuit.evaluate(row))
            n = ((1 << (1 << width)) - 1) ^ p
            columns = signal_tables(width)
            requirements = certificate_requirements(circuit, columns, p, n)
            for col, (ones, zeros) in zip(columns, requirements):
                self.assertFalse(ones & ~col or zeros & col)
            for a in _bits(p):
                for b in _bits(n):
                    common = sum(bool(ones & a and zeros & b) for ones, zeros in requirements)
                    self.assertTrue(1 <= common <= excess + 1)
                    counts['pairs'] += 1
            counts['shared'] += excess > 0
        print(f'certificate check: 300 circuits, {counts["shared"]} shared cones, {counts["pairs"]} pairs')

    def test_certificate_bound_is_attained(self):
        # (x0 AND x1 AND x2) OR (x1 OR x2), with a true certificate using the left branch.
        circuit = ac.Circuit(3, ((0, 0, 1), (0, 3, 2), (1, 1, 2), (1, 4, 5)), 6)
        p, n = 1 << 7, 1
        requirements = certificate_requirements(circuit, signal_tables(3), p, n)
        self.assertEqual(requirements, ((p, n),) * 3)

    def test_exact_mixed_queries_against_independent_gate_sets(self):
        rng = Random(4753)
        counts = Counter()
        for _ in range(150):
            rows, cols = rng.choice(((2, 2), (2, 3), (3, 2), (3, 3)))
            p = (1 << rows) - 1
            n = ((1 << cols) - 1) << rows
            columns = tuple(rng.sample(range(1 << (rows + cols)), rng.randint(3, 7)))
            separated = all(any(col & a and not col & b for col in columns) for a in _bits(p) for b in _bits(n))
            stats = Counter()
            result = minimum_partial_circuit(columns, p, n, stats=stats)
            expected = exact_by_gate_sets(columns, p, rows * cols - 1) if separated else None
            self.assertEqual(None if result is None else len(result.gates), expected, columns)
            if result is not None:
                self.check_witness(result, columns, p, n)
                counts['feasible'] += 1
                counts['reduced'] += bool(stats['deleted_cells'])
                distinctions = [sum(bool(col & a and not col & b) for col in columns)
                                for a in _bits(p) for b in _bits(n)]
                counts['overlapping'] += max(distinctions) > 1
        self.assertGreater(counts['reduced'], 0)
        print(f'gate-set comparison: 150 queries, {dict(counts)}')

    def test_padded_overlaps_against_independent_gate_sets(self):
        rng = Random(1164)
        checked = 0
        for _ in range(400):
            p, core_n = 3, rng.choice((12, 28))
            new_n = 1 << core_n.bit_length()
            original = tuple(rng.sample(range(new_n), 4))
            counts = [sum(bool(col & a and not col & b) for col in original)
                      for a in _bits(p) for b in _bits(core_n)]
            if not min(counts) or max(counts) == 1:
                continue
            columns = tuple(col | new_n for col in original) + (core_n | 1, core_n | 2)
            n = core_n | new_n
            stats = Counter()
            result = minimum_partial_circuit(columns, p, n, stats=stats)
            self.assertGreaterEqual(stats['deleted_cells'], 2)
            self.assertEqual(len(result.gates), exact_by_gate_sets(columns, p, 2 * n.bit_count() - 1))
            self.check_witness(result, columns, p, n)
            checked += 1
            if checked == 60:
                break
        self.assertEqual(checked, 60)

    def test_one_polarity_inputs_must_be_fixed_before_relocation(self):
        # Move the first positive row to the second. The old positive certificate uses x1.
        columns = (3, 5, 2)
        circuit = ac.Circuit(3, ((0, 0, 1), (1, 3, 2)), 4)
        self.assertEqual(certificate_requirements(circuit, columns, 1, 4), ((1, 4), (1, 0), (0, 4)))
        self.assertFalse(circuit.evaluate(1))  # Moved positive row if only x2 is fixed to zero.
        self.assertTrue(circuit.evaluate(3))   # Also fixing x1 to one preserves its certificate.
        self.assertFalse(circuit.evaluate(2))

    def test_homogeneous_labels_use_the_automatic_opposite_row(self):
        columns = (3, 6, 12)
        for p, n, table in ((15, 0, columns), (0, 15, tuple(15 ^ col for col in columns))):
            result = minimum_partial_circuit(table, p, n)
            self.assertEqual(len(result.gates), 1)
            self.check_witness(result, table, p, n)
        self.assertIsNone(minimum_partial_circuit((1, 2), 7, 0))
        self.assertEqual(minimum_partial_circuit((0,), 0, 0), ac.Circuit(1, (), 0))

    def test_lifting_a_large_singleton_grid_uses_no_recursion_on_deleted_rows(self):
        width = 1050
        columns = tuple(1 << i for i in range(width))
        result = minimum_partial_circuit(columns, (1 << width) - 1, 0)
        self.assertEqual(len(result.gates), width - 1)
        self.assertTrue(result.evaluate(1))
        self.assertTrue(result.evaluate(1 << (width - 1)))

    def test_capped_requests_can_share_a_column_without_sharing_an_owner(self):
        rectangles = [(3, 1, 0)]
        for i in range(2, 8):
            rectangles.append((1 | (1 << i), 1, i))
        for i in range(8, 14):
            rectangles.append((2 | (1 << i), 1, i))
        extra = 1 << 14
        rectangles.extend(((1 | extra, 1, 14), (2 | extra, 1, 15)))
        endpoints = _matching_endpoints(rectangles)
        self.assertEqual(endpoints, ((1, 1), (2, 1)))
        candidates = _request_candidates(_fringe_patterns(rectangles, 3, endpoints), 6)
        self.assertEqual(candidates[((1, 1), (1, 2))], [extra])

    def test_request_matching_reassigns_a_flexible_coordinate(self):
        flexible = ((4, 1),)
        constrained = ((4, 2),)
        candidates = {flexible: [8, 16], constrained: [8]}
        self.assertEqual(_match_requests([flexible, constrained], candidates), 24)
        self.assertIsNone(_match_requests([constrained, constrained], candidates))

    def test_representative_cap_on_a_large_overlapping_star(self):
        p, n = (1 << 11) - 1, 7 << 11
        single = tuple((1 << i) | (n ^ (1 << (11 + j))) for i in range(11) for j in range(3))
        double = tuple((1 | (1 << i)) | (n ^ (1 << 11)) for i in range(1, 11))
        columns = single + double
        stats = Counter()
        result = minimum_partial_circuit(columns, p, n, stats=stats)
        # At most one doubly covered pair can be saved, and a column-first formula attains it.
        self.assertEqual(ac.hitting_number(ac.frontier_demands(columns, p, n)), 32)
        self.assertEqual(len(result.gates), 31)
        self.assertEqual(stats, {'cores': 1, 'deleted_cells': 27})
        self.check_witness(result, columns, p, n)

    def test_searches_multiple_maximal_candidate_cores(self):
        p, n = (1 << 9) - 1, 1 << 9
        columns = (3,) + tuple(1 | (1 << i) for i in range(2, 9)) + (2 | (1 << 8),)
        # Saving two cells needs the late row, which can pair with either marked row.
        stats = Counter()
        result = minimum_partial_circuit(columns, p, n, stats=stats)
        self.assertEqual(stats, {'cores': 2, 'deleted_cells': 2})
        self.assertEqual(len(result.gates), 6)
        cover = next(size for size in range(1, len(columns) + 1)
                     if any(reduce(or_, subset) == p for subset in combinations(columns, size)))
        self.assertEqual(len(result.gates), cover - 1)
        self.check_witness(result, columns, p, n)

    def test_core_input_sets_try_multiple_exceptional_owner_choices(self):
        columns = (1, 2, 4, 3, 5, 6, 7)
        canonical = {1, 2, 4}
        endpoints = ((1, 8), (2, 8))
        choices = list(_core_input_sets(columns, canonical, endpoints, limit=2))
        self.assertEqual(len(choices), 6)
        self.assertTrue(all(canonical.issubset(support) and len(support) == 5 for support in choices))
        self.assertTrue(any(exact_by_gate_sets(support, 7, 0) == 0 for support in choices))

    def test_cover_search_accounts_for_optional_owners_of_outside_cells(self):
        mixed_choices = ((3, 16, 0), (5, 16, 1), (6, 16, 2), (9, 16, 3), (10, 16, 4))
        endpoints = _matching_endpoints(mixed_choices)
        self.assertEqual(endpoints, ((1, 16), (2, 16)))
        self.assertEqual(_cover_size(mixed_choices, endpoints), 2)

        all_marked = ((1, 12, 0), (2, 12, 1))
        self.assertEqual(_cover_size(all_marked, _matching_endpoints(all_marked)), 2)

    def test_canonical_with_exceptional_inputs_preserves_small_optima(self):
        rng = Random(4170)
        tested = 0
        for _ in range(180):
            p, n = 7, 56
            cols = tuple(rng.sample(range(1, 63), 6))
            cells = {(a, b): next((col for col in cols if col & a and not col & b), None)
                     for a in _bits(p) for b in _bits(n)}
            if None in cells.values():
                continue
            minimum = exact_by_gate_sets(cols, p, 8)
            required = ac.hitting_number(ac.frontier_demands(cols, p, n))
            rectangles = _rectangles(cols, p, n)
            endpoints = _matching_endpoints(rectangles)
            self.assertEqual(_cover_size(rectangles, endpoints), required)
            limit = len(endpoints) * (minimum - required + 2)
            supports = _core_input_sets(cols, set(cells.values()), endpoints, limit)
            self.assertTrue(any(exact_by_gate_sets(support, p, minimum) == minimum for support in supports))
            tested += 1
        self.assertGreaterEqual(tested, 50)
        print(f'canonical input and marked-cell cover checks: {tested} feasible grids')

    def test_padded_overlap_with_pooled_sharing(self):
        # Two pinwheels cost ten gates with pooled wires. Supply one pooled wire as an extra input.
        tiles = ((1, 3), (3, 4), (4, 6), (6, 1), (2, 2))
        columns = tuple((rows << (3 * i)) | ((15 ^ cols) << 6) for i in range(2) for rows, cols in tiles)
        columns += (columns[4] | columns[9],)
        # Each positive has a private distinguishing input against the added negative row.
        columns += tuple(448 | (1 << i) for i in range(6))
        p, n = 63, 15 << 6
        stats = Counter()
        result = minimum_partial_circuit(columns, p, n, stats=stats)
        self.assertEqual(stats, {'cores': 1, 'deleted_cells': 6})
        self.assertEqual(ac.hitting_number(ac.frontier_demands(columns, p, n)), 15)
        self.assertEqual(len(result.gates), 15)  # Nine for the overlapping core plus six mandatory padding gates.
        self.assertEqual(minimum_partial_formula(columns, p, n)[0], 17)
        self.check_witness(result, columns, p, n)

    def check_witness(self, circuit, columns, p, n):
        for row in _bits(p | n):
            assignment = sum(1 << i for i, col in enumerate(columns) if col & row)
            self.assertEqual(circuit.evaluate(assignment), bool(p & row))


if __name__ == '__main__':
    unittest.main()
