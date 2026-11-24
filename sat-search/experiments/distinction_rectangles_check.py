"""Verify the rectangular distinction criterion and its first obstruction."""

from collections import Counter
from functools import lru_cache
from functools import reduce
from operator import or_
from random import Random
import unittest

import antichain_search as ac
from distinction_rectangles import (_extend_grid, _rectangles, _reduce_grid, minimum_formula, minimum_partial_formula,
                                    singleton_padding_core, slicing_tree, unique_distinction_tree)
from regional_synthesis import _bits, synthesize_regions


def tilings(size):
    full = (1 << size) - 1
    rectangles = tuple((sum(1 << (i * size + j) for i in range(size) for j in range(size)
                            if rows >> i & cols >> j & 1), rows, cols)
                       for rows in range(1, full + 1) for cols in range(1, full + 1))

    def walk(cells):
        if not cells:
            yield ()
        first = cells & -cells
        for grid, rows, cols in rectangles:
            if grid & first and grid & cells == grid:
                for rest in walk(cells ^ grid):
                    yield ((rows, cols), *rest)

    return walk((1 << (size * size)) - 1)


def exact_leaf_count(size, rectangles):
    grid = {(i, j): color for color, (rows, cols) in enumerate(rectangles)
            for i in range(size) for j in range(size) if rows >> i & cols >> j & 1}

    @lru_cache(maxsize=None)
    def best(rows, cols):
        if len({grid[i, j] for i in rows for j in cols}) == 1:
            return 1
        costs = []
        for mask in range(1, (1 << len(rows)) - 1):
            a = tuple(i for k, i in enumerate(rows) if mask >> k & 1)
            b = tuple(i for k, i in enumerate(rows) if not mask >> k & 1)
            costs.append(best(a, cols) + best(b, cols))
        for mask in range(1, (1 << len(cols)) - 1):
            a = tuple(i for k, i in enumerate(cols) if mask >> k & 1)
            b = tuple(i for k, i in enumerate(cols) if not mask >> k & 1)
            costs.append(best(rows, a) + best(rows, b))
        return min(costs)

    indices = tuple(range(size))
    result = best(indices, indices)
    best.cache_clear()
    return result


class DistinctionRectangleChecks(unittest.TestCase):
    def test_all_three_by_three_tilings_against_exact_leaf_count(self):
        total = 0
        failures = Counter()
        for rects in tilings(3):
            rectangles = tuple((rows, cols, i) for i, (rows, cols) in enumerate(rects))
            count = exact_leaf_count(3, rects)
            expected = count == len(rects)
            tree, obstruction = slicing_tree(rectangles)
            self.assertEqual(tree is not None, expected, rects)
            self.assertEqual(minimum_formula(rectangles)[0], count, rects)
            if not expected:
                failures[9 - len(rects)] += 1
                self.assertEqual(sorted(rows.bit_count() * cols.bit_count() for rows, cols, _ in obstruction),
                                 [1, 2, 2, 2, 2])
            total += 1
        self.assertEqual(min(failures), 4)
        print(f'{total} tilings, nonseparable by savings: {dict(sorted(failures.items()))}')

    def test_pinwheel_forces_one_extra_gate(self):
        # Rows share the same unique owner precisely on each indicated rectangle.
        rects = ((1, 3), (3, 4), (4, 6), (6, 1), (2, 2))  # A, B, C, D, E
        cols = tuple(rows | ((7 ^ cols) << 3) for rows, cols in rects)
        status, obstruction = unique_distinction_tree(cols, 7, 56)
        self.assertEqual(status, 'unsat')
        self.assertEqual(len(obstruction), 5)
        self.assertEqual(exact_leaf_count(3, rects), 6)
        labels = {sum(1 << i for i, col in enumerate(cols) if col >> j & 1): j < 3 for j in range(6)}
        self.assertIsNone(synthesize_regions((31,), (0,), labels, formula_encoding='cograph'))
        self.assertIsNone(ac.solve_partial(5, labels, 4))
        witness = ac.solve_partial(5, labels, 5, sharing=1)
        self.assertIsNotNone(witness)
        self.assertEqual(len(witness.gates), 5)
        self.assertTrue(all(witness.evaluate(row) == high for row, high in labels.items()))

    def test_obstruction_certificate_discards_extra_rows_and_columns(self):
        core = ((1, 3), (3, 4), (4, 6), (6, 1), (2, 2))
        padding = tuple((1 << i, 1 << j) for i in range(5) for j in range(5) if i >= 3 or j >= 3)
        rectangles = tuple((rows, cols, i) for i, (rows, cols) in enumerate(core + padding))
        tree, obstruction = slicing_tree(rectangles)
        self.assertIsNone(tree)
        self.assertEqual(obstruction, rectangles[:len(core)])
        height, width = (reduce(or_, (rect[axis] for rect in obstruction)).bit_count() for axis in (0, 1))
        gap = height * width - len(obstruction)
        self.assertLessEqual(height + width, gap + 2)
        count, witness = minimum_formula(rectangles)
        self.assertEqual(count, len(rectangles) + 1)
        columns = tuple(rows | ((31 ^ cols) << 5) for rows, cols, _ in rectangles)
        steps = []
        self.assertEqual(ac._formula_steps(witness, columns, steps), 31)
        self.assertEqual(len(steps), count - 1)

        p, n, reduced = singleton_padding_core(rectangles)
        self.assertEqual((p, n, reduced), (7, 7, rectangles[:len(core)]))
        cells = {(row, col): leaf for rows, cols, leaf in rectangles for row in _bits(rows) for col in _bits(cols)}
        pinwheel = (1, (0, 1, (1, 0, (0, 3, 4))), (0, 3, 2))
        padded = _extend_grid(pinwheel, p, n, 31, 31, cells)
        steps = []
        self.assertEqual(ac._formula_steps(padded, columns, steps), 31)
        self.assertEqual(len(steps), 5 + len(padding))

    def test_sharing_overhead_does_not_add_across_row_components(self):
        copies = 3
        pos = (1 << (3 * copies)) - 1
        neg = 7 << (3 * copies)
        tiles = ((1, 3), (3, 4), (4, 6), (6, 1), (2, 2))
        columns = tuple((rows << (3 * i)) | ((7 ^ cols) << (3 * copies))
                        for i in range(copies) for rows, cols in tiles)
        status, _ = unique_distinction_tree(columns, pos, neg)
        self.assertEqual(status, 'unsat')
        self.assertEqual(ac.hitting_number(ac.frontier_demands(columns, pos, neg)), 5 * copies)
        steps, pooled = [], []
        for j in range(5):
            signal = columns[j]
            for i in range(1, copies):
                following = columns[5 * i + j]
                steps.append((1, signal, following, signal | following))
                signal |= following
            pooled.append(signal)
        pinwheel = (1, (0, 1, (1, 0, (0, 3, 4))), (0, 3, 2))
        self.assertEqual(ac._formula_steps(pinwheel, pooled, steps), pos)
        circuit = ac._reconstruct(columns, steps, pos)
        self.assertEqual(len(circuit.gates), 5 * copies)
        self.assertLess(len(circuit.gates), 6 * copies - 1)

    def test_reduction_preserves_formula_and_cover_savings(self):
        rng = Random(4178)
        for _ in range(120):
            columns = tuple(rng.sample(range(64), rng.randint(3, 15)))
            p, n = 7, 56
            leaves = [set(), set(columns)]
            seen = set(columns)
            expected = 1 if p in seen else None
            for cost in range(2, 10):
                if expected is not None:
                    break
                fresh = {value for lower in range(1, cost // 2 + 1)
                         for a in leaves[lower] for b in leaves[cost - lower] for value in (a & b, a | b)} - seen
                if p in fresh:
                    expected = cost
                leaves.append(fresh)
                seen.update(fresh)
            answer = minimum_partial_formula(columns, p, n)
            self.assertEqual(None if answer is None else answer[0], expected, columns)
            if answer is not None:
                cost, tree = answer
                steps = []
                self.assertEqual(ac._formula_steps(tree, columns, steps), p)
                self.assertEqual(len(steps), cost - 1)
                a, b = _reduce_grid(_rectangles(columns, p, n), p, n)
                k = ac.hitting_number(ac.frontier_demands(columns, p, n))
                small = ac.hitting_number(ac.frontier_demands(columns, a, b))
                self.assertEqual(9 - k, a.bit_count() * b.bit_count() - small)

    def test_many_rows_with_the_same_nontrivial_request(self):
        p, n = (1 << 11) - 1, 7 << 11
        singleton = tuple((1 << i) | (n ^ (1 << (11 + j))) for i in range(11) for j in range(3))
        overlapping = tuple((1 | (1 << i)) | (n ^ (1 << 11)) for i in range(1, 11))
        columns = singleton + overlapping
        a, b = _reduce_grid(_rectangles(columns, p, n), p, n)
        self.assertEqual((a.bit_count(), b.bit_count()), (4, 1))
        cost, tree = minimum_partial_formula(columns, p, n)
        self.assertEqual(cost, 32)
        steps = []
        self.assertEqual(ac._formula_steps(tree, columns, steps), p)
        self.assertEqual(len(steps), 31)


if __name__ == '__main__':
    unittest.main()
