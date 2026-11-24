"""Cross-check the tight-frontier coloring reduction and profile its applicability."""

from collections import Counter
from itertools import combinations
from pathlib import Path
from random import Random
import sys
import unittest

import antichain_search as ac
from regional_synthesis import _formulas
from synthesis_cases import boundary_labels
from synthesis_followup import load_cases, read_rows
from twocolor_completion import complete


RESULTS = Path(__file__).resolve().parents[1] / 'results'


def single_zero(width, edges):
    full = (1 << width) - 1
    return {**{full ^ (1 << i): True for i in range(width)}, **{full ^ edge: False for edge in edges}}


def columns(width, labels):
    return (tuple(sum(1 << x for x in labels if x >> i & 1) for i in range(width)),
            sum(1 << x for x in labels if labels[x]), sum(1 << x for x in labels if not labels[x]))


class TwoColorChecks(unittest.TestCase):
    def test_six_leaf_reduction_against_exhaustive_read_once_tables(self):
        width = 6
        full = (1 << width) - 1
        partners = tuple((1 << i) | (1 << (i + 3)) for i in range(3))
        extra = tuple(sum(1 << i for i in edge) for size in (2, 3)
                      for edge in combinations(range(width), size) if sum(1 << i for i in edge) not in partners)
        tables = _formulas(width, full)
        pos = sum(1 << (full ^ (1 << i)) for i in range(width))
        eligible = [table for table in tables if table & pos == pos]
        self.assertEqual((len(tables), len(eligible)), (5504, 3317))
        rng = Random(641)
        yes = 0
        for _ in range(200):
            edges = partners + tuple(rng.sample(extra, rng.randint(2, 10)))
            labels = single_zero(width, edges)
            cols, p, n = columns(width, labels)
            colorable = any(all(color & edge and ~color & edge for edge in edges) for color in range(full + 1))
            self.assertEqual(any(not table & n for table in eligible), colorable)
            self.assertEqual(ac.hitting_number(ac.frontier_demands(cols, p, n)), width)
            self.assertEqual(complete(cols, p, n)[0], 'sat' if colorable else 'unsat')
            yes += colorable
        print(f'Exhaustive six-leaf check: {yes} colorable and {200 - yes} uncolorable')

    def test_witness_and_unsat_paths_bypass_formula_width_cap(self):
        width = 12
        pairs = tuple((1 << i) | (1 << (i + 6)) for i in range(6))
        triangle = (3, 5, 6)
        for edges, answer in ((pairs, True), (pairs + triangle, False)):
            labels = single_zero(width, edges)
            stats = Counter()
            witness = ac.solve_partial(width, labels, width - 1, twocolorcompletion=True, stats=stats)
            self.assertEqual(witness is not None, answer)
            self.assertEqual(stats['twocolor_sat' if answer else 'twocolor_unsat'], 1)
            self.assertEqual(stats['formula_tests'], 0)
            if witness is not None:
                self.assertEqual(len(witness.gates), width - 1)
                self.assertTrue(all(witness.evaluate(row) == high for row, high in labels.items()))

    def test_extra_positive_rows_can_require_exact_fallback(self):
        labels = {row: bool(row) for row in range(8)}  # OR needs more than two monomials on three inputs
        self.assertEqual(complete(*columns(3, labels))[0], 'fallback')
        stats = Counter()
        witness = ac.solve_partial(3, labels, 2, twocolorcompletion=True, stats=stats)
        self.assertIsNotNone(witness)
        self.assertEqual(stats['twocolor_fallback'], 1)
        self.assertTrue(all(witness.evaluate(row) == high for row, high in labels.items()))

    def test_missing_single_zero_label_is_inapplicable(self):
        labels = {3: True, 5: True, 0: False}
        self.assertEqual(complete(*columns(3, labels)), ('inapplicable', None))

    def test_width_three_hardness_gadgets_preserve_satisfiability(self):
        clauses = tuple(tuple(i + 1 if mask >> i & 1 else -(i + 1) for i in range(3)) for mask in range(8))

        def bit(literal):
            return 1 << (2 * (abs(literal) - 1) + (literal < 0))

        for count, expected in ((7, True), (8, False)):
            variables = 4 + count  # three original variables, a reference color, and one per clause
            width = 2 * variables
            edges = {bit(i) | bit(-i) for i in range(1, variables + 1)}
            for aux, (x, y, z) in enumerate(clauses[:count], 5):
                edges.update((bit(x) | bit(y) | bit(aux), bit(-aux) | bit(z) | bit(4)))
            labels = single_zero(width, edges)
            p = [row for row in labels if labels[row]]
            n = [row for row in labels if not labels[row]]
            demands = {a & ~b for a in p for b in n}
            self.assertEqual(max(d.bit_count() for d in demands), 3)
            self.assertEqual(set(ac.minimal_demands(demands)), {1 << i for i in range(width)})
            witness = ac.solve_partial(width, labels, width - 1, twocolorcompletion=True)
            self.assertEqual(witness is not None, expected)
            if witness is not None:
                self.assertTrue(all(witness.evaluate(row) == high for row, high in labels.items()))


def profile(cases, path):
    """Replay completed E jobs with the new shortcut enabled."""
    jobs = [row for row in read_rows(path)
            if row['kind'] == 'job' and row['configuration'] == 'E' and row['status'] in ('SAT', 'UNSAT')]
    counts = Counter()
    applicable = 0
    for row in jobs:
        case = cases[row['case']]
        target = case.labels()
        labels = boundary_labels(case.n, target)
        stats = Counter()
        witness = ac.solve_partial(case.n, labels, row['budget'], sharing=1, nondegenerate=False,
                                   twocolorcompletion=True, stats=stats)
        if (witness is not None) != (row['status'] == 'SAT') or (witness is not None and (
                len(witness.gates) > row['budget'] or any(witness.evaluate(x) != y for x, y in target.items()))):
            raise RuntimeError(f"verdict or witness mismatch for {case.name} budget {row['budget']}")
        applicable += any(stats[f'twocolor_{key}'] for key in ('sat', 'unsat', 'fallback'))
        counts.update({key: count for key, count in stats.items() if key.startswith('twocolor_')})
    print(f'{path.name}: {len(jobs)} jobs, {applicable} with an eligible query, counts {dict(counts)}')


if __name__ == '__main__':
    if sys.argv[1:] == ['--profile']:
        cases = load_cases(RESULTS / 'synthesis_cases.json')
        for name in ('synthesis_endpoints.jsonl', 'synthesis_ablation.jsonl'):
            profile(cases, RESULTS / name)
    else:
        unittest.main()
