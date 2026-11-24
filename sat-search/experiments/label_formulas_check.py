"""Known-answer checks and archived-job replay for label-driven completion."""

from collections import Counter
from pathlib import Path
from random import Random
import sys
from time import perf_counter
import unittest

import antichain_search as ac
from label_formulas import obligation_tree
from regional_search import _known_formulas
from regional_synthesis import _formulas
from subtree_formulas import _prepared_cuts, constrained_formulas, forced_by_outside, subtree_possible
from synthesis_cases import boundary_labels
from synthesis_followup import load_cases, read_rows


RESULTS = Path(__file__).resolve().parents[1] / 'results'


def query(width, positives, negatives):
    rows = set(positives) | set(negatives)
    return (tuple(sum(1 << row for row in rows if row >> i & 1) for i in range(width)),
            sum(1 << row for row in positives), sum(1 << row for row in negatives))


def partial_queries():
    rng = Random(20261124)
    for width in (4, 5, 6):
        for _ in range(300):
            rows = range(1 << width)
            terms = rng.sample(range(1, 1 << width), rng.randint(2, 2 * width))
            selected = rng.sample(rows, rng.randint(4, min(len(rows), 4 * width)))
            p = [row for row in selected if any(row & term == term for term in terms)]
            n = [row for row in selected if row not in p]
            yield width, query(width, p, n)


class LabelFormulaChecks(unittest.TestCase):
    def test_five_leaf_counterexample(self):
        positives, negatives = (3, 14, 20, 24, 27, 29, 30), (4, 5, 9, 17, 18)
        cols, p, n = query(5, positives, negatives)
        self.assertTrue(subtree_possible(cols, p, n))
        self.assertIsNone(obligation_tree(cols, p, n, exact=False))
        self.assertIsNone(obligation_tree(cols, p, n, exact=True))
        stats = Counter()
        labels = {**dict.fromkeys(positives, True), **dict.fromkeys(negatives, False)}
        self.assertIsNone(ac.solve_partial(5, labels, 4, typedsubtreecuts=True, stats=stats))
        self.assertEqual(stats['typed_subtree_rejections'], 1)

    def test_exact_and_relaxed_against_exhaustive_formulas(self):
        totals = Counter()
        for width, (cols, p, n) in partial_queries():
            full = (1 << width) - 1
            exists = any(table & p == p and not table & n for table in _formulas(width, full))
            formula = obligation_tree(cols, p, n, exact=True)
            self.assertEqual(formula is not None, exists, (width, p, n))
            structural = subtree_possible(cols, p, n)
            typed = obligation_tree(cols, p, n, exact=False) is not None
            totals['cases'] += 1
            totals['original exclusions'] += not structural
            totals['additional typed exclusions'] += structural and not typed
            totals['remaining exact exclusions'] += structural and typed and not exists
            if formula is not None:
                steps = []
                self.assertEqual(ac._formula_steps(formula, cols, steps), p)
                self.assertEqual(len(steps), width - 1)
                self.assertTrue(structural and typed)
        print(dict(totals))

    def test_duplicate_occurrences_and_homogeneous_labels(self):
        cases = ((1, 2, True), (1, 0, True), (0, 2, True), (2, 0, False), (0, 1, False))
        for p, n, answer in cases:
            cols = (1, 1, 1)
            tree = obligation_tree(cols, p, n, exact=True)
            self.assertEqual(tree is not None, answer)
            if tree is not None:
                steps = []
                self.assertEqual(ac._formula_steps(tree, cols, steps) & (p | n), p)
                self.assertEqual(len(steps), 2)

    def test_ambiguous_rows_can_require_exact_search(self):
        cols, p, n = query(6, (19, 38, 50, 52), (11, 25, 26, 41))
        self.assertTrue(subtree_possible(cols, p, n))
        self.assertIsNotNone(obligation_tree(cols, p, n, exact=False))
        self.assertIsNone(obligation_tree(cols, p, n, exact=True))
        self.assertFalse(any(table & p == p and not table & n for table in _formulas(6, 63)))

    def test_row_product_gate_bound_is_attained(self):
        positives, negatives = 2, 3
        width = positives * negatives
        full = (1 << width) - 1
        p = [sum(1 << (i * negatives + j) for j in range(negatives)) for i in range(positives)]
        n = [full ^ sum(1 << (i * negatives + j) for i in range(positives)) for j in range(negatives)]
        cols, high, low = query(width, p, n)
        self.assertEqual(ac.hitting_number(ac.frontier_demands(cols, high, low)), width)
        labels = {**dict.fromkeys(p, True), **dict.fromkeys(n, False)}
        self.assertIsNone(ac.solve_partial(width, labels, width - 2))
        witness = ac.solve_partial(width, labels, width - 1, typedsubtreecuts=True, labelcompletion=True)
        self.assertIsNotNone(witness)
        self.assertEqual(len(witness.gates), width - 1)
        self.assertTrue(all(witness.evaluate(row) == target for row, target in labels.items()))


def profile():
    cases = load_cases(RESULTS / 'synthesis_cases.json')
    jobs = [(path, row) for path in ('synthesis_endpoints.jsonl', 'synthesis_ablation.jsonl')
            for row in read_rows(RESULTS / path) if row['kind'] == 'job' and row['configuration'] == 'E'
            and row['status'] in ('SAT', 'UNSAT')]
    for typed, exact in ((False, False), (True, False), (False, True), (True, True)):
        for cached in (_known_formulas, _prepared_cuts, constrained_formulas, forced_by_outside, obligation_tree,
                       ac.hitting_number):
            cached.cache_clear()
        seconds = Counter()
        counts = {path: Counter() for path, _ in jobs}
        for path, row in jobs:
            case = cases[row['case']]
            target = case.labels()
            labels = boundary_labels(case.n, target)
            stats = Counter()
            started = perf_counter()
            witness = ac.solve_partial(case.n, labels, row['budget'], sharing=1, nondegenerate=False,
                                       typedsubtreecuts=typed, labelcompletion=exact, stats=stats)
            seconds[path] += perf_counter() - started
            if (witness is not None) != (row['status'] == 'SAT') or (witness is not None and (
                    len(witness.gates) > row['budget'] or any(witness.evaluate(x) != y for x, y in target.items()))):
                raise RuntimeError(f"verdict or witness mismatch for {case.name} budget {row['budget']}")
            stats['jobs'] = 1
            counts[path].update(stats)
        for path, count in counts.items():
            fields = ('jobs', 'output_subtree_rejections', 'typed_subtree_tests', 'typed_subtree_rejections',
                      'label_completion_tests', 'distinct_formula_enumerations')
            print(path, f'typed={typed} exact={exact} seconds={seconds[path]:.3f}',
                  {key: count[key] for key in fields}, flush=True)


if __name__ == '__main__':
    if sys.argv[1:] == ['--profile']:
        profile()
    else:
        unittest.main()
