"""Checks for the benchmark corpus, direct SAT reference, and certified intervals."""

from collections import Counter
from itertools import combinations
import unittest

from synthesis_bench import direct_sat, interval, isolated
from synthesis_cases import boundary_labels, corpus, essential, full_rows, truth_table


def reachable(n, limit, allow_not):
    universe = full_rows(n)
    inputs = frozenset(sum(1 << x for x in range(1 << n) if x >> i & 1) for i in range(n))
    states = {inputs}
    values = set(inputs)
    for _ in range(limit):
        following = set()
        for state in states:
            found = {y for a, b in combinations(state, 2) for y in (a & b, a | b)}
            if allow_not:
                found.update(universe ^ x for x in state)
            values.update(found)
            following.update(state | {x} for x in found)
        states = following
    return values


class BenchmarkChecks(unittest.TestCase):
    def test_corpus_is_unique_complete_and_partially_labeled(self):
        cases = corpus()
        self.assertEqual(len(cases), 100)
        self.assertEqual(len({c.name for c in cases}), 100)
        self.assertEqual(len({(c.n, c.known, c.truth) for c in cases}), 100)
        self.assertEqual(Counter(c.family for c in cases),
                         dict(hypergraph=24, graph=14, generated=12, threshold=10, comparator=10,
                              partial=10, **{'random-monotone': 10, 'read-once': 10}))
        for case in cases:
            self.assertEqual(truth_table(case.n, case.witness) & case.known, case.truth)
            self.assertEqual(essential(case.n, case.labels()), case.n)
            self.assertEqual(case.known == full_rows(case.n), case.family != 'partial')
            if case.family == 'hypergraph':
                self.assertTrue(all(row.bit_count() == 3 for row, high in boundary_labels(case.n, case.labels()).items()
                                    if high))
            if case.family == 'threshold':
                level = int(case.name.rsplit('-', 1)[1])
                self.assertTrue(all(high == (row.bit_count() >= level) for row, high in case.labels().items()))

    def test_direct_sat_against_exhaustive_small_circuits(self):
        n = 2
        for budget in range(4):
            for allow_not in (False, True):
                reference = reachable(n, budget, allow_not)
                for values in range(16):
                    labels = {row: bool(values >> row & 1) for row in range(4)}
                    witness = direct_sat(n, labels, budget, allow_not)
                    self.assertEqual(witness is not None, values in reference, (values, budget, allow_not))
                    if witness is not None:
                        self.assertLessEqual(len(witness.gates), budget)
                        self.assertEqual(truth_table(n, witness), values)

    def test_not_enabled_uses_unreduced_labels(self):
        # XOR agrees with OR's monotone boundary, but NOT allows it to fail the omitted row.
        labels = {row: bool(row) for row in range(4)}
        boundary = boundary_labels(2, labels)
        self.assertNotIn(3, boundary)
        self.assertTrue(all((x.bit_count() == 1) == val for x, val in boundary.items()))
        self.assertNotEqual(labels[3], (3).bit_count() == 1)

    def test_timeouts_do_not_move_a_certificate(self):
        evidence = [(3, {'status': 'UNSAT'}), (4, {'status': 'TIMEOUT'}), (6, {'status': 'SAT', 'gates': 5})]
        self.assertEqual(interval(evidence, 3, 9), dict(lower=4, upper=5, minimum=None))

    def test_worker_returns_memory_and_verified_witness(self):
        item = next(c for c in corpus() if c.name == 'hypergraph-01')
        result = isolated(item, 'E', 'mono', len(item.witness.gates), {}, 4)
        self.assertEqual(result['status'], 'SAT')
        self.assertTrue(result['verified'])
        self.assertGreater(result['peak_bytes'], 0)


if __name__ == '__main__':
    unittest.main()
