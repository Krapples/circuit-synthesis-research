"""Validate the reference SAT backend against brute-force enumeration, and the input contracts.

Exhaustive: every monotone function of n <= 3 inputs (all antichains), plus every 4-input graph function,
for G = 1..4 (n <= 3) / 3..4 (n = 4), both bases, with and without every-wire-read, and with every
one-gate prefix. Run: python verify/test_reference.py"""
import os, sys, time, unittest
from itertools import combinations
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import reference as ref


def antichains(n):
    subsets = list(range(1, 1 << n))
    out = set()
    for k in range(1, len(subsets) + 1):
        for fam in combinations(subsets, k):
            out.add(ref.normalize_terms(n, fam))
    return sorted(out)


class Contracts(unittest.TestCase):
    def test_graph_terms(self):
        self.assertEqual(ref.graph_terms(3, [(0, 1), (1, 0), (0, 1), (1, 2)]), (3, 6))
        with self.assertRaises(ValueError):
            ref.graph_terms(3, [(1, 1)])
        with self.assertRaises(ValueError):
            ref.graph_terms(3, [(0, 3)])
        with self.assertRaises(ValueError):
            ref.graph_terms(3, [])

    def test_normalize_terms(self):
        self.assertEqual(ref.normalize_terms(3, [3, 7, 3, 6]), (3, 6))
        for bad in ([0], [8], [-1]):
            with self.assertRaises(ValueError):
                ref.normalize_terms(3, bad)


class SatAgainstBrute(unittest.TestCase):
    def compare(self, n, terms, Gs, prefixes):
        tt = ref.truth_table(n, terms)
        for basis in ('monotone', 'general'):
            for all_read in (True, False):
                for G in Gs:
                    for prefix in prefixes:
                        b = ref.brute_exists(n, tt, G, basis, prefix, all_read)
                        s, _ = ref.sat_exists(n, tt, G, basis, prefix, all_read)
                        if b is not None:
                            self.assertTrue(ref.check_witness(n, tt, b, prefix, all_read, basis))
                        self.assertEqual(b is None, s is None,
                                         (n, terms, G, basis, prefix, all_read, b, s))
                        self.count += 1

    def test_all_small(self):
        self.count = 0
        t0 = time.time()
        for n in (1, 2, 3):
            pre = [()] + [(g,) for g in ref.options(n, 'monotone')]
            for terms in antichains(n):
                self.compare(n, terms, range(1, 6) if n < 3 else range(1, 5), pre)
        print(f'\n  n<=3: {self.count} (function, G, basis, prefix, all_read) cases agree ({time.time() - t0:.0f}s)')

    def test_graphs4(self):
        self.count = 0
        t0 = time.time()
        pairs = list(combinations(range(4), 2))
        seen = set()
        for k in range(1, 7):
            for es in combinations(pairs, k):
                terms = ref.graph_terms(4, es)
                if terms in seen:
                    continue
                seen.add(terms)
                self.compare(4, terms, (3, 4), [()])
        print(f'\n  4-vertex graphs: {self.count} cases agree ({time.time() - t0:.0f}s)')


if __name__ == '__main__':
    unittest.main(verbosity=1)
