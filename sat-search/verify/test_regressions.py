"""Regression tests for defects found by the verification work (verify/AUDIT.md), each with an explicit
expected verdict checked against the independent reference. Run: python verify/test_regressions.py"""
import os, sys, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))
import reference as ref
import cube_search as cs

FIRST = lambda n: [(op, l, r) for op in (0, 1) for r in range(n) for l in range(r)]


def whole(n, masks, G, fanout=False, readonce=False, **flags):
    for c in FIRST(n):
        _, st, circ, _, _ = cs.run_cube((n, list(masks), G, 'maplechrono', c, fanout, readonce, dict(flags)))
        if st == 'WITNESS':
            return 'SAT'
    return 'UNSAT'


class Regressions(unittest.TestCase):
    def test_duplicate_edge_typed_bound(self):
        """R1: a repeated edge inflated the typed OR bound (#OR >= log2 #terms): path 0-1,1-2 has a 2-gate
        monotone circuit, but [0-1, 0-1, 1-2] with typed returned UNSAT. Expected: SAT."""
        tt = ref.truth_table(3, ref.graph_terms(3, [(0, 1), (1, 2)]))
        self.assertIsNotNone(ref.sat_exists(3, tt, 2, 'monotone')[0])
        self.assertEqual(whole(3, [3, 3, 6], 2, nonot=True, typed=True), 'SAT')
        self.assertEqual(whole(3, [3, 6, 3], 2, nonot=True, typed=True), 'SAT')

    def test_minimal_with_pinned_gates(self):
        """R2: MAJ3 (minimum 4). OR(0,1), AND(0,1), x2 AND, OR is a minimum circuit, yet --minimal with these
        two gates pinned returned UNSAT (its duplicate-gate op ordering assumes free swaps). Expected: the
        combination is rejected; without --minimal the pinned search is SAT."""
        n, masks, P = 3, [3, 5, 6], ((1, 0, 1), (0, 0, 1))
        tt = ref.truth_table(n, masks)
        self.assertEqual(ref.minimum(n, tt, 'monotone')[0], 4)
        self.assertIsNotNone(ref.sat_exists(n, tt, 4, 'monotone', P)[0])
        flags = dict(nonot=True, colex_from=2, fixgates=[(1, *P[1])])
        self.assertEqual(cs.run_cube((n, masks, 4, 'maplechrono', P[0], False, False, dict(flags)))[1], 'WITNESS')
        with self.assertRaises(ValueError):
            cs.run_cube((n, masks, 4, 'maplechrono', P[0], False, False, dict(flags, minimal=True)))
        # whole-function use (no pinned gates) keeps its proof: G - 1 and G - 2 UNSAT -> SAT at the minimum
        self.assertEqual(whole(n, masks, 4, nonot=True, minimal=True), 'SAT')

    def test_graph_only_rules_rejected_on_non_graphs(self):
        """R3: graph-only rules crashed on non-graph families (tuple unpacking). Expected: clear ValueError."""
        for flags, fanout in ((dict(sens=True), False), (dict(elim=True), False), (dict(bypass=True), True),
                              ({}, True)):
            with self.assertRaises(ValueError):
                cs.run_cube((3, [7], 2, 'maplechrono', (0, 0, 1), fanout, bool(flags.get('bypass')), flags))

    def test_malformed_terms_rejected(self):
        for bad in ([0, 3], [8, 3], [-1]):
            with self.assertRaises(ValueError):
                cs.run_cube((3, bad, 2, 'maplechrono', (0, 0, 1), False, False, {}))


if __name__ == '__main__':
    unittest.main(verbosity=2)
