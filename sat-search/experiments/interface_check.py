"""Checks for biclique widths, relaxed list coloring, and structural SAT pruning."""

from itertools import combinations, product
from random import Random
import unittest

from interface_coloring import biclique_cover_number, synthesize_interface
import cube_search as cs
from monotone_interface import crossing_matching, graph_neighbors, matching_cuts, pinned_interface_excess
from pysat.solvers import Solver


class InterfaceChecks(unittest.TestCase):
    def test_heawood_matching_and_residuals(self):
        edges = tuple((1 << ((line + d) % 7)) | (1 << (7 + line))
                      for line in range(7) for d in (0, 1, 3))
        neighbors = graph_neighbors(14, edges)
        side = 127
        residuals = {0}
        for neighbor in neighbors[:7]:
            residuals |= {row | neighbor for row in residuals}
        self.assertEqual(len(residuals), 37)
        self.assertEqual((len(residuals) - 1).bit_length(), 6)
        self.assertEqual(crossing_matching(neighbors, side), 7)
        self.assertEqual(biclique_cover_number(14, edges, side), 7)
        self.assertEqual(pinned_interface_excess(14, {0: (1, 0, 1)}, matching_cuts(14, edges)), (1, side))
        _, status, _, _, reason = cs.run_cube((14, edges, 13, 'maplechrono', (1, 0, 1), False, False,
                                              {'nonot': True, 'matchinginterface': True}))
        self.assertEqual(status, 'UNSAT')
        self.assertIn('analytical: matching interface on mask 0x7f', reason)

    def test_crossing_four_cycle_excludes_the_matching_rule(self):
        edges = (3, 6, 9, 12)
        side = 5
        self.assertEqual(crossing_matching(graph_neighbors(4, edges), side), 2)
        self.assertEqual(biclique_cover_number(4, edges, side), 1)
        self.assertNotIn(side, dict(matching_cuts(4, edges)))
        solution = synthesize_interface(side, (side,), *cs.boundary_rows(4, edges))
        self.assertIsNotNone(solution)
        self.assertTrue(all(solution.evaluate(row) == any(row & edge == edge for edge in edges)
                            for row in range(16)))

    def test_atlas_cut_widths(self):
        try:
            from networkx import graph_atlas_g
        except ImportError:
            self.skipTest('the atlas comparison uses NetworkX')
        graphs = cuts = 0
        for graph in graph_atlas_g():
            n = len(graph)
            if n < 2 or any(not degree for _, degree in graph.degree()):
                continue
            edges = tuple((1 << a) | (1 << b) for a, b in graph.edges())
            neighbors = graph_neighbors(n, edges)
            if any((a & b).bit_count() >= 2 for a, b in combinations(neighbors, 2)):
                continue
            graphs += 1
            for side in range(1, (1 << n) - 1):
                if any(side & edge == edge for edge in edges):
                    continue
                cuts += 1
                residuals = {0}
                for i, neighbor in enumerate(neighbors):
                    if side >> i & 1:
                        residuals |= {row | neighbor for row in residuals}
                self.assertEqual(crossing_matching(neighbors, side), (len(residuals) - 1).bit_length())
        self.assertEqual((graphs, cuts), (116, 3095))

    def test_export_clauses_count_distinct_wires_not_readers(self):
        def possible(circuit, add_cut):
            output, pool, clauses, ops, select = cs.build(4, len(circuit), colex_from=len(circuit))
            if add_cut:
                cs.add_matching_interface(4, output, pool, ops, select, clauses, ((5, 2),))
            pins = [lit for j, (op, a, b) in enumerate(circuit, 4)
                    for lit in (ops[j][op], select[j, 0][a], select[j, 1][b])]
            with Solver(name='g4', bootstrap_with=clauses) as sat:
                return sat.solve(assumptions=pins)

        two_reads = ((1, 0, 2), (0, 1, 4), (0, 3, 4), (1, 5, 6))
        two_wires = ((0, 0, 1), (1, 1, 3), (0, 2, 5), (1, 4, 6))
        self.assertTrue(possible(two_reads, False))
        self.assertFalse(possible(two_reads, True))
        self.assertTrue(possible(two_wires, True))
        self.assertTrue(all(cs.evaluate(4, two_wires, row) == any(row & edge == edge for edge in (3, 6, 12))
                            for row in range(16)))

    def test_list_coloring_detects_collective_conflicts(self):
        edges = (9, 18, 36)  # three disjoint crossing edges
        positives, negatives = cs.boundary_rows(6, edges)
        hidden = 7
        self.assertIsNone(synthesize_interface(hidden, (hidden, hidden), positives, negatives))
        solution = synthesize_interface(hidden, (hidden,) * 3, positives, negatives)
        self.assertIsNotNone(solution)
        self.assertTrue(all(solution.evaluate(row) == any(row & edge == edge for edge in edges)
                            for row in range(64)))

    def test_provider_specific_lists_match_brute_monotone_tables(self):
        def tables(mask):
            rows = tuple(x for x in range(8) if x & ~mask == 0)
            return [frozenset(a for a, high in zip(rows, flags) if high)
                    for flags in product((0, 1), repeat=len(rows))
                    if all(not va or vb or a & ~b for a, va in zip(rows, flags) for b, vb in zip(rows, flags))]

        def feasible(hidden, ancestors, pos, neg):
            for truth in product(*(tables(mask) for mask in ancestors)):
                def signature(row):
                    return (row & ~hidden) | sum(1 << (3 + i) for i, mask in enumerate(ancestors)
                                                  if row & mask in truth[i])

                if all(signature(a) & ~signature(b) for a in pos for b in neg):
                    return True
            return False

        rng = Random(985)
        for _ in range(80):
            hidden = rng.randrange(1, 8)
            ancestors = tuple(rng.randrange(7) for _ in range(rng.randrange(4)))
            rows = rng.sample(range(8), rng.randrange(1, 9))
            pivot = rng.randrange(len(rows) + 1)
            pos, neg = rows[:pivot], rows[pivot:]
            solution = synthesize_interface(hidden, ancestors, pos, neg)
            self.assertEqual(solution is not None, feasible(hidden, ancestors, pos, neg))
            if solution:
                self.assertTrue(all(solution.evaluate(row) for row in pos))
                self.assertTrue(all(not solution.evaluate(row) for row in neg))
                self.assertTrue(all(term & ~mask == 0 for mask, terms in zip(ancestors, solution.provider_terms)
                                    for term in terms))


if __name__ == '__main__':
    unittest.main()
