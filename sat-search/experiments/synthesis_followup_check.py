"""Regression checks for endpoint probing, proof verification, and signed targets."""

from itertools import product
from pathlib import Path
from random import Random
import unittest
from unittest.mock import patch

from audit_synthesis import audit
from certify_synthesis import RupChecker, check_proof, encode
from nonmonotone_bench import descending_edge, signed_cases
from synthesis_bench import direct_sat
from synthesis_cases import truth_table
from synthesis_followup import endpoint_order, load_cases, probe, read_rows
from pysat.solvers import Solver


RESULTS = Path(__file__).resolve().parents[1] / 'results'


def naive_bcp(clauses, assumptions):
    known = set(assumptions)
    if any(-lit in known for lit in known):
        return True
    while True:
        size = len(known)
        for clause in clauses:
            if any(lit in known for lit in clause):
                continue
            alive = {lit for lit in clause if -lit not in known}
            if not alive:
                return True
            if len(alive) == 1:
                known.update(alive)
        if len(known) == size:
            return False


class FollowupChecks(unittest.TestCase):
    def test_baseline_audit_and_endpoint_order(self):
        cases = load_cases(RESULTS / 'synthesis_cases.json')
        rows = read_rows(RESULTS / 'synthesis_ablation.jsonl')
        result = audit(rows, cases)
        self.assertEqual(result['verdicts'], {'SAT': 583, 'UNSAT': 868, 'TIMEOUT': 634})
        self.assertEqual((result['harder_budgets'], result['untested_endpoints']), (92, 39))
        previously_tried = {(r['case'], r['budget']) for r in rows if r['kind'] == 'job' and r['basis'] == 'mono'}
        self.assertTrue(all((r['case'], r['final']['lower']) not in previously_tried for r in endpoint_order(rows)[:39]))

    def test_probe_advances_only_after_a_certificate(self):
        frame = {'final': {'lower': 4, 'upper': 6, 'minimum': None}}
        case = load_cases(RESULTS / 'synthesis_cases.json')['hypergraph-07']

        def answer(case, config, basis, budget, bounds, seconds):
            if budget == 4 and config == 'D':
                return {'status': 'UNSAT'}
            if budget == 5 and config == 'E':
                return {'status': 'SAT', 'gates': 5}
            return {'status': 'TIMEOUT'}

        with patch('synthesis_followup.isolated', side_effect=answer):
            rows = probe(case, frame, 1, 3)
        self.assertEqual([r['budget'] for r in rows[:-1]], [4] * 4 + [5] * 4)
        self.assertEqual(rows[-1]['final'], {'lower': 5, 'upper': 5, 'minimum': 5})

    def test_independent_encoding_matches_reference_on_tiny_tables(self):
        for bits, budget in product(range(16), (1, 2, 3)):
            labels = {i: bool(bits >> i & 1) for i in range(4)}
            _, clauses = encode(2, labels, budget)
            with Solver(name='g4', bootstrap_with=clauses) as solver:
                self.assertEqual(solver.solve(), direct_sat(2, labels, budget, False) is not None)

    def test_watched_propagation_matches_naive_and_rejects_invalid_proofs(self):
        rng = Random(201)
        literals = (-4, -3, -2, -1, 1, 2, 3, 4)
        for _ in range(45):
            clauses = [rng.sample(literals, rng.randint(1, 3)) for _ in range(9)]
            checker = RupChecker(4, clauses)
            for _ in range(8):
                assumptions = rng.sample(literals, rng.randint(0, 3))
                self.assertEqual(checker.contradicts(assumptions), naive_bcp(clauses, assumptions))
        self.assertEqual(check_proof(2, [[1], [-1, 2], [-2]], ['0']), 1)
        with self.assertRaises(ValueError):
            check_proof(2, [[1, 2]], ['0'])
        with self.assertRaises(ValueError):
            check_proof(2, [[1, 2]], ['1 0', '0'])

    def test_signed_targets_require_negation(self):
        cases = signed_cases()
        self.assertEqual(len(cases), 16)
        self.assertEqual(len({(c.n, c.truth) for c in cases}), 16)
        for case in cases:
            below, above = descending_edge(case)
            self.assertEqual(below & above, below)
            self.assertTrue(case.labels()[below])
            self.assertFalse(case.labels()[above])
            self.assertEqual(truth_table(case.n, case.witness), case.truth)
            self.assertTrue(any(op == 2 for op, _, _ in case.witness.gates))


if __name__ == '__main__':
    unittest.main()
