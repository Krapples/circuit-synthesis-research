"""Tests for the evidence ledger and the proof checker it relies on. Run: python verify/test_evidence.py"""
import os, sys, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'experiments'))
import reference as ref
import evidence as ev
from certify_synthesis import check_proof


class Checker(unittest.TestCase):
    def test_rejects_proofs_for_satisfiable_cnf(self):
        tt = ref.truth_table(4, ref.graph_terms(4, [(0, 1), (1, 2), (2, 3)]))
        _, info = ref.sat_exists(4, tt, 3, 'monotone', proof=True)
        V = info['vars'] + 1
        sat_cnf = [c + [V] for c in info['cnf']]      # satisfiable with the fresh variable true
        for proof in (list(info['proof']) + ['0'], ['0']):
            with self.assertRaises(ValueError):
                check_proof(V, sat_cnf, proof)
        self.assertGreater(check_proof(info['vars'], info['cnf'], list(info['proof']) + ['0']), 0)


class Ledger(unittest.TestCase):
    def test_certified_minima(self):
        """Expected minima, all certified (verified witness + checked exclusions at M-1, M-2)."""
        cases = [(4, ref.graph_terms(4, [(0, 1), (1, 2), (2, 3)]), 'monotone', 4),
                 (3, (3, 5, 6), 'general', 4),
                 (3, (3, 5, 6), 'monotone', 4),
                 (5, ref.graph_terms(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]), 'monotone', 7)]
        for n, terms, basis, M in cases:
            with self.subTest(n=n, terms=terms, basis=basis):
                r = ev.certify_minimum(n, terms, basis)
                self.assertEqual(r['minimum_found'], M)
                self.assertTrue(r['report'].startswith(f'CERTIFIED minimum {M}'), r['report'])

    def test_grades(self):
        self.assertEqual(ev.grade([dict(kind='checked_unsat')] * 3), 'certified')
        self.assertEqual(ev.grade([dict(kind='checked_unsat'), dict(kind='analytical')]), 'rule-dependent')
        self.assertEqual(ev.grade([dict(kind='unchecked_unsat'), dict(kind='open')]), 'open')
        self.assertEqual(ev.grade([]), 'open')
        self.assertEqual(ev.grade([dict(kind='witness', verified=False)]), 'bad-witness')

    def test_inessential_input_rejected(self):
        with self.assertRaises(ValueError):
            ev.certify_minimum(3, (3,), 'monotone')     # x2 is not essential


if __name__ == '__main__':
    unittest.main(verbosity=2)
