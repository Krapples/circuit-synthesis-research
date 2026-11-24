"""Regression tests from the independent theory audit (verify/theory_audit_checks.py), with explicit
expected values, plus cross-checks of the complete-function FPT prototypes (sat-search/theory) against the
independent reference (verify/reference.py), and the padding theorem's boundary condition.
Finite tests here are evidence, not proofs (statuses in verify/AUDIT.md). Run: python verify/test_theory.py"""
import os, sys, random, unittest
from itertools import combinations
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'theory'))
import reference as ref
import theory_audit_checks as tac
from complete_sharing_fpt import Solver as Mono
from complete_signed_fpt import Solver as Signed


class RankTightFamily(unittest.TestCase):
    def test_rank_witnesses(self):
        """Explicit certificate witnesses (each row checked as a minimal certificate of the stated function)
        with ranks (P, N, H) = (3e-1, 3e, 3e-1) for e = 1..30: rank(H) = 3e - 1 > 2e for e >= 2, so the
        universal bound rank(H) <= 2e fails. Tested for e <= 30; the general-e statement is not proved here."""
        for e in range(1, 31):
            P, N = tac.make_rank_witnesses(e, True), tac.make_rank_witnesses(e, False)
            a, b = tac.rank2(v for _, v in P), tac.rank2(v for _, v in N)
            H = tac.rank2(sum((((p & q).bit_count() - 1) & 1) << j for j, (q, _) in enumerate(N)) for p, _ in P)
            self.assertEqual((a, b, H), (3 * e - 1, 3 * e, 3 * e - 1))
            if e >= 2:
                self.assertGreater(H, 2 * e)


class Padding(unittest.TestCase):
    def test_exhaustive_padding_and_prefixes(self):
        """Every trimmed program of 0..3 gates on 1..3 inputs (both bases): appending AND(x0, out), OR(out, g)
        keeps every wire read, computes the same function, and preserves every pinned prefix. Expected counts
        from the supplied audit: 721 programs, 2825 prefix checks, 2 one-wire programs (n = 1, no gates)."""
        import io, contextlib
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            tac.exact_padding_audit()
        self.assertIn('padding: 721 trimmed circuits; 2825 prefix checks; 2 one-wire cases', buf.getvalue())

    def test_one_wire_boundary(self):
        """Padding needs a wire other than the output (n + s >= 2). With one input and no gates the monotone
        exact-2 model is UNSAT although exact-0 holds; the general basis pads by double negation instead."""
        tt = ref.truth_table(1, (1,))
        self.assertIsNone(ref.brute_exists(1, tt, 2, 'monotone'))
        self.assertIsNotNone(ref.brute_exists(1, tt, 2, 'general'))
        for n in (2, 3):
            tt = ref.truth_table(n, ((1 << n) - 1,))
            M = ref.minimum(n, tt, 'monotone')[0]
            for basis in ('monotone', 'general'):
                for k in (1, 2):
                    self.assertIsNotNone(ref.sat_exists(n, tt, M + 2 * k, basis)[0])

    def test_padded_prefix_completions(self):
        """Pinned-prefix exactness: if a circuit of exact size s starts with prefix P, so does one of size s + 2
        (the padding gates go at the end). Checked with the reference on minimum and nonminimum prefixes."""
        rng = random.Random(5)
        checked = 0
        for n, terms in ((3, (3, 5, 6)), (4, (3, 6, 12)), (4, (3, 5, 9, 6)), (3, (7,))):
            tt = ref.truth_table(n, ref.normalize_terms(n, terms))
            for basis in ('monotone', 'general'):
                M = ref.minimum(n, tt, basis)[0]
                for _ in range(6):
                    k = rng.randint(1, 2)
                    P = []
                    for j in range(k):
                        b = rng.randrange(1, n + j)
                        P.append((rng.randint(0, 1), rng.randrange(b), b))
                    P = tuple(P)
                    MP = next((G for G in range(max(M, k), M + 4) if ref.sat_exists(n, tt, G, basis, P)[0]), None)
                    if MP is None:
                        continue
                    for extra in (2, 4):
                        self.assertIsNotNone(ref.sat_exists(n, tt, MP + extra, basis, P)[0], (n, terms, basis, P))
                    checked += 1
        self.assertGreater(checked, 10)


class FptPrototypes(unittest.TestCase):
    def test_contracts(self):
        for cls in (Mono, Signed):
            sol = cls(3)
            for bad in (0, sol.ONE, -1, sol.ONE + 1):
                with self.assertRaises(ValueError):
                    sol.solve(bad, 1)
            with self.assertRaises(ValueError):
                sol.solve(sol.var[0] & sol.var[1], 1)          # x2 inessential
            with self.assertRaises(ValueError):
                sol.solve(sol.var[0] & sol.var[1] | sol.var[2], -1)
        sol = Mono(2)
        with self.assertRaises(ValueError):
            sol.solve(sol.var[0] ^ sol.var[1], 2)               # not monotone
        self.assertTrue(Signed(2).solve(Signed(2).var[0] ^ Signed(2).var[1], 2) in (True, False))

    def test_against_reference(self):
        """solve(f, s) must equal 'minimum <= n - 1 + s' from the independent reference, for every monotone
        (resp. every) function of 3 inputs with all inputs essential, s = 0..2."""
        for cls, basis, mono_only in ((Mono, 'monotone', True), (Signed, 'general', False)):
            n = 3
            sol = cls(n)
            count = 0
            for f in range(1, sol.ONE):
                if not all(sol.res(f, 1 << i, 0) != sol.res(f, 1 << i, 1 << i) for i in range(n)):
                    continue
                if mono_only and any((f >> a & 1) > (f >> (a | 1 << i) & 1) for a in range(8) for i in range(n)):
                    continue
                M = ref.minimum(n, f, basis, Gmax=n + 2)[0]
                for s in range(3):
                    self.assertEqual(sol.solve(f, s), M is not None and M <= n - 1 + s, (basis, f, s, M))
                    count += 1
            self.assertGreaterEqual(count, 27)   # 9 monotone essential 3-input functions x 3 budgets


if __name__ == '__main__':
    unittest.main(verbosity=2)
