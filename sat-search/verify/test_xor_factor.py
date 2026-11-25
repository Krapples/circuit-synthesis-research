"""Targeted check of theory/xor_factor.py against independent free-NOT gate-set enumeration
(theory/module_contraction.brute, basis 'free': binary AND/OR gates, NOT free).
Expected: for every function f on n <= 4 inputs (all essential) with an XOR factor f = x_i XOR h,
C(f) = C(h) + 3 whenever both are within the enumeration cap; when C(h) + 3 exceeds the cap, f is not found
within the cap either. Also: parity of n inputs strips completely to one input, C = 3(n - 1).
Run: python verify/test_xor_factor.py"""
import os, sys, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'theory'))
from module_contraction import brute, essential
from xor_factor import xor_factor, strip_xor

CAP = {1: 3, 2: 5, 3: 6, 4: 5}


class XorFactor(unittest.TestCase):
    def test_identity_against_enumeration(self):
        tables = {n: brute(n, CAP[n], 'free') for n in CAP}
        checked = 0
        for n in (2, 3, 4):
            one = (1 << (1 << n)) - 1
            for f in range(1, one):
                if not essential(n, f):
                    continue
                s = xor_factor(n, f)
                if s is None:
                    continue
                _, h = s
                ch = tables[n - 1].get(h)
                cf = tables[n].get(f)
                if ch is not None and ch + 3 <= CAP[n]:
                    self.assertEqual(cf, ch + 3, (n, f, h))
                    checked += 1
                elif ch is None or ch + 3 > CAP[n]:
                    self.assertTrue(cf is None or cf >= min(CAP[n - 1], ch or CAP[n]) , (n, f, h, cf, ch))
        print(f'\n  {checked} XOR-factor identities checked against enumeration')
        self.assertGreater(checked, 50)

    def test_parity(self):
        for n in range(2, 7):
            par = sum(1 << a for a in range(1 << n) if bin(a).count('1') % 2)
            m, core, k = strip_xor(n, par)
            self.assertEqual((m, k), (1, n - 1))


if __name__ == '__main__':
    unittest.main(verbosity=2)
