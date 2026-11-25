"""Targeted differential check of the signed regional bound (theory/signed_region_bounds.py) against the
independent reference: n - 1 + lower() + not_lower() <= the exact general-basis minimum (NOT gates counted),
and n - 1 + lower() <= the monotone minimum for monotone targets (monotone circuits are general circuits).
Cases: every decided instance in results/reference_minima.jsonl, and random nonmonotone 4-input functions.
Run: python verify/test_signed_bound.py"""
import json, os, random, sys, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(ROOT, 'theory'))
import reference as ref
from signed_region_bounds import Bound


def signed_total(n, f):
    b = Bound(n, f)
    return n - 1 + b.lower(), n - 1 + b.lower() + b.not_lower()


class SignedBound(unittest.TestCase):
    def test_reference_instances(self):
        checked = tight = 0
        for line in open(os.path.join(ROOT, 'results', 'reference_minima.jsonl'), encoding='utf-8'):
            r = json.loads(line)
            if r.get('minimum') is None:
                continue
            n, tt = r['n'], ref.truth_table(r['n'], tuple(r['terms']))
            if len(ref.essential_inputs(n, tt)) != n:
                continue
            binary, total = signed_total(n, tt)
            self.assertLessEqual(total if r['basis'] == 'general' else binary, r['minimum'], r)
            checked += 1
            tight += (total if r['basis'] == 'general' else binary) == r['minimum']
        print(f'\n  reference instances: {checked} checked, {tight} tight')
        self.assertGreater(checked, 50)

    def test_random_nonmonotone(self):
        rng = random.Random(7)
        fs = []
        while len(fs) < 40:
            f = rng.getrandbits(16)
            if len(ref.essential_inputs(4, f)) == 4:
                fs.append(f)
        from multiprocessing import Pool
        with Pool(11) as p:
            for k, (f, M) in enumerate(p.imap_unordered(_ref_min4, fs), 1):
                st = signed_total(4, f)[1]
                print(f'  [{k}/{len(fs)}] f={f:#06x} reference minimum {M}, signed bound {st}', flush=True)
                if M == 'undecided':
                    continue                  # an undecided reference minimum is not evidence either way
                self.assertIsNotNone(M)
                self.assertLessEqual(st, M, f)


def _ref_min4(f):
    return f, ref.minimum(4, f, 'general', Gmax=12, seconds=120)[0]


if __name__ == '__main__':
    unittest.main(verbosity=2)
