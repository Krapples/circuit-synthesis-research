"""End-to-end evidence-manifest tests through the production command line.
Expected: complete ALL UNSAT runs at M-1 and M-2 produce manifests graded rule-dependent by the independent
verifier; --minimal at M accepts them and finds a verified witness; --minimal rejects log files and tampered
manifests; tampering (missing cube record, wrong group, skipped cube) makes the verifier grade 'invalid'.
Run: python verify/test_manifest.py"""
import copy, json, os, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import manifest as mf

CLI = os.path.join(ROOT, 'cube_search.py')
EDGES = '0-1,1-2,2-3,3-4,0-4'        # five-cycle, monotone minimum 7


def cli(size, *extra):
    p = subprocess.run([sys.executable, CLI, '--n', '5', '--edges', EDGES, '--size', str(size), '--monotone',
                        '--workers', '2', *extra], capture_output=True, text=True, cwd=ROOT)
    return p.returncode, p.stdout + p.stderr


class Manifests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.mkdtemp(prefix='manifest_test_')
        cls.paths = {}
        for G in (5, 6):
            path = os.path.join(cls.dir, f'c5_{G}.json')
            code, out = cli(G, '--symmetry', '--fanout', '--readonce', '--manifest', path)
            assert 'RESULT: ALL UNSAT' in out, out[-500:]
            cls.paths[G] = path

    def test_verifier_grades(self):
        for G, path in self.paths.items():
            r = mf.verify_manifest(json.load(open(path)), recheck_analytical=True)
            self.assertEqual(r['grade'], 'rule-dependent', r)
            self.assertEqual(r['problems'], [])

    def test_minimal_accepts_manifests(self):
        code, out = cli(7, '--minimal', '--minimal-evidence', self.paths[6], '--minimal-evidence', self.paths[5])
        self.assertIn('RESULT: WITNESS', out, out[-500:])
        self.assertIn('verified=True', out)

    def test_minimal_rejects_logs_and_tampering(self):
        log = os.path.join(self.dir, 'old.log')
        open(log, 'w').write('search: n=5, 5 edges, exactly 6 gates (mode=monotone) edges=0-1,0-4,1-2,2-3,3-4\n'
                             'RESULT: ALL UNSAT (exactly 6 gates)\n')
        code, out = cli(7, '--minimal', '--minimal-evidence', log, '--minimal-evidence', self.paths[5])
        self.assertNotEqual(code, 0)
        self.assertIn('manifest', out)
        m = json.load(open(self.paths[6]))
        bad = copy.deepcopy(m); bad['cubes'] = bad['cubes'][1:]
        path = os.path.join(self.dir, 'tampered.json'); json.dump(bad, open(path, 'w'))
        code, out = cli(7, '--minimal', '--minimal-evidence', path, '--minimal-evidence', self.paths[5])
        self.assertNotEqual(code, 0)

    def test_verifier_detects_tampering(self):
        m = json.load(open(self.paths[6]))
        cases = []
        x = copy.deepcopy(m); x['cubes'] = x['cubes'][1:]; cases.append(x)
        x = copy.deepcopy(m); x['coverage']['automorphisms'].append([1, 0, 2, 3, 4]); cases.append(x)
        x = copy.deepcopy(m); x['coverage']['skipped_by_logs'] = [x['coverage']['selected'][0]]; cases.append(x)
        x = copy.deepcopy(m); x['target']['edges'][0] = [0, 2]; cases.append(x)
        for x in cases:
            self.assertEqual(mf.verify_manifest(x)['grade'], 'invalid')


if __name__ == '__main__':
    unittest.main(verbosity=2)
