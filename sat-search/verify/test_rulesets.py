"""Configuration-drift guard: the --fast rule set has one definition (sat-search/rulesets.py).
Expected: cube_search.py main() turns on exactly rulesets.FAST_CLI for --fast; no module re-defines a FAST
flag dictionary literally (solver_bench.py keeps its older, smaller benchmark set on purpose and is listed);
the verification harness's 'fast' configuration matches. Run: python verify/test_rulesets.py"""
import ast, glob, os, re, sys, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
SAT = os.path.dirname(HERE)
sys.path.insert(0, SAT); sys.path.insert(0, HERE)
import rulesets

DOCUMENTED_EXCEPTIONS = {'solver_bench.py': 'older solver-benchmark set (sens, units, usens, bypass, elim, '
                                            'elimclosure, signeddom, recursivebounds, notbypass)'}


class Rulesets(unittest.TestCase):
    def test_cli_fast_matches(self):
        src = open(os.path.join(SAT, 'cube_search.py'), encoding='utf-8').read()
        m = re.search(r"if a\.fast:\s*\n\s*for k in \((.*?)\):", src, re.S)
        self.assertIsNotNone(m)
        cli = ast.literal_eval('(' + m.group(1) + ')')
        self.assertEqual(tuple(cli), rulesets.FAST_CLI)

    def test_no_literal_copies(self):
        offenders = []
        for f in glob.glob(os.path.join(SAT, '**', '*.py'), recursive=True):
            rel = os.path.relpath(f, SAT).replace(os.sep, '/')
            if rel in DOCUMENTED_EXCEPTIONS or rel.startswith(('verify/', 'experiments/archive/')):
                continue
            try:
                tree = ast.parse(open(f, encoding='utf-8', errors='ignore').read())
            except SyntaxError:
                continue
            for node in tree.body:
                if (isinstance(node, ast.Assign) and any(getattr(t, 'id', '') == 'FAST' for t in node.targets)
                        and isinstance(node.value, (ast.Dict, ast.Call))
                        and not (isinstance(node.value, ast.Call) and getattr(node.value.func, 'id', '') == 'fast_flags')):
                    offenders.append(rel)
        self.assertEqual(offenders, [])

    def test_harness_fast_matches(self):
        import differential as dif
        spec = dif.configs()['fast']
        self.assertEqual(set(spec['flags']), set(rulesets.FAST_RULES))
        self.assertTrue(spec['fanout'] and spec['readonce'] and spec['symmetry'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
