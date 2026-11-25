"""Targeted correctness check of bnb.py against the independent reference (monotone exact-G model).
For small connected graphs with reference minimum M: at G = M - 1 the tree must close with no witness and no
open node; at G = M it must report a verified witness. Also for pinned two-gate seeds: the verdict must equal
the reference prefix minimum. Run: python verify/test_bnb.py"""
import json, os, random, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, ROOT)
from bnb import read_tree, tree_scope
import reference as ref
import differential as dif


def bnb(n, terms, G, seed=(), workers=2):
    edges = ','.join(f'{u}-{v}' for u, v in (tuple(i for i in range(n) if t >> i & 1) for t in terms))
    tree = tempfile.mktemp(suffix='.jsonl')
    cmd = [sys.executable, os.path.join(ROOT, 'bnb.py'), '--n', str(n), '--edges', edges, '--size', str(G),
           '--workers', str(workers), '--tree', tree, '--sat-seconds', '60']
    if seed:
        cmd += ['--seed-prefix', ';'.join(','.join(map(str, g)) for g in seed), '--root-children']
    out = subprocess.run(cmd, capture_output=True, text=True, cwd=ROOT).stdout
    line = [l for l in out.splitlines() if l.startswith('RESULT')][-1]
    stats = eval(line.split('RESULT ')[1].split(' (')[0])
    with open(tree, encoding='utf-8') as stream:
        witnesses = [json.loads(l) for l in stream if '"witness"' in l]
    os.remove(tree)
    return stats, witnesses


class BranchAndBound(unittest.TestCase):
    def test_expanded_children_reuse_their_probe(self):
        terms = (3, 6, 12)
        truth = ref.truth_table(4, terms)
        self.assertIsNotNone(ref.sat_exists(4, truth, 4, 'monotone')[0])
        stats, witnesses = bnb(4, terms, 4, workers=1)
        self.assertGreater(stats['probe_reused'], 0)
        self.assertGreater(stats['witness'], 0)
        self.assertTrue(all(ref.check_witness(4, truth, row['circuit']) for row in witnesses))

    def test_resume_scope_and_legacy_evidence(self):
        seed = ((1, 0, 1),)
        scope = tree_scope(4, (3, 6, 12), 4, seed, 1, True)
        other = tree_scope(4, (3, 5, 9), 4, seed, 1, True)
        first = dict(prefix=[[1, 0, 1]], status='sat-unsat', G=4)
        second = dict(prefix=[[1, 0, 1], [0, 2, 4]], status='expanded', G=4)
        with tempfile.TemporaryDirectory() as directory:
            path = os.path.join(directory, 'tree.jsonl')
            with open(path, 'w', encoding='utf-8') as stream:
                stream.write(json.dumps(first) + '\n')
            self.assertEqual(read_tree(path, scope), ({}, False))
            with open(path, 'a', encoding='utf-8') as stream:
                stream.write(json.dumps(dict(kind='scope', scope=scope)) + '\n')
                stream.write(json.dumps(second) + '\n')
            self.assertEqual(read_tree(path, scope), ({(*seed, (0, 2, 4)): 'expanded'}, True))
            with self.assertRaisesRegex(ValueError, 'different target'):
                read_tree(path, other)

    def test_whole_function(self):
        cache = dif.load_ref_cache()
        graphs = [(n, t) for kind, n, t in dif.instances(True) if kind == 'graph' and n >= 4]
        for n, t in graphs[:8]:
            M = cache[(n, t, 'monotone')]['minimum']
            s, w = bnb(n, t, M - 1)
            self.assertEqual((s['witness'], s['open']), (0, 0), (n, t, 'G=M-1', s))
            s, w = bnb(n, t, M)
            self.assertGreater(s['witness'], 0, (n, t, 'G=M', s))
            self.assertTrue(all(x['verified'] for x in w))

    def test_seeded(self):
        rng = random.Random(4)
        cache = dif.load_ref_cache()
        graphs = [(n, t) for kind, n, t in dif.instances(True) if kind == 'graph' and n >= 4][:6]
        for n, t in graphs:
            tt = ref.truth_table(n, t)
            M = cache[(n, t, 'monotone')]['minimum']
            w = [tuple(g) for g in cache[(n, t, 'monotone')]['witness']]
            seed = tuple(w[:1])                      # a first gate of a minimum circuit
            MP = next(G for G in range(M, M + 4) if ref.sat_exists(n, tt, G, 'monotone', seed)[0] is not None)
            s, _ = bnb(n, t, MP - 1, seed)
            self.assertEqual((s['witness'], s['open']), (0, 0), (n, t, seed, MP, s))
            s, wit = bnb(n, t, MP, seed)
            self.assertGreater(s['witness'], 0, (n, t, seed, MP, s))


if __name__ == '__main__':
    unittest.main(verbosity=2)
