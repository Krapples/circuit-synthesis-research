"""Independent graft checks and matched surplus-heavy Windows benchmarks."""

import argparse
from collections import Counter
import json
from pathlib import Path
from random import Random
import sys
import unittest

from regional_completion_check import check_tree
from conditional_provider import formula_columns
from port_certificates_check import bounded
from regional_cover_stress import stress_batch
from regional_padding import columns, evaluate, fast_witness, graft


def random_tree(leaves, signed, rng):
    pool = [('x', leaf, bool(signed and rng.randrange(2))) for leaf in leaves]
    while len(pool) > 1:
        left, right = (pool.pop(rng.randrange(len(pool))) for _ in range(2))
        pool.append((rng.choice(('&', '|')), left, right))
    return pool[0]


def all_graft_values(node, fill, values, one):
    current = evaluate(node, values, one)
    yield current & fill
    yield current | fill
    if node[0] != 'x':
        op, left, right = node
        for a, b in ((left, right), (right, left)):
            sibling = evaluate(b, values, one)
            for child in all_graft_values(a, fill, values, one):
                yield child & sibling if op == '&' else child | sibling


class PaddingChecks(unittest.TestCase):
    def test_exhaustive_single_graft_oracle(self):
        rng = Random(892451)
        internal_only = 0
        for signed in (False, True):
            for _ in range(700):
                nc, ns, rows = rng.randrange(1, 5), rng.randrange(1, 5), rng.randrange(1, 13)
                one = (1 << rows) - 1
                values = {i: rng.randrange(one + 1) for i in range(nc + ns)}
                core = random_tree(range(nc), signed, rng)
                spare = tuple(range(nc, nc + ns))
                target = evaluate(core, values, one)
                fillers = formula_columns(tuple(sorted(values[i] for i in spare)), one, signed)
                possible = any(target in all_graft_values(core, fill, values, one) for fill in fillers)
                witness = graft(core, spare, values, one, signed)
                self.assertEqual(witness is not None, possible)
                if witness is not None:
                    self.assertEqual(evaluate(witness, values, one), target)
                    internal_only += not any(target in (target & fill, target | fill) for fill in fillers)
                if signed and 1 << ns > min(target.bit_count(), (one ^ target).bit_count()):
                    self.assertTrue(possible)
        self.assertGreater(internal_only, 0)

    def test_small_query_witnesses_against_formula_columns(self):
        rng = Random(892453)
        found = 0
        for signed in (False, True):
            for _ in range(150):
                m = rng.randrange(3)
                q = rng.randrange(1, 6 - m)
                r = rng.randrange(1, q + 1)
                ports = tuple(rng.randrange(r) * 2 for _ in range(q))
                pats = tuple(sum((a >> i & 1) << (2 * i) for i in range(r))
                             for a in range(1 << r) if rng.random() < .7) or (0,)
                values, _, one = columns(m, ports, pats, (0,) * len(pats))
                full_cols = tuple(sorted(values[i] for i in (*range(m), *(m + p for p in ports))))
                oracle = formula_columns(full_cols, one, signed)
                target = rng.choice(sorted(oracle)) if rng.randrange(2) else rng.randrange(one + 1)
                small = (1 << (1 << m)) - 1
                ts = tuple((target >> (j * (1 << m))) & small for j in range(len(pats)))
                witness = fast_witness(m, ports, pats, ts, signed)
                if witness is not None:
                    self.assertIn(target, oracle)
                    check_tree(witness, m, ports, pats, ts, signed)
                    found += 1
        self.assertGreater(found, 20)


def padded_queries():
    rng = Random(218746)
    for signed in (False, True):
        j = 0
        while j < 30:
            m, r = j % 3, 8 + j % 4
            ports = tuple(range(r)) + (tuple(rng.randrange(r) for _ in range(2)) if j % 2 else ())
            pats = tuple(sorted(rng.sample(range(1 << r), 64)))
            values, _, one = columns(m, ports, pats, (0,) * len(pats))
            kept = tuple(rng.sample(ports, 4 - m + j % 2))
            core = random_tree((*range(m), *(m + i for i in kept)), signed, rng)
            target = evaluate(core, values, one)
            if target in (0, one):
                continue
            spare = tuple(m + p for p in (Counter(ports) - Counter(kept)).elements())
            witness = graft(core, spare, values, one, signed)
            if witness is None:
                continue
            width = 1 << m
            labels = tuple((target >> (k * width)) & ((1 << width) - 1) for k in range(len(pats)))
            check_tree(witness, m, ports, pats, labels, signed)
            yield j, (m, ports, pats, labels, signed), True
            j += 1


if __name__ == '__main__':
    if '--bench' not in sys.argv:
        unittest.main()
    else:
        parser = argparse.ArgumentParser(description=__doc__)
        parser.add_argument('--bench', action='store_true')
        parser.add_argument('--seconds', type=float, default=.20)
        parser.add_argument('--output', type=Path, required=True)
        args = parser.parse_args()
        if args.seconds <= 0:
            parser.error('deadline must be positive')
        cases = list(padded_queries())
        with args.output.open('x', encoding='utf-8') as stream:
            for mode in ('row-quotient', 'padding-first'):
                for signed in (False, True):
                    scope = [case for case in cases if case[1][-1] == signed]
                    result = bounded(stress_batch, (scope, mode, args.seconds), len(scope) * (args.seconds + .1) + 2)
                    record = dict(mode=mode, signed=signed, cap=args.seconds, **result)
                    stream.write(json.dumps(record, sort_keys=True) + '\n')
                    print(mode, signed, Counter(r['status'] for r in result.get('jobs', ())), result['seconds'], flush=True)
