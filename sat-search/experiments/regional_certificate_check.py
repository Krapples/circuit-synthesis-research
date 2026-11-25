"""Independent regional CDCL checks and bounded backend comparisons."""

import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
from random import Random
import sys
from threading import Event
import unittest

from regional_completion_check import check_tree, make_completion
from pysat.formula import IDPool
from cograph_formulas import CographFormula
from conditional_provider import formula_columns
from module_contraction import vars as truth_variables
from port_certificates_check import bounded
from regional_certificate_cnf import local_cnf
from regional_cover_stress import layout_job, regional_job, stress_batch
from regional_deadline import cdcl_deadline, timed
from regional_order_check import selected_layouts, wide_queries
from regional_root_relaxation import allocations, families
from two_sharing_core import ANY


BASE = 'row-quotient'
CNF_MODES = ('certificate-cnf', 'certificate-lazy', 'certificate-rows', 'certificate-anchored', 'certificate-fallback')
ABSORPTION = 'certificate-absorption'
ROOT_MODES = ('root-relaxation', 'root-portfolio')
DEFAULT_CAPTURE = Path(__file__).resolve().parents[1] / 'results' / 'regional_order_captured.jsonl'
EARLIER_CAPTURE = DEFAULT_CAPTURE.with_name('regional_cover_captured.jsonl')


class RegionalCertificateChecks(unittest.TestCase):
    def test_native_deadline_interrupts_active_solver(self):
        interrupted = Event()

        class NativeSolve:
            interrupt = interrupted.set

        def job():
            with cdcl_deadline(NativeSolve()) as deadline:
                self.assertTrue(interrupted.wait(1))
                deadline.check()

        self.assertEqual(timed(.02, job, dict), {'status': 'TIMEOUT'})

    def test_all_four_vertex_models_against_eager_clauses(self):
        clauses = []
        graph = CographFormula(4, IDPool(), 'p4', clauses)
        for bits in range(64):
            variables = tuple(graph.edges.values())
            assignment = {v if bits >> i & 1 else -v for i, v in enumerate(variables)}
            violated = [clause for clause in clauses if not any(literal in assignment for literal in clause)]
            self.assertEqual(list(graph.induced_path_clauses(assignment)), violated)

    def test_free_not_phases_are_per_occurrence(self):
        # With no constants, p & !p needs opposite phases on the repeated port.
        case = (0, (17, 17), (0, 1 << 17), (0, 0), True)
        for mode in CNF_MODES[:-1]:
            witness = make_completion(mode)(*case)
            self.assertIsNotNone(witness)
            check_tree(witness, *case)
            self.assertEqual({leaf[2] for leaf in witness[1:]}, {False, True})

    def test_empty_and_conflicting_obligations(self):
        self.assertIsNone(local_cnf(0, (), (), (), False))
        self.assertIsNone(local_cnf(0, (1,), (0, 4), (0, 1), False))
        case = (1, (), (0,), (ANY,), True)
        tree = local_cnf(*case, eager=False, lazy_rows=True)
        self.assertIsNotNone(tree)
        check_tree(tree, *case)

    def test_small_queries_against_independent_formula_columns(self):
        rng = Random(71002)
        backends = tuple(make_completion(mode, cache_size=128) for mode in (*CNF_MODES[:-1], ABSORPTION))
        for _ in range(180):
            m = rng.randrange(3)
            q = rng.randrange(max(1, 2 - m), 5 - m)
            r = rng.randrange(1, min(q, 3) + 1)
            signed = bool(rng.randrange(2))
            ports = tuple(rng.randrange(r) * 2 + 1 for _ in range(q))
            ids = tuple(sorted(set(ports)))
            pats = tuple(sum((row >> i & 1) << p for i, p in enumerate(ids))
                         for row in range(1 << len(ids)) if rng.random() < .7) or (0,)
            width = 1 << m
            small, one = (1 << width) - 1, (1 << (len(pats) * width)) - 1
            columns = tuple(sum(v << (i * width) for i in range(len(pats))) for v in truth_variables(m))
            columns += tuple(sum((small if row >> port & 1 else 0) << (i * width) for i, row in enumerate(pats))
                             for port in ports)
            known = formula_columns(tuple(sorted(columns)), one, signed)
            for table in (rng.choice(sorted(known)), rng.randrange(one + 1)):
                targets = tuple((table >> (width * i)) & small if rng.random() < .85 else ANY
                                for i in range(len(pats)))
                case = m, ports, pats, targets, signed
                expected = any(all(t == ANY or (value >> (width * i) & small) == t for i, t in enumerate(targets))
                               for value in known)
                for backend in backends:
                    witness = backend(*case)
                    self.assertEqual(witness is not None, expected, case)
                    if witness is not None:
                        check_tree(witness, *case)

    def test_absorption_lifts_the_signed_stress_query(self):
        case = next(case for meta, case in wide_queries() if meta['case'] == 'wide-8-1-1')
        completion = make_completion(ABSORPTION)
        witness = completion(*case)
        self.assertIsNotNone(witness)
        self.assertEqual(completion.metrics().get('absorption_witnesses'), 1)
        check_tree(witness, *case)

    def test_root_relaxation_against_all_group_allocations(self):
        rng = Random(77142)
        for q in range(2, 8):
            for _ in range(100):
                groups = []
                for i in range(q):
                    if groups and rng.random() < .3:
                        groups[rng.randrange(len(groups))].append(1 << i)
                    else:
                        groups.append([1 << i])
                masks = tuple(map(sum, groups))
                full = sum(masks)
                rows = [sum(mask for i, mask in enumerate(masks) if row >> i & 1) for row in range(1 << len(masks))]
                rng.shuffle(rows)
                p, n = rows[:len(rows) // 3], rows[len(rows) // 3:2 * len(rows) // 3]
                for signed, is_and in product((False, True), repeat=2):
                    actual = set(allocations(groups, families(p, n, masks, signed, is_and)))
                    expected = set()
                    for counts in product(*(range(len(group) + 1) for group in groups)):
                        left = sum(sum(group[:count]) for group, count in zip(groups, counts))
                        if not left & 1 or left == full:
                            continue
                        if all(any(all(side & (a ^ b if signed else a & ~b) for a in p)
                                   for side in (left, full ^ left)) for b in n) if is_and else (
                                all(any(all(side & (a ^ b if signed else a & ~b) for b in n)
                                        for side in (left, full ^ left)) for a in p)):
                            expected.add(left)
                    self.assertEqual(actual, expected)


def root_stress_queries():
    """The supplied root benchmark's seed and exact query generator."""
    rng = Random(21267)
    for signed in (False, True):
        for j in range(30):
            m, q = j % 3, 6 + j % 5
            r = q - (m == 0)
            ports = (*range(r), *range(q - r))
            pats = tuple(sorted(rng.sample(range(1 << r), min(64, 1 << r))))
            width = 1 << m
            small, one = (1 << width) - 1, (1 << (len(pats) * width)) - 1
            values = [sum(v << (i * width) for i in range(len(pats))) for v in truth_variables(m)]
            values.extend(sum((small if row >> port & 1 else 0) << (i * width) for i, row in enumerate(pats))
                          for port in ports)
            values = [x ^ one if signed and rng.randrange(2) else x for x in values]
            while len(values) > 1:
                a, b = (values.pop(rng.randrange(len(values))) for _ in range(2))
                values.append(a & b if rng.randrange(2) else a | b)
            targets = [(values[0] >> (i * width)) & small for i in range(len(pats))]
            if j % 2:
                targets[rng.randrange(len(pats))] ^= 1 << rng.randrange(width)
            yield j, (m, ports, pats, tuple(targets), signed), j % 2 == 0


def captured_queries(paths):
    seen = set()
    for path in paths:
        for rec in map(json.loads, path.read_text(encoding='utf-8').splitlines()):
            for row in rec['calls']:
                m, ports, patterns, targets, signed = row['query']
                case = m, tuple(ports), tuple(patterns), tuple(targets), signed
                if case in seen:
                    continue
                seen.add(case)
                yield dict(case=rec['case'], excess=rec['excess'], sequence=row['sequence'], roles=row['roles'],
                           m=m, ports=len(ports), rows=len(patterns), signed=signed, expected=row.get('status')), case
    for meta, case in wide_queries():
        if meta['case'] == 'wide-8-1-1':
            yield dict(**meta, ports=len(case[1]), rows=len(case[2])), case


def benchmark(args, emit):
    expected = {}

    def check(key, verdict, wanted=None):
        if verdict != 'TIMEOUT':
            assert expected.setdefault(key, wanted or verdict) == verdict, (key, verdict, wanted)

    for mode in args.modes:
        if args.dataset == 'roots':
            for signed in (False, True):
                cases = [work for work in root_stress_queries() if work[1][-1] == signed]
                result = bounded(stress_batch, (cases, mode, args.seconds), len(cases) * (args.seconds + .1) + 2)
                for job in result.get('jobs', ()):
                    check((signed, job['case']), job['status'], 'SAT' if job['known_sat'] else None)
                emit(dict(mode=mode, signed=signed, **result))
        elif args.dataset == 'layouts':
            for work in selected_layouts(True):
                name, n, target, excess, signed, engine = work
                if args.cases and name not in args.cases:
                    continue
                result = bounded(layout_job, (work, mode, args.seconds, False, True), args.seconds + 1)
                check(name, result['status'])
                emit({**result, 'mode': mode, 'case': name, 'n': n, 'excess': excess, 'truth': hex(target)})
        else:
            for meta, work in captured_queries(args.source or (DEFAULT_CAPTURE, EARLIER_CAPTURE)):
                if args.cases and meta['case'] not in args.cases:
                    continue
                result = bounded(regional_job, (work, mode, args.seconds), args.seconds + 1)
                check((meta['case'], meta.get('excess'), meta.get('sequence')), result['status'], meta['expected'])
                emit(dict(mode=mode, **meta, **result))


def main():
    if '--bench' not in sys.argv:
        unittest.main()
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bench', action='store_true')
    parser.add_argument('--dataset', choices=('queries', 'roots', 'layouts'), required=True)
    parser.add_argument('--modes', nargs='+', choices=(BASE, *CNF_MODES, ABSORPTION, *ROOT_MODES, 'padding-first'))
    parser.add_argument('--case', dest='cases', action='append')
    parser.add_argument('--source', action='append', type=Path)
    parser.add_argument('--seconds', type=float, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.seconds <= 0:
        parser.error('deadline must be positive')
    if args.modes is None:
        args.modes = (BASE, *(ROOT_MODES if args.dataset == 'roots' else CNF_MODES))
    with args.output.open('x', encoding='utf-8') as stream:
        def emit(record):
            line = json.dumps(dict(dataset=args.dataset, cap=args.seconds, **record), sort_keys=True)
            stream.write(line + '\n')
            stream.flush()
            print(line, flush=True)

        benchmark(args, emit)


if __name__ == '__main__':
    main()
