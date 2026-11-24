"""Check and compare incremental regional certificate compatibility."""

import argparse
from collections import Counter
from itertools import combinations
import json
from random import Random
from subprocess import TimeoutExpired, run
import sys
from time import perf_counter
import unittest

from certificate_compatibility import (Obstruction, compatible_tree, indices, obstruction_clause,
                                       restrict_certificates, tree_leaves)
from certificate_decomposition import complete_status, decomposition_status
from certificate_rank import analyze, intersection_matrix
from certificate_rank_check import RESULTS, complete_certificates, gate_count, graph_certificates
from certify_synthesis import check_proof
from provider_capacity import CAPACITY_LEVELS
from regional_synthesis import _formulas
from synthesis_cases import full_rows
from synthesis_followup import load_cases


MODES = ('complete-terminal', 'lazy-certificates', 'lazy-local-intersection')
JOBS = (('cycle-5', 6), ('cycle-5', 7), ('complete-5', 9), ('threshold-5-3', 9),
        ('threshold-5-3', 10), ('hypergraph-12', 7), ('hypergraph-21', 8), ('hypergraph-03', 9))
FRONTIER_JOBS = (('hypergraph-12', 7), ('hypergraph-04', 10),
                 ('hypergraph-09', 10), ('hypergraph-10', 11), ('threshold-6-4', 10),
                 ('random-monotone-05', 11), ('comparator-02', 8), ('comparator-04', 10))


def options(mode):
    return dict(backend='lazy-certificates' if mode != MODES[0] else mode,
                local_intersection=mode == MODES[2])


def evaluate(tree, row):
    if isinstance(tree, int):
        return bool(row >> tree & 1)
    op, a, b = tree
    return (evaluate(a, row) or evaluate(b, row)) if op else (evaluate(a, row) and evaluate(b, row))


class LazyCertificateChecks(unittest.TestCase):
    def test_compatibility_against_exhaustive_cographs(self):
        rng = Random(5681)
        accepted = dropped = 0
        for n, count in ((4, 52), (5, 472), (6, 5504)):
            full = (1 << n) - 1
            pair_bit = {pair: 1 << i for i, pair in enumerate(combinations(range(n), 2))}
            choices = {mask: sum(pair_bit[pair] for pair in combinations(indices(mask), 2))
                       for mask in range(1, full + 1)}

            def relation(tree):
                if isinstance(tree, int):
                    return 0
                op, a, b = tree
                cross = sum(pair_bit[tuple(sorted((i, j)))] for i in indices(tree_leaves(a))
                            for j in indices(tree_leaves(b))) if op == 0 else 0
                return relation(a) | relation(b) | cross

            def cooccurrences(family):
                combined = 0
                for cert in family:
                    combined |= choices[cert]
                return combined

            reference = {relation(tree) for tree in _formulas(n, full).values()}
            self.assertEqual(len(reference), count)
            for _ in range(600):
                p = rng.sample(range(1, full + 1), rng.randint(1, 4))
                z = rng.sample(range(1, full + 1), rng.randint(1, 4))
                a, b = cooccurrences(p), cooccurrences(z)
                expected = any(mask & a == a and not mask & b for mask in reference)
                tree, obstruction = compatible_tree(full, p, z)
                self.assertEqual(tree is not None, expected)
                self.assertEqual(obstruction is None, expected)
                if expected and all(x & y for x in p for y in z):
                    accepted += 1
                    formula = restrict_certificates(tree, p, z)
                    dropped += tree_leaves(formula) != full
                    self.assertTrue(all(evaluate(formula, row) for row in p))
                    self.assertTrue(all(not evaluate(formula, full ^ row) for row in z))
        self.assertGreater(dropped, 0)
        print(f'1,800 compatibility queries, {accepted} reconstructible, {dropped} dropping leaves')

    def test_complete_read_once_families_reconstruct_all_leaves(self):
        rng = Random(817)
        for n in (4, 5, 6):
            full = (1 << n) - 1
            for truth in rng.choices(tuple(_formulas(n, full)), k=100):
                p, z = complete_certificates(n, truth)
                tree, obstruction = compatible_tree(full, p, z)
                self.assertIsNone(obstruction)
                formula = restrict_certificates(tree, p, z)
                self.assertEqual(tree_leaves(formula), full)
                self.assertTrue(all(evaluate(formula, row) == bool(truth >> row & 1) for row in range(full + 1)))

    def test_pinwheel_has_a_checked_spanning_tree_clause(self):
        p, z = (3, 26, 12), (9, 21, 6)
        self.assertTrue(all((a & b).bit_count() == 1 for a in p for b in z))
        _, obstruction = compatible_tree(31, p, z)
        self.assertEqual(obstruction.leaves, 31)
        memberships = tuple(tuple(tuple(1 + (sign * 3 + row) * 5 + i if cert >> i & 1 else None
                                        for i in range(5)) for row, cert in enumerate(family))
                            for sign, family in enumerate((p, z)))
        self.assertLessEqual(len(obstruction_clause(obstruction, memberships)), 16)
        spoiled = Obstruction(31, (obstruction.trees[0][:-1], obstruction.trees[1]))
        with self.assertRaises(ValueError):
            obstruction_clause(spoiled, memberships)

        # Submit these fixed local obligations to the zero-sharing SAT shape.
        stats, proofs = Counter(), []

        def checked(_, variables, clauses, trace):
            proofs.append(check_proof(variables, clauses, [*(trace or ()), '0']))

        status = decomposition_status(intersection_matrix(p, z), 0, certificates=(p, z), stats=stats,
                                      verify_unsat=checked, **options(MODES[2]))
        self.assertEqual(status, 'UNSAT')
        self.assertEqual((stats['models'], stats['cuts'], len(proofs)), (1, 1, 1))

    def test_lazy_backends_match_reference_and_check_unsat_proofs(self):
        cases = ((4, ((0, 1), (1, 2), (2, 3), (3, 0)), 0),
                 (4, ((0, 1), (1, 2), (2, 3)), 1),
                 (5, tuple((i, (i + 1) % 5) for i in range(5)), 3))
        for n, edges, minimum in cases:
            p, z = graph_certificates(n, edges)
            for excess in range(max(0, minimum - 1), minimum + 1):
                expected = 'SAT' if excess == minimum else 'UNSAT'
                for mode in MODES:
                    witnesses = []
                    proofs = []

                    def checked(_, variables, clauses, trace):
                        proofs.append(check_proof(variables, clauses, [*(trace or ()), '0']))

                    result = complete_status(p, z, excess, conflicts=None, on_sat=lambda _, s: witnesses.append(s),
                                             verify_unsat=checked, **options(mode))
                    self.assertEqual(result, expected, (n, excess, mode))
                    if result == 'SAT':
                        self.assertEqual(gate_count(witnesses[0]), n - 1 + minimum)
                        self.assertTrue(all(witnesses[0].evaluate(row) == any(row & term == term for term in p)
                                            for row in range(1 << n)))
                    elif n == 5:
                        self.assertTrue(proofs)


def job(name, budget, mode, conflicts, proof, provider_capacity=None):
    case = load_cases(RESULTS / 'synthesis_cases.json')[name]
    if case.known != full_rows(case.n):
        raise ValueError('the backend expects complete certificates')
    p, z = complete_certificates(case.n, case.truth)
    bound = analyze(p, z)
    excess = budget - (bound.gates - bound.excess)
    stats, proofs, gates = Counter(), [], []

    def witness(_, solution):
        if gate_count(solution) > budget or any(solution.evaluate(row) != high for row, high in case.labels().items()):
            raise RuntimeError(f'invalid witness for {name} at {budget} gates')
        gates.append(gate_count(solution))

    def verified(readers, variables, clauses, trace):
        proofs.append((readers, check_proof(variables, clauses, [*(trace or ()), '0'])))

    before = perf_counter()
    status = complete_status(p, z, excess, conflicts=conflicts, stats=stats, on_sat=witness,
                             verify_unsat=verified if proof else None, provider_capacity=provider_capacity,
                             **options(mode))
    print(json.dumps(dict(name=name, budget=budget, mode=mode, status=status, seconds=round(perf_counter() - before, 4),
                          stats=stats, gates=gates, checked=proofs, provider_capacity=provider_capacity)), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--compare', action='store_true')
    group.add_argument('--frontier', action='store_true')
    group.add_argument('--job', nargs=3, metavar=('CASE', 'BUDGET', 'MODE'))
    parser.add_argument('--seconds', type=float, default=6)
    parser.add_argument('--conflicts', type=int, default=1500)
    parser.add_argument('--rounds', type=int, default=1, help='frontier steps per case while budgets are excluded')
    parser.add_argument('--proof', action='store_true')
    parser.add_argument('--providercapacity', nargs='?', const='subsets', choices=CAPACITY_LEVELS,
                        help='prescreen lazy regional layouts with shared outgoing capacities')
    args = parser.parse_args()
    if not args.seconds > 0 or args.conflicts < 1 or args.rounds < 1:
        parser.error('seconds, conflicts, and rounds must be positive')
    if args.job:
        name, budget, mode = args.job
        if mode not in MODES:
            parser.error(f'expected a backend in {MODES}')
        if args.providercapacity and mode == MODES[0]:
            parser.error('--providercapacity requires a lazy backend')
        job(name, int(budget), mode, args.conflicts, args.proof, args.providercapacity)
    else:
        for name, budget in FRONTIER_JOBS if args.frontier else JOBS:
            for mode in MODES[-1:] if args.frontier else MODES:
                steps = args.rounds if args.frontier else 1
                for current in range(budget, budget + steps):
                    command = [sys.executable, __file__, '--job', name, str(current), mode,
                               '--conflicts', str(args.conflicts)]
                    if args.proof:
                        command.append('--proof')
                    if args.providercapacity and mode != MODES[0]:
                        command.extend(('--providercapacity', args.providercapacity))
                    try:
                        child = run(command, timeout=args.seconds, capture_output=True, text=True)
                        if child.returncode:
                            raise RuntimeError(f'{name} at {current} using {mode} exited {child.returncode}\n'
                                               f'{child.stdout}{child.stderr}')
                        record = json.loads(child.stdout)
                    except TimeoutExpired:
                        record = dict(name=name, budget=current, mode=mode, status='TIMEOUT', seconds=args.seconds,
                                      provider_capacity=args.providercapacity if mode != MODES[0] else None)
                    print(json.dumps(record), flush=True)
                    if record['status'] != 'UNSAT':
                        break


if __name__ == '__main__':
    if any(flag in sys.argv for flag in ('--job', '--compare', '--frontier')):
        main()
    else:
        unittest.main()
