"""Check the cotree SAT encoding against exhaustive and linked witnesses."""

from collections import Counter
from random import Random
import sys
from time import perf_counter
import unittest

from antichain_search import _formula_steps, _joint_completion, frontier_demands, hitting_number, solve_partial
from certify_synthesis import check_proof
from joint_regional_synthesis import synthesize_partition
from label_formulas_check import RESULTS, partial_queries, query
from regional_search import _known_formulas, canonical_layouts, find_minimum, synthesize_forward
from regional_synthesis import MAX_LEAVES, _bits, _formulas, synthesize_regions, synthesize_signed_formula
from cube_search import boundary_rows
from synthesis_cases import boundary_labels
from synthesis_followup import load_cases


class CographFormulaChecks(unittest.TestCase):
    def test_static_labels_against_exhaustive_formulas(self):
        for width, (_, p, n) in partial_queries():
            full = (1 << width) - 1
            labels = {row.bit_length() - 1: bool(row & p) for row in _bits(p | n)}
            expected = any(table & p == p and not table & n for table in _formulas(width, full))
            result = synthesize_regions((full,), (0,), labels, formula_encoding='cograph')
            self.assertEqual(result is not None, expected, (width, p, n))
            if result is not None:
                self.assertTrue(all(result.evaluate(row) == high for row, high in labels.items()))

    def test_symbolic_ports_against_table_encoding(self):
        rng = Random(9241)
        for _ in range(60):
            group = rng.choice((1, 3, 5, 7))
            groups = (group, 15 ^ group)
            ports = (0, rng.randint(1, 2))
            terms = rng.sample(range(1, 15), 4)
            labels = {row: any(row & term == term for term in terms) for row in rng.sample(range(16), 10)}
            mode = rng.choice(('free', 'consistent', 'linked'))
            expected = synthesize_regions(groups, ports, labels, mode=mode)
            result = synthesize_regions(groups, ports, labels, mode=mode, formula_encoding='cograph')
            self.assertEqual(result is not None, expected is not None, (groups, ports, labels, mode))
            if result is not None and mode == 'linked':
                self.assertTrue(all(result.evaluate(row) == high for row, high in labels.items()))

    def test_linked_readers_on_a_region_wider_than_table_cap(self):
        width = MAX_LEAVES + 2
        early = (1 << width) - 1
        a, b, c = (1 << (width + i) for i in range(3))
        groups = (early, a | b | c)
        terms = (early | a, a | b, early | c)
        p, n = boundary_rows(width + 3, terms)
        labels = {**dict.fromkeys(p, True), **dict.fromkeys(n, False)}
        self.assertIsNone(synthesize_regions(groups, (0, 1), labels, formula_encoding='cograph'))
        result = synthesize_regions(groups, (0, 2), labels, reader_limits=((2, 2),), formula_encoding='cograph')
        self.assertIsNotNone(result)
        self.assertEqual(result.providers, ((), (0, 0)))
        self.assertTrue(all(result.evaluate(row) == any(row & term == term for term in terms)
                            for row in range(1 << (width + 3))))

    def test_minimum_search_with_cograph_backend(self):
        for width, terms, minimum in ((4, (3, 6, 12), 4), (10, (31, 31 << 5), 9)):
            p, n = boundary_rows(width, terms)
            labels = {**dict.fromkeys(p, True), **dict.fromkeys(n, False)}
            for backend in ('cograph', 'joint-cograph'):
                self.assertIsNone(find_minimum(width, labels, minimum - 1, formula_backend=backend))
                gates, result = find_minimum(width, labels, minimum, formula_backend=backend)
                self.assertEqual(gates, minimum)
                self.assertTrue(all(result.evaluate(row) == any(row & term == term for term in terms)
                                    for row in range(1 << width)))

    def test_joint_primary_partition_matches_explicit_layout_search(self):
        for terms in ((3, 6, 12), (3, 6, 9, 12), (3, 5, 9, 14), (3, 12)):
            p, n = boundary_rows(4, terms)
            labels = {**dict.fromkeys(p, True), **dict.fromkeys(n, False)}
            for ports in ((0,), (0, 2), (0, 3), (0, 0, 4), (0, 1, 3)):
                gates = 4 + sum(ports) - len(ports)
                expected = any(synthesize_regions(groups, ports, labels, formula_encoding='cograph',
                                                  reader_limits=((2, None),) * (len(ports) - 1)) is not None
                               for groups, counts in canonical_layouts(4, gates) if counts == ports)
                result = synthesize_partition(4, ports, labels)
                self.assertEqual(result is not None, expected, (terms, ports))
                if result is not None:
                    self.assertTrue(all(result.evaluate(row) == any(row & term == term for term in terms)
                                        for row in range(16)))

    def test_joint_partition_selects_only_the_required_inputs(self):
        labels = {row: row & 5 == 5 for row in range(8)}
        self.assertIsNone(synthesize_partition(3, (0,), labels, input_limit=1))
        result = synthesize_partition(3, (0,), labels, input_limit=2)
        self.assertIsNotNone(result)
        self.assertEqual(result.groups, (5,))
        self.assertTrue(all(result.evaluate(row) == high for row, high in labels.items()))

    def test_signed_formulas_against_enumeration_of_leaf_signs(self):
        rng = Random(1298)
        for width in range(2, 5):
            rows = range(1 << width)
            full = (1 << width) - 1
            tables = _formulas(width, full)
            for _ in range(40):
                labels = {row: rng.choice((False, True)) for row in rng.sample(rows, rng.randint(2, len(rows)))}
                cols, p, n = query(width, [row for row in labels if labels[row]], [row for row in labels if not labels[row]])
                expected = any(all(bool(table >> (row ^ sign) & 1) == high for row, high in labels.items())
                               for sign in rows for table in tables)
                solved = synthesize_signed_formula(cols, p, n)
                self.assertEqual(solved is not None, expected, labels)
                if solved is not None:
                    formula, sign = solved
                    signed = tuple(col ^ (p | n) if sign >> i & 1 else col for i, col in enumerate(cols))
                    steps = []
                    self.assertEqual(_formula_steps(formula, signed, steps), p)
                    self.assertEqual(len(steps), width - 1)

    def test_signed_known_answers(self):
        # A single OR with a negative leaf is read-once. Parity and a multiplexer are not.
        cases = ((2, lambda row: bool(row & 1 or not row & 2), True),
                 (2, lambda row: row.bit_count() == 1, False),
                 (3, lambda row: bool(row & (4 if row & 1 else 2)), False))
        for width, target, expected in cases:
            rows = range(1 << width)
            args = query(width, [row for row in rows if target(row)], [row for row in rows if not target(row)])
            self.assertEqual(synthesize_signed_formula(*args) is not None, expected)

    def test_free_signs_can_reduce_the_binary_budget_on_a_monotone_partial_table(self):
        labels = {5: True, 9: True, 3: False, 12: False}
        self.assertIsNone(solve_partial(4, labels, 1))
        self.assertIsNotNone(solve_partial(4, labels, 2))
        cols, p, n = query(4, (5, 9), (3, 12))
        self.assertTrue(all(col not in (p, n) for col in cols))
        formula, sign = synthesize_signed_formula(cols[:2], p, n)
        signed = tuple(col ^ (p | n) if sign >> i & 1 else col for i, col in enumerate(cols[:2]))
        steps = []
        self.assertEqual(_formula_steps(formula, signed, steps), p)
        self.assertEqual(len(steps), 1)


def profile():
    cases = [case for case in load_cases(RESULTS / 'synthesis_cases.json').values() if case.n == 5]
    expected = None
    for encoding in ('tables', 'cograph', 'forward'):
        _formulas.cache_clear()
        _known_formulas.cache_clear()
        verdicts = []
        elapsed = 0
        for case in cases:
            all_labels = case.labels()
            labels = boundary_labels(case.n, all_labels)
            start = perf_counter()
            if encoding == 'forward':
                result = synthesize_forward((1, 30), (0, 2), labels, reader_limits=((2, 2),))
            else:
                result = synthesize_regions((1, 30), (0, 2), labels, formula_encoding=encoding,
                                            reader_limits=((2, 2),))
            elapsed += perf_counter() - start
            verdicts.append(result is not None)
            if result is not None and any(result.evaluate(row) != high for row, high in all_labels.items()):
                raise RuntimeError(f'invalid {encoding} witness for {case.name}')
        if expected is None:
            expected = verdicts
        elif expected != verdicts:
            raise RuntimeError('the table and cograph verdicts disagreed')
        print(f'{encoding}: {len(verdicts)} cases, {sum(verdicts)} SAT, {elapsed:.3f}s', flush=True)


def frontier_profile():
    cases = load_cases(RESULTS / 'synthesis_cases.json')
    for name, minimum in (('hypergraph-07', 7), ('cycle-5', 7), ('comparator-10', 9)):
        case = cases[name]
        target = case.labels()
        labels = boundary_labels(case.n, target)
        for budget in (minimum - 1, minimum):
            for joint in (False, True):
                stats = Counter()
                started = perf_counter()
                result = solve_partial(case.n, labels, budget, sharing=budget + 1 - case.n,
                                       jointcompletion=joint, stats=stats)
                elapsed = perf_counter() - started
                if (result is not None) != (budget == minimum) or (result is not None and (
                        len(result.gates) > budget or any(result.evaluate(row) != high for row, high in target.items()))):
                    raise RuntimeError(f'bad verdict or witness for {name} budget {budget}')
                print(f'{name} b={budget} joint={joint} {elapsed:.4f}s '
                      f'({stats["joint_completion_patterns"]} SAT patterns)', flush=True)


def certify_frontier():
    cases = load_cases(RESULTS / 'synthesis_cases.json')
    for name in ('hypergraph-07', 'cycle-5'):
        case = cases[name]
        labels = boundary_labels(case.n, case.labels())
        cols, p, n = query(case.n, [row for row in labels if labels[row]], [row for row in labels if not labels[row]])
        required = hitting_number(frontier_demands(cols, p, n))
        stats = Counter()
        proof_steps = []

        def checked(variables, clauses, trace):
            proof_steps.append(check_proof(variables, clauses, [*(trace or ()), '0']))

        result = _joint_completion(cols, required, 6, p, n, stats, on_unsat=checked)
        if result is not None or len(proof_steps) != stats['joint_completion_patterns'] or not proof_steps:
            raise RuntimeError(f'incomplete joint proof for {name}')
        print(f'{name} b=6: {len(proof_steps)} checked SAT patterns, {sum(proof_steps)} DRUP additions', flush=True)


if __name__ == '__main__':
    if sys.argv[1:] == ['--profile']:
        profile()
    elif sys.argv[1:] == ['--frontier-profile']:
        frontier_profile()
    elif sys.argv[1:] == ['--certify-frontier']:
        certify_frontier()
    else:
        unittest.main()
