"""Cross-check complete-function certificate bounds and profile the frozen corpus."""

from collections import Counter
from pathlib import Path
from random import Random
import sys
from time import perf_counter
import unittest

import antichain_search as ac
from certificate_decomposition import complete_status, decomposition_status
from certificate_rank import analyze, coexistence_color_bound, intersection_matrix, modular_rank, one_share_support
from certify_synthesis import check_proof
from cube_search import boundary_rows
from synthesis_cases import Builder, Witness, full_rows, trim, truth_table
from synthesis_followup import load_cases, read_rows


RESULTS = Path(__file__).resolve().parents[1] / 'results'


def complete_certificates(n, truth):
    full = (1 << n) - 1
    positive, zero = [], []
    for row in range(full + 1):
        high = bool(truth >> row & 1)
        neighbors = (row ^ (1 << i) for i in range(n) if bool(row >> i & 1) == high)
        if not any(bool(truth >> change & 1) == high for change in neighbors):
            (positive if high else zero).append(row if high else full ^ row)
    return positive, zero


def graph_certificates(n, edges):
    high, low = boundary_rows(n, tuple((1 << i) | (1 << j) for i, j in edges))
    return high, tuple(((1 << n) - 1) ^ row for row in low)


def gate_count(solution):
    return sum(group.bit_count() + len(ports) - 1 for group, ports in zip(solution.groups, solution.providers))


def concrete_certificate(n, circuit, row):
    tables = [bool(row >> i & 1) for i in range(n)]
    for op, a, b in circuit.gates:
        tables.append((tables[a] or tables[b]) if op else (tables[a] and tables[b]))
    reached, edges = {circuit.output}, set()
    high = tables[circuit.output]
    for v in range(n + len(circuit.gates) - 1, n - 1, -1):
        if v in reached:
            op, a, b = circuit.gates[v - n]
            children = ((0, a), (1, b)) if op != high else (((0, a),) if tables[a] == high else ((1, b),))
            for slot, child in children:
                reached.add(child)
                edges.add((v, slot, child))
    return reached, edges


class CertificateRankChecks(unittest.TestCase):
    def test_one_share_support_strictly_strengthens_rank(self):
        matrix = ((1, 1), (0, 1))
        self.assertEqual(modular_rank(matrix, 101), 2)
        self.assertFalse(one_share_support(matrix))
        self.assertEqual(decomposition_status(matrix, 1), 'UNSAT')
        self.assertTrue(one_share_support(((1, 1, 0), (0, 0, 1), (0, 0, 0))))
        self.assertEqual(modular_rank(((1, 1), (1, -1)), 2), 1)
        self.assertEqual(modular_rank(((1, 1), (1, -1)), 101), 2)

    def test_majority_with_guard_exact_bound(self):
        labels = sum(1 << row for row in range(16) if row & 1 and (row >> 1).bit_count() >= 2)
        positive, zeros = complete_certificates(4, labels)
        bound = analyze(positive, zeros)
        self.assertEqual((bound.max_entry, bound.rank, bound.gates), (1, 3, 5))
        circuit = ac.Circuit(4, ((0, 1, 2), (1, 1, 2), (0, 3, 5), (1, 4, 6), (0, 0, 7)), 8)
        self.assertTrue(all(circuit.evaluate(row) == bool(labels >> row & 1) for row in range(16)))

    def test_ordering_strictly_strengthens_boolean_factorization(self):
        matrix = ((0, 0, 1, 0, 0, 1), (0, 0, 0, 1, 1, 0), (0, 1, 0, 1, 1, 0),
                  (1, 1, 1, 1, 1, 1), (0, 0, 1, 1, 0, 0))
        self.assertEqual(modular_rank(matrix, 101), 5)
        self.assertEqual(decomposition_status(matrix, 2, prefix=False), 'SAT')
        self.assertEqual(decomposition_status(matrix, 2), 'UNSAT')

    def test_guarded_union_has_exact_twelve_gates(self):
        # OR of a guarded majority and a guarded five-vertex path, on disjoint inputs.
        terms = [1 | (1 << i) | (1 << j) for i, j in ((1, 2), (1, 3), (2, 3))]
        terms += [(1 << 4) | (3 << i) for i in range(5, 9)]
        truth = sum(1 << row for row in range(1 << 10) if any(row & term == term for term in terms))
        p, n = complete_certificates(10, truth)
        bound = analyze(p, n)
        self.assertEqual((bound.rank, bound.max_entry, bound.gates), (5, 1, 11))
        matrix = intersection_matrix(p, n)
        active_rows = [i for i, row in enumerate(matrix) if any(row)]
        self.assertEqual(len(active_rows), 5)
        self.assertTrue(all(tuple(int(i == j) for i in range(5)) in zip(*[matrix[r] for r in active_rows])
                            for j in range(5)))
        self.assertEqual(decomposition_status(matrix, 2), 'UNSAT')

        b = Builder(10)
        maj = b.gate(1, b.gate(0, 1, 2), b.gate(0, 3, b.gate(1, 1, 2)))
        path = b.gate(1, b.gate(0, 6, b.gate(1, 5, 7)), b.gate(0, 8, b.gate(1, 7, 9)))
        witness = b.finish(b.gate(1, b.gate(0, 0, maj), b.gate(0, 4, path)))
        self.assertEqual(len(witness.gates), 12)
        self.assertEqual(truth_table(10, witness), truth)
        self.assertEqual(decomposition_status(matrix, 3, regions=True, conflicts=None), 'SAT')

    def test_five_cycle_decomposition_exclusion_has_checked_proof(self):
        positive, zeros = graph_certificates(5, [(i, (i + 1) % 5) for i in range(5)])
        self.assertEqual(analyze(positive, zeros).gates, 6)
        matrix = intersection_matrix(positive, zeros)
        steps = []

        def checked(readers, variables, clauses, trace):
            self.assertEqual(readers, (2, 2))
            steps.append(check_proof(variables, clauses, [*(trace or ()), '0']))

        self.assertEqual(decomposition_status(matrix, 2, conflicts=None, verify_unsat=checked), 'UNSAT')
        self.assertEqual(len(steps), 1)
        self.assertEqual(decomposition_status(matrix, 3), 'SAT')

    def test_complete_terminal_certificates_at_known_small_minima(self):
        for width, edges, excess in ((4, [(0, 1), (1, 2), (2, 3), (3, 0)], 0),
                                     (4, [(0, 1), (1, 2), (2, 3)], 1),
                                     (5, [(i, (i + 1) % 5) for i in range(5)], 3)):
            positive, zeros = graph_certificates(width, edges)
            if excess:
                self.assertEqual(complete_status(positive, zeros, excess - 1, conflicts=3000), 'UNSAT')
            witnesses = []
            self.assertEqual(complete_status(positive, zeros, excess, conflicts=3000,
                                             on_sat=lambda _, solution: witnesses.append(solution)), 'SAT')
            self.assertEqual(len(witnesses), 1)
            self.assertEqual(gate_count(witnesses[0]), width - 1 + excess)
            self.assertTrue(all(witnesses[0].evaluate(row) == any(row & term == term for term in positive)
                                for row in range(1 << width)))

    def test_cooccurrence_colors_detect_odd_cycle_and_threshold_clique(self):
        p, n = graph_certificates(5, [(i, (i + 1) % 5) for i in range(5)])
        self.assertEqual(coexistence_color_bound(p, n), 3)
        triples = tuple(row for row in range(32) if row.bit_count() == 3)
        self.assertEqual(coexistence_color_bound(triples, triples), 5)

    def test_five_input_thresholds_have_ten_gate_constructions(self):
        for threshold in (2, 3):
            b = Builder(5)
            p, q = b.gate(1, 0, 1), b.gate(1, 2, 3)
            both = b.gate(1, b.gate(0, 0, 1), b.gate(0, 2, 3))

            def majority(a, b0, c):
                pair = b.gate(0, a, b0)
                other = b.gate(0, c, b.gate(1, a, b0))
                return b.gate(1, pair, other)

            out = b.gate(1, both, majority(p, q, 4)) if threshold == 2 else majority(both, b.gate(0, p, q), 4)
            circuit = b.finish(out)
            self.assertEqual(len(circuit.gates), 10)
            expected = sum(1 << row for row in range(32) if row.bit_count() >= threshold)
            self.assertEqual(truth_table(5, circuit), expected)

    def test_concrete_circuits_obey_rank_and_prefix(self):
        rng = Random(441)
        counts = Counter()
        for _ in range(360):
            n = rng.randint(2, 6)
            steps = tuple((rng.randrange(2), *sorted(rng.sample(range(i), 2)))
                          for i in range(n, n + rng.randint(1, 12)))
            circuit = trim(n, Witness(steps, n + len(steps) - 1))
            truth = truth_table(n, circuit)
            positive, zeros = complete_certificates(n, truth)
            low = [((1 << n) - 1) ^ row for row in zeros]
            # Sort in output-to-input order and retain wires with repeated reads.
            reads = Counter(wire for _, a, b in circuit.gates for wire in (a, b))
            repeated = sorted((wire for wire in reads if reads[wire] > 1), reverse=True)
            excess = sum(reads[wire] - 1 for wire in repeated)
            self.assertLessEqual(analyze(positive, zeros).gates, len(circuit.gates))
            self.assertLessEqual(coexistence_color_bound(positive, zeros), len(repeated) + 1)
            pos_certs = [concrete_certificate(n, circuit, row) for row in positive]
            neg_certs = [concrete_certificate(n, circuit, row) for row in low]
            for (a_vertices, a_edges), a in zip(pos_certs, positive):
                for (b_vertices, b_edges), b in zip(neg_certs, zeros):
                    common = Counter(wire for _, _, wire in a_edges & b_edges)
                    paths = 1
                    for wire in repeated:
                        self.assertLessEqual(common[wire], paths)
                        paths += int(wire in a_vertices and wire in b_vertices) - common[wire]
                    self.assertEqual(paths, (a & b).bit_count())
                    counts['pairs'] += 1
            counts['shared'] += bool(excess)
            if 1 <= excess <= 2 and counts['relaxation'] < 24:
                self.assertEqual(decomposition_status(intersection_matrix(positive, zeros), excess, regions=True), 'SAT')
                counts['relaxation'] += 1
        print(f'circuit check: 360 cones, {counts["shared"]} shared, {counts["pairs"]} certificate pairs')


def profile():
    cases = load_cases(RESULTS / 'synthesis_cases.json')
    rows = read_rows(RESULTS / 'synthesis_ablation.jsonl')
    analytic = {row['case']: max(row['bounds'].get(key, 0) for key in ('support', 'frontier', 'tight', 'graph_mono'))
                for row in rows if row['kind'] == 'analytical'}
    certified = {row['case']: row['final'] for row in rows if row['kind'] == 'interval' and row['basis'] == 'mono'}
    for row in read_rows(RESULTS / 'synthesis_endpoints.jsonl'):
        if row['kind'] == 'interval':
            certified[row['case']] = row['final']
    counts = Counter()
    seconds = Counter()
    for case in cases.values():
        if case.known != full_rows(case.n):
            continue
        start = perf_counter()
        p, n = complete_certificates(case.n, case.truth)
        basic = analyze(p, n)
        seconds['rank'] += perf_counter() - start
        pointwise = basic.gates - basic.excess + basic.max_entry
        combined = basic.gates
        counts['complete'] += 1
        counts['rank_over_pointwise'] += combined > pointwise
        counts['rank_over_analytical'] += combined > analytic[case.name]
        color_bound = basic.gates - basic.excess + coexistence_color_bound(p, n) - 1
        counts['colors_over_rank'] += color_bound > combined
        if basic.excess <= 2:
            start = perf_counter()
            status = decomposition_status(intersection_matrix(p, n), 2, conflicts=500)
            seconds['decomposition'] += perf_counter() - start
            counts[status] += 1
            if status == 'UNSAT':
                combined = basic.gates - basic.excess + 3
                counts['decomposition_over_rank'] += 1
        combined = max(combined, color_bound)
        if combined > certified[case.name]['upper']:
            raise RuntimeError(f'bound exceeds a verified witness on {case.name}')
        if combined > certified[case.name]['lower']:
            counts['combined_over_certified'] += 1
            print(f'{case.name}: certified {certified[case.name]}, candidate lower {combined}, '
                  f'pointwise {pointwise}, rank stage {basic.gates}, colors {color_bound}', flush=True)
        counts['combined_over_analytical'] += combined > analytic[case.name]
    print(dict(counts), {key: round(time, 3) for key, time in seconds.items()}, flush=True)


def endpoint(name, budget, proof=False):
    case = load_cases(RESULTS / 'synthesis_cases.json')[name]
    if case.known != full_rows(case.n):
        raise ValueError('expected a complete corpus target')
    p, n = complete_certificates(case.n, case.truth)
    base = analyze(p, n)
    support = base.gates - base.excess
    checked, witnesses = [], []

    def verify(readers, variables, clauses, trace):
        checked.append((readers, check_proof(variables, clauses, [*(trace or ()), '0'])))

    def witness(_, solution):
        if gate_count(solution) > budget or any(solution.evaluate(row) != high for row, high in case.labels().items()):
            raise RuntimeError(f'{name} decoded an invalid witness')
        witnesses.append(solution)

    status = complete_status(p, n, budget - support, conflicts=1500, on_sat=witness,
                             verify_unsat=verify if proof else None)
    print(f'{name} at {budget} gates: {status}, checked traces {checked}, verified witnesses {witnesses}', flush=True)


if __name__ == '__main__':
    if sys.argv[1:] == ['--profile']:
        profile()
    elif len(sys.argv) in (4, 5) and sys.argv[1] == '--endpoint':
        endpoint(sys.argv[2], int(sys.argv[3]), len(sys.argv) == 5 and sys.argv[4] == '--proof')
    else:
        unittest.main()
