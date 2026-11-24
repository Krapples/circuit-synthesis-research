"""Independent checks and matched frozen-corpus port certificate benchmarks."""

import argparse
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import chain, combinations, product
import json
from multiprocessing import get_context
from pathlib import Path
from random import Random
from time import perf_counter, process_time
import traceback
import unittest

from certificate_decomposition import complete_status
from certificate_rank_check import RESULTS, complete_certificates, gate_count, graph_certificates
from certify_synthesis import check_proof, write_gzip
from cube_search import ordered_port_lb, port_costs, rterms_support
from port_certificates import (PORT_CERTIFICATE_LEVELS, incoming_port_bound, minimal_zero_certificates,
                               modular_rank, rectangle_clique, rectangle_partition, residual_matrix)
from synthesis_bench import peak_bytes
from synthesis_cases import Builder, Witness, full_rows, trim, truth_table
from synthesis_followup import digest, load_cases, read_rows
from pysat.solvers import Solver


MANIFEST = RESULTS / 'synthesis_cases.json'
ENDPOINTS = RESULTS / 'synthesis_endpoints.jsonl'
LEVELS = (None, *PORT_CERTIFICATE_LEVELS)
PROFILE_LEVELS = ('baseline', 'compatibility', *PORT_CERTIFICATE_LEVELS, 'rank-output')
JOBS = (('hypergraph-12', 7), ('hypergraph-12', 8), ('threshold-5-3', 9),
        ('hypergraph-04', 12), ('hypergraph-09', 11), ('hypergraph-10', 12),
        ('threshold-6-4', 12), ('random-monotone-05', 13))


def reference_partition(matrix):
    """Slow reference that covers a set of cell coordinates."""
    height, width = len(matrix), len(matrix[0])
    ones = frozenset((i, j) for i, j in product(range(height), range(width)) if matrix[i][j])
    rectangles = []
    for rs, cs in product(range(1, 1 << height), range(1, 1 << width)):
        rectangle = frozenset((i, j) for i, j in product(range(height), range(width))
                              if rs >> i & 1 and cs >> j & 1)
        if rectangle <= ones:
            rectangles.append(rectangle)

    @lru_cache(maxsize=None)
    def solve(remaining):
        if not remaining:
            return 0
        first = min(remaining)
        return 1 + min(solve(remaining - rect) for rect in rectangles if first in rect and rect <= remaining)

    return solve(ones)


def certificate_paths(n, circuit, row):
    values = [bool(row >> i & 1) for i in range(n)]
    for op, a, b in circuit.gates:
        values.append((values[a] or values[b]) if op else (values[a] and values[b]))
    required = values[circuit.output]
    edges = set()
    visited = set()

    def visit(wire):
        if wire < n or wire in visited:
            return
        visited.add(wire)
        op, a, b = circuit.gates[wire - n]
        for slot, child in enumerate((a, b)):
            if values[child] == required:
                edges.add((wire, slot, child))
                visit(child)
                if op == required:
                    break

    visit(circuit.output)
    return edges


def check_with_minisat(variables, clauses, proof):
    """Check each Glucose DRUP addition using only MiniSat unit propagation."""
    with Solver(name='m22', bootstrap_with=clauses) as checker:
        count = 0
        for line in proof:
            fields = line.split()
            if not fields or fields[0] == 'd':
                continue
            terms = list(map(int, fields))
            if terms[-1] != 0 or any(not lit or abs(lit) > variables for lit in terms[:-1]):
                raise ValueError('invalid DRUP addition')
            clause = terms[:-1]
            consistent, _ = checker.propagate(assumptions=[-lit for lit in clause])
            if consistent:
                raise ValueError(f'DRUP addition {count + 1} is not RUP')
            count += 1
            if not clause:
                return count
            checker.add_clause(clause)
    raise ValueError('proof never derived the empty clause')


def flatten_witness(n, candidate):
    """Compile the decoded regional formulas to independently checkable gates."""
    builder = Builder(n)
    signals = []

    def compile_tree(tree, leaves):
        if isinstance(tree, int):
            return leaves[tree]
        op, left, right = tree
        return builder.gate(op, compile_tree(left, leaves), compile_tree(right, leaves))

    for group, ports, formula in zip(candidate.groups, candidate.providers, candidate.formulas):
        leaves = [i for i in range(n) if group >> i & 1] + [signals[i] for i in ports]
        signals.append(compile_tree(formula, leaves))
    return builder.finish(signals[-1])


class PortCertificateChecks(unittest.TestCase):
    def test_all_three_by_three_matrices_and_strict_clique_gap(self):
        for mask in range(1 << 9):
            matrix = tuple(tuple(mask >> (i * 3 + j) & 1 for j in range(3)) for i in range(3))
            exact = reference_partition(matrix)
            rank = max(modular_rank(matrix, p) for p in (2, 101))
            clique = rectangle_clique(matrix)
            self.assertLessEqual(max(rank, clique), exact)
            self.assertEqual(rectangle_partition(matrix, max(rank, clique)), exact)
        cycle = ((1, 1, 0, 0), (0, 1, 1, 0), (0, 0, 1, 1), (1, 0, 0, 1))
        self.assertEqual((modular_rank(cycle, 101), rectangle_clique(cycle), rectangle_partition(cycle)), (3, 4, 4))

    def test_exact_partition_strictly_exceeds_rank_and_maximum_clique(self):
        matrix = ((1, 0, 1, 1, 1, 1), (1, 0, 0, 0, 0, 1), (0, 1, 1, 1, 0, 1),
                  (1, 1, 0, 0, 1, 0), (0, 1, 1, 1, 1, 0), (1, 0, 0, 1, 1, 1))
        self.assertEqual(max(modular_rank(matrix, p) for p in (2, 101)), 5)
        self.assertEqual(rectangle_clique(matrix), 5)
        cells = [(i, j) for i, row in enumerate(matrix) for j, value in enumerate(row) if value]
        self.assertFalse(any(all(not (matrix[i][c] and matrix[r][j]) for (i, j), (r, c) in combinations(group, 2))
                             for group in combinations(cells, 6)))
        self.assertEqual(rectangle_partition(matrix, 5), reference_partition(matrix))
        self.assertEqual(rectangle_partition(matrix, 5), 6)
        self.assertIsNone(rectangle_partition(matrix, 5, max_states=0))

    def test_residual_and_complete_scope(self):
        p, z = graph_certificates(4, ((0, 1), (1, 2), (2, 3)))
        self.assertEqual(minimal_zero_certificates(tuple(p)), tuple(sorted(z)))
        self.assertIsNone(residual_matrix(tuple(p), tuple(z), 6))
        self.assertEqual(incoming_port_bound(tuple(p), tuple(z), 1), 0)
        self.assertEqual(incoming_port_bound(tuple(p), tuple(z), 1, output=True), 2)
        with self.assertRaisesRegex(ValueError, 'complete monotone'):
            complete_status(p, z[:-1], 2, backend='lazy-certificates', portcertrank='rank')

    def test_concrete_circuit_regional_ports_and_partition_lower_bound(self):
        random = Random(59211)
        samples = []
        for _ in range(3200):
            n = random.randrange(3, 7)
            steps = tuple((random.randrange(2), *sorted(random.sample(range(wire), 2)))
                          for wire in range(n, n + random.randrange(3, 14)))
            samples.append((n, trim(n, Witness(steps, n + len(steps) - 1))))
        samples += [(c.n, c.witness) for c in load_cases(MANIFEST).values() if c.known == full_rows(c.n)]
        groups_checked = positive_bounds = output_bounds = pairs_checked = circuits_checked = 0
        for n, circuit in samples:
            truth = truth_table(n, circuit)
            p, z = (tuple(axis) for axis in complete_certificates(n, truth))
            if not p or not z:
                continue
            full = (1 << n) - 1
            if any(not any(term >> i & 1 for term in p) for i in range(n)):
                continue
            circuits_checked += 1
            self.assertEqual(minimal_zero_certificates(p), tuple(sorted(z)))
            parents = defaultdict(list)
            for wire, (_, a, b) in enumerate(circuit.gates, n):
                for slot, child in enumerate((a, b)):
                    parents[child].append((wire, slot, child))
            terminals = {wire for wire in parents if len(parents[wire]) > 1} | {circuit.output}

            def owner(wire):
                while wire not in terminals:
                    wire = parents[wire][0][0]
                return wire

            groups = Counter()
            local_ports = defaultdict(set)
            for i in range(n):
                groups[owner(i)] |= 1 << i
            for terminal in terminals:
                for edge in parents[terminal]:
                    local_ports[owner(edge[0])].add(edge)
            true_paths = {a: certificate_paths(n, circuit, a) for a in p}
            false_paths = {b: certificate_paths(n, circuit, full ^ b) for b in z}
            local_cost = 0
            for root, primary in groups.items():
                groups_checked += 1
                bound = incoming_port_bound(p, z, primary, 'exact')
                self.assertIsNotNone(bound)
                self.assertLessEqual(bound, len(local_ports[root]))
                local_cost += bound
                positive_bounds += bool(bound)
                output = root == circuit.output
                if output:
                    output_bound = incoming_port_bound(p, z, primary, 'exact', output=True)
                    self.assertIsNotNone(output_bound)
                    self.assertLessEqual(output_bound, len(local_ports[root]))
                    output_bounds += output_bound > bound
                for a, b in product(p, z):
                    if output or (a & primary and b & primary):
                        required = 1 - (a & b & primary).bit_count()
                        self.assertEqual(len(true_paths[a] & false_paths[b] & local_ports[root]), required)
                        pairs_checked += 1
            excess = len(circuit.gates) - n + 1
            self.assertLessEqual(max(len(groups) - 1, local_cost - len(groups) + 1), excess)
            if n <= 6:
                costs = port_costs(p, mono=True, certificate_level='exact')
                self.assertLessEqual(ordered_port_lb(p, costs), len(circuit.gates))
                output_costs = port_costs(p, mono=True, certificate_level='rank', certificate_output=True)
                self.assertLessEqual(ordered_port_lb(p, output_costs), len(circuit.gates))
        self.assertGreater(positive_bounds, 20)
        self.assertGreater(output_bounds, 20)
        print(f'regional check: {circuits_checked} circuits, {groups_checked} groups, {positive_bounds} nonzero bounds, '
              f'{output_bounds} strengthened output bounds, {pairs_checked} pairs')

    def test_guarded_cuts_preserve_known_answers_and_checked_unsat(self):
        for n, edges, minimum in ((4, ((0, 1), (1, 2), (2, 3)), 4),
                                  (5, tuple((i, (i + 1) % 5) for i in range(5)), 7)):
            p, z = graph_certificates(n, edges)
            for budget in (minimum - 1, minimum):
                for level in (*LEVELS, 'rank-output'):
                    stats, checked, witnesses = Counter(), [], []

                    def proof(_, variables, clauses, trace):
                        trace = [*(trace or ()), '0']
                        steps = check_proof(variables, clauses, trace)
                        self.assertEqual(check_with_minisat(variables, clauses, trace), steps)
                        checked.append(steps)

                    status = complete_status(p, z, budget - n + 1, conflicts=None, stats=stats,
                                             backend='lazy-certificates', local_intersection=True,
                                             portcertrank='rank' if level == 'rank-output' else level,
                                             portcertoutput=level == 'rank-output', verify_unsat=proof,
                                             on_sat=lambda _, candidate: witnesses.append(candidate))
                    if budget == minimum:
                        self.assertEqual(status, 'SAT')
                        self.assertEqual(gate_count(witnesses[0]), minimum)
                        self.assertTrue(all(witnesses[0].evaluate(x) == any(x & t == t for t in p)
                                            for x in range(1 << n)))
                    else:
                        self.assertEqual(status, 'UNSAT')
                        if n == 5:
                            self.assertTrue(checked)
        with self.assertRaisesRegex(ValueError, 'not RUP'):
            check_with_minisat(2, ((1, 2),), ('1 0', '0'))


def ordered_profile(level):
    endpoints = {row['case']: row['final'] for row in read_rows(ENDPOINTS) if row['kind'] == 'interval'}
    rows = []
    for case in load_cases(MANIFEST).values():
        if case.known != full_rows(case.n):
            continue
        p, z = (tuple(axis) for axis in complete_certificates(case.n, case.truth))
        begin = perf_counter()
        output = level == 'rank-output'
        certificate_level = 'rank' if output else level
        costs = port_costs(p, mono=True, certificate_level=certificate_level, certificate_output=output)
        bound = ordered_port_lb(p, costs)
        rows.append(dict(name=case.name, family=case.family, lower=bound, regions=len(costs),
                         seconds=perf_counter() - begin,
                         archive_lower=endpoints.get(case.name, {}).get('lower'),
                         regional_costs=costs))
        if certificate_level in PORT_CERTIFICATE_LEVELS:
            rows[-1]['certificate_costs'] = {mask: incoming_port_bound(p, z, mask, certificate_level) for mask in costs}
        if output:
            rows[-1]['output_costs'] = costs.pout
    return dict(status='OK', cases=rows)


def lazy_job(name, budget, level, conflicts, proof, local_intersection=True, proof_dir=None):
    case = load_cases(MANIFEST)[name]
    p, z = complete_certificates(case.n, case.truth)
    stats, checked, witnesses, packets = Counter(), [], [], []

    def witness(_, candidate):
        gates = gate_count(candidate)
        circuit = flatten_witness(case.n, candidate)
        if (gates > budget or len(circuit.gates) > gates or truth_table(case.n, circuit) != case.truth
                or any(candidate.evaluate(row) != high for row, high in case.labels().items())):
            raise RuntimeError(f'invalid witness for {name} at {budget}')
        witnesses.append(dict(gates=gates, groups=candidate.groups, providers=candidate.providers,
                              formulas=candidate.formulas, circuit=circuit.gates, output=circuit.output))

    def verify(readers, variables, clauses, trace):
        proof_lines = [*(trace or ()), '0']
        steps = check_with_minisat(variables, clauses, proof_lines)
        checked.append((readers, steps))
        if proof_dir is not None:
            identifier = f'{name}-b{budget}-{level or "baseline"}-r' + '-'.join(map(str, readers))
            cnf = proof_dir / f'{identifier}.cnf.gz'
            drup = proof_dir / f'{identifier}.drup.gz'
            cnf_lines = chain((f'p cnf {variables} {len(clauses)}',),
                              (' '.join(map(str, (*clause, 0))) for clause in clauses))
            write_gzip(cnf, cnf_lines)
            write_gzip(drup, proof_lines)
            packets.append(dict(readers=readers, cnf=cnf.name, drup=drup.name,
                                cnf_sha256=digest(cnf), drup_sha256=digest(drup), steps=steps))

    status = complete_status(p, z, budget - rterms_support(p).bit_count() + 1, backend='lazy-certificates',
                             local_intersection=local_intersection,
                             portcertrank='rank' if level == 'rank-output' else level,
                             portcertoutput=level == 'rank-output', conflicts=conflicts, stats=stats, on_sat=witness,
                             verify_unsat=verify if proof else None)
    return dict(status=status, stats=stats, witnesses=witnesses, checked=checked, packets=packets)


def worker(pipe, function, args):
    with pipe:
        pipe.send('ready')
        pipe.recv()
        start, cpu = perf_counter(), process_time()
        try:
            result = function(*args)
        except Exception:
            result = dict(status='ERROR', traceback=traceback.format_exc())
        result.update(seconds=perf_counter() - start, cpu_seconds=process_time() - cpu, peak_bytes=peak_bytes())
        pipe.send(result)


def bounded(function, args, seconds):
    context = get_context('spawn')
    parent, child = context.Pipe()
    process = context.Process(target=worker, args=(child, function, args))
    process.start()
    child.close()
    try:
        with parent:
            if not parent.poll(20) or parent.recv() != 'ready':
                raise RuntimeError('benchmark worker did not start')
            parent.send(True)
            if not parent.poll(seconds):
                return dict(status='TIMEOUT', seconds=seconds, peak_bytes=peak_bytes(process.pid))
            result = parent.recv()
        if result['status'] == 'ERROR':
            raise RuntimeError(result['traceback'])
        return result
    finally:
        if process.is_alive():
            process.terminate()
        process.join()
        process.close()


def benchmark(args):
    jobs = JOBS if args.job is None else tuple((name, int(budget)) for name, budget in args.job)
    levels = LEVELS if args.levels is None else tuple(None if level == 'baseline' else level for level in args.levels)
    local = not args.without_local_intersection
    with args.benchmark.open('x', encoding='utf-8') as output:
        if args.proof_dir is not None:
            args.proof_dir.mkdir(parents=True, exist_ok=False)

        def write(record):
            output.write(json.dumps(record, sort_keys=True) + '\n')
            output.flush()

        write(dict(kind='meta', manifest_sha256=digest(MANIFEST), endpoints_sha256=digest(ENDPOINTS),
                   seconds=args.seconds, conflicts=args.conflicts, proof=args.proof, jobs=jobs,
                   local_intersection=local, levels=levels))
        if args.job is None:
            for level in levels:
                result = bounded(ordered_profile, (level,), 60)
                write(dict(kind='ordered', level=level, **result))
                print('ordered', level, result['status'], round(result['seconds'], 3), flush=True)
        for name, budget in jobs:
            for level in levels:
                if level == 'compatibility':
                    continue
                result = bounded(lazy_job, (name, budget, level, args.conflicts, args.proof, local, args.proof_dir),
                                 args.seconds)
                write(dict(kind='lazy', name=name, budget=budget, level=level, **result))
                print(name, budget, level, result['status'], round(result['seconds'], 3), flush=True)


if __name__ == '__main__':
    import sys
    if '--benchmark' in sys.argv:
        parser = argparse.ArgumentParser(description=__doc__)
        parser.add_argument('--benchmark', type=Path, required=True)
        parser.add_argument('--seconds', type=float, default=3)
        parser.add_argument('--conflicts', type=int, default=2500)
        parser.add_argument('--proof', action='store_true')
        parser.add_argument('--proof-dir', type=Path, help='write checked DIMACS and DRUP packets to a new directory')
        parser.add_argument('--without-local-intersection', action='store_true')
        parser.add_argument('--levels', nargs='+', choices=PROFILE_LEVELS)
        parser.add_argument('--job', nargs=2, action='append', metavar=('CASE', 'BUDGET'))
        args = parser.parse_args()
        if args.seconds <= 0 or args.conflicts < 1:
            parser.error('seconds and conflicts must be positive')
        if args.proof_dir is not None and not args.proof:
            parser.error('--proof-dir requires --proof')
        benchmark(args)
    else:
        unittest.main()
