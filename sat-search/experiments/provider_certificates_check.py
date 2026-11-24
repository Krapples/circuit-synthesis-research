"""Independent provider-bound tests and a serial ablation on the frozen corpus."""

import argparse
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
from random import Random
import sys
from time import perf_counter
import unittest

from certificate_decomposition import LazyTopology, _provider_model_cuts, complete_status
from certificate_rank_check import complete_certificates, graph_certificates
from cube_search import ordered_port_lb, port_cost_key, port_costs
from port_certificates_check import (MANIFEST, bounded, certificate_paths, check_with_minisat,
                                     flatten_witness, lazy_job)
from port_certificates import incompatible_primary_pairs
from provider_certificates import (ProviderResidual, compatible_partition, has_capacity,
                                   provider_obstruction, provider_residual, required_distinctions)
from synthesis_cases import Witness, full_rows, trim, truth_table
from synthesis_followup import digest, load_cases


@lru_cache(maxsize=None)
def monotone_tables(width):
    size = 1 << width
    return tuple(table for table in range(1 << size)
                 if all(not (table >> x & 1) or table >> (x | (1 << i)) & 1
                        for x in range(size) for i in range(width)))


def reference(positives, zeros, primary, providers):
    """Enumerate actual monotone provider tables, then cover the residual set."""
    p = tuple(a for a in positives if a & primary)
    z = tuple(b for b in zeros if b & primary)
    if any((a & b & primary).bit_count() > 1 for a, b in product(p, z)):
        return False
    cells = frozenset((i, j) for i, a in enumerate(p) for j, b in enumerate(z) if not a & b & primary)
    candidates = []
    for support, _ in providers:
        bits = tuple(1 << i for i in range(support.bit_length()) if support >> i & 1)

        def packed(mask):
            return sum(1 << i for i, bit in enumerate(bits) if mask & bit)

        candidates.append({frozenset((i, j) for i, j in cells
                                     if table >> packed(p[i]) & 1 and not table >> packed(~z[j]) & 1)
                           for table in monotone_tables(len(bits))})
    for selected in product(*candidates):
        if not cells <= frozenset().union(*selected):
            continue
        rectangles = []
        for provider, available in enumerate(selected):
            for rs, cs in product(range(1, 1 << len(p)), range(1, 1 << len(z))):
                rectangle = frozenset((i, j) for i in range(len(p)) for j in range(len(z))
                                      if rs >> i & 1 and cs >> j & 1)
                if rectangle <= available:
                    rectangles.append((provider, rectangle))

        def cover(remaining, caps):
            if not remaining:
                return True
            first = min(remaining)
            return any(cover(remaining - rect, (*caps[:j], caps[j] - 1, *caps[j + 1:]))
                       for j, rect in rectangles if caps[j] and first in rect and rect <= remaining)

        if cover(cells, tuple(cap for _, cap in providers)):
            return True
    return False


class ProviderCertificateChecks(unittest.TestCase):
    def test_full_certificate_ids_and_layer_separations(self):
        p, z, s = (5, 6, 8), (11, 12), 12
        query = provider_residual(p, z, s)
        self.assertEqual(query.rows, (1, 1, 0))
        self.assertEqual(query.common, ((1, 4), (2, 4), (8, 8)))
        self.assertEqual(required_distinctions(p, z, s), (1, 2))
        self.assertEqual(provider_obstruction(query, ((1, 2),)), 'eligibility')
        diagonal = provider_residual((5, 10), (9, 6), 12)
        self.assertIsNone(provider_obstruction(diagonal, ((3, 1), (16, 1))))
        self.assertEqual(provider_obstruction(diagonal, ((3, 1), (16, 1)), 'matching'), 'matching')
        self.assertEqual(provider_obstruction(diagonal, ((3, 2),), 'matching'), 'forced_consistency')
        self.assertTrue(compatible_partition(diagonal, ((3, 1), (3, 1))))
        self.assertFalse(compatible_partition(diagonal, ((3, 2),)))
        self.assertIsNone(compatible_partition(diagonal, ((3, 2),), max_states=0))
        triple = ProviderResidual(((1, 8, 8), (8, 2, 8), (8, 8, 4)), (1, 2, 4))
        self.assertIsNone(provider_obstruction(triple, ((7, 2), (7, 2)), 'matching'))
        self.assertEqual(provider_obstruction(triple, ((7, 2), (7, 2)), 'exact'), 'partition')
        self.assertTrue(has_capacity((3, 1, 2), (1, 2)))
        self.assertFalse(has_capacity((1, 1, 3), (1, 2)))

    def test_exact_against_enumerated_monotone_provider_tables(self):
        rng = Random(35299)
        comparisons = feasible = 0
        for _ in range(1000):
            p = tuple(sorted(rng.sample(range(1, 16), rng.randrange(1, 4))))
            z = tuple(sorted(rng.sample(range(1, 16), rng.randrange(1, 4))))
            primary = rng.randrange(1, 16)
            providers = tuple((rng.randrange(1, 15), rng.randrange(1, 4)) for _ in range(rng.randrange(1, 3)))
            query = provider_residual(p, z, primary)
            if query is None or not any(query.rows):
                continue
            expected = reference(p, z, primary, providers)
            self.assertIs(compatible_partition(query, providers), expected)
            actual = provider_obstruction(query, providers, 'exact')
            self.assertEqual(actual is None, expected)
            feasible += expected
            comparisons += 1
        self.assertGreater(comparisons, 100)
        self.assertGreater(feasible, 20)
        print(f'{comparisons} independent provider-table comparisons with {feasible} feasible')

    def test_concrete_circuits_match_ancestry_and_regional_capacity(self):
        rng = Random(9521)
        circuits = []
        for _ in range(1200):
            n = rng.randrange(3, 7)
            gates = tuple((rng.randrange(2), *sorted(rng.sample(range(wire), 2)))
                          for wire in range(n, n + rng.randrange(3, 15)))
            circuits.append((n, trim(n, Witness(gates, n + len(gates) - 1))))
        counts = Counter()
        for n, circuit in circuits:
            truth = truth_table(n, circuit)
            p, z = (tuple(axis) for axis in complete_certificates(n, truth))
            full = (1 << n) - 1
            if any(not any(a >> i & 1 for a in p) for i in range(n)):
                continue
            parents = defaultdict(list)
            supports = [1 << i for i in range(n)]
            for gate, (_, a, b) in enumerate(circuit.gates, n):
                supports.append(supports[a] | supports[b])
                for slot, wire in enumerate((a, b)):
                    parents[wire].append((gate, slot, wire))
            repeated = {wire for wire, edges in parents.items() if len(edges) > 1}
            terminals = repeated | {circuit.output}

            def region(wire):
                while wire not in terminals:
                    wire = parents[wire][0][0]
                return wire

            primaries = Counter()
            incoming = defaultdict(Counter)
            for i in range(n):
                primaries[region(i)] |= 1 << i
            for wire in repeated:
                for gate, _, _ in parents[wire]:
                    incoming[region(gate)][wire] += 1
            paths = ({a: certificate_paths(n, circuit, a) for a in p},
                     {b: certificate_paths(n, circuit, full ^ b) for b in z})
            for wire in repeated:
                reader_edges = set(parents[wire])
                high, low = ([c for c, edges in axis.items() if reader_edges & edges] for axis in paths)
                for a, b in product(high, low):
                    self.assertTrue(a & b & supports[wire])
                    counts['provider_pairs'] += 1
            for root in terminals:
                query = provider_residual(p, z, primaries[root], output=root == circuit.output)
                providers = tuple((supports[wire], cap) for wire, cap in incoming[root].items())
                self.assertIsNotNone(query)
                self.assertIsNone(provider_obstruction(query, providers, 'exact'))
                counts['regions'] += 1
                counts['nonempty_residuals'] += any(query.rows)
            base = port_costs(p, mono=True, certificate_level='compatibility')
            refined = port_costs(p, mono=True, certificate_level='compatibility', provider_eligibility=True)
            self.assertNotEqual(port_cost_key(base), port_cost_key(refined))
            self.assertLessEqual(ordered_port_lb(p, base), ordered_port_lb(p, refined))
            self.assertLessEqual(ordered_port_lb(p, refined), len(circuit.gates))
            counts['circuits'] += 1
        self.assertGreater(counts['nonempty_residuals'], 20)
        self.assertGreater(counts['provider_pairs'], 100)
        print(f'concrete verification {dict(counts)}')

    def test_lazy_known_answers_and_proofs(self):
        p, z = graph_certificates(5, tuple((i, (i + 1) % 5) for i in range(5)))
        for local, level in product((False, True), (None, 'eligibility', 'matching', 'exact')):
            for budget in (6, 7):
                checked, witnesses, stats = [], [], Counter()

                def verify(_, variables, clauses, proof):
                    checked.append(check_with_minisat(variables, clauses, [*(proof or ()), '0']))

                status = complete_status(p, z, budget - 4, backend='lazy-certificates', conflicts=None,
                                         local_intersection=local, provider_level=level, stats=stats,
                                         verify_unsat=verify, on_sat=lambda _, w: witnesses.append(w))
                self.assertEqual(status, 'SAT' if budget == 7 else 'UNSAT')
                if status == 'UNSAT':
                    self.assertTrue(checked)
                else:
                    circuit = flatten_witness(5, witnesses[0])
                    self.assertEqual(len(circuit.gates), 7)
                    self.assertEqual(truth_table(5, circuit), sum(1 << x for x in range(32)
                                                                if any(a & x == a for a in p)))
                if local and level is not None:
                    self.assertGreater(stats['provider_static_clauses'], 0)
        with self.assertRaisesRegex(ValueError, 'complete monotone'):
            complete_status(p, z[:-1], 2, backend='lazy-certificates', provider_level='eligibility')

    def test_shared_provider_cut_keeps_all_cone_escape_options(self):
        owners = ((1,), (2,), (3, 4), (5, 6), (7, 8, 9), (10, 11, 12))
        topology = LazyTopology(owners, (1, 2), (), (((13, 14),), ((15, 16),)))
        certificates = (3,), (2,)
        # Wire 1 has only the first primary, while wire 2 owns the second.
        # Either port of wire 2 can enter wire 1's cone by changing owner.
        model = {1, 2, 3, 5, 8, 12, 13, 15}
        kind, cuts = _provider_model_cuts(topology, (2, 2), model, certificates, 'eligibility')
        self.assertEqual(kind, 'consistency')
        self.assertEqual(cuts, [(-13, -15, 11, 4, 6)])
        self.assertTrue(all(-lit in model if lit < 0 else lit not in model for lit in cuts[0]))


JOBS = (('cycle-5', 6), ('cycle-5', 7), ('threshold-4-3', 6), ('threshold-4-3', 7),
        ('hypergraph-19', 9), ('hypergraph-19', 10), ('comparator-02', 8),
        ('comparator-02', 9), ('random-monotone-05', 13), ('hypergraph-05', 13))


def ordered_profile(enabled):
    records = []
    for case in load_cases(MANIFEST).values():
        if case.known != full_rows(case.n):
            continue
        p, _ = complete_certificates(case.n, case.truth)
        start = perf_counter()
        costs = port_costs(p, mono=True, certificate_level='compatibility', provider_eligibility=enabled)
        stats = Counter()
        lower = ordered_port_lb(tuple(p), costs, stats=stats)
        records.append(dict(name=case.name, lower=lower, seconds=perf_counter()-start, stats=stats))
    return dict(status='OK', cases=records)


def sampled_provider_queries():
    """Sample ancestor/capacity hypotheses across every complete frozen target."""
    rng = Random(73013)
    queries = []
    for case in load_cases(MANIFEST).values():
        if case.known != full_rows(case.n):
            continue
        p, z = (tuple(axis) for axis in complete_certificates(case.n, case.truth))
        conflicts = incompatible_primary_pairs(p, z)
        for sample in range(12):
            atoms = [1 << i for i in range(case.n)]
            rng.shuffle(atoms)
            primary = 0
            for atom in atoms:
                if rng.randrange(2) and all((primary | atom) & pair != pair for pair in conflicts):
                    primary |= atom
            outside = [atom for atom in atoms if not atom & primary]
            if not outside or not primary:
                continue
            query = provider_residual(p, z, primary, output=bool(sample % 2))
            if not any(query.rows):
                continue
            providers = tuple((sum(atom for atom in outside if rng.randrange(2)) or rng.choice(outside),
                               rng.randrange(1, 4)) for _ in range(rng.randrange(1, 5)))
            queries.append((query, providers))
    return queries


def query_profile(level, queries):
    start = perf_counter()
    counts = Counter()
    for query, providers in queries:
        obstruction = provider_obstruction(query, providers, 'matching' if level == 'exact' else level)
        if obstruction is not None:
            counts[obstruction] += 1
        elif level == 'exact':
            exact = compatible_partition(query, providers)
            counts[{True: 'feasible', False: 'partition', None: 'outside_exact_limits'}[exact]] += 1
        else:
            counts['no_exclusion'] += 1
    return dict(kind='query', level=level, queries=len(queries), counts=counts, seconds=perf_counter() - start)


def benchmark(args):
    jobs = JOBS if args.job is None else tuple((name, int(budget)) for name, budget in args.job)
    with args.benchmark.open('x', encoding='utf-8') as out:
        def record(row):
            out.write(json.dumps(row, sort_keys=True) + '\n')
            out.flush()

        record(dict(kind='meta', manifest_sha256=digest(MANIFEST), jobs=jobs, seconds=args.seconds,
                    conflicts=args.conflicts, exact=args.exact, query_profile=args.query_profile))
        if args.query_profile:
            queries = sampled_provider_queries()
            for level in ('eligibility', 'matching', 'exact') if args.exact else ('eligibility', 'matching'):
                result = query_profile(level, queries)
                record(result)
                print(json.dumps(result), flush=True)
            return
        if args.job is None and not args.exact:
            for enabled in (False, True):
                result = bounded(ordered_profile, (enabled,), 30)
                record(dict(kind='ordered', enabled=enabled, **result))
                print('ordered', enabled, result['status'], round(result['seconds'], 3), flush=True)
        modes = ((False, 'matching'), (False, 'exact')) if args.exact else (
            (False, None), (False, 'eligibility'), (False, 'matching'), (True, None), (True, 'eligibility'))
        for name, budget in jobs:
            for local, level in modes:
                result = bounded(lazy_job, (name, budget, None, args.conflicts, False, local, None, level), args.seconds)
                record(dict(kind='lazy', name=name, budget=budget, local=local, level=level, **result))
                print(name, budget, local, level, result['status'], round(result['seconds'], 3), flush=True)


if __name__ == '__main__':
    if '--benchmark' in sys.argv:
        parser = argparse.ArgumentParser(description=__doc__)
        parser.add_argument('--benchmark', type=Path, required=True)
        parser.add_argument('--seconds', type=float, default=1.25)
        parser.add_argument('--conflicts', type=int, default=1800)
        parser.add_argument('--job', nargs=2, action='append', metavar=('CASE', 'BUDGET'))
        parser.add_argument('--exact', action='store_true')
        parser.add_argument('--query-profile', action='store_true',
                            help='benchmark sampled standalone queries from the frozen targets')
        args = parser.parse_args()
        if args.seconds <= 0 or args.conflicts < 1:
            parser.error('seconds and conflicts must be positive')
        benchmark(args)
    else:
        unittest.main()
