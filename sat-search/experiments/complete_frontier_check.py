"""Audit supplied complete-synthesis prototypes against independent gate programs."""

import argparse
from functools import lru_cache
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations
import json
from pathlib import Path
from random import Random
import sys
from time import perf_counter
import unittest

from complete_frontier import ANY, NONCONSTANT, CompleteFrontier, FrontierLimit, subsets
from rank_tight_family import verify_minor
from synthesis_bench import direct_sat
from synthesis_cases import truth_table


@lru_cache(maxsize=None)
def programs(n, maximum, signed):
    variables = CompleteFrontier(n).variables
    universe = (1 << (1 << n)) - 1
    minima = dict.fromkeys(variables, 0)
    frontier = {frozenset(variables)}
    for budget in range(1, maximum + 1):
        following = set()
        for state in frontier:
            results = {value for a, b in combinations(state, 2) for value in (a & b, a | b)}
            if signed:
                results.update(universe ^ a for a in state)
            for value in results - state:
                minima.setdefault(value, budget)
                following.add(state | {value})
        frontier = following
    return minima


def essential(n, table):
    return all(any((table >> a ^ table >> (a ^ (1 << i))) & 1 for a in range(1 << n)) for i in range(n))


def targets(n, signed):
    for table in range(1, (1 << (1 << n)) - 1):
        if essential(n, table) and (signed or all((table >> a & 1) <= (table >> (a | (1 << i)) & 1)
                                                  for a in range(1 << n) for i in range(n))):
            yield table


GRIDS = ((2, 4, True), (3, 4, True), (3, 4, False), (4, 5, False))


def compare(prototypes=None):
    checked = 0
    start = perf_counter()
    for n, maximum, signed in GRIDS:
        oracle = programs(n, maximum, signed)
        solver = CompleteFrontier(n, signed=signed)
        prototype = None if prototypes is None else prototypes[signed].Solver(n)
        records = []
        for table in targets(n, signed):
            for budget in range(n - 1, maximum + 1):
                witness = solver.synthesize(table, budget - n + 1, check_invariant=True)
                expected = oracle.get(table, maximum + 1) <= budget
                assert (witness is not None) == expected, (n, table, budget, signed)
                if witness is not None:
                    assert len(witness.gates) <= budget and truth_table(n, witness) == table
                if prototype is not None:
                    assert prototype.solve(table, budget - n + 1) == expected, (n, table, budget, signed)
                records.append(expected)
        checked += len(records)
        print(json.dumps(dict(experiment='minima', n=n, signed=signed, cases=len(records),
                              feasible=sum(records), prototypes=prototypes is not None,
                              seconds=round(perf_counter() - start, 4))), flush=True)
    return checked


class FrontierChecks(unittest.TestCase):
    def test_small_complete_minima_and_reconstruction(self):
        self.assertGreater(compare(), 600)

    def test_multislice_against_direct_formula_enumeration(self):
        rng = Random(62414)
        comparisons = 0
        for signed in (False, True):
            solver = CompleteFrontier(3, signed=signed)
            for _ in range(90):
                primary = rng.randrange(1, 8)
                ports = tuple(rng.randrange(2) for _ in range(rng.randrange(3)))
                patterns = tuple(sorted(rng.sample(range(4), rng.randrange(1, 5))))
                budget = rng.randrange(3) if signed else 0
                leaves = primary | (((1 << len(ports)) - 1) << 3)
                one = solver.one

                @lru_cache(maxsize=None)
                def enumerate_trees(support, left):
                    if support.bit_count() == 1:
                        index = support.bit_length() - 1
                        values = {tuple(solver.variables[index] if index < 3
                                        else one if pattern >> ports[index - 3] & 1 else 0 for pattern in patterns)}
                    else:
                        values = set()
                        low = support & -support
                        for sub in subsets(support ^ low):
                            a = sub | low
                            if a == support:
                                continue
                            for allowance in range(left + 1):
                                for x in enumerate_trees(a, allowance):
                                    for y in enumerate_trees(support ^ a, left - allowance):
                                        values.update((tuple(a & b for a, b in zip(x, y)),
                                                       tuple(a | b for a, b in zip(x, y))))
                    if left:
                        values.update(tuple(value ^ one for value in row) for row in enumerate_trees(support, left - 1))
                    return values

                actual = sorted(enumerate_trees(leaves, budget))
                selected = rng.choice(actual)
                for variant in range(3):
                    pool = (ANY, NONCONSTANT, 0, one)
                    desired = tuple(rng.choice((value, ANY, NONCONSTANT)) if variant == 0 else
                                    rng.choice((*pool, solver.variables[rng.randrange(3)], value))
                                    for value in selected)
                    expected = any(all(t == ANY or t == v or t == NONCONSTANT and v not in (0, one)
                                       for t, v in zip(desired, candidate)) for candidate in actual)
                    self.assertEqual(solver._local(primary, ports, patterns, desired, budget) is not None, expected)
                    comparisons += 1
        self.assertEqual(comparisons, 540)

    def test_state_limit_keeps_an_open_verdict(self):
        solver = CompleteFrontier(2)
        with self.assertRaises(FrontierLimit):
            solver.synthesize(solver.variables[0] & solver.variables[1], 0, max_states=0)


def load_prototype(path, name):
    spec = spec_from_file_location(name, path)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def profile():
    samples = []
    for n, maximum, signed in GRIDS:
        oracle = programs(n, maximum, signed)
        selected = tuple(targets(n, signed))
        samples.extend((n, table, budget, signed, oracle.get(table, maximum + 1) <= budget)
                       for table in selected[::max(1, len(selected) // 10)]
                       for budget in (maximum - 1, maximum))
    for mode in ('uncompressed', 'uncached', 'frontier', 'sat', 'hybrid'):
        start = perf_counter()
        results = dict(states=0, local_states=0, cache_hits=0, merged=0, fallbacks=0)
        for n, table, budget, signed, expected in samples:
            witness = None
            if mode != 'sat':
                solver = CompleteFrontier(n, signed=signed, compress=mode != 'uncompressed', cache=mode != 'uncached')
                try:
                    witness = solver.synthesize(table, budget - n + 1, max_states=60 if mode == 'hybrid' else None)
                except FrontierLimit:
                    results['fallbacks'] += 1
                    witness = direct_sat(n, {a: bool(table >> a & 1) for a in range(1 << n)}, budget, signed)
                results['states'] += solver.stats['states']
                results['local_states'] += solver.stats['local_states']
                results['cache_hits'] += solver.stats['local_hits']
                results['merged'] += solver.stats['merged_patterns']
            else:
                witness = direct_sat(n, {a: bool(table >> a & 1) for a in range(1 << n)}, budget, signed)
            assert (witness is not None) == expected
            if witness is not None:
                assert truth_table(n, witness) == table and len(witness.gates) <= budget
        print(json.dumps(dict(experiment='profile', mode=mode, jobs=len(samples),
                              seconds=round(perf_counter() - start, 4), **results)), flush=True)


if __name__ == '__main__':
    if '--prototypes' in sys.argv or '--profile' in sys.argv:
        parser = argparse.ArgumentParser(description=__doc__)
        parser.add_argument('--prototypes', nargs=3, type=Path, metavar=('MONOTONE', 'SIGNED', 'RANK_TIGHT'))
        parser.add_argument('--profile', action='store_true')
        args = parser.parse_args()
        if args.prototypes:
            monotone, signed, rank_tight = (load_prototype(path, f'prototype_{i}')
                                            for i, path in enumerate(args.prototypes))
            print(json.dumps(dict(experiment='rank', records=[(e, *rank_tight.family(e))
                                                             for e in (1, 2, 3)],
                                  explicit_minors=[verify_minor(e) for e in (1, 2, 3, 5, 8, 12)])), flush=True)
            compare({False: monotone, True: signed})
        if args.profile:
            profile()
    else:
        unittest.main()
