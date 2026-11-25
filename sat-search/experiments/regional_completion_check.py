"""Independent completion checks and bounded matched quotient benchmarks."""

import argparse
from _thread import interrupt_main
from collections import Counter
import json
from pathlib import Path
from random import Random
import sys
from threading import Event, Thread, get_ident
from time import perf_counter
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'theory'))

from conditional_provider import formula_columns
from layout_projection import search_exact
from layout_projection_check import matched_three
from module_contraction import simplify, vars as truth_variables
from ordered_quotient_core import make_completion, materialize3, reconstruct, solve3
from port_certificates_check import bounded
from regional_block_completion import local_blocks
from regional_obligation_cache import ObligationCache
from signed_bound_compare import cases, restrict_essential
from two_sharing_core import ANY, local

COMPLETION_MODES = ('reference', 'cached', 'blocks', 'row-bounds', 'endpoint-branches', 'dominance-branches',
                    'port-first', 'witness-cover', 'port-first-witness', 'ordered-block', 'row-quotient',
                    'root-relaxation', 'root-portfolio', 'certificate-cnf', 'certificate-lazy', 'certificate-rows', 'certificate-anchored',
                    'certificate-absorption', 'certificate-fallback', 'padding-first', 'phase-first', 'bounded-multiplicity', 'phase-certificate')


def check_tree(tree, m, ports, pats, targets, signed):
    counts = Counter()
    one = (1 << (1 << m)) - 1

    def walk(node):
        if node[0] == 'x':
            counts[node[1]] += 1
            assert signed or not node[2]
        else:
            for child in node[1:]:
                walk(child)

    def value(node, mask):
        if node[0] == 'x':
            _, i, neg = node
            column = truth_variables(m)[i] if i < m else one if mask >> (i-m) & 1 else 0
            return column ^ (one if neg else 0)
        left, right = (value(child, mask) for child in node[1:])
        return left & right if node[0] == '&' else left | right

    walk(tree)
    assert counts == Counter((*range(m), *(m + i for i in ports)))
    assert all(target == ANY or value(tree, pat) == target for pat, target in zip(pats, targets))


class RegionalCompletionChecks(unittest.TestCase):
    def test_independent_multislice_oracle(self):
        rng = Random(74228)
        cache = ObligationCache(solver=local_blocks, maxsize=512)
        variants = tuple(make_completion(mode, cache_size=512) for mode in
                         ('port-first', 'witness-cover', 'port-first-witness', 'ordered-block', 'row-quotient',
                          'root-relaxation', 'phase-first', 'bounded-multiplicity', 'phase-certificate'))
        verdicts = Counter()
        for _ in range(500):
            m = rng.randrange(3)
            q = rng.randrange(max(1, 2-m), 5)
            signed = bool(rng.randrange(2))
            ports = tuple(rng.randrange(min(q, 3))*2+1 for _ in range(q))
            providers = tuple(sorted(set(ports)))
            pats = tuple(sum((mask >> j & 1) << i for j, i in enumerate(providers))
                         for mask in range(1 << len(providers)) if rng.random() < .65) or (0,)
            width = 1 << m
            ones = (1 << width) - 1
            total = (1 << (len(pats) * width)) - 1
            columns = tuple(sum(v << (j * width) for j in range(len(pats))) for v in truth_variables(m))
            columns += tuple(sum((ones if p >> i & 1 else 0) << (j * width) for j, p in enumerate(pats))
                             for i in ports)
            known = formula_columns(tuple(sorted(columns)), total, signed)
            for target in (rng.choice(sorted(known)), rng.randrange(total+1)):
                values = tuple((target >> (j*width)) & ones if rng.random() < .8 else ANY for j in range(len(pats)))
                expected = any(all(v == ANY or t >> (j*width) & ones == v for j, v in enumerate(values))
                               for t in known)
                self.assertEqual(local(m, ports, pats, values, signed) is not None, expected)
                direct = local_blocks(m, ports, pats, values, signed)
                self.assertEqual(direct is not None, expected)
                mapped = tuple(rng.sample(range(32, 88), len(providers)))
                replacement = dict(zip(providers, mapped))
                phases = {i: bool(signed and rng.randrange(2)) for i in providers}
                new_pats = tuple(sum(((p >> i & 1) ^ phases[i]) << replacement[i] for i in providers) for p in pats)
                for ps, port_ids, ts in ((pats, ports, values),
                                         (new_pats[::-1], tuple(replacement[i] for i in ports), values[::-1])):
                    witness = cache(m, port_ids, ps, ts, signed)
                    self.assertEqual(witness is not None, expected)
                    if witness is not None:
                        check_tree(witness, m, port_ids, ps, ts, signed)
                    for variant in variants:
                        candidate = variant(m, port_ids, ps, ts, signed)
                        self.assertEqual(candidate is not None, expected)
                        if candidate is not None:
                            check_tree(candidate, m, port_ids, ps, ts, signed)
                    verdicts['queries'] += 1
                    verdicts['feasible'] += expected
        self.assertEqual(verdicts['queries'], 2000)
        self.assertLessEqual(cache.metrics()['cache_entries'], 512)
        self.assertGreater(cache.metrics()['cache_hits'], 1000)
        print(json.dumps(dict(kind='oracle', feasible=verdicts['feasible'], **cache.metrics()), sort_keys=True), flush=True)

    def test_canonical_ties_equivalent_columns_and_polarity(self):
        cache = ObligationCache(maxsize=4, solver=local_blocks)
        ports = (2, 2, 5, 9)
        rows = tuple((x << 2) | (y << 5) | ((1 ^ x) << 9) for x in range(2) for y in range(2))
        values = (0, 2, 2, 2)
        a = cache(1, ports, rows, values, True)
        self.assertIsNotNone(a)
        check_tree(a, 1, ports, rows, values, True)
        rename = {2: 23, 5: 15, 9: 42}
        changed = tuple(sum(((row >> i & 1) ^ (i != 5)) << j for i, j in rename.items()) for row in rows)
        new_ports = tuple(rename[i] for i in ports)
        b = cache(1, new_ports, changed[::-1], values[::-1], True)
        self.assertIsNotNone(b)
        check_tree(b, 1, new_ports, changed[::-1], values[::-1], True)
        self.assertEqual(cache.metrics()['cache_hits'], 1)
        self.assertIsNone(cache(1, ports, (rows[0], rows[0] | 1), (0, 2), True))

    def test_quotient_backends_reconstruct_the_same_budget(self):
        targets = (0xffecf080, 0xeea0e000, 0xfcc8e0c0)
        for target, expected in zip(targets, (True, True, False)):
            for name in COMPLETION_MODES[:COMPLETION_MODES.index('root-relaxation')]:
                completion = make_completion(name)
                result = solve3(5, target, completion=completion)
                self.assertEqual(result is not None, expected)
                if result is not None:
                    gates, _ = materialize3(5, target, result)
                    self.assertLessEqual(len(gates), 7)

    def test_known_excess_four_corpus_witnesses(self):
        for n, target in ((5, 0xf880e880), (5, 0xfae0a800), (6, 0xeeeaecc0a880a880)):
            with self.subTest(truth=hex(target)):
                result = search_exact(n, target, 4)
                self.assertIsNotNone(result)
                gates, _ = reconstruct(n, target, *result, 4)
                self.assertEqual(len(gates), n + 3)


def record_call(work, mode, completion, stats=None, *, input_symmetry=False):
    name, n, target, excess, signed, engine = work
    if stats is None:
        stats = Counter()
    before = completion.metrics() if hasattr(completion, 'metrics') else {}
    start = perf_counter()
    if engine == 'quotient':
        result = solve3(n, target, signed, stats, completion=completion)
        witness = materialize3(n, target, result, signed) if result is not None else None
    else:
        result = search_exact(n, target, excess, signed, stats, completion=completion, input_symmetry=input_symmetry)
        witness = reconstruct(n, target, *result, excess) if result is not None else None
    if witness is not None:
        gates, output = witness
        values = list(truth_variables(n))
        universe = (1 << (1 << n)) - 1
        for op, a, b in gates:
            x, y = tuple(values[i] ^ (universe if phase else 0) for i, phase in (a, b))
            values.append(x & y if op == '&' else x | y)
        assert values[output[0]] ^ (universe if output[1] else 0) == target
        assert len(gates) <= n - 1 + excess
    after = completion.metrics() if hasattr(completion, 'metrics') else {}
    metrics = {key: value if key.endswith('_entries') else value - before.get(key, 0) for key, value in after.items()}
    return dict(case=name, n=n, truth=hex(target), excess=excess, basis='free' if signed else 'monotone',
                engine=engine, completion=mode, seconds=perf_counter()-start, stats=stats, cache=metrics,
                status='SAT' if witness is not None else 'LAYOUT_EXCLUDED',
                witness=witness)


def batch(worklist, mode):
    completion = make_completion(mode)
    return dict(status='OK', jobs=[record_call(work, mode, completion) for work in worklist])


def single(work, mode):
    return record_call(work, mode, make_completion(mode))


def profile(work, mode, seconds):
    """Sample a timed worker's Python stack without instrumenting the solver."""
    done, samples, stats = Event(), Counter(), Counter()
    completion = make_completion(mode)
    caller = get_ident()
    deadline = perf_counter() + seconds
    started = perf_counter()

    def sample():
        while not done.wait(.005):
            if perf_counter() >= deadline:
                interrupt_main()
                return
            frame = sys._current_frames().get(caller)
            while frame is not None and frame.f_code is not search_exact.__code__:
                code = frame.f_code
                if code.co_filename.endswith('regional_obligation_cache.py'):
                    samples['completion'] += 1
                    break
                if code.co_name == 'fixed' and code.co_filename.endswith('ordered_quotient_core.py'):
                    samples['fixed_layout'] += 1
                    break
                if code.co_filename.endswith('restriction_excess.py'):
                    samples['restriction'] += 1
                    break
                if code.co_name in ('_cut', '_step') and code.co_filename.endswith('layout_projection.py'):
                    samples['projection'] += 1
                    break
                frame = frame.f_back
            else:
                samples['other'] += 1

    sampler = Thread(target=sample, daemon=True)
    try:
        sampler.start()
        result = record_call(work, mode, completion, stats)
    except KeyboardInterrupt:
        result = dict(status='TIMEOUT', stats=stats, cache=completion.metrics())
    finally:
        done.set()
        sampler.join()
    return {**result, 'profile_seconds': perf_counter() - started, 'samples': samples}


def benchmark(args):
    if args.higher:
        corpus = {name: (n, target) for name, _, n, target in cases()}
        worklist = []
        for name, excess in (('hypergraph-12', 4), ('hypergraph-21', 4), ('hypergraph-03', 4),
                             ('comparator-02', 5), ('graph-03', 4), ('comparator-09', 5),
                             ('random-monotone-10', 4), ('comparator-04', 5)):
            n, target = corpus[name]
            n, target, _ = restrict_essential(n, target)
            n, target, _ = simplify(n, target, False)
            worklist.append((name, n, target, excess, False, 'layout'))
        if args.profile and not (args.row_bounds or args.endpoint_branches or args.dominance_branches or args.mode):
            worklist = [work for work in worklist if work[0] in ('hypergraph-12', 'comparator-09',
                                                                'random-monotone-10')]
    else:
        targets = matched_three()
        worklist = [(hex(target), 5, target, 3, False, 'layout') for target in targets]
        x, y, z, w, u = truth_variables(5)
        target = x&w | x&y&u | x&z&u | y&z&u | w&u
        worklist.append(('supplied-excess-four', 5, target, 4, False, 'layout'))
        worklist.extend((hex(target), 5, target, 3, False, 'quotient') for target in targets[:2])

    results = []
    expected = {}
    modes = ('cached', 'blocks') if args.higher else ('reference', 'cached', 'blocks')
    if args.row_bounds:
        modes = ('blocks', 'row-bounds')
    if args.endpoint_branches:
        modes = ('row-bounds', 'endpoint-branches')
    if args.dominance_branches:
        modes = ('endpoint-branches', 'dominance-branches')
    if args.mode:
        modes = (args.mode,)
    for mode in modes:
        if args.higher:
            for work in worklist:
                if args.profile:
                    result = bounded(profile, (work, mode, args.seconds), args.seconds + 2)
                else:
                    result = bounded(single, (work, mode), args.seconds)
                result = dict(case=work[0], n=work[1], truth=hex(work[2]), excess=work[3], basis='monotone',
                              engine=work[5], completion=mode, **{k: v for k, v in result.items()
                                                               if k not in ('case', 'n', 'truth', 'excess',
                                                                            'basis', 'engine', 'completion')})
                results.append(result)
                print(json.dumps(result, sort_keys=True), flush=True)
                key = work[0], work[3]
                if result['status'] != 'TIMEOUT':
                    assert expected.setdefault(key, result['status']) == result['status']
            continue
        result = bounded(batch, (worklist, mode), args.seconds)
        for job in result.get('jobs', ()):
            key = job['case'], job['engine']
            assert expected.setdefault(key, job['status']) == job['status']
            print(json.dumps(job, sort_keys=True), flush=True)
        summary = dict(kind='batch', completion=mode, **result)
        results.append(summary)
        print(json.dumps({k: v for k, v in summary.items() if k != 'jobs'}, sort_keys=True), flush=True)
    if args.output:
        with args.output.open('x', encoding='utf-8') as stream:
            for result in results:
                stream.write(json.dumps(result, sort_keys=True) + '\n')


def main():
    if '--bench' not in sys.argv:
        unittest.main(module=__name__)
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bench', action='store_true')
    parser.add_argument('--higher', action='store_true')
    parser.add_argument('--profile', action='store_true', help='sample higher-excess workers until the cap')
    variants = parser.add_mutually_exclusive_group()
    variants.add_argument('--row-bounds', action='store_true', help='compare block completion with monotone row bounds')
    variants.add_argument('--endpoint-branches', action='store_true', help='compare prefiltering constant row branches')
    variants.add_argument('--dominance-branches', action='store_true', help='compare prefiltering by row dominance')
    variants.add_argument('--mode', choices=COMPLETION_MODES, help='run one named completion mode')
    parser.add_argument('--seconds', type=float)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.profile and not args.higher:
        parser.error('--profile requires --higher')
    if args.seconds is None:
        args.seconds = 4 if args.higher else 25
    if args.seconds <= 0:
        parser.error('seconds must be positive')
    benchmark(args)


if __name__ == '__main__':
    main()
