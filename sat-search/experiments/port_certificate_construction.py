"""Probe construction upper bounds on complete targets with tighter port bounds."""

import argparse
from functools import lru_cache
import json
from pathlib import Path
from random import Random
from time import perf_counter

from certificate_rank_check import RESULTS, complete_certificates
from port_certificates import minimal_zero_certificates
from synthesis_cases import Builder, truth_table
from synthesis_followup import digest, load_cases


TARGETS = {
    'hypergraph-05': (11, 19), 'hypergraph-15': (11, 23), 'hypergraph-19': (10, 18),
    'hypergraph-20': (12, 25), 'hypergraph-09': (12, 21), 'hypergraph-10': (13, 21),
    'hypergraph-04': (12, 21), 'threshold-7-4': (12, 24), 'threshold-8-5': (14, 31),
    'comparator-05': (14, 31), 'comparator-09': (11, 28),
}
FALSE, TRUE = -1, -2


def combine(op, a, b):
    identity, absorbing = (TRUE, FALSE) if op == 0 else (FALSE, TRUE)
    if a == absorbing or b == absorbing:
        return absorbing
    if a == identity or a == b:
        return b
    if b == identity:
        return a
    a, b = sorted((a, b), key=repr)
    return op, a, b


def factored_witness(n, minterms, seed):
    """Recursively factor on either axis and prefer smaller shared expressions."""
    order = list(range(n))
    Random(seed).shuffle(order)

    @lru_cache(maxsize=None)
    def nodes(tree):
        if isinstance(tree, int):
            return frozenset()
        return nodes(tree[1]) | nodes(tree[2]) | {tree}

    @lru_cache(maxsize=None)
    def best(family):
        if not family:
            return FALSE
        if family == (0,):
            return TRUE
        if len(family) == 1 and family[0].bit_count() == 1:
            return family[0].bit_length() - 1
        candidates = []
        for axis, certificates in enumerate((family, minimal_zero_certificates(family))):
            for wire in order:
                bit = 1 << wire
                projected = tuple(sorted(term ^ bit for term in certificates if term & bit))
                if not projected:
                    continue
                remainder = tuple(term for term in certificates if not term & bit)
                if axis:
                    projected = minimal_zero_certificates(projected)
                    remainder = minimal_zero_certificates(remainder)
                split = combine(axis, wire, best(projected))
                candidates.append(combine(1 - axis, best(remainder), split))
        return min(candidates, key=lambda tree: len(nodes(tree)))

    builder = Builder(n)

    def compile_tree(node):
        if isinstance(node, int):
            if not 0 <= node < n:
                raise ValueError('expected a nonconstant target')
            return node
        op, left, right = node
        return builder.gate(op, compile_tree(left), compile_tree(right))

    return builder.finish(compile_tree(best(tuple(sorted(minterms)))))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seeds', type=int, default=6)
    args = parser.parse_args()
    if args.seeds < 1:
        parser.error('--seeds must be positive')
    manifest = RESULTS / 'synthesis_cases.json'
    cases = load_cases(manifest)

    with args.output.open('x', encoding='utf-8') as out:
        def record(value):
            out.write(json.dumps(value, sort_keys=True) + '\n')
            out.flush()

        record(dict(kind='meta', method='primal and dual single-variable factoring',
                    manifest_sha256=digest(manifest), seeds=list(range(args.seeds)), targets=TARGETS))
        for name, (lower, upper) in TARGETS.items():
            start = perf_counter()
            case = cases[name]
            minterms, _ = complete_certificates(case.n, case.truth)
            witness = min((factored_witness(case.n, minterms, seed) for seed in range(args.seeds)),
                          key=lambda candidate: len(candidate.gates))
            gates = len(witness.gates)
            if truth_table(case.n, witness) != case.truth or gates < lower:
                raise RuntimeError(f'inconsistent construction for {name}')
            record(dict(kind='result', case=name, lower=lower, old_upper=upper, new_upper=min(upper, gates),
                        gates=gates, output=witness.output, witness=witness.gates, seconds=perf_counter() - start))
            print(f'{name} | {lower} to {min(upper, gates)} gates | factored construction {gates}', flush=True)


if __name__ == '__main__':
    main()
