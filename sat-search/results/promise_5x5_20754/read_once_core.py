"""Independent finite check of read-once and once-shared formulas on the active promise."""

from functools import lru_cache
import json
from time import perf_counter


MASK = 12815360
ROWS = (2, 3, 4)
COLS = (0, 1, 2, 3)
PAIRS = tuple((u, v) for u in ROWS for v in COLS)
INPUTS = tuple(sum(1 << i for i, (u, _) in enumerate(PAIRS) if u == row) for row in ROWS) + tuple(
    sum(1 << i for i, (_, v) in enumerate(PAIRS) if v == col) for col in COLS
)
TARGET = sum(((MASK >> (5 * u + v)) & 1) << i for i, (u, v) in enumerate(PAIRS))


def partitions(leaves):
    """Unordered nontrivial bipartitions, counting equal leaves with multiplicity."""
    subsets = set()
    for bits in range(1, (1 << len(leaves)) - 1, 2):
        left = tuple(v for i, v in enumerate(leaves) if bits & (1 << i))
        right = tuple(v for i, v in enumerate(leaves) if not bits & (1 << i))
        pair = min((left, right), (right, left))
        if pair not in subsets:
            subsets.add(pair)
            yield pair


@lru_cache(maxsize=100_000)
def read_once(leaves):
    if len(leaves) == 1:
        return frozenset(leaves)
    results = set()
    for left, right in partitions(leaves):
        for a in read_once(left):
            for b in read_once(right):
                results.add(a & b)
                results.add(a | b)
    return frozenset(results)


def main():
    started = perf_counter()
    essentiality = []
    for i, column in enumerate(INPUTS):
        witness = next((p, n) for p in range(len(PAIRS)) for n in range(len(PAIRS))
                       if TARGET >> p & 1 and not (TARGET >> n & 1)
                       and column >> p & 1 and not (column >> n & 1)
                       and all(not (w >> p & 1) or w >> n & 1 for j, w in enumerate(INPUTS) if j != i))
        essentiality.append([i, *witness])

    ordinary = read_once(tuple(sorted(INPUTS)))
    counts = {}
    candidates = 0
    for bits in range(1, 1 << len(INPUTS)):
        module = tuple(sorted(v for i, v in enumerate(INPUTS) if bits & (1 << i)))
        outside = tuple(v for i, v in enumerate(INPUTS) if not bits & (1 << i))
        choices = read_once(module)
        counts[len(module)] = counts.get(len(module), 0) + len(choices)
        for value in choices:
            candidates += 1
            if TARGET in read_once(tuple(sorted((*outside, value, value)))):
                raise AssertionError(f'once-shared witness with module {bits} and value {value}')
    assert TARGET not in ordinary
    print(json.dumps({'target': TARGET, 'columns': INPUTS, 'essentiality': essentiality,
                      'read_once_target': False, 'ordinary_function_count': len(ordinary), 'module_candidates': candidates,
                      'function_counts_by_size': counts, 'seconds': round(perf_counter() - started, 6)}))


if __name__ == '__main__':
    main()
