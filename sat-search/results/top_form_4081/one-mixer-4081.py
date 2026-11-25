"""Finite relaxation of the one-mixing-OR case, using graph and threshold clauses."""
from collections import Counter
from itertools import combinations
import runpy

data = runpy.run_path(__file__.replace("one-mixer-4081.py", "search-4081.py"))
N, EDGES, POS, NEG = (data[k] for k in ("N", "EDGES", "POS", "NEG"))
ALL = (1 << N) - 1
NEIGHBORS = [sum(1 << b if a == v else 1 << a if b == v else 0 for a, b in EDGES)
             for v in range(N)]


def submasks(mask):
    while mask:
        yield mask
        mask = (mask - 1) & mask


def clause_options(uncovered, negatives):
    hit_all = [all(support & e for e in uncovered) for support in range(ALL + 1)]
    remove = set()
    for support, is_cover in enumerate(hit_all):
        if is_cover and all(not hit_all[support ^ (1 << v)] for v in range(N) if support >> v & 1):
            remove.add(sum(1 << i for i, negative in enumerate(negatives) if not support & negative))
    return [m for m in remove if m and not any(m != k and not m & ~k for k in remove)]


def min_clauses(choices, uncovered_negatives, limit):
    if not uncovered_negatives:
        return 0
    if not limit or not choices:
        return None
    pick = min((1 << i for i in range(uncovered_negatives.bit_length()) if uncovered_negatives >> i & 1),
               key=lambda bit: sum(bool(c & bit) for c in choices))
    bounds = [min_clauses(choices, uncovered_negatives & ~m, limit - 1)
              for m in choices if m & pick]
    finite = [sub + 1 for sub in bounds if sub is not None]
    return min(finite, default=None)


if __name__ == "__main__":
    counts = Counter()
    example = None
    for s, neighbors in enumerate(NEIGHBORS):
        for w in submasks(neighbors):
            if w.bit_count() < 2:
                continue
            candidates = [e for e in POS if e & w and not e & (1 << s)]
            negatives = [row for row in NEG if row & w]
            for missing in combinations(candidates, 5):
                options = clause_options(missing, negatives)
                bound = min_clauses(options, (1 << len(negatives)) - 1, 4)
                counts[bound] += 1
                if bound is not None and (example is None or bound < example[0]):
                    example = bound, s, w, missing
    print("minimum clause count up to four:", counts)
    print("minimum example:", example)
