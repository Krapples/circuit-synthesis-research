"""Check the monotone source-separation bound without using a SAT solver."""
from collections import Counter
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path
import runpy
import sys

data = runpy.run_path(str(Path(__file__).with_name("search-5258.py")))


def maximum_columns(active, by_line):
    rows = data["ROWS"]
    edges = data["EDGES"]
    centers = data["POINTS"]
    lines = data["LINES"]
    uncovered = sum(1 << i for i, (p, l) in enumerate(edges)
                    if (l - 13 if by_line else p) in active)
    columns = data["COLUMNS"].copy()
    for center in set(centers) - set(active):
        leaves = lines[center] if by_line else [l for p, l in edges if p == center]
        for size in (2, 3, 4):
            for support in combinations(sorted(leaves), size):
                mask = sum(1 << j for j in support)
                columns.append(sum(1 << i for i, row in enumerate(rows) if row & mask))
    return uncovered, columns


def support_bound(uncovered, columns):
    p = len(data["POS"])
    n = len(data["ROWS"])
    raw_count = sum(bool(column & uncovered) for column in columns[:26])
    constraints = set()
    for i in range(p):
        if uncovered >> i & 1:
            for j in range(p, n):
                constraints.add(sum(1 << k for k, bits in enumerate(columns)
                                    if bits >> i & 1 and not (bits >> j & 1)))
    minimal = []
    for clause in sorted(constraints, key=lambda c: (c.bit_count(), c)):
        if not any(s & clause == s for s in minimal):
            minimal.append(clause)
    coverage = [sum(1 << i for i, clause in enumerate(minimal) if clause >> w & 1)
                for w in range(len(columns))]
    allowed = 0
    maximal = []
    for w in sorted(range(len(columns)), key=lambda w: (-coverage[w].bit_count(), w)):
        covers = coverage[w]
        if covers and not any(covers & prior == covers for prior in maximal):
            maximal.append(covers)
            allowed |= 1 << w
    minimal = sorted({clause & allowed for clause in minimal}, key=lambda c: (c.bit_count(), c))

    @lru_cache(maxsize=None)
    def find(needs, left):
        if not needs:
            return 0
        if not left:
            return None
        taken = 0
        packing = 0
        for clause in needs:
            if not (clause & taken):
                taken |= clause
                packing += 1
                if packing > left:
                    return None
        choices = needs[0]
        while choices:
            x = choices & -choices
            choices -= x
            rem = find(tuple(c for c in needs if not c & x), left - 1)
            if rem is not None:
                return rem | x
        return None

    for size in range(1, raw_count + 1):
        support = find(tuple(minimal), size)
        if support is not None:
            assert all(clause & support for clause in constraints)
            return dict(clauses=len(minimal), bound=size,
                        support=[j for j in range(len(columns)) if support >> j & 1],
                        explored=find.cache_info().misses)
    raise AssertionError("The raw boundary separates all relevant rows.")


if __name__ == "__main__":
    if "--maximal-providers" in sys.argv:
        count = 3 if "--triples" in sys.argv else 2
        results = [dict(active=active, by_line=by_line,
                        **support_bound(*maximum_columns(active, by_line)))
                   for active in combinations(data["POINTS"], count) for by_line in (False, True)]
    else:
        results = []
        for i in range(16):
            seed, by_line = 5258 + i, bool(i % 2)
            _, _, _, _, uncovered, columns, _ = data["prefix_columns"](2, seed, by_line)
            results.append(dict(seed=seed, by_line=by_line, **support_bound(uncovered, columns)))
    with Path(sys.argv[1]).open("x", encoding="utf-8") as records:
        for r in results:
            print(json.dumps(r), file=records)
        print(Counter(r["bound"] for r in results))
