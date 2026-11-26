"""Classify the possible prefix sources in every three-star residual."""
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path
import runpy
import sys

data = runpy.run_path(str(Path(__file__).with_name("search-5258.py")))
cs = data["cs"]


def supports(active, by_line):
    edges = data["EDGES"]
    residual = [(p, l) for p, l in edges if (l - 13 if by_line else p) in active]
    raw = {v for e in residual for v in e}
    providers = set()
    for j in set(data["POINTS"]) - set(active):
        leaves = data["LINES"][j] if by_line else {l for p, l in edges if p == j}
        useful = sorted(raw.intersection(leaves))
        providers.update(s for n in (2, 3) for s in combinations(useful, n))
    sources = [(i,) for i in sorted(raw)] + sorted(providers)
    masks = [sum(1 << v for v in s) for s in sources]
    constraints = set()
    for a, b in residual:
        row = (1 << a) | (1 << b)
        for neg in data["NEG"]:
            constraints.add(sum(1 << i for i, mask in enumerate(masks)
                                if row & mask and not (neg & mask)))
    minimal = []
    for clause in sorted(constraints, key=lambda c: (c.bit_count(), c)):
        if not any(c & clause == c for c in minimal):
            minimal.append(clause)
    return len(raw), sources, tuple(minimal)


def theorem_screen(job):
    active, by_line, verify_sat = job
    raw, sources, clauses = supports(active, by_line)
    providers = list(range(raw, len(sources)))

    @lru_cache(maxsize=None)
    def possible(needs, left):
        if not needs:
            return True
        if not left:
            return False
        taken = 0
        packing = 0
        for clause in needs:
            if not (clause & taken):
                taken |= clause
                packing += 1
                if packing > left:
                    return False
        choices = needs[0]
        while choices:
            x = choices & -choices
            choices -= x
            if possible(tuple(clause for clause in needs if not (clause & x)), left - 1):
                return True
        return False

    def has_providers(budget, count):
        if not count:
            return possible(clauses, budget)
        for selected in combinations(providers, count):
            selected_mask = sum(1 << i for i in selected)
            if possible(tuple(c for c in clauses if not (c & selected_mask)), budget - count):
                return True
        return False

    below_raw = has_providers(raw - 1, 0)
    provider_at_raw = has_providers(raw, 1)
    two_at_thirteen = has_providers(13, 2)
    one_at_thirteen = has_providers(13, 1)
    expected = [False, False, False, raw == 12]
    enumerated = [below_raw, provider_at_raw, two_at_thirteen, one_at_thirteen]
    assert enumerated == expected

    # Independently encode the four cardinality queries in the local SAT solver.
    n = len(sources)
    cnf = [[i + 1 for i in range(n) if c >> i & 1] for c in clauses]
    checks = []
    if verify_sat:
        for budget, count in ((raw - 1, 0), (raw, 1), (13, 2), (13, 1)):
            at_most = cs.CardEnc.atmost(list(range(1, n + 1)), bound=budget)
            at_least = (cs.CardEnc.atleast([i + 1 for i in providers], bound=count, top_id=at_most.nv).clauses
                        if count else [])
            with cs.Solver(name="maplechrono", bootstrap_with=cnf + at_most.clauses + at_least) as solver:
                checks.append(solver.solve())
        assert checks == enumerated
    return dict(active=active, by_line=by_line, raw=raw, providers=len(providers), clauses=len(clauses),
                enumerated=enumerated, sat=checks, search_nodes=possible.cache_info().misses)


if __name__ == "__main__":
    jobs = [(active, by_line, "--sat" in sys.argv)
            for active in combinations(data["POINTS"], 3) for by_line in (False, True)]
    with Path(sys.argv[1]).open("x", encoding="utf-8") as records:
        with ProcessPoolExecutor(max_workers=22) as executor:
            summary = Counter()
            for result in executor.map(theorem_screen, jobs, chunksize=8):
                print(json.dumps(result), file=records, flush=True)
                summary[result["raw"]] += 1
        print(summary)
