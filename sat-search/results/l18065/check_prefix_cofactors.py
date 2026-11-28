"""Build checked prefix exclusions for saturated singleton AO2 layouts."""
import argparse
from functools import lru_cache
import hashlib
from itertools import combinations, permutations, product
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / "experiments"))

from certificate_decomposition import _add_closed_set_cut, complete_status
from certificate_rank import analyze, coexistence_color_bound
from certify_synthesis import check_proof
from monotone_frontier import monotone_frontier
from pysat.formula import IDPool
from pysat.solvers import Solver
from synthesis_cases import full_rows
from synthesis_followup import load_cases


def split(n, truth, i):
    """Return truth masks after assigning input i to zero and one."""
    bit = 1 << i
    low = high = 0
    for row in range(1 << (n - 1)):
        original = (row & (bit - 1)) | ((row & -bit) << 1)
        low |= ((truth >> original) & 1) << row
        high |= ((truth >> (original | bit)) & 1) << row
    return low, high


def checked_prefix_cofactors(n, truth):
    """Return excluded fixed-input sets and a summary of the checks."""
    checked = []
    derived = []

    @lru_cache(maxsize=None)
    def excluded(width, table):
        values = [bool(table >> row & 1) for row in range(1 << width)]
        positive, negative = monotone_frontier(values)
        if not positive or not negative:
            return False
        zeros = [(len(values) - 1) ^ row for row in negative]
        rank = analyze(positive, zeros)
        color = coexistence_color_bound(positive, zeros)
        budget = 2 * width - 2
        if max(rank.gates, rank.gates - rank.excess + color - 1) > budget:
            return True
        if color != width:
            return False

        if width > 3 and all(any(excluded(width - 1, cofactor)
                                 for cofactor in split(width, table, i))
                             for i in range(width)):
            derived.append(dict(width=width, truth=hex(table)))
            return True
        if width not in (4, 5):
            return False

        traces = []

        def verify(readers, variables, clauses, trace):
            steps = check_proof(variables, clauses, [*(trace or ()), "0"])
            traces.append(dict(readers=readers, checked_steps=steps))

        result = complete_status(positive, zeros, width - 1, backend="lazy-certificates",
                                 local_intersection=True, conflicts=500, verify_unsat=verify)
        checked.append(dict(width=width, truth=hex(table), verdict=result, traces=traces))
        return result == "UNSAT"

    cuts = []
    for size in range(1, n):
        for fixed in combinations(range(n), size):
            cofactors = {truth}
            for removed, i in enumerate(reversed(fixed)):
                cofactors = {t for f in cofactors for t in split(n - removed, f, i)}
            if any(excluded(n - size, t) for t in sorted(cofactors)):
                cuts.append(sum(1 << i for i in fixed))
    return cuts, dict(checked=checked, derived=derived)


def target_fingerprint(n, truth):
    return hashlib.sha256(f"{n}:{truth:x}".encode("ascii")).hexdigest()


def load_checked_prefixes(path, n, truth):
    """Load the checked cuts for the exact complete target and budget."""
    data = json.loads(Path(path).read_text(encoding="utf-8-sig"))
    if (data.get("schema") != "singleton-prefix-cofactors/1"
            or data.get("inputs") != n
            or data.get("truth_sha256") != target_fingerprint(n, truth)
            or data.get("budget") != 2 * n - 2):
        raise ValueError("cofactor evidence does not match the complete target and budget")
    cuts = tuple(data["cuts"])
    if len(cuts) != len(set(cuts)) or any(not 0 < cut < 1 << n for cut in cuts):
        raise ValueError("cofactor evidence contains invalid input sets")
    return cuts, data


def check_crossing_encoding():
    """Compare projected CNF models with all four-region port placements."""
    sources = (1, 1, 2, 2, 3, 3)
    tests = 0
    for fixed in range(1, 15):
        pool = IDPool()
        owners = {1 << i: [pool.id() for _ in range(4)] for i in range(4)}
        port_owners = [[pool.id() for _ in range(source)] for source in sources]
        clauses = []
        _add_closed_set_cut(clauses, pool, (2, 2, 2), owners, port_owners, fixed)
        with Solver(name="g4", bootstrap_with=clauses) as solver:
            for layout in permutations(range(4)):
                primary = [literal if region == layout[i] else -literal
                           for i in range(4) for region, literal in enumerate(owners[1 << i])]
                inside = {layout[i] for i in range(4) if fixed & (1 << i)}
                for targets in product(*(range(i) for i in sources)):
                    ports = [literal if region == target else -literal
                             for choices, target in zip(port_owners, targets)
                             for region, literal in enumerate(choices)]
                    crossing = any(target in inside and source not in inside
                                   for source, target in zip(sources, targets))
                    assert solver.solve(assumptions=primary + ports) == crossing
                    tests += 1
    return tests


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", nargs="?")
    parser.add_argument("--check-encoding", action="store_true")
    args = parser.parse_args()
    if args.check_encoding:
        print(f"{check_crossing_encoding()} crossing encodings matched the port test")
        return
    case = load_cases(HERE.parent / "synthesis_cases.json").get(args.target)
    if case is None or not 2 <= case.n <= 8 or case.known != full_rows(case.n):
        parser.error("expected a complete target with two through eight inputs")
    cuts, evidence = checked_prefix_cofactors(case.n, case.truth)
    print(json.dumps(dict(schema="singleton-prefix-cofactors/1", case=case.name,
                          inputs=case.n, budget=2 * case.n - 2,
                          truth_sha256=target_fingerprint(case.n, case.truth),
                          cuts=cuts, **evidence), indent=2))


if __name__ == "__main__":
    main()
