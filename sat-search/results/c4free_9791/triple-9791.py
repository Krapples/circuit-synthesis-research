"""Decide canonical three-star cores with overapproximated prefix providers."""
from concurrent.futures import ProcessPoolExecutor
from itertools import combinations
import json
from pathlib import Path
import runpy
import sys
from threading import Timer
from time import perf_counter

project = runpy.run_path(str(Path(__file__).with_name("project-9791.py")))
cs = project["cs"]
boundary = project["boundary"]


def solve(job):
    common, gates, solver_name = job
    core = ({9: (0, 1, 2, 3), 10: (0, 4, 5, 6), 11: (0, 7, 8, 12)} if common
            else {9: (0, 1, 3, 4), 10: (0, 2, 5, 6), 11: (1, 2, 7, 8)})
    left = set().union(*map(set, core.values()))
    raw = sorted(left | set(core))
    slack = gates + 1 - len(raw)
    # When there are three remaining stars, a surviving prefix disjunction has
    # at most three leaves, because it intersects every star in at most one.
    supports = [{i} for i in raw]
    if slack:
        for size in (2, 3):
            for subset in map(set, combinations(sorted(left), size)):
                if all(len(subset.intersection(neighbors)) <= 1 for neighbors in core.values()):
                    supports.append(subset)
    n = len(supports)
    output, pool, cnf, ops, select = cs.build(n, gates, require_used=False)
    cnf.extend([-flags[2]] for flags in ops.values())
    optional = []
    for wire in range(output):
        uses = [select[j, slot][wire] for j in ops if j > wire for slot in (0, 1)]
        if len(raw) <= wire < n:
            used = pool.id(("provider", wire))
            cnf.extend([-lit, used] for lit in uses)
            optional.append(used)
        else:
            cnf.append(uses)
    if optional and slack < len(optional):
        cnf.extend(cs.CardEnc.atmost(optional, bound=slack, vpool=pool).clauses)
    for r, (ones, want) in enumerate(boundary(core)):
        values = [pool.id(("wire", r, i)) for i in range(output + 1)]
        cnf.extend([v if support & ones else -v] for v, support in zip(values, supports))
        cnf.append([values[output] if want else -values[output]])
        cnf.extend(cs.truth_gate_clauses(r, values, pool, ops, select))
    start = perf_counter()
    with cs.Solver(name=solver_name, bootstrap_with=cnf) as solver:
        timer = Timer(150, solver.interrupt)
        timer.start()
        try:
            verdict = solver.solve_limited(expect_interrupt=True)
            stats = solver.accum_stats()
            witness = None
            if verdict:
                model = set(solver.get_model())
                witness = [
                    (int(flags[1] in model), *(next(i for i, flag in enumerate(select[j, slot])
                                                   if flag in model) for slot in (0, 1)))
                    for j, flags in ops.items()
                ]
                for ones, expected in boundary(core):
                    bits = [bool(support & ones) for support in supports]
                    for is_or, a, b in witness:
                        bits.append(bits[a] or bits[b] if is_or else bits[a] and bits[b])
                    assert bits[-1] == expected
        finally:
            timer.cancel()
    return dict(common=common, gates=gates, solver=solver_name, providers=len(supports) - len(raw),
                result="SAT" if verdict else "UNSAT" if verdict is False else "OPEN",
                seconds=round(perf_counter() - start, 3), stats=stats, witness=witness)


if __name__ == "__main__":
    solvers = ("glucose42", "minisat22", "maplechrono", "maplesat")
    jobs = [(common, gates, name) for common, first in ((False, 11), (True, 12))
            for gates in range(first, 14) for name in solvers]
    jobs += [(False, 13, "mergesat3"), (True, 13, "mergesat3")]
    with Path(sys.argv[1]).open("x", encoding="utf-8") as records:
        with ProcessPoolExecutor(max_workers=22) as pool:
            for row in pool.map(solve, jobs):
                line = json.dumps(row)
                print(line, flush=True)
                print(line, file=records, flush=True)
