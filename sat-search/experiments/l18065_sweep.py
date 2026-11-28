"""Sweep C4-free bipartite graphs with a perfect matching in the exact AO2 model."""
import argparse
import itertools
import math
import platform
from pathlib import Path
import sys

import pysat
from l18065_synth import solve

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from workflow.supervise import Job, emit, run_jobs


def c4free(m, E):
    for a, b in itertools.combinations(range(m), 2):
        for c, d in itertools.combinations(range(m), 2):
            if {(a, c), (a, d), (b, c), (b, d)} <= E:
                return False
    return True


def canon(m, E):
    best = None
    for T in (False, True):
        F = {(b, a) for a, b in E} if T else E
        for p in itertools.permutations(range(m)):
            for q in itertools.permutations(range(m)):
                key = tuple(sorted((p[a], q[b]) for a, b in F))
                if best is None or key < best:
                    best = key
    return best


def graphs(m):
    diag = [(i, i) for i in range(m)]
    off = [(a, b) for a in range(m) for b in range(m) if a != b]
    seen = set()
    for r in range(len(off) + 1):
        for extra in itertools.combinations(off, r):
            E = set(diag) | set(extra)
            if not c4free(m, E):
                continue
            c = canon(m, E)
            if c not in seen:
                seen.add(c)
                yield m, sorted(E)


def work(report, m, edges, row_mode, plain_budget, conflict_limit, restrictions, read_once_bound):
    def publish(event, **data):
        snapshot = {key: data[key] for key in (
            "budget", "owned", "rows", "rounds", "conflicts", "verdict") if key in data}
        report(event, phase=snapshot, throttle=event == "solving", **data)

    def check(budget, owned):
        result = solve(m, edges, budget, owned, row_mode=row_mode, report=publish,
                       conflict_limit=conflict_limit, restrictions=restrictions,
                       read_once_bound=read_once_bound)
        publish("budget_result", budget=budget, owned=owned, **result)
        return result["verdict"]

    if plain_budget is not None:
        return {"plain_budget": plain_budget, "plain": check(plain_budget, False)}
    # A connected output cone with 2m essential inputs needs at least 2m-1
    # binary gates. The OR of individual graph edges uses 2|E|-1 gates.
    for budget in range(2 * m - 1, 2 * len(edges)):
        verdict = check(budget, True)
        if verdict == "SAT":
            plain = check(budget - 1, False)
            return {"owned_minimum": budget, "plain_budget": budget - 1, "plain_km1": plain}
        if verdict != "UNSAT":
            return {"owned_budget": budget, "owned_status": verdict}
    raise RuntimeError("edge-owned search excluded the direct edge-DNF upper bound")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sizes", type=int, choices=(3, 4), nargs="*")
    parser.add_argument("--case", type=int, action="append", help="Select a case index from --list")
    parser.add_argument("--list", action="store_true", help="List graph cases without solving")
    parser.add_argument("--plain-budget", type=int, help="Replay a fixed plain budget only")
    parser.add_argument("--rows", choices=("legacy", "frontier"), default="legacy")
    parser.add_argument("--restrictions", type=int, choices=(0, 1, 2, 3), default=0,
                        help="Bound direct gate readers of up to this many fixed inputs")
    parser.add_argument("--read-once-bound", action="store_true",
                        help="Strengthen cofactor bounds with a minterm/maxterm obstruction")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--wall", type=float, default=60.0, help="Hard seconds per graph")
    parser.add_argument("--heartbeat", type=float, default=5.0, help="Seconds between parent updates")
    parser.add_argument("--conflicts", type=int, help="Conflict limit per fixed-budget solve")
    args = parser.parse_args()
    if not (1 <= args.workers <= 22) or not all(
            math.isfinite(limit) and limit > 0 for limit in (args.wall, args.heartbeat)):
        parser.error("workers must be between 1 and 22, and limits must be positive")
    for limit in (args.conflicts, args.plain_budget):
        if limit is not None and limit <= 0:
            parser.error("conflict and plain gate budgets must be positive")
    if args.read_once_bound and not args.restrictions:
        parser.error("--read-once-bound requires --restrictions")
    items = [g for m in sorted(set(args.sizes or [3, 4])) for g in graphs(m)]
    items.sort(key=lambda g: (g[0], len(g[1])))
    if any(not 0 <= case < len(items) for case in (args.case or [])):
        parser.error("case index out of range for the given sizes")
    selected = set(args.case if args.case is not None else range(len(items)))
    jobs = [(case, item) for case, item in enumerate(items) if case in selected]
    if args.list:
        for case, (m, edges) in jobs:
            emit("graph", case=case, m=m, E=edges)
        return 0
    emit("run_start", graphs=len(jobs), rows=args.rows, wall=args.wall, workers=args.workers,
         conflicts=args.conflicts, plain_budget=args.plain_budget, restrictions=args.restrictions,
         read_once_bound=args.read_once_bound, python=platform.python_version(),
         pysat=pysat.__version__, solver="cadical195")
    work_items = [
        Job(case, (m, edges, args.rows, args.plain_budget, args.conflicts, args.restrictions,
                   args.read_once_bound),
            {"m": m, "E": edges})
        for case, (m, edges) in jobs
    ]
    return run_jobs(work_items, work, workers=args.workers, wall=args.wall, heartbeat=args.heartbeat)


if __name__ == "__main__":
    raise SystemExit(main())
