"""Exact OR-budget screening with unrestricted binary AND gates."""

import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path
from random import Random
import sys
from threading import Timer
from time import perf_counter

from check_geometry import DIFFERENCES, ORDER

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from cube_search import IDPool, Solver


@lru_cache(maxsize=64)
def target_rows(n, edges):
    terms = [((1 << a) | (1 << b)) for a, b in edges]
    covers = [row for row in range(1 << n) if not any(row & term == term for term in terms)]
    false = set(covers)
    maximal = [row for row in covers if all(row | 1 << v not in false for v in range(n) if not row >> v & 1)]
    return [(term, True) for term in terms] + [(row, False) for row in maximal]


def encode(n, edges, budget):
    pool = IDPool()
    choices = [[pool.id((j, v)) for v in range(n + j // 2)] for j in range(2 * budget + 1)]
    clauses = []
    for row, positive in target_rows(n, edges):
        or_values = [pool.id(("or", row, j)) for j in range(budget)]
        conjunctions = [pool.id(("operand", row, j)) for j in range(len(choices))]
        for j, (selection, value) in enumerate(zip(choices, conjunctions)):
            failure = []
            for v, selected in enumerate(selection):
                if v < n:
                    if not row >> v & 1:
                        failure.append(selected)
                else:
                    source = or_values[v - n]
                    blocked = pool.id(("blocked", row, j, v))
                    clauses.extend(([-blocked, selected], [-blocked, -source], [blocked, -selected, source]))
                    failure.append(blocked)
            clauses.extend([-value, -fail] for fail in failure)
            clauses.append([value, *failure])
        for j, value in enumerate(or_values):
            a, b = conjunctions[2 * j:2 * j + 2]
            clauses.extend(([-a, value], [-b, value], [a, b, -value]))
        clauses.append([conjunctions[-1] if positive else -conjunctions[-1]])
    return choices, clauses, pool.top


def joint_search(job):
    name, n, edges, budget, seconds = job
    start = perf_counter()
    choices, clauses, variables = encode(n, edges, budget)
    encoding_seconds = perf_counter() - start
    with Solver(name="maplechrono", bootstrap_with=clauses) as solver:
        timer = Timer(max(0.01, seconds - (perf_counter() - start)), solver.interrupt)
        timer.start()
        try:
            result = solver.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
            timer.join()
        selected_sources = None
        if result is True:
            model = set(solver.get_model())
            selected_sources = [[v for v, selected in enumerate(group) if selected in model] for group in choices]
            verify(n, edges, selected_sources)
        return {"name": name, "n": n, "edges": edges, "or_budget": budget, "cap_seconds": seconds,
                "status": {True: "verified_sat", False: "solver_unsat", None: "open"}[result],
                "seconds": round(perf_counter() - start, 3), "variables": variables, "clauses": len(clauses),
                "encoding_seconds": round(encoding_seconds, 6),
                "stats": solver.accum_stats(), "witness": selected_sources}


def verify(n, edges, operands):
    for row in range(1 << n):
        wires = [bool(row >> v & 1) for v in range(n)]
        for a, b in zip(operands[0:-1:2], operands[1:-1:2]):
            wires.append(all(wires[v] for v in a) or all(wires[v] for v in b))
        assert all(wires[v] for v in operands[-1]) == any(wires[a] and wires[b] for a, b in edges)


def connected(n, edges):
    reached = {0}
    for _ in range(n - 1):
        reached.update(v for edge in edges if reached.intersection(edge) for v in edge)
    return len(reached) == n


def profiles():
    """Fixed-seed low-order subgraphs using the project's cyclic coordinates."""
    yield "square_control", 4, [(0, 2), (0, 3), (1, 2), (1, 3)], 2
    yield "path_control", 4, [(0, 1), (1, 2), (2, 3)], 1
    yield "cycle6", 6, [(i, (i + 1) % 6) for i in range(6)], 4
    generator = Random(4653)
    seen = set()
    for left, right, target, count in [(3, 4, 7, 4), (4, 4, 8, 5), (4, 5, 9, 5), (5, 5, 10, 5)]:
        generated = 0
        for _ in range(100_000):
            points = sorted(generator.sample(range(ORDER), left))
            lines = sorted(generator.sample(range(ORDER), right))
            edges = tuple((i, left + j) for i, p in enumerate(points) for j, l in enumerate(lines)
                          if (l - p) % ORDER in DIFFERENCES)
            if len(edges) != target or edges in seen or not connected(left + right, edges):
                continue
            assert all(sum((i, l) in edges and (j, l) in edges for l in range(left, left + right)) <= 1
                       for i, j in combinations(range(left), 2))
            seen.add(edges)
            generated += 1
            yield f"{left}x{right}_{generated}", left + right, edges, target - 2
            if generated == count:
                break
        assert generated == count


def job_key(name, n, edges, budget, seconds):
    return name, n, tuple(tuple(e) for e in edges), budget, seconds


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile-cnf", action="store_true", help="build each formula without running SAT")
    parser.add_argument("--cap", type=int, default=105)
    parser.add_argument("--output", type=Path, help="append each completed query to this JSONL checkpoint")
    args = parser.parse_args()
    jobs = [job_key(*profile, args.cap) for profile in profiles()]
    assert len(jobs) == 22

    if args.profile_cnf:
        for name, n, edges, budget, _ in jobs:
            start = perf_counter()
            _, clauses, variables = encode(n, edges, budget)
            print(json.dumps({"name": name, "variables": variables, "clauses": len(clauses),
                              "encoding_seconds": round(perf_counter() - start, 6)}), flush=True)
        return

    if args.output and args.output.exists():
        previous = set()
        with args.output.open(encoding="utf-8-sig") as checkpoint:
            for line in checkpoint:
                if line.strip():
                    row = json.loads(line)
                    previous.add(job_key(row["name"], row["n"], row["edges"], row["or_budget"], row["cap_seconds"]))
        jobs = [job for job in jobs if job not in previous]
    if not jobs:
        return
    with ProcessPoolExecutor(max_workers=22) as workers:
        for future in as_completed([workers.submit(joint_search, job) for job in jobs]):
            result = json.dumps(future.result())
            if args.output:
                with args.output.open("a", encoding="utf-8", newline="\n") as checkpoint:
                    checkpoint.write(result + "\n")
            print(result, flush=True)


if __name__ == "__main__":
    main()
