from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import combinations
import json
from pathlib import Path
import sys
import threading
import time

SAT_SEARCH = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(SAT_SEARCH))
import cube_search as circuits
import networkx as nx
from pysat.card import CardEnc
from pysat.solvers import Solver

POINTS = tuple(range(12))
LINES = tuple(range(12, 25))
PROXY = (12, 13, 15, 21)
EDGE_SET = {(p, q) for p in POINTS for q in LINES if (p + q + 2) % 13 in (0, 1, 3, 9)}


def problem(vertices):
    points = [i for i in vertices if i in POINTS]
    lines = [i for i in vertices if i in LINES]
    index = {value: i for i, value in enumerate(vertices)}
    edge_labels = {1 << index[p] | 1 << index[q] for p in points for q in lines if (p, q) in EDGE_SET}

    def maximal_independent(excluded):
        right = {q for q in lines if q not in excluded}
        maximal = set()
        for pattern in range(1 << len(points)):
            left = {p for i, p in enumerate(points) if pattern >> i & 1}
            allowed_right = {q for q in right if not any((p, q) in EDGE_SET for p in left)}
            closed_left = {p for p in points if not any((p, q) in EDGE_SET for q in allowed_right)}
            if closed_left == left:
                maximal.add(sum(1 << index[x] for x in left | allowed_right))
        return maximal

    output_tests = {row: True for row in edge_labels} | {row: False for row in maximal_independent(())}
    proxy_tests = {1 << index[q]: True for q in PROXY} | {row: False for row in maximal_independent(PROXY)}
    return output_tests, proxy_tests


def check(vertices, program, f_out, w_out):
    for output, tests in zip((f_out, w_out), problem(vertices)):
        for row, expected in tests.items():
            wires = [bool(row >> j & 1) for j in range(len(vertices))]
            for op, left, right in program:
                wires.append(wires[left] or wires[right] if op else wires[left] and wires[right])
            assert wires[output] == expected


def extend(vertices, program, f_out, w_out):
    mapping = list(vertices)
    gates = []
    for op, left, right in program:
        mapping.append(25 + len(gates))
        gates.append((op, mapping[left], mapping[right]))
    proxy = mapping[w_out]
    output = mapping[f_out]

    def emit(op, left, right):
        i = 25 + len(gates)
        gates.append((op, left, right))
        return i

    for p in POINTS:
        if p in vertices:
            continue
        a, b, c, d = sorted(q for q in LINES if (p, q) in EDGE_SET)
        star = emit(0, p, emit(1, emit(1, a, b), emit(1, c, d)))
        output = emit(1, output, star)
    assert len(gates) <= 61
    check(tuple(range(25)), gates, output, proxy)
    return gates, output, proxy


def solve(points):
    start = time.monotonic()
    budget = 5 * len(points) + 1
    vertices = tuple(points) + tuple(sorted(set(PROXY) | {q for p, q in EDGE_SET if p in points}))
    n = len(vertices)
    output_tests, proxy_tests = problem(vertices)
    limit, pool, clauses, ops, select = circuits.build(n, budget, colex_from=0, require_used=False)
    clauses.extend([-lits[2]] for lits in ops.values())
    outputs = {}
    for name, tests in enumerate((output_tests, proxy_tests)):
        outputs[name] = [pool.id(("output", name, j)) for j in ops]
        clauses.extend(CardEnc.equals(outputs[name], 1, vpool=pool).clauses)
    for row in sorted(output_tests.keys() | proxy_tests.keys()):
        values = [pool.id(("wire", row, j)) for j in range(limit + 1)]
        clauses.extend([values[i] if row >> i & 1 else -values[i]] for i in range(n))
        clauses.extend(circuits.truth_gate_clauses(row, values, pool, ops, select))
        for name, tests in enumerate((output_tests, proxy_tests)):
            if row in tests:
                clauses.extend([-chosen, values[j] if tests[row] else -values[j]]
                               for j, chosen in zip(ops, outputs[name]))
    with Solver(name="maplechrono", bootstrap_with=clauses) as solver:
        timer = threading.Timer(35, solver.interrupt)
        timer.start()
        try:
            result = solver.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
        stats = solver.accum_stats()
        if result:
            model = set(solver.get_model())
    record = {"points": points, "n": n, "budget": budget,
              "labels": [len(output_tests), len(proxy_tests)], "clauses": len(clauses),
              "elapsed_s": round(time.monotonic() - start, 3), "stats": stats,
              "result": "SAT" if result else "OPEN" if result is None else "UNSAT"}
    if result:
        gates = [tuple([next(k for k, lit in enumerate(types) if lit in model)] +
                      [next(k for k, flag in enumerate(select[j, slot]) if flag in model)
                       for slot in range(2)])
                 for j, types in ops.items()]
        f_out, w_out = [next(j for j, flag in zip(ops, outputs[name]) if flag in model) for name in (0, 1)]
        check(vertices, gates, f_out, w_out)
        gates, f_out, w_out = extend(vertices, gates, f_out, w_out)
        record.update(gates=gates, output=f_out, proxy=w_out)
    return record


def representatives():
    graph = nx.Graph()
    graph.add_nodes_from((p, {"part": "point"}) for p in POINTS)
    graph.add_nodes_from((q, {"part": "proxy" if q in PROXY else "line"}) for q in LINES)
    graph.add_edges_from(EDGE_SET)
    matcher = nx.algorithms.isomorphism.GraphMatcher(
        graph, graph, node_match=lambda a, b: a["part"] == b["part"])
    order = [tuple(perm[i] for i in POINTS) for perm in matcher.isomorphisms_iter()]
    print(f"{len(order)} automorphisms", flush=True)
    for size in range(1, 7):
        seen = set()
        for subset in combinations(POINTS, size):
            if subset in seen:
                continue
            seen.update(tuple(sorted(perm[p] for p in subset)) for perm in order)
            yield subset


def main():
    maximal = problem(tuple(range(25)))
    print(f"Full boundary sizes: {[len(tests) for tests in maximal]}", flush=True)
    reps = list(representatives())
    log_path = Path(sys.argv[1])
    with log_path.open("x", encoding="utf-8") as log, ProcessPoolExecutor(max_workers=22) as pool:
        pending = {pool.submit(solve, points) for points in reps}
        print(f"22 workers, {len(pending)} point-subset orbits", flush=True)
        for future in as_completed(pending):
            record = future.result()
            print(json.dumps(record), file=log, flush=True)
            print(json.dumps(record), flush=True)
            if record["result"] == "SAT":
                for other in pending:
                    other.cancel()
                break


if __name__ == "__main__":
    main()
