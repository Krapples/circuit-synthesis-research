"""Test a smaller seeded incidence grid, sharded by first-gate symmetry."""
from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import combinations, permutations, product
import json
from pathlib import Path
import sys
from threading import Timer

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
import cube_search as cs

WIRES = (("seed", 0, 0), ("hub", 0, 0), ("hub", 1, 0),
         *(("line", side, i) for side, i in product(range(2), repeat=2)),
         *(("point", i, j) for i, j in product(range(2), repeat=2)))
N = len(WIRES)
LINES = range(3, 7)
POINTS = [1, 2, 7, 8, 9, 10]
EDGES = [(3 + i, 1) for i in range(2)] + [(5 + j, 2) for j in range(2)]
for i, j in product(range(2), repeat=2):
    p = 7 + 2 * i + j
    EDGES.extend(((3 + i, p), (5 + j, p)))
BUDGET = 14


def paired_row(entries):
    active = set(entries)
    return tuple(j in active or (j == 0 and bool(active & {1, 2})) for j in range(N))


def boundary():
    for edge in EDGES:
        yield paired_row(edge), True
    for bits in product((False, True), repeat=len(LINES)):
        lines = {j for j, bit in zip(LINES, bits) if bit}
        points = set(POINTS) - {p for j, p in EDGES if j in lines}
        if all(j in lines or any(k == j and p in points for k, p in EDGES) for j in LINES):
            yield paired_row(lines | points), False


def first_pairs():
    def transform(wire, row, col, swap):
        kind, i, j = wire
        if kind == "seed":
            return wire
        if kind == "hub":
            return kind, i ^ swap, j
        if kind == "line":
            return kind, i ^ swap, (row, col)[i][j]
        return (kind, col[j], row[i]) if swap else (kind, row[i], col[j])

    group = [tuple(WIRES.index(transform(wire, row, col, swap)) for wire in WIRES)
             for row, col, swap in product(permutations(range(2)), permutations(range(2)), range(2))]
    edges = {tuple(sorted(edge)) for edge in EDGES}
    assert all({tuple(sorted((m[a], m[b]))) for a, b in EDGES} == edges for m in group)
    return sorted({min(tuple(sorted((m[a], m[b]))) for m in group)
                   for a, b in combinations(range(N), 2)})


def run(job):
    kind, a, b = job
    output, pool, cnf, ops, select = cs.build(N, BUDGET, colex_from=1, require_used=False)
    cnf.extend([-flags[2]] for flags in ops.values())
    cnf.extend([[ops[N][kind]], [select[N, 0][a]], [select[N, 1][b]]])
    for r, (bits, target) in enumerate(boundary()):
        wires = [pool.id(("wire", r, j)) for j in range(output + 1)]
        cnf.extend([w if bit else -w] for w, bit in zip(wires, bits))
        cnf.append([wires[output] if target else -wires[output]])
        cnf.extend(cs.truth_gate_clauses(r, wires, pool, ops, select))
    witness = None
    with cs.Solver(name="maplechrono", bootstrap_with=cnf) as solver:
        timer = Timer(75, solver.interrupt)
        timer.start()
        try:
            result = solver.solve_limited(expect_interrupt=True)
            if result:
                model = set(solver.get_model())
                witness = [
                    (next(k for k, flag in enumerate(flags) if flag in model),
                     *(next(i for i, flag in enumerate(select[w, slot]) if flag in model)
                       for slot in (0, 1)))
                    for w, flags in ops.items()
                ]
                for raw in product((False, True), repeat=N - 1):
                    values = [raw[0] or raw[1], *raw]
                    expected = any(values[i] and values[j] for i, j in EDGES)
                    for op, i, j in witness:
                        values.append((values[i] or values[j]) if op else (values[i] and values[j]))
                    assert values[-1] == expected
        finally:
            timer.cancel()
        verdict = "SAT" if result else "OPEN" if result is None else "UNSAT"
        return dict(shard=job, verdict=verdict, stats=solver.accum_stats(), witness=witness)


if __name__ == "__main__":
    jobs = [(kind, a, b) for a, b in first_pairs() for kind in range(2)]
    print(f"22 SAT workers, {len(jobs)} first-gate shards, {sum(1 for _ in boundary())} rows", flush=True)
    with Path(sys.argv[1]).open("x", encoding="utf-8") as stream:
        with ProcessPoolExecutor(max_workers=22) as pool:
            for task in as_completed(pool.submit(run, job) for job in jobs):
                result = json.dumps(task.result())
                print(result, file=stream, flush=True)
                print(result, flush=True)
