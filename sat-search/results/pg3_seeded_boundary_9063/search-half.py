"""Search the 28-gate six-line subproblem of L-meta-9063."""
from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import combinations
import json
from pathlib import Path
import random
import sys
from threading import Timer

BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(BASE.parents[1]))
import cube_search as cs

LINES = (0, 2, 5, 6, 11, 12)
NEIGHBORS = {13 + j: tuple((line + d) % 13 for d in (0, 1, 3, 9))
             for j, line in enumerate(LINES)}
PROVIDER = 19
INPUTS = 20
BUDGET = 28
POS = [(1 << p) | (1 << line) for line, points in NEIGHBORS.items() for p in points]


def maximal_independent():
    for mask in range(1 << len(LINES)):
        lines = [line for line in NEIGHBORS if mask >> (line - 13) & 1]
        allowed = set(range(13)) - {p for line in lines for p in NEIGHBORS[line]}
        if all(line in lines or allowed.intersection(points) for line, points in NEIGHBORS.items()):
            yield sum(1 << v for v in [*lines, *allowed])


NEG = list(maximal_independent())
ROWS = POS + NEG
KNOWN = (1 << len(POS)) - 1
FULL = (1 << len(ROWS)) - 1
BASE_COLUMNS = [sum(1 << i for i, row in enumerate(ROWS) if row >> j & 1)
                for j in range(PROVIDER)]
BASE_COLUMNS.append(BASE_COLUMNS[1] | BASE_COLUMNS[2])


def solve(job):
    frozen, seed = job
    rand = random.Random(seed)
    gates = []

    def emit(op, a, b):
        gates.append((op, min(a, b), max(a, b)))
        return INPUTS + len(gates) - 1

    roots = []
    for line in frozen:
        points = list(NEIGHBORS[line])
        rand.shuffle(points)
        a, b, c, d = points
        root = emit(1, emit(1, a, b), emit(1, c, d))
        roots.append(emit(0, line, root))
    joined = roots[0]
    for root in roots[1:]:
        joined = emit(1, joined, root)
    columns = BASE_COLUMNS.copy()
    for op, a, b in gates:
        columns.append(columns[a] | columns[b] if op else columns[a] & columns[b])
    count = len(columns)
    output, pool, cnf, ops, select = cs.build(count, BUDGET - len(gates) - 1, require_used=False)
    cnf.extend([-flags[2]] for flags in ops.values())
    for gate in range(count, output):
        cnf.append([select[reader, slot][gate] for reader in range(gate + 1, output + 1)
                    for slot in (0, 1)])
    care = FULL ^ columns[joined]
    active = set()
    models = 0
    verdict = "OPEN"
    witness = None
    with cs.Solver(name="maplechrono", bootstrap_with=cnf) as solver:
        def add_rows(indices):
            for i in set(indices) - active:
                wire = [pool.id(("wire", i, j)) for j in range(output + 1)]
                solver.append_formula([[wire[j] if col >> i & 1 else -wire[j]]
                                       for j, col in enumerate(columns)])
                solver.add_clause([wire[output] if KNOWN >> i & 1 else -wire[output]])
                solver.append_formula(list(cs.truth_gate_clauses(i, wire, pool, ops, select)))
                active.add(i)

        add_rows([j for j in range(len(POS)) if care >> j & 1] +
                 rand.sample(range(len(POS), len(ROWS)), min(14, len(NEG))))
        timer = Timer(90, solver.interrupt)
        timer.start()
        try:
            while True:
                sat = solver.solve_limited(expect_interrupt=True)
                if sat is None:
                    break
                if not sat:
                    verdict = "UNSAT"
                    break
                models += 1
                model = set(solver.get_model())
                suffix = [
                    (next(op for op, flag in enumerate(flags) if flag in model),
                     *(next(j for j, flag in enumerate(select[wire, slot]) if flag in model)
                       for slot in (0, 1)))
                    for wire, flags in ops.items()
                ]
                values = columns.copy()
                for op, a, b in suffix:
                    values.append(values[a] | values[b] if op else values[a] & values[b])
                missed = (values[output] ^ KNOWN) & care
                if not missed:
                    witness = gates + suffix + [(1, joined, output)]
                    verdict = "SAT"
                    break
                add_rows([i for i in range(len(ROWS)) if missed >> i & 1])
        finally:
            timer.cancel()
        return dict(frozen=frozen, seed=seed, result=verdict, rows=len(active),
                    models=models, stats=solver.accum_stats(), witness=witness)


if __name__ == "__main__":
    pinned = list(combinations(NEIGHBORS, 3)) + [(13, 15), (14, 17)]
    print(f"22 SAT workers, {len(POS)} minimal positives and {len(NEG)} maximal negatives", flush=True)
    with Path(sys.argv[1]).open("x", encoding="utf-8") as log:
        with ProcessPoolExecutor(max_workers=22) as pool:
            for future in as_completed(pool.submit(solve, (frozen, 9063 + j))
                                       for j, frozen in enumerate(pinned)):
                result = json.dumps(future.result())
                print(result, file=log, flush=True)
                print(result, flush=True)
