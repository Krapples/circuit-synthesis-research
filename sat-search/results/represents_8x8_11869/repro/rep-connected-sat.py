from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import combinations, permutations
import json
from pathlib import Path
import sys
import threading
import time

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "sat-search"))
import cube_search as circuits
from pysat.card import CardEnc
from pysat.solvers import Solver

N = 15
ROW_INPUTS = 7
TABLE = 7583035862004050432
LABELS = {
    (0 if row == 0 else 1 << (row - 1)) | (1 << (ROW_INPUTS + col)):
    (TABLE >> (8 * row + col)) & 1
    for row in range(8) for col in range(8)
}
PAIRS = tuple(combinations(range(N), 2))


def legal_pairs():
    return [(op, a, b) for a, b in PAIRS for op in (0, 1) if op or a < ROW_INPUTS <= b]


def orbit_representatives():
    rows = [(TABLE >> (8 * r)) & 255 for r in range(8)]
    index = {mask: i for i, mask in enumerate(rows)}
    autos = []
    for column in permutations(range(8)):
        lookup = [sum(1 << column[c] for c in range(8) if mask >> c & 1) for mask in rows]
        if all(mask in index for mask in lookup):
            autos.append(tuple(index[mask] - 1 for mask in lookup[1:]) +
                         tuple(ROW_INPUTS + c for c in column))
    return sorted({min((op, *sorted((auto[a], auto[b]))) for auto in autos)
                   for op, a, b in legal_pairs()})


def lost_distinctions():
    """When both primaries feed this gate, at least one indicated raw input needs another reader."""
    positive = [row for row, bit in LABELS.items() if bit]
    negative = [row for row, bit in LABELS.items() if not bit]
    legal = {}
    for op, a, b in legal_pairs():
        mask = (1 << a) | (1 << b)
        output = (lambda x: bool(x & mask)) if op else (lambda x: x & mask == mask)
        needs = {p & ~q for p in positive for q in negative
                 if not (p & ~q & ~mask) and output(p) <= output(q)}
        assert 0 not in needs
        legal[op, a, b] = [tuple(i for i in (a, b) if need >> i & 1)
                           for need in needs if not any(other != need and other & need == other for other in needs)]
    return legal


LOST = lost_distinctions()


def solve(task):
    gates, first = task
    start = time.monotonic()
    output, pool, clauses, ops, select = circuits.build(N, gates, colex_from=1)
    clauses.extend([-types[2]] for types in ops.values())
    opcode, left, right = first
    clauses.extend(([ops[N][opcode]], [select[N, 0][left]], [select[N, 1][right]]))
    repeated = {i: pool.id(("rep", i)) for i in range(output - 1)}
    for i, repeat in repeated.items():
        readers = [select[j, k][i] for j in range(max(N, i + 1), output + 1) for k in (0, 1)]
        if len(readers) > 1:
            clauses.extend([repeat, *clause] for clause in CardEnc.atmost(readers, 1, vpool=pool).clauses)
    clauses.extend(CardEnc.atmost(list(repeated.values()), gates - N + 1, vpool=pool).clauses)
    for j, types in ops.items():
        for a, b in PAIRS:
            premise = [-select[j, 0][a], -select[j, 1][b]]
            if not a < ROW_INPUTS <= b:
                clauses.append([-types[0], *premise])
            for op in (0, 1):
                for needed_repeats in LOST.get((op, a, b), ()):
                    clauses.append([-types[op], *premise, *(repeated[i] for i in needed_repeats)])
    values_by_gate = {j: [] for j in ops}
    for row, target in LABELS.items():
        values = [pool.id(("wire", row, j)) for j in range(output + 1)]
        clauses.extend([values[j] if row >> j & 1 else -values[j]] for j in range(N))
        clauses.extend(circuits.truth_gate_clauses(row, values, pool, ops, select))
        clauses.append([values[output] if target else -values[output]])
        for j in ops:
            values_by_gate[j].append(values[j])
    for j, values in values_by_gate.items():
        clauses.append(values)
        clauses.append([-v for v in values])
    with Solver(name="maplechrono", bootstrap_with=clauses) as solver:
        timer = threading.Timer(25, solver.interrupt)
        timer.start()
        try:
            answer = solver.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
        stats = solver.accum_stats()
        if answer:
            model = set(solver.get_model())
    record = {"budget": gates, "first_gate": first, "elapsed_s": round(time.monotonic() - start, 3),
              "result": "SAT" if answer else "OPEN" if answer is None else "UNSAT",
              "vars": pool.top, "clauses": len(clauses), "stats": stats}
    if answer:
        program = [tuple([next(k for k, lit in enumerate(types) if lit in model)] +
                         [next(k for k, lit in enumerate(select[j, slot]) if lit in model)
                          for slot in range(2)])
                   for j, types in ops.items()]
        for row, target in LABELS.items():
            values = [(row >> i) & 1 for i in range(N)]
            for op, a, b in program:
                values.append(values[a] | values[b] if op else values[a] & values[b])
            assert values[output] == target
        record.update(gates=program, output=output)
    return record


def main():
    reps = orbit_representatives()
    tasks = [(budget, seed) for budget in (15, 16, 17, 18, 19, 20) for seed in reps]
    log = (ROOT / "sat-search" / "logs").joinpath("L-meta-11869-connected-shards.jsonl")
    with log.open("x", encoding="utf-8") as out, ProcessPoolExecutor(max_workers=22) as pool:
        pending = {pool.submit(solve, task) for task in tasks}
        print(f"22 workers, {len(reps)} first-gate orbits per budget", flush=True)
        for future in as_completed(pending):
            record = future.result()
            print(json.dumps(record), file=out, flush=True)
            if record["result"] == "SAT":
                print(json.dumps(record), flush=True)
                for other in pending:
                    other.cancel()
                break
    print("Search finished", flush=True)


if __name__ == "__main__":
    main()
