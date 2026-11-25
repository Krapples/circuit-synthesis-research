from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import combinations
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
GATES = 20
TABLE = 7583035862004050432
LABELS = {
    (0 if row == 0 else 1 << (row - 1)) | (1 << (7 + col)):
    (TABLE >> (8 * row + col)) & 1
    for row in range(8) for col in range(8)
}


def solve(first):
    start = time.monotonic()
    output, pool, clauses, ops, select = circuits.build(N, GATES, colex_from=1, require_used=False)
    clauses.extend([-types[2]] for types in ops.values())
    opcode, left, right = first
    clauses.extend(([ops[N][opcode]], [select[N, 0][left]], [select[N, 1][right]]))
    outputs = [pool.id(("output", i)) for i in range(N, output + 1)]
    clauses.extend(CardEnc.equals(outputs, 1, vpool=pool).clauses)
    for row, target in LABELS.items():
        values = [pool.id(("wire", row, j)) for j in range(output + 1)]
        clauses.extend([values[j] if row >> j & 1 else -values[j]] for j in range(N))
        clauses.extend(circuits.truth_gate_clauses(row, values, pool, ops, select))
        clauses.extend([-selector, values[i] if target else -values[i]]
                       for i, selector in zip(range(N, output + 1), outputs))
    with Solver(name="maplechrono", bootstrap_with=clauses) as solver:
        timer = threading.Timer(24, solver.interrupt)
        timer.start()
        try:
            answer = solver.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
        if answer:
            model = set(solver.get_model())
    record = {"first_gate": first, "elapsed_s": round(time.monotonic() - start, 3),
              "result": "SAT" if answer else "OPEN" if answer is None else "UNSAT"}
    if answer:
        gates = [tuple([next(k for k, lit in enumerate(types) if lit in model)] +
                       [next(k for k, lit in enumerate(select[j, slot]) if lit in model)
                        for slot in range(2)])
                 for j, types in ops.items()]
        chosen_out = next(i for i, selector in zip(range(N, output + 1), outputs)
                          if selector in model)
        for row, target in LABELS.items():
            values = [(row >> i) & 1 for i in range(N)]
            for op, left, right in gates:
                values.append(values[left] | values[right] if op else values[left] & values[right])
            assert values[chosen_out] == target
        record.update(gates=gates, output=chosen_out)
    return record


def main():
    seeds = [(op, l, r) for l, r in combinations(range(N), 2) for op in (0, 1)
             if op == 1 or l < 7 <= r]
    seeds.sort(key=lambda gate: (gate[0] != 1, (gate[1] < 7) != (gate[2] < 7), gate[1:]))
    log = (ROOT / "sat-search" / "logs").joinpath("L-meta-11869-rep20-shards.jsonl")
    with log.open("x", encoding="utf-8") as out, ProcessPoolExecutor(max_workers=22) as pool:
        pending = {pool.submit(solve, seed) for seed in seeds}
        print(f"22 workers, {len(pending)} first-gate shards", flush=True)
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
