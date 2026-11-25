from concurrent.futures import ProcessPoolExecutor, as_completed
from importlib.util import module_from_spec, spec_from_file_location
import json
from pathlib import Path
import random
import sys
import threading
import time

source = Path(__file__).with_name("pg3-proxy-sat.py")
spec = spec_from_file_location("incidence", source)
incidence = module_from_spec(spec)
spec.loader.exec_module(incidence)

G = 60
INPUTS = tuple(range(25))
TESTS = incidence.problem(INPUTS)
ALL_ROWS = sorted(TESTS[0].keys() | TESTS[1].keys())
ROW_INDEX = {r: i for i, r in enumerate(ALL_ROWS)}
RAW_COLUMNS = [sum(1 << i for i, flags in enumerate(ALL_ROWS) if flags >> j & 1) for j in INPUTS]
EXPECTED = [
    (sum(1 << ROW_INDEX[row] for row, value in test.items() if value),
     sum(1 << ROW_INDEX[row] for row in test))
    for test in TESTS
]


def fixed_stars(open_points, rng):
    gates = []

    def emit(op, a, b):
        wire = 25 + len(gates)
        gates.append((op, a, b))
        return wire

    roots = []
    for point in incidence.POINTS:
        if point in open_points:
            continue
        neighbors = sorted(line for p, line in incidence.EDGE_SET if p == point)
        rng.shuffle(neighbors)
        a, b, c, d = neighbors
        roots.append(emit(0, point, emit(1, emit(1, a, b), emit(1, c, d))))
    result = roots[0]
    for star in roots[1:]:
        result = emit(1, result, star)
    return gates


def active_suffix(pool, clauses, ops, select, outputs):
    active = {j: pool.id(("active", j)) for j in ops}
    output_pair = {j: (outputs[0][i], outputs[1][i]) for i, j in enumerate(ops)}
    for j in ops:
        own = output_pair[j]
        uses = list(own)
        if j + 1 in ops:
            clauses.append([-active[j + 1], active[j]])
            continuations = [active[j + 1], *own]
        else:
            continuations = list(own)
        for lit in own:
            clauses.append([-lit, active[j]])
        clauses.append([-active[j], *continuations])
        for k in range(j + 1, max(ops) + 1):
            for side in (0, 1):
                reader = pool.id(("live_reader", k, side, j))
                clauses.extend(([-reader, active[k]], [-reader, select[k, side][j]]))
                uses.append(reader)
        clauses.append([-active[j], *uses])


def solve(task):
    points, seed = task
    rng = random.Random(seed)
    start = time.monotonic()
    prefix = fixed_stars(points, rng)
    initial = RAW_COLUMNS.copy()
    for op, a, b in prefix:
        initial.append(initial[a] | initial[b] if op else initial[a] & initial[b])
    n = len(initial)
    prefix_output = initial[-1]
    local_tests = [{r:v for r,v in TESTS[0].items() if not prefix_output >> ROW_INDEX[r] & 1}, TESTS[1]]
    local_expected = [(sum(1 << ROW_INDEX[row] for row, value in test.items() if value),
                       sum(1 << ROW_INDEX[row] for row in test)) for test in local_tests]
    limit, pool, clauses, ops, select = incidence.circuits.build(n, G - len(prefix), require_used=False)
    clauses.extend([-lits[2]] for lits in ops.values())
    outputs = [
        [pool.id(("output", name, j)) for j in ops]
        for name in range(2)
    ]
    for choices in outputs:
        clauses.extend(incidence.CardEnc.equals(choices, 1, vpool=pool).clauses)
    active_suffix(pool, clauses, ops, select, outputs)
    with incidence.Solver(name="maplechrono", bootstrap_with=clauses) as solver:
        used = set()

        def add_rows(sample):
            for row_id in set(sample) - used:
                values = [pool.id(("wire", row_id, j)) for j in range(limit + 1)]
                for i, column in enumerate(initial):
                    solver.add_clause([values[i] if column >> row_id & 1 else -values[i]])
                solver.append_formula(list(incidence.circuits.truth_gate_clauses(row_id, values, pool, ops, select)))
                for j, tests in enumerate(local_tests):
                    row = ALL_ROWS[row_id]
                    if row in tests:
                        solver.append_formula([[-chosen, values[k] if tests[row] else -values[k]]
                                               for k, chosen in zip(ops, outputs[j])])
                used.add(row_id)

        sample = {ROW_INDEX[row] for test in local_tests for row, value in test.items() if value}
        for tests in local_tests:
            negatives = [ROW_INDEX[row] for row, value in tests.items() if not value]
            sample.update(rng.sample(negatives, 25))
        add_rows(sample)
        timer = threading.Timer(110, solver.interrupt)
        timer.start()
        verdict, attempts = "OPEN", 0
        try:
            while time.monotonic() - start < 118:
                result = solver.solve_limited(expect_interrupt=True)
                if result is None:
                    break
                if not result:
                    verdict = "UNSAT"
                    break
                attempts += 1
                model = set(solver.get_model())
                suffix = [
                    tuple([next(i for i, lit in enumerate(types) if lit in model)] +
                          [next(i for i, lit in enumerate(select[j, side]) if lit in model)
                           for side in range(2)])
                    for j, types in ops.items()
                ]
                f, proxy = [next(j for j, lit in zip(ops, choices) if lit in model) for choices in outputs]
                values = initial.copy()
                for op, a, b in suffix:
                    values.append(values[a] | values[b] if op else values[a] & values[b])
                fails = []
                for gate, (expected, known) in zip((f, proxy), local_expected):
                    wrong = (values[gate] ^ expected) & known
                    points_wrong = [i for i in range(len(ALL_ROWS)) if wrong >> i & 1]
                    fails.extend(rng.sample(points_wrong, min(12, len(points_wrong))))
                if not fails:
                    verdict = "SAT"
                    break
                add_rows(fails)
        finally:
            timer.cancel()
    record = {"points": points, "seed": seed, "budget": G + 1, "fixed": len(prefix),
              "elapsed_s": round(time.monotonic() - start, 3), "rows": len(used),
              "models": attempts, "result": verdict}
    if verdict == "SAT":
        program = prefix + suffix + [(1, n - 1, f)]
        f = 25 + len(program) - 1
        incidence.check(INPUTS, program, f, proxy)
        record.update(gates=program, output=f, proxy=proxy)
    return record


def main():
    reps = [subset for subset in incidence.representatives() if 2 <= len(subset) <= 4]
    tasks = [(points, 2232 + i) for i in range(3) for points in reps][:22]
    print(f"22 workers, {len(tasks)} fixed final-OR windows", flush=True)
    log_path = Path(sys.argv[1])
    with log_path.open("x", encoding="utf-8") as log, ProcessPoolExecutor(max_workers=22) as pool:
        pending = {pool.submit(solve, task) for task in tasks}
        for future in as_completed(pending):
            row = future.result()
            print(json.dumps(row), file=log, flush=True)
            print(json.dumps(row), flush=True)
            if row["result"] == "SAT":
                for item in pending:
                    item.cancel()
                break


if __name__ == "__main__":
    main()
