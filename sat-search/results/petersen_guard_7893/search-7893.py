"""Search for expanded Petersen circuits with the L-meta-7893 OR substitution."""
from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import permutations
import json
from pathlib import Path
import random
import runpy
import sys
from threading import Timer

BASE = Path(__file__).resolve().parent
ROOT = next(parent for parent in BASE.parents if (parent / "sat-search" / "cube_search.py").is_file())
sys.path.insert(0, str(ROOT / "sat-search"))
import cube_search as cs

N = 10
POS = (3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640)
NEG = (50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773)
GUARD_OFF = frozenset((50, 104, 116, 138, 208, 276, 402, 548, 554, 770))
SECONDS = 150


def check_edge_orbits():
    edges = {tuple(i for i in range(N) if row >> i & 1) for row in POS}
    deleted = {edge for edge in edges if 0 not in edge}
    permutations_fixing_zero = ((0, *rest) for rest in permutations(range(1, N)))
    aut = [p for p in permutations_fixing_zero
           if all(tuple(sorted((p[a], p[b]))) in edges for a, b in edges)]
    first = {tuple(sorted((p[1], p[2]))) for p in aut}
    second = {tuple(sorted((p[2], p[3]))) for p in aut}
    assert len(aut) == 12 and first.isdisjoint(second) and first | second == deleted


def evaluate(gates, row):
    wires = [bool(row >> j & 1) for j in range(N)]
    for op, a, b in gates:
        wires.append((wires[a] or wires[b]) if op else (wires[a] and wires[b]))
    return wires


def check_gates(gates):
    special = [(j, b) for j, (op, a, b) in enumerate(gates, start=N) if a == 0 and op == 1]
    assert len(special) == 1
    index, guard = special[0]
    assert sum(a == 0 or b == 0 for _, a, b in gates) == 1
    assert all(not evaluate(gates, row)[guard] for row in GUARD_OFF)
    for row in range(1 << N):
        assert evaluate(gates, row)[-1] == any(row & edge == edge for edge in POS)

    def contract(w):
        return 0 if w == index else w - (w > index)

    base = [(op, contract(a), contract(b)) for w, (op, a, b) in enumerate(gates, start=N)
            if w != index]
    guard = contract(guard)
    output = N + len(base) - 1
    while len(base) < 16:
        base.append((0, 1, 2))
    assert len(base) <= 18 and guard != 0
    assert all(0 not in (a, b) for j, (_, a, b) in enumerate(base, start=N) if j <= guard)
    assert all(not evaluate(base, row & ~1)[guard] for row in GUARD_OFF)
    for row in range(1 << N):
        h = evaluate(base, row & ~1)[guard]
        assert evaluate(base, row | int(h))[output] == any(row & e == e for e in POS)
    return dict(base=base, guard=guard, output=output)


def search(job):
    size, first, band, distinct, fixed = job
    canonical = band is not None
    output, pool, clauses, ops, select = cs.build(N, size, colex_from=size if canonical or fixed else 0)
    clauses.extend([-flags[2]] for flags in ops.values())
    if first is not None:
        clauses.append([ops[N][first]])
    cs.add_fanout_rules(N, POS, ops, select, clauses)
    cs.add_readonce_rules(N, size, POS, pool, ops, select, clauses)
    special = {j: select[j, 0][0] for j in ops}
    clauses.extend(cs.CardEnc.equals(list(special.values()), 1, vpool=pool).clauses)
    for j, sel in special.items():
        clauses.append([-sel, ops[j][1]])
        clauses.extend([-sel, -primary] for primary in select[j, 1][:N])
    for j, op, a, b in fixed:
        clauses.extend(([ops[j][op]], [select[j, 0][a]], [select[j, 1][b]]))
    if distinct:
        # A one-gate guard is an edge AND. The stabilizer of input 0 has two edge orbits.
        one_gate = special[N + 1]
        clauses.extend(([-one_gate, ops[N][0]], [-one_gate, select[N, 0][1], select[N, 0][2]]))
        clauses.extend(([-one_gate, -select[N, 0][1], select[N, 1][2]],
                        [-one_gate, -select[N, 0][2], select[N, 1][3]]))
    if canonical:
        clauses.append([sel for j, sel in special.items() if j - N in band])
        for j in range(N + 1, output + 1):
            sel = special[j]
            # The special OR immediately follows its guard. All earlier gates feed the guard.
            clauses.append([-sel, select[j, 1][j - 1]])
            for w in range(N, j - 1):
                clauses.append([-sel, *(select[r, b][w] for r in range(w + 1, j) for b in (0, 1))])
        for j in range(N, output):
            left, right = select[j, 0], select[j, 1]
            next_left, next_right = select[j + 1, 0], select[j + 1, 1]
            boundary = [special[j], special[j + 1]]
            for r in range(j):
                clauses.extend([*boundary, -right[r], -next_right[smaller]] for smaller in range(r))
                for l in range(r):
                    clauses.extend([*boundary, -right[r], -next_right[r], -left[l], -next_left[smaller]]
                                   for smaller in range(l))
    truth = {}
    for row in POS + NEG:
        values = [pool.id(("truth", row, w)) for w in range(output + 1)]
        truth[row] = values
        clauses.extend([values[v] if row >> v & 1 else -values[v]] for v in range(N))
        clauses.append([values[-1] if row in POS else -values[-1]])
        clauses.extend(cs.truth_gate_clauses(row, values, pool, ops, select))
        projected = row & ~1
        if row in GUARD_OFF or distinct and any(projected & off == projected for off in GUARD_OFF):
            for j, sel in special.items():
                guard_value = pool.id(("arg", row, j, 1))
                clauses.append([-sel, -guard_value])
    if distinct:
        # Replacing a boundary-equivalent ordinary wire by an earlier wire keeps
        # all labels. Never remove the special OR or introduce another raw x0 reader.
        for b in range(N, output + 1):
            for a in range(1, b):
                differences = [special[b]]
                for row, values in truth.items():
                    v = values[b]
                    if a < N:
                        differences.append(-v if row >> a & 1 else v)
                        continue
                    u = values[a]
                    diff = pool.id(("diff", a, b, row))
                    differences.append(diff)
                    clauses.extend(([-diff, u, v], [-diff, -u, -v],
                                    [diff, -u, v], [diff, u, -v]))
                clauses.append(differences)
    with cs.Solver(name="maplechrono", bootstrap_with=clauses) as solver:
        seconds = 95 if fixed else 180 if canonical else SECONDS
        timer = Timer(seconds, solver.interrupt)
        timer.start()
        try:
            result = solver.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
        witness = None
        if result:
            model = set(solver.get_model())
            gates = [(int(flags[1] in model),
                      *(next(w for w, sel in enumerate(select[j, b]) if sel in model)
                        for b in (0, 1))) for j, flags in ops.items()]
            witness = check_gates(gates)
        return dict(size=size, first=first, guard_prefix=band, seconds=seconds, distinct=distinct,
                    fixed=fixed,
                    result={True: "SAT", False: "UNSAT", None: "OPEN"}[result],
                    clauses=len(clauses), statistics=solver.accum_stats(), witness=witness)


def repair_jobs():
    path = ROOT / "sat-search" / "results" / "petersen_guard_7893" / "construct-20.py"
    base, guard, _ = runpy.run_path(str(path))["build"]()
    prefix = [tuple(g) for g in base[:2]] + [(1, 0, guard)]
    physical = [*prefix, *((op, (guard + 1 if a == 0 else a + (a > guard)),
                           (guard + 1 if b == 0 else b + (b > guard))) for op, a, b in base[2:])]
    for seed in range(22):
        removed = 13 + seed % 16
        choices = []
        for w, (op, a, b) in enumerate(physical, start=N):
            if w <= 12 or removed in (w, a, b):
                continue
            a, b = sorted((a - (a > removed), b - (b > removed)))
            choices.append((w - (w > removed), op, a, b))
        pins = [(w, op, *sorted((a, b))) for w, (op, a, b) in enumerate(prefix, start=N)]
        pins.extend(random.Random(7893 + seed).sample(choices, 6 if seed < 16 else 3))
        yield 19, None, None, False, pins


if __name__ == "__main__":
    repair = "--repair" in sys.argv[1:]
    distinct = "--distinct" in sys.argv[1:]
    canonical = distinct or "--canonical" in sys.argv[1:]
    if distinct:
        check_edge_orbits()
    if repair:
        jobs = list(repair_jobs())
    elif canonical:
        jobs = [(size, None, list(band), distinct, []) for size in range(13, 19)
                for band in ([1], [2, 3], range(4, size - 1))]
        jobs.extend((19, None, list(band), distinct, []) for band in ([1], [2], [3, 4], range(5, 18)))
    else:
        jobs = [(size, first, None, False, []) for size in range(9, 20) for first in (0, 1)]
    assert len(jobs) == 22
    run = "repair" if repair else "distinct" if distinct else "canonical" if canonical else "search"
    with (BASE / f"L-meta-7893-{run}.jsonl").open("x", encoding="utf-8") as log:
        with ProcessPoolExecutor(max_workers=22) as pool:
            for future in as_completed(pool.submit(search, job) for job in jobs):
                result = json.dumps(future.result())
                print(result, file=log, flush=True)
                print(result, flush=True)
