"""Search the exact restriction of each pinned-star circuit family."""
from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import combinations, product
import json
from pathlib import Path
import runpy
import sys
from threading import Timer

ROOT = Path(__file__).resolve().parent
target = runpy.run_path(str(ROOT / "search-9791.py"))
cs = target["cs"]
NEIGHBORS = target["NEIGHBORS"]
BUDGET = target["BUDGET"]


def setup(frozen, seed, retain=None):
    import random

    circuit = []
    providers = []
    gen = random.Random(seed)
    roots = []

    def emit(kind, left, right):
        circuit.append((kind, left, right))
        return 23 + len(circuit)

    for line in frozen:
        points = list(NEIGHBORS[line])
        gen.shuffle(points)
        if retain is not None:
            subset = retain.intersection(points)
            assert len(subset) <= 2
            if len(subset) == 2:
                points = sorted(subset) + [i for i in points if i not in subset]
        a, b, c, d = points
        left = emit(1, a, b)
        right = emit(1, c, d)
        whole = emit(1, left, right)
        providers.extend([(left, {a, b}), (right, {c, d}), (whole, set(points))])
        roots.append(emit(0, line, whole))
    root = roots[0]
    for nxt in roots[1:]:
        root = emit(1, root, nxt)
    return circuit, providers, root


def boundary(core):
    for b, points in core.items():
        for a in points:
            yield {a, b}, True
    left = set().union(*map(set, core.values()))
    for flags in product((False, True), repeat=len(core)):
        lines = {b for b, flag in zip(core, flags) if flag}
        points = left - {a for b in lines for a in core[b]}
        if all(b in lines or points.intersection(neighbors) for b, neighbors in core.items()):
            yield lines | points, False


def solve(job):
    frozen, seed, all_pairs, direct = job
    core = {b: points for b, points in NEIGHBORS.items() if b not in frozen}
    left_inputs = {a for points in core.values() for a in points}
    active = set(core) | left_inputs
    prefix, providers, fixed = setup(frozen, seed, left_inputs if all_pairs else None)
    usable = [(i, {i}) for i in sorted(active)] + [
        (wire, support) for wire, support in providers if support <= active]
    n = len(usable)
    k = BUDGET - len(prefix) - 1
    output, pool, cnf, ops, select = cs.build(n, k, require_used=False)
    cnf.extend([-flags[2]] for flags in ops.values())
    covered = set().union(*(support for _, support in usable[len(active):]))
    if direct:
        for _, support in usable[len(active):]:
            assert len(support) >= 2 and all(len(support.intersection(points)) <= 1
                                            for points in core.values())
    for i, (wire, _) in enumerate(usable[:len(active)]):
        if direct or wire not in covered:
            cnf.append([select[j, slot][i] for j in ops for slot in (0, 1)])
    rows = list(boundary(core))
    for r, (ones, want) in enumerate(rows):
        values = [pool.id(("wire", r, i)) for i in range(output + 1)]
        cnf.extend([v if support & ones else -v] for v, (_, support) in zip(values, usable))
        cnf.append([values[output] if want else -values[output]])
        cnf.extend(cs.truth_gate_clauses(r, values, pool, ops, select))
    with cs.Solver(name="maplechrono", bootstrap_with=cnf) as solver:
        timer = Timer(65 if all_pairs else 105, solver.interrupt)
        timer.start()
        try:
            result = solver.solve_limited(expect_interrupt=True)
            witness = None
            if result:
                model = set(solver.get_model())
                index = [wire for wire, _ in usable]
                witness = prefix.copy()
                for wire, flags in ops.items():
                    kind = next(i for i, flag in enumerate(flags) if flag in model)
                    left, right = (index[next(j for j, flag in enumerate(select[wire, slot])
                                              if flag in model)] for slot in (0, 1))
                    witness.append((kind, left, right))
                    index.append(23 + len(witness))
                witness.append((1, fixed, index[output]))
                columns = target["BASE_COLUMNS"].copy()
                for kind, left, right in witness:
                    columns.append(columns[left] | columns[right] if kind else columns[left] & columns[right])
                assert columns[-1] == target["KNOWN"]
        finally:
            timer.cancel()
        verdict = "SAT" if result else "OPEN" if result is None else "UNSAT"
    return dict(frozen=frozen, seed=seed, result=verdict, inputs=n, suffix=k,
                    direct=direct,
                    rows=len(rows), stats=solver.accum_stats(), witness=witness)


if __name__ == "__main__":
    direct = "--direct" in sys.argv
    if "--pairs" in sys.argv:
        jobs = [(sorted(set(NEIGHBORS) - set(core)), 9791 + i, True, direct)
                for i, core in enumerate(combinations(NEIGHBORS, 2))]
    else:
        with (ROOT / "search-9791-run1.jsonl").open(encoding="utf-8") as previous:
            jobs = sorted([(row["frozen"], row["seed"], False, direct)
                            for row in map(json.loads, previous)],
                          key=lambda job: job[1])
    print(f"22 SAT workers, {len(jobs)} projected fixed-prefix queries", flush=True)
    with Path(sys.argv[1]).open("x", encoding="utf-8") as records:
        with ProcessPoolExecutor(max_workers=22) as pool:
            for task in as_completed(pool.submit(solve, job) for job in jobs):
                row = json.dumps(task.result())
                print(row, flush=True)
                print(row, file=records, flush=True)
