"""Look for a sub-63-gate two-output quadrangle witness in pinned-star families."""
from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import combinations
import json
from pathlib import Path
import random
import runpy
import sys
from threading import Timer
from time import perf_counter

ROOT = Path.cwd() / "sat-search"
sys.path.insert(0, str(ROOT))
import cube_search as cs

active_suffix = runpy.run_path(str(ROOT / "results/pg3_deleted_point_proxy_2216/pg3-final-or-sat.py"))["active_suffix"]
DIFF = {0, 1, 3, 9}
POINTS = range(13)
LINES = [set(p for p in POINTS if (p - l) % 13 in DIFF) for l in POINTS]
EDGES = [(p, l + 13) for l, points in enumerate(LINES) for p in sorted(points)]
POS = [(1 << p) | (1 << l) for p, l in EDGES]
NEG = []
for points in map(set, combinations(POINTS, 4)):
    if any(len(points & incident) > 2 for incident in LINES):
        continue
    missing = [l + 13 for l, incident in enumerate(LINES) if not points & incident]
    assert len(missing) == 3
    NEG.append(sum(1 << v for v in [*points, *missing]))
assert (len(POS), len(NEG)) == (52, 234)
ROWS = POS + NEG
POS_MASK = (1 << len(POS)) - 1
NEG_MASK = ((1 << len(ROWS)) - 1) ^ POS_MASK
COLUMNS = [sum(1 << i for i, row in enumerate(ROWS) if row >> v & 1) for v in range(26)]


def prefix_columns(leave, seed, by_line):
    rng = random.Random(seed)
    frozen = sorted(rng.sample(list(POINTS), 13 - leave))
    gates = []

    def emit(is_or, a, b):
        gates.append((is_or, a, b))
        return 25 + len(gates)

    terms = []
    for center in frozen:
        if by_line:
            side, leaves = center + 13, list(LINES[center])
        else:
            side = center
            leaves = [l for p, l in EDGES if p == center]
        rng.shuffle(leaves)
        a, b, c, d = leaves
        terms.append(emit(0, side, emit(1, emit(1, a, b), emit(1, c, d))))
    common = terms[0]
    for term in terms[1:]:
        common = emit(1, common, term)
    columns = COLUMNS.copy()
    for is_or, a, b in gates:
        columns.append(columns[a] | columns[b] if is_or else columns[a] & columns[b])
    common_column = columns[common]
    assert not (common_column & NEG_MASK)
    uncovered = POS_MASK ^ common_column
    return frozen, gates, common, common_column, uncovered, columns, rng


def solve(job):
    leave, seed, by_line, compact = job
    frozen, gates, common, common_column, uncovered, columns, rng = prefix_columns(leave, seed, by_line)
    index = list(range(len(columns)))
    if compact:
        care = uncovered | NEG_MASK
        representative = {}
        for j, column in enumerate(columns):
            bits = column & care
            if bits:
                representative.setdefault(bits, j)
        index = list(representative.values())
        columns = [columns[j] for j in index]
    n = len(columns)
    budget = 62 - len(gates) - 2
    largest, pool, cnf, ops, select = cs.build(n, budget, require_used=False)
    cnf.extend([-flags[2]] for flags in ops.values())
    wires = range(0 if compact else n, largest + 1)
    choices = [[pool.id(("output", a, j)) for j in wires] for a in range(2)]
    for output in choices:
        cnf.extend(cs.CardEnc.equals(output, 1, vpool=pool).clauses)
    # The output names can be swapped, so put the earlier gate first.
    cnf.extend([-a, -b] for i, a in enumerate(choices[0]) for b in choices[1][:i + 1])
    active_suffix(pool, cnf, ops, select, [output[-budget:] for output in choices])
    samples = set()
    wanted = [pool.id(("separator", o, r)) for o in range(2) for r in range(len(POS), len(ROWS))]
    for o in range(2):
        cnf.append(wanted[o * len(NEG):(o + 1) * len(NEG)])
    for o in range(2):
        for index, r in enumerate(range(len(POS), len(ROWS))):
            opposite = choices[1 - o]
            witness = wanted[o * len(NEG) + index]
            # A separator selector enforces output polarity even before CEGAR adds its truth row.
            for j, selected in zip(wires, choices[o]):
                cnf.append([-witness, -selected, pool.id(("wire", r, j))])
            for j, selected in zip(wires, opposite):
                cnf.append([-witness, -selected, -pool.id(("wire", r, j))])
    wall = 115
    start = perf_counter()
    with cs.Solver(name="maplechrono", bootstrap_with=cnf) as solver:
        def add_rows(ids):
            for r in sorted(set(ids) - samples):
                values = [pool.id(("wire", r, j)) for j in range(largest + 1)]
                solver.append_formula([[v if col >> r & 1 else -v] for v, col in zip(values, columns)])
                solver.append_formula(list(cs.truth_gate_clauses(r, values, pool, ops, select)))
                if r < len(POS):
                    for output in choices:
                        solver.append_formula([[-lit, values[j]] for lit, j in zip(output, wires)])
                else:
                    first = pool.id(("first-output", r))
                    solver.append_formula([[-lit, -values[j], first] for lit, j in zip(choices[0], wires)])
                    solver.append_formula([[-lit, -values[j], -first] for lit, j in zip(choices[1], wires)])
                samples.add(r)

        add_rows([r for r in range(len(POS)) if uncovered >> r & 1]
                 + (list(range(len(POS), len(ROWS))) if compact
                    else rng.sample(range(len(POS), len(ROWS)), 18)))
        timer = Timer(wall, solver.interrupt)
        timer.start()
        verdict, witness, models = "OPEN", None, 0
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
                    (int(flags[1] in model), *(next(i for i, lit in enumerate(select[j, side])
                                                   if lit in model) for side in range(2)))
                    for j, flags in ops.items()
                ]
                outputs = [next(j for j, lit in zip(wires, output) if lit in model) for output in choices]
                vals = columns.copy()
                for is_or, a, b in suffix:
                    vals.append(vals[a] | vals[b] if is_or else vals[a] & vals[b])
                a, b = (vals[j] | common_column for j in outputs)
                failures = (a & b & NEG_MASK) | (~(a & b) & POS_MASK)
                selected = [r for o in range(2) for r, lit in
                            zip(range(len(POS), len(ROWS)), wanted[o * len(NEG):(o + 1) * len(NEG)])
                            if lit in model and not ((a if o == 0 else b) >> r & 1
                                                     and not ((b if o == 0 else a) >> r & 1))]
                if not failures and (a & ~b & NEG_MASK) and (b & ~a & NEG_MASK):
                    used = max(0, max(outputs) - n + 1)
                    lifted = gates.copy()
                    for op, lhs, rhs in suffix[:used]:
                        lifted.append((op, index[lhs], index[rhs]))
                        index.append(25 + len(lifted))
                    outs = [26 + len(lifted), 27 + len(lifted)]
                    lifted.extend((1, common, index[j]) for j in outputs)
                    checked = COLUMNS.copy()
                    for op, lhs, rhs in lifted:
                        checked.append(checked[lhs] | checked[rhs] if op else checked[lhs] & checked[rhs])
                    assert [checked[j] for j in outs] == [a, b]
                    witness = dict(gates=lifted, outputs=outs)
                    verdict = "SAT"
                    break
                bad = [r for r in range(len(ROWS)) if failures >> r & 1]
                assert set(bad + selected) - samples
                rng.shuffle(bad)
                add_rows(selected + bad[:12])
            stats = solver.accum_stats()
        finally:
            timer.cancel()
    return dict(open_stars=leave, by_line=by_line, frozen=frozen, suffix_budget=budget,
                seed=seed, compact=compact, inputs=n, verdict=verdict, seconds=round(perf_counter() - start, 2),
                models=models, rows=len(samples), stats=stats, witness=witness)


if __name__ == "__main__":
    compact = "--compact" in sys.argv
    shapes = [2] * 16 + [3] * 6 if compact else [3] * 6 + [4] * 6 + [5] * 6 + [6] * 4
    jobs = [(leave, 5258 + i, bool(i % 2), compact) for i, leave in enumerate(shapes)]
    with Path(sys.argv[1]).open("x", encoding="utf-8") as records:
        with ProcessPoolExecutor(max_workers=22) as executor:
            for task in as_completed(executor.submit(solve, job) for job in jobs):
                row = json.dumps(task.result())
                print(row, flush=True)
                print(row, file=records, flush=True)
