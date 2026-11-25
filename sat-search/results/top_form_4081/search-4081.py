"""Bounded synthesis for the eleven-vertex L-meta-4081 graph."""
from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import product
import json
from pathlib import Path
import random
import sys
from threading import Timer

BASE = Path(__file__).resolve().parent
ROOT = next(parent for parent in BASE.parents if (parent / "sat-search" / "cube_search.py").is_file())
sys.path.insert(0, str(ROOT / "sat-search"))
import cube_search as cs

N = 11
EDGES = ((0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9))
POS = tuple((1 << a) | (1 << b) for a, b in EDGES)
LOSING = {row for row in range(1 << N) if all(row & edge != edge for edge in POS)}
NEG = sorted(row for row in LOSING if all(row >> v & 1 or row | (1 << v) not in LOSING for v in range(N)))
ROWS = POS + tuple(NEG)
TARGET = (1 << len(POS)) - 1
COLUMNS = [sum(1 << i for i, row in enumerate(ROWS) if row >> v & 1) for v in range(N)]


def solve(job):
    size, parity, subset, seed = job
    rand = random.Random(seed)
    output, pool, cnf, ops, select = cs.build(N, size)
    cnf.extend([-flags[2]] for flags in ops.values())
    cnf.append([ops[N][parity]])
    cnf.append([select[N, 1][v] for v in subset])
    cs.add_fanout_rules(N, POS, ops, select, cnf)
    cs.add_readonce_rules(N, size, POS, pool, ops, select, cnf)
    active = set()
    verdict = "OPEN"
    models = 0
    witness = None
    with cs.Solver(name="maplechrono", bootstrap_with=cnf) as solver:
        def add_rows(group):
            for i in set(group) - active:
                values = [pool.id(("wire", i, v)) for v in range(output + 1)]
                solver.append_formula([[values[v] if ROWS[i] >> v & 1 else -values[v]] for v in range(N)])
                solver.add_clause([values[output] if TARGET >> i & 1 else -values[output]])
                solver.append_formula(list(cs.truth_gate_clauses(i, values, pool, ops, select)))
                active.add(i)

        add_rows(list(range(len(POS))) + rand.sample(range(len(POS), len(ROWS)), min(16, len(NEG))))
        timer = Timer(95, solver.interrupt)
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
                gates = [
                    (next(op for op, flag in enumerate(flags) if flag in model),
                     *(next(a for a, flag in enumerate(select[v, slot]) if flag in model)
                       for slot in (0, 1)))
                    for v, flags in ops.items()
                ]
                packed = COLUMNS.copy()
                for op, a, b in gates:
                    packed.append(packed[a] | packed[b] if op else packed[a] & packed[b])
                missed = packed[-1] ^ TARGET
                if not missed:
                    for row in range(1 << N):
                        values = [bool(row >> v & 1) for v in range(N)]
                        for op, a, b in gates:
                            values.append(values[a] or values[b] if op else values[a] and values[b])
                        assert values[-1] == (row not in LOSING)
                    witness = gates
                    verdict = "SAT"
                    break
                add_rows([i for i in range(len(ROWS)) if missed >> i & 1])
        finally:
            timer.cancel()
        return dict(size=size, op=parity, right=list(subset), seed=seed, result=verdict,
                    models=models, rows=len(active), stats=solver.accum_stats(), witness=witness)


if __name__ == "__main__":
    groups = ((1, 6), (2, 7), (3, 8), (4, 9), (5, 10))
    jobs = [(size, op, group, 4081 + i) for i, (size, op, group) in
            enumerate(product((20, 21), (0, 1), groups))]
    jobs.extend([(19, op, tuple(range(1, N)), 4101 + op) for op in (0, 1)])
    print(f"22 workers, {len(POS)} edge rows, {len(NEG)} maximal independent rows", flush=True)
    with (BASE / "L-meta-4081-search.jsonl").open("x", encoding="utf-8") as log:
        with ProcessPoolExecutor(max_workers=22) as pool:
            for future in as_completed(pool.submit(solve, job) for job in jobs):
                result = json.dumps(future.result())
                print(result, file=log, flush=True)
                print(result, flush=True)
