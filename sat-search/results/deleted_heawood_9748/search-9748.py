"""Search the deleted Heawood line in the counted-NOT basis."""
from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import combinations
import json
from pathlib import Path
import random
import sys
from threading import Timer
from time import perf_counter

sys.path.insert(0, str(Path.cwd() / "sat-search"))
import cube_search as cs

N = 13
K = 22
EDGES = [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (2, 8), (2, 12), (3, 7),
         (3, 11), (3, 12), (4, 10), (4, 11), (5, 9), (5, 10), (5, 12),
         (6, 8), (6, 9), (6, 11)]
POS = [(1 << a) | (1 << b) for a, b in EDGES]
ROWS = range(1 << N)
FULL = (1 << len(ROWS)) - 1
KNOWN = sum(1 << x for x in ROWS if any(x & edge == edge for edge in POS))
BASE = [sum(1 << x for x in ROWS if x >> j & 1) for j in range(N)]
NEG = [x for x in ROWS if not (KNOWN >> x & 1) and all(KNOWN >> (x | (1 << j)) & 1
                                                       for j in range(N) if not (x >> j & 1))]


def search(job):
    cube, seed = job
    out, pool, cnf, ops, select = cs.build(N, K, require_used=False)
    nots = [flags[2] for flags in ops.values()]
    cnf.append(nots)
    if cube is not None:
        op, a, b = cube
        cnf.extend([[ops[N][op]], [select[N, 0][a]], [select[N, 1][b]]])
    else:
        cnf.extend(cs.CardEnc.atmost(nots, bound=1, vpool=pool).clauses)
    for i in range(N):
        cnf.append([select[j, side][i] for j in ops for side in (0, 1)])

    rng = random.Random(seed)
    seen = set()
    start = perf_counter()
    with cs.Solver(name="maplechrono", bootstrap_with=cnf) as solver:
        def add_rows(rows):
            for x in sorted(set(rows) - seen):
                wire = [pool.id(("wire", x, j)) for j in range(out + 1)]
                solver.append_formula([[wire[j] if x >> j & 1 else -wire[j]] for j in range(N)])
                solver.add_clause([wire[out] if KNOWN >> x & 1 else -wire[out]])
                solver.append_formula(list(cs.truth_gate_clauses(x, wire, pool, ops, select)))
                seen.add(x)

        add_rows([0, *[1 << i for i in range(N)], *POS, *NEG, *rng.sample(ROWS, 24)])
        timer = Timer(125, solver.interrupt)
        timer.start()
        verdict, witness, models = "OPEN", None, 0
        try:
            while True:
                result = solver.solve_limited(expect_interrupt=True)
                if result is None:
                    break
                if not result:
                    verdict = "UNSAT"
                    break
                models += 1
                model = set(solver.get_model())
                gates = [(next(i for i, lit in enumerate(flags) if lit in model),
                          *(next(i for i, lit in enumerate(select[j, side]) if lit in model)
                            for side in (0, 1)))
                         for j, flags in ops.items()]
                values = BASE.copy()
                for op, a, b in gates:
                    values.append((values[a] & values[b]) if op == 0 else
                                  (values[a] | values[b]) if op == 1 else (FULL ^ values[a]))
                errors = values[-1] ^ KNOWN
                if not errors:
                    assert all(cs.evaluate(N, gates, x) == any(x & edge == edge for edge in POS)
                               for x in ROWS)
                    verdict, witness = "SAT", gates
                    break
                bad = [x for x in ROWS if errors >> x & 1]
                assert not (seen & set(bad))
                add_rows(rng.sample(bad, min(35, len(bad))))
            stats = solver.accum_stats()
        finally:
            timer.cancel()
    return dict(cube=cube, seed=seed, verdict=verdict, witness=witness, models=models,
                rows=len(seen), seconds=round(perf_counter() - start, 2), stats=stats)


if __name__ == "__main__":
    automorphisms = cs.automorphisms(N, EDGES)
    pairs = [(op, a, b) for op in (0, 1) for a, b in combinations(range(N), 2)
             if cs.orbit_min((op, a, b), automorphisms)]
    singletons = [(2, a, a) for a in range(N) if cs.orbit_min((2, a, a), automorphisms)]
    jobs = [(cube, 9748 + i) for i, cube in enumerate(pairs + singletons + [None])]
    if len(jobs) != 22:
        raise ValueError("Expected 21 first-gate orbits and one one-NOT search.")
    with Path(sys.argv[1]).open("x", encoding="utf-8") as log:
        with ProcessPoolExecutor(max_workers=22) as workers:
            for task in as_completed(workers.submit(search, job) for job in jobs):
                entry = json.dumps(task.result())
                print(entry, file=log, flush=True)
                print(entry, flush=True)
