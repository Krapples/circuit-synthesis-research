"""Exact SAT repairs around a 27-gate near witness."""
from concurrent.futures import ProcessPoolExecutor, as_completed
from importlib.util import module_from_spec, spec_from_file_location
import json
from pathlib import Path
import random
import sys
from threading import Timer

BASE = Path(__file__).parent
spec = spec_from_file_location("fano_search", BASE / "search-4874-fano.py")
fano = module_from_spec(spec)
spec.loader.exec_module(fano)
cs = fano.cs


def search(job):
    seed, released, gates = job
    # The pinned witness uses its original topological order.
    out, pool, clauses, ops, select = cs.build(fano.N, 27, colex_from=27, require_used=False)
    clauses.extend([-flags[2]] for flags in ops.values())
    clauses.append([ops[out][0]])
    for wire, (op, a, b) in enumerate(gates, fano.N):
        if wire not in released:
            clauses.extend(([ops[wire][op]], [select[wire, 0][a]], [select[wire, 1][b]]))
    for index, row in enumerate(fano.ROWS):
        values = [pool.id(("wire", index, wire)) for wire in range(out + 1)]
        clauses.extend([values[wire] if row >> wire & 1 else -values[wire]]
                       for wire in range(fano.N))
        if fano.OUTPUT_KNOWN >> index & 1:
            clauses.append([values[out] if fano.POSITIVES >> index & 1 else -values[out]])
        if fano.MARKED_ROWS >> index & 1:
            clauses.extend([-flag, -values[wire]]
                           for slot in (0, 1) for wire, flag in enumerate(select[out, slot]))
        clauses.extend(cs.truth_gate_clauses(index, values, pool, ops, select))
    with cs.Solver(name="maplechrono", bootstrap_with=clauses) as solver:
        timer = Timer(45, solver.interrupt)
        timer.start()
        try:
            sat = solver.solve_limited(expect_interrupt=True)
            record = dict(seed=seed, released=sorted(released),
                          result={None: "OPEN", False: "UNSAT", True: "SAT"}[sat],
                          solver=solver.accum_stats())
            if sat:
                model = set(solver.get_model())
                witness = [
                    (next(op for op, flag in enumerate(flags) if flag in model),
                     *(next(i for i, flag in enumerate(select[wire, slot]) if flag in model)
                       for slot in (0, 1)))
                    for wire, flags in ops.items()
                ]
                fano.check(witness)
                record["gates"] = witness
            return record
        finally:
            timer.cancel()


def main():
    gates = json.loads((BASE / "L-meta-4874-near-witness.jsonl").read_text().splitlines()[0])["gates"]
    last = range(31, 41)
    jobs = [(seed, set(last) | set(random.Random(seed).sample(range(14, 31), 3 + seed % 5)), gates)
            for seed in range(4874, 4896)]
    with Path(sys.argv[1]).open("x", encoding="utf-8") as log, ProcessPoolExecutor(max_workers=22) as pool:
        for future in as_completed(pool.submit(search, job) for job in jobs):
            line = json.dumps(future.result())
            print(line, flush=True)
            print(line, file=log, flush=True)


if __name__ == "__main__":
    main()
