"""Search a six-input table with a live NOT reading an earlier gate."""
from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import combinations, permutations
import json
from pathlib import Path
import sys
from threading import Timer
from time import monotonic

SAT_SEARCH = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(SAT_SEARCH))
import cube_search as cs

N = 6
TABLE = 18445899635892944896
ROWS = range(1 << N)


def mask_list():
    return [r for r in ROWS if TABLE >> r & 1 and
            all(not (TABLE >> (r ^ (1 << i)) & 1) for i in range(N) if r >> i & 1)]


def first_gates():
    def remap(row, permutation):
        return sum(((row >> i) & 1) << j for i, j in enumerate(permutation))
    symmetries = [p for p in permutations(range(N)) if all(
        (TABLE >> r & 1) == (TABLE >> remap(r, p) & 1) for r in ROWS)]
    print(f"{len(symmetries)} input automorphisms, minterms {mask_list()}", flush=True)
    seen = set()
    for op in range(3):
        pairs = combinations(range(N), 2) if op != 2 else ((i,i) for i in range(N))
        for a, b in pairs:
            if (op,a,b) in seen:
                continue
            seen.update((op,*sorted((p[a],p[b]))) for p in symmetries)
            yield op,a,b


def verify(gates):
    assert any(op == 2 and left >= N for op, left, _ in gates)
    uses = set()
    for j, (op, a, b) in enumerate(gates, N):
        assert a < j and b < j
        if op == 2:
            assert a == b
            if a >= N:
                assert gates[a - N][0] != 2
        uses.update((a,b))
    assert set(range(N + len(gates) - 1)) <= uses
    for row in ROWS:
        vals = [(row >> i) & 1 for i in range(N)]
        for op, a, b in gates:
            vals.append([vals[a] & vals[b], vals[a] | vals[b], 1 ^ vals[a]][op])
        assert vals[-1] == (TABLE >> row & 1)


def solve(job):
    size, first, signed = job
    start = monotonic()
    end, pool, clauses, ops, select = cs.build(N, size)
    if first is not None:
        op,a,b = first
        clauses.extend(([ops[N][op]], [select[N,0][a]], [select[N,1][b]]))
    if signed:
        clauses.append([choices[2] for choices in ops.values()])
    else:
        clauses.extend([-choices[2]] for choices in ops.values())
    for j, choices in ops.items():
        clauses.extend([-choices[2],-lit] for lit in select[j,0][N:])
    for row in ROWS:
        values = [pool.id(("wire", row, j)) for j in range(end+1)]
        clauses.extend([values[i] if row >> i & 1 else -values[i]] for i in range(N))
        clauses.append([values[end] if TABLE >> row & 1 else -values[end]])
        clauses.extend(cs.truth_gate_clauses(row,values,pool,ops,select))
    with cs.Solver(name="maplechrono",bootstrap_with=clauses) as solver:
        timer = Timer(70,solver.interrupt)
        timer.start()
        try:
            result = solver.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
        record = dict(size=size,first=first,signed=signed,result="SAT" if result else "OPEN" if result is None else "UNSAT",
                      elapsed_s=round(monotonic()-start,4), solver=solver.accum_stats())
        if result:
            model = set(solver.get_model())
            gates = [tuple([next(k for k,lit in enumerate(ops[j]) if lit in model)] +
                           [next(k for k,lit in enumerate(select[j,side]) if lit in model) for side in (0,1)])
                     for j in ops]
            assert any(g[0] == 2 for g in gates) == signed
            for row in ROWS:
                vals = [(row >> i) & 1 for i in range(N)]
                for op,a,b in gates:
                    vals.append([vals[a]&vals[b], vals[a]|vals[b], 1^vals[a]][op])
                assert vals[-1] == (TABLE >> row & 1)
            record.update(gates=gates,output=end)
    return record


def main():
    first = list(first_gates())
    jobs = [(size,None,False) for size in (5,6,7)] + [(size,None,True) for size in (6,7)]
    jobs += [(8,gate,True) for gate in first]
    print(f"{len(jobs)} shards, 22 workers", flush=True)
    log = Path(sys.argv[1])
    with log.open("x",encoding="utf-8") as file, ProcessPoolExecutor(max_workers=22) as pool:
        tasks = [pool.submit(solve,job) for job in jobs]
        for task in as_completed(tasks):
            record = task.result()
            print(json.dumps(record),flush=True)
            print(json.dumps(record),file=file,flush=True)
            if record["result"] == "SAT":
                log.with_suffix(".witness.json").write_text(json.dumps(record),encoding="utf-8")
                for pending in tasks:
                    pending.cancel()
                break


if __name__ == "__main__":
    main()
