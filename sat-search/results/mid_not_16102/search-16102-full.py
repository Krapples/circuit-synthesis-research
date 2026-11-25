"""Search the full at-most-two syntax of the L-meta-16102 Lean target."""
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
MISSING = -1


def verify(gates):
    assert any(op == 2 and inputs and inputs[0] >= N for op, inputs in gates)
    uses = set()
    for j, (op, inputs) in enumerate(gates,N):
        assert 0 <= op <= 2 and len(inputs) <= 2
        assert all(0 <= i < j for i in inputs)
        if op == 2 and inputs and inputs[0] >= N:
            assert gates[inputs[0]-N][0] != 2
        uses.update(inputs)
    assert set(range(N+len(gates)-1)) <= uses
    for r in ROWS:
        wires = [bool(r >> i & 1) for i in range(N)]
        for op, inputs in gates:
            a = [wires[i] for i in inputs]
            wires.append(all(a) if op == 0 else any(a) if op == 1 else not (a and a[0]))
        assert wires[-1] == bool(TABLE >> r & 1)


def build(size):
    pool = cs.IDPool()
    clauses = []
    end = N+size-1
    ops = {j: [pool.id(("op",j,op)) for op in range(3)] for j in range(N,end+1)}
    selectors = {
        (j,slot): [pool.id(("input",j,slot,i)) for i in (*range(j),MISSING)]
        for j in ops for slot in (0,1)
    }
    maxima = {}
    mids = []

    def one(options):
        clauses.extend(cs.CardEnc.equals(options, 1, vpool=pool).clauses)

    for j, (is_and,is_or,is_not) in ops.items():
        left,right = selectors[j,0],selectors[j,1]
        one(ops[j]); one(left); one(right)
        clauses.append([-left[-1],right[-1]])
        for a in range(j):
            for b in range(a+1):
                clauses.append([-left[a],-right[b],is_not])
            if a >= N:
                clauses.append([-is_not,-left[a],-ops[a][2]])

        # An independent adjacency can be sorted by largest referenced wire.
        max_options = [pool.id(("max",j,i)) for i in range(j+1)]
        maxima[j] = max_options
        one(max_options)
        for a in range(j):
            for b in range(j):
                clauses.append([-left[a],-right[b],max_options[1+max(a,b)]])
            clauses.append([-left[a],-right[-1],max_options[1+a]])
        clauses.append([-left[-1],max_options[0]])
        if j>N:
            for b, higher in enumerate(maxima[j-1]):
                clauses.extend([-higher, -lower] for lower in max_options[:b])

        if j > N:
            mid = pool.id(("middle",j))
            mids.append(mid)
            clauses.extend(([-mid,is_not],[-mid,*left[N:j]]))
    clauses.append(mids)

    for i in range(end):
        clauses.append([selectors[j,slot][i] for j in range(max(N,i+1),end+1) for slot in (0,1)])

    for row in ROWS:
        values = [pool.id(("value",row,i)) for i in range(end+1)]
        clauses.extend([values[i] if row >> i & 1 else -values[i]] for i in range(N))
        clauses.append([values[end] if TABLE >> row & 1 else -values[end]])
        for j, (is_and,is_or,is_not) in ops.items():
            a,b = (pool.id(("arg",row,j,slot)) for slot in (0,1))
            for slot, arg in enumerate((a,b)):
                choices = selectors[j,slot]
                for i, flag in enumerate(choices[:-1]):
                    clauses.extend(([-flag,-arg,values[i]],[-flag,arg,-values[i]]))
                clauses.extend(([-choices[-1],-is_and,arg],[-choices[-1],-arg,is_and]))
            f=values[j]
            clauses.extend(([-is_and,-a,-b,f],[-is_and,a,-f],[-is_and,b,-f],
                            [-is_or,a,b,-f],[-is_or,-a,f],[-is_or,-b,f],
                            [-is_not,-a,-f],[-is_not,a,f]))
    return clauses,ops,selectors


def jobs():
    def remap(row,p):
        return sum(1 << p[i] for i in range(N) if row >> i & 1)
    autos = [p for p in permutations(range(N)) if all(
        (TABLE >> row & 1) == (TABLE >> remap(row,p) & 1) for row in ROWS)]
    first = []
    seen = set()
    for op in range(3):
        inputs = [()] + [(i,) for i in range(N)]
        inputs += list(permutations(range(N),2) if op==2 else combinations(range(N),2))
        for args in inputs:
            if (op,args) in seen:
                continue
            first.append((op,args))
            for p in autos:
                moved=tuple(p[i] for i in args)
                seen.add((op,moved if op==2 else tuple(sorted(moved))))
    for size in (6,7,8):
        yield size,None
    for candidate in first:
        yield 9,candidate


def solve(job):
    start=monotonic()
    size,first=job
    clauses,ops,sel=build(size)
    if first is not None:
        op,args=first
        a,b=(list(args)+[MISSING,MISSING])[:2]
        clauses.extend(([ops[N][op]],[sel[N,0][a]],[sel[N,1][b]]))
    with cs.Solver(name="maplechrono",bootstrap_with=clauses) as solver:
        timer=Timer(95,solver.interrupt)
        timer.start()
        try:
            sat=solver.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
        record=dict(size=size,first=first,result="SAT" if sat else "OPEN" if sat is None else "UNSAT",
                    elapsed_s=round(monotonic()-start,4),solver=solver.accum_stats())
        if sat:
            model=set(solver.get_model())
            gates=[]
            for j,choices in ops.items():
                op=next(i for i,lit in enumerate(choices) if lit in model)
                args=[i for slot in (0,1) for i,lit in enumerate(sel[j,slot][:-1]) if lit in model]
                gates.append((op,args))
            verify(gates)
            record.update(gates=gates,output=N+size-1)
    return record


def main():
    path=Path(sys.argv[1])
    inputs=list(jobs())
    print(f"{len(inputs)} full-arity shards, 22 workers",flush=True)
    with path.open("x",encoding="utf-8") as sink, ProcessPoolExecutor(max_workers=22) as pool:
        pending=[pool.submit(solve,item) for item in inputs]
        for future in as_completed(pending):
            record=future.result()
            print(json.dumps(record),file=sink,flush=True)
            print(json.dumps(record),flush=True)
            if record["result"]=="SAT":
                path.with_suffix(".witness.json").write_text(json.dumps(record),encoding="utf-8")
                for task in pending:
                    task.cancel()
                break


if __name__=="__main__":
    main()
