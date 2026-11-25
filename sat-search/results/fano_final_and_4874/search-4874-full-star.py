"""Try 27-gate Fano final-AND circuits with several line stars pinned."""
from concurrent.futures import ProcessPoolExecutor, as_completed
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations
import json
from pathlib import Path
import random
import sys
from threading import Timer
from time import monotonic

BASE=Path(__file__).parent
spec=spec_from_file_location("fano_search",BASE/"search-4874-fano.py")
fano=module_from_spec(spec)
spec.loader.exec_module(fano)
cs=fano.cs

N=14
LINES=tuple(range(7,14))
EDGES=fano.EDGES
NEIGHBORS={l:[p for p,q in EDGES if q==l] for l in LINES}
MASKS=fano.EDGE_MASKS
NEG=fano.NEGATIVES
SINGLE=[1<<v for v in fano.MARKED]
ROWS=MASKS+NEG+SINGLE
RAW=[sum(1<<i for i,row in enumerate(ROWS) if row>>v&1) for v in range(N)]
EXPECTED=(1<<len(MASKS))-1
MARKED_BITS=sum(1<<ROWS.index(r) for r in SINGLE)


def search(job):
    fixed,seed=job
    t0=monotonic()
    rng=random.Random(seed)
    prefix=[]
    def emit(op,a,b):
        prefix.append((op,min(a,b),max(a,b)))
        return N+len(prefix)-1
    roots=[]
    for line in fixed:
        pts=NEIGHBORS[line].copy()
        rng.shuffle(pts)
        a,b,c=pts
        roots.append(emit(0,line,emit(1,emit(1,a,b),c)))
    right=roots[0]
    for root in roots[1:]:
        right=emit(1,right,root)
    wires=RAW.copy()
    for op,a,b in prefix:
        wires.append(wires[a]|wires[b] if op else wires[a]&wires[b])
    length=len(wires)
    output,pool,clauses,ops,select=cs.build(length,27-len(prefix),require_used=False)
    clauses.extend([-types[2]] for types in ops.values())
    for g in range(length,output):
        clauses.append([select[j,slot][g] for j in range(g+1,output+1) for slot in (0,1)])
    clauses.extend(([ops[output][0]], [select[output,1][output-1]], select[output,0][length:output-1]))
    goal_mask=(1<<len(ROWS))-1

    with cs.Solver(name="maplechrono",bootstrap_with=clauses) as solver:
        labels=set()
        def add_rows(indices):
            for i in set(indices)-labels:
                values=[pool.id(("wire",i,j)) for j in range(output+1)]
                solver.append_formula([[values[j] if col>>i&1 else -values[j]] for j,col in enumerate(wires)])
                solver.add_clause([values[output] if EXPECTED>>i&1 else -values[output]])
                if MARKED_BITS>>i&1:
                    solver.add_clause([-values[output-1]])
                    solver.append_formula([[-flag,-values[j]] for j,flag in enumerate(select[output,0])])
                solver.append_formula(list(cs.truth_gate_clauses(i,values,pool,ops,select)))
                labels.add(i)
        minimum=list(range(len(MASKS)))+list(range(len(ROWS)-2,len(ROWS)))
        minimum+=rng.sample(range(len(MASKS),len(MASKS)+len(NEG)),16)
        add_rows(minimum)
        timer=Timer(78,solver.interrupt)
        timer.start()
        models=0
        result="OPEN"
        try:
            while True:
                sat=solver.solve_limited(expect_interrupt=True)
                if sat is None:
                    break
                if not sat:
                    result="UNSAT"
                    break
                models+=1
                model=set(solver.get_model())
                suffix=[tuple([next(op for op,lit in enumerate(types) if lit in model)]+
                         [next(i for i,lit in enumerate(select[j,k]) if lit in model) for k in (0,1)])
                        for j,types in ops.items()]
                values=wires.copy()
                for op,a,b in suffix:
                    values.append(values[a]|values[b] if op else values[a]&values[b])
                a,b=suffix[-1][1:]
                fail=((values[output]^EXPECTED)&goal_mask)|((values[a]|values[b])&MARKED_BITS)
                if not fail:
                    result="SAT"
                    gates=prefix+suffix
                    fano.check(gates)
                    break
                missed=[i for i in range(len(ROWS)) if fail>>i&1]
                add_rows(rng.sample(missed,min(10,len(missed))))
        finally:
            timer.cancel()
        record=dict(fixed=fixed,seed=seed,result=result,labels=len(labels),
                    models=models,elapsed_s=round(monotonic()-t0,3),solver=solver.accum_stats())
    if result=="SAT":
        record["gates"]=gates
    return record


def main():
    options=[]
    for size in (5,4,3):
        group=list(combinations(LINES,size))
        random.Random(4874+size).shuffle(group)
        options+=group[:(8 if size==5 else 7)]
    assert len(options)==22
    jobs=list(zip(options,range(7750,7772)))
    target=Path(sys.argv[1])
    print(f"{N} inputs, {len(MASKS)} edges, {len(NEG)} negatives, {len(jobs)} windows, 22 workers",flush=True)
    with target.open("x",encoding="utf-8") as log,ProcessPoolExecutor(max_workers=22) as pool:
        work=[pool.submit(search,job) for job in jobs]
        for future in as_completed(work):
            row=future.result()
            print(json.dumps(row),file=log,flush=True)
            print(json.dumps(row),flush=True)
            if row["result"]=="SAT":
                target.with_suffix(".witness.json").write_text(json.dumps(row),encoding="utf-8")
                for w in work:
                    w.cancel()
                break


if __name__=="__main__":
    main()
