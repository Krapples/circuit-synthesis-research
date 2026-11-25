"""Bounded Fano incidence search with a prescribed AND output and two marked singletons."""
from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import combinations
import json
from pathlib import Path
import random
import sys
import sys
from threading import Timer
from time import monotonic

SAT_SEARCH = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(SAT_SEARCH))
import cube_search as cs

N=14
EDGES=[(p,7+l) for p in range(7) for l in range(7) if (p-l)%7 in (0,1,3)]
EDGE_MASKS=[(1<<p)|(1<<l) for p,l in EDGES]
MARKED=(0,7)


def boundaries():
    negative=[]
    for row in range(1<<N):
        if any(row&edge==edge for edge in EDGE_MASKS):
            continue
        if all(row>>i&1 or any((row|(1<<i))&edge==edge for edge in EDGE_MASKS)
               for i in range(N)):
            negative.append(row)
    return negative


NEGATIVES=boundaries()
ROWS=sorted(set(EDGE_MASKS+NEGATIVES+[1<<v for v in range(N)]))
RAW=[sum(1<<i for i,row in enumerate(ROWS) if row>>v&1) for v in range(N)]
UNIVERSE=(1<<len(ROWS))-1
POSITIVES=sum(1<<i for i,row in enumerate(ROWS) if row in EDGE_MASKS)
OUTPUT_KNOWN=sum(1<<i for i,row in enumerate(ROWS) if row in EDGE_MASKS or row in NEGATIVES or row.bit_count()==1)
SINGLETONS=sum(1<<i for i,row in enumerate(ROWS) if row.bit_count()==1)
MARKED_ROWS=sum(1<<ROWS.index(1<<v) for v in MARKED)


def min_root_gates():
    required=set(MARKED)
    for p,q in EDGES:
        if p in MARKED or q in MARKED:
            required.update((p,q))
    other=[v for v in range(N) if v not in required]
    for count in range(len(other)+1):
        for extras in combinations(other,count):
            covers=required|set(extras)
            if all(p in covers or q in covers for p,q in EDGES):
                return len(covers)-1
    raise AssertionError("every vertex covers every edge")


def check(gates):
    assert gates[-1][0]==0 and len(gates)<=27
    for row in range(1<<N):
        values=[bool(row>>i&1) for i in range(N)]
        for j,(op,a,b) in enumerate(gates,N):
            assert 0<=a<b<j and op in (0,1)
            values.append(values[a] or values[b] if op else values[a] and values[b])
        assert values[-1]==any(row&edge==edge for edge in EDGE_MASKS)
        if row in [1<<v for v in MARKED]:
            assert not any(values[i] for i in gates[-1][1:])


def solve(job):
    start=monotonic()
    size,left,seed=job
    rng=random.Random(seed)
    output, pool, clauses, ops, select=cs.build(N,size)
    clauses.extend([-v[2]] for v in ops.values())
    clauses.extend(([ops[output][0]],[select[output,0][left]],[select[output,1][output-1]]))
    cs.add_fanout_rules(N,EDGE_MASKS,ops,select,clauses)
    cs.add_readonce_rules(N,size,EDGE_MASKS,pool,ops,select,clauses)
    _, depa = cs.add_dep_vars(N,size,pool,ops,select,clauses)
    full_side = pool.id(("full_side",))
    required = set(MARKED)
    for a,b in EDGES:
        if a in MARKED or b in MARKED:
            required.update((a,b))
    if left-N+1 < N-1:
        clauses.append([full_side])
    for side in (0,1):
        must_choose = full_side if side==1 else -full_side
        for v in range(N):
            clauses.append([-must_choose,depa[output,side,v]])
        for v in required:
            clauses.append([depa[output,side,v]])
        for a,b in EDGES:
            clauses.append([depa[output,side,a],depa[output,side,b]])
    elapsed_setup=monotonic()-start
    with cs.Solver(name="maplechrono",bootstrap_with=clauses) as solver:
        active=set()

        def add_rows(rows):
            for rid in set(rows)-active:
                values=[pool.id(("wire",rid,i)) for i in range(output+1)]
                row=ROWS[rid]
                solver.append_formula([[values[i] if row>>i&1 else -values[i]] for i in range(N)])
                if OUTPUT_KNOWN>>rid&1:
                    solver.add_clause([values[output] if POSITIVES>>rid&1 else -values[output]])
                if MARKED_ROWS>>rid&1:
                    solver.append_formula([[-values[left]],[-values[output-1]]])
                solver.append_formula(list(cs.truth_gate_clauses(rid,values,pool,ops,select)))
                active.add(rid)

        sample=[j for j in range(len(ROWS)) if (POSITIVES|SINGLETONS)>>j&1]
        negatives=[ROWS.index(row) for row in NEGATIVES]
        sample.extend(rng.sample(negatives,14))
        add_rows(sample)
        timer=Timer(110,solver.interrupt)
        timer.start()
        verdict="OPEN"
        models=0
        try:
            while True:
                sat=solver.solve_limited(expect_interrupt=True)
                if sat is None:
                    break
                if not sat:
                    verdict="UNSAT"
                    break
                model=set(solver.get_model())
                gates=[tuple([next(i for i,lit in enumerate(choices) if lit in model)]
                             + [next(i for i,lit in enumerate(select[j,slot]) if lit in model)
                                for slot in (0,1)]) for j,choices in ops.items()]
                values=RAW.copy()
                for op,a,b in gates:
                    values.append(values[a]|values[b] if op else values[a]&values[b])
                fails=((values[output]^POSITIVES)&OUTPUT_KNOWN) | ((values[left]|values[output-1])&MARKED_ROWS)
                models+=1
                if not fails:
                    check(gates)
                    verdict="SAT"
                    break
                options=[j for j in range(len(ROWS)) if fails>>j&1]
                add_rows(rng.sample(options,min(12,len(options))))
        finally:
            timer.cancel()
        record=dict(size=size,left=left,seed=seed,result=verdict,models=models,
                    rows=len(active),clauses=len(clauses),setup_s=round(elapsed_setup,3),
                    elapsed_s=round(monotonic()-start,3),solver=solver.accum_stats())
    if verdict=="SAT":
        record.update(gates=gates,output=output)
    return record


def main():
    assert len(EDGES)==21 and len(NEGATIVES)==37 and len(ROWS)==72
    tt={row for row in range(1<<N) if any(row & edge == edge for edge in EDGE_MASKS)}
    for a,b in combinations(range(N),2):
        a,b=1<<a,1<<b
        assert any(not (r & (a|b)) and r not in tt and (r|a) in tt and (r|b) in tt
                   for r in range(1<<N))
    start_left=N+min_root_gates()-1
    jobs=[(27,left,7374+left) for left in range(start_left,N+27-2)]
    jobs.extend((26,left,7474+left) for left in range(N+26-7,N+26-2))
    assert len(jobs)==22
    print(f"{len(jobs)} left-root shards, 22 workers, first left wire {start_left}",flush=True)
    target=Path(sys.argv[1])
    with target.open("x",encoding="utf-8") as log, ProcessPoolExecutor(max_workers=22) as pool:
        futures=[pool.submit(solve,job) for job in jobs]
        for future in as_completed(futures):
            verdict=future.result()
            print(json.dumps(verdict),file=log,flush=True)
            print(json.dumps(verdict),flush=True)
            if verdict["result"]=="SAT":
                target.with_suffix(".witness.json").write_text(json.dumps(verdict),encoding="utf-8")
                for task in futures:
                    task.cancel()
                break


if __name__=="__main__":
    main()
