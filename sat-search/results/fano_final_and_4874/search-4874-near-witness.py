"""Search degree-limited rewrites of a checked 28-gate Fano witness."""
from concurrent.futures import ProcessPoolExecutor, as_completed
from importlib.util import module_from_spec, spec_from_file_location
import json
from math import exp
from pathlib import Path
import random
import sys
from time import monotonic

BASE=Path(__file__).parent
spec=spec_from_file_location("fano_search",BASE/"search-4874-fano.py")
fano=module_from_spec(spec)
spec.loader.exec_module(fano)
N=fano.N
SOURCE=json.loads((BASE/"L-meta-4874-upper28.json").read_text(encoding="utf-8"))["gates"]


def errors(gates):
    values=fano.RAW.copy()
    for op,a,b in gates:
        values.append(values[a]|values[b] if op else values[a]&values[b])
    a,b=gates[-1][1:]
    main=((values[-1]^fano.POSITIVES)&fano.OUTPUT_KNOWN)
    marked=(values[a]|values[b])&fano.MARKED_ROWS
    return main.bit_count()+2*marked.bit_count()


def deletion_pool():
    seeds={}
    for removed in range(len(SOURCE)-1):
        cut=N+removed
        for substitute in range(cut):
            gates=[]
            for i,(op,a,b) in enumerate(SOURCE):
                if i==removed:
                    continue
                parents=[substitute if a==cut else a,substitute if b==cut else b]
                parents=[p-int(p>cut) for p in parents]
                if parents[0]==parents[1]:
                    parents[1]=0 if parents[0] else 1
                gates.append((op,*sorted(parents)))
            gates=tuple(gates)
            seeds[gates]=errors(gates)
    return sorted((score,gates) for gates,score in seeds.items())


def random_edit(gates,rng):
    index=rng.randrange(len(gates))
    old=gates[index]
    op,a,b=old
    modification=rng.randrange(3 if index!=len(gates)-1 else 2)
    top=N+index
    if modification==0:
        a=rng.randrange(top-1)
        a+=a>=b
    elif modification==1:
        b=rng.randrange(top-1)
        b+=b>=a
    else:
        op=1-op
    gates[index]=(op,min(a,b),max(a,b))
    return index,old


def solve(job):
    seed,cap=job
    rng=random.Random(seed)
    pool=deletion_pool()
    start=monotonic()
    best, best_gates=pool[0]
    evaluations=0
    cycles=0
    while monotonic()-start<cap and best:
        limit=min(len(pool),5+cycles)
        current,gates=pool[rng.randrange(limit)]
        gates=list(gates)
        for i in range(12000):
            chance=i/12000
            temp=1.25*(1-chance)**2+.10
            old=[random_edit(gates,rng)]
            if rng.random()<.12:
                old.append(random_edit(gates,rng))
            score=errors(gates)
            evaluations+=1
            if score<=current or rng.random()<exp((current-score)/temp):
                current=score
                if score<best:
                    best,best_gates=score,tuple(gates)
                    if not best:
                        fano.check(best_gates)
                        break
            else:
                for index,gate in reversed(old):
                    gates[index]=gate
        cycles+=1
    return dict(seed=seed,best=best,gates=best_gates,evaluations=evaluations,
                seconds=round(monotonic()-start,3),result="SAT" if best==0 else "OPEN")


def main():
    target=Path(sys.argv[1])
    print("22 workers on deletion and rewrite seeds",flush=True)
    with target.open("x",encoding="utf-8") as file,ProcessPoolExecutor(max_workers=22) as pool:
        work=[pool.submit(solve,(9100+i,65)) for i in range(22)]
        for future in as_completed(work):
            record=future.result()
            print(json.dumps(record),file=file,flush=True)
            print(json.dumps({k:v for k,v in record.items() if k!="gates"}),flush=True)
            if record["result"]=="SAT":
                target.with_suffix(".witness.json").write_text(json.dumps(record),encoding="utf-8")
                for w in work:
                    w.cancel()
                break


if __name__=="__main__":
    main()
