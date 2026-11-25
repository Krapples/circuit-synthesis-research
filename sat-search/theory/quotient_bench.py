"""Targeted benchmark and examples for ordered quotient reconstruction."""
from random import Random
from collections import Counter
from time import perf_counter
from itertools import product
from module_contraction import vars, essential, simplify, raw_monotone
from two_sharing_core import solve as two
from conditional_provider import solve as one_internal
from ordered_quotient_core import fixed, reconstruct, solve3, materialize3
from complete_sharing_fpt import Solver

def targeted(limit=6):
    rng=Random(891);cnt=Counter();out=[];t=perf_counter()
    # h1 = x op a; h2 = h1 op b (optionally a private chain); decoder
    # reads x once, h1 once, h2 twice. These are genuine 3-excess layouts.
    for it in range(5000):
        n=rng.choice((6,7));signed=bool(rng.randrange(2));R=(0,);groups=((1,),(2,),tuple(range(3,n)));P=((0,),(1,),(0,1,2,2));v=vars(n);one=(1<<(1<<n))-1
        def lit(x):return x^(one if signed and rng.randrange(2) else 0)
        def gate(a,b):return a&b if rng.randrange(2) else a|b
        h1=gate(lit(v[0]),lit(v[1]));h2=gate(lit(h1),lit(v[2]))
        # Four port leaves, each can have a chain of private inputs.
        A=list(map(lit,(v[0],h1,h2,h2)));order=list(groups[2]);rng.shuffle(order)
        for x in order:
            i=rng.randrange(len(A));A[i]=gate(A[i],lit(v[x]))
        while len(A)>1:
            a=A.pop(rng.randrange(len(A)));b=A.pop(rng.randrange(len(A)));A.append(gate(a,b))
        f=A[0]
        if not essential(n,f) or simplify(n,f,signed)[0]!=n:continue
        cnt['irreducible']+=1
        if two(n,f,signed) is not None:continue
        cnt['beyond_two']+=1
        a=fixed(n,f,R,groups,P,signed);assert a;G,z=reconstruct(n,f,R,groups,P,a,3)
        assert len(G)==n+2,(n,f,G)
        out.append((n,f,signed));print('exact excess-three witness',n,hex(f),signed,'gates',len(G),'iter',it,flush=True)
        if len(out)>=limit:break
    print('targeted',dict(cnt),'time',perf_counter()-t,flush=True)
    return out

if __name__=='__main__':
    fs=targeted()
    for n,f,signed in fs:
        t=perf_counter();stats=Counter();a=one_internal(n,f,3,signed,stats);dt=perf_counter()-t
        print('one-internal class',n,hex(f),signed,'found',a is not None,'sec',dt,'stats',dict(stats),flush=True)
        if a is None:
            t=perf_counter();a=solve3(n,f,signed);assert a;materialize3(n,f,a,signed);print('full',a[0],perf_counter()-t,flush=True)
