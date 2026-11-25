"""Restriction-based excess bounds for complete monotone / free-NOT circuits.
Requires module_contraction.py, one_sharing_core.py. Constants are assigned
excess 0 as a bound, not treated as a constant-free circuit construction.
All costs are lower bounds on binary excess, not counted total gates.
"""
from functools import lru_cache
from itertools import combinations
from random import Random
from collections import Counter
from time import perf_counter
from module_contraction import cofactor1, pair_cof, simplify, essential, raw_monotone, vars, brute
from one_sharing_core import solve_core

@lru_cache(None)
def reduce_table(n,f,signed):
    for i in range(n-1,-1,-1):
        a,b=(cofactor1(n,f,i,v) for v in (0,1))
        if a==b:n-=1;f=a
    if n<=1:return n,f
    n,f,_=simplify(n,f,signed)
    if signed:f=min(f,((1<<(1<<n))-1)^f)
    return n,f

@lru_cache(None)
def lower(n,f,signed=False,mode=2):
    """mode 0: unary restrictions; 1: first gate + double restrictions;
    2: additionally exact sharing-one recognition on each reduced core.
    Monotone inputs required when signed=False.
    """
    n,f=reduce_table(n,f,signed)
    return core(n,f,signed,mode)

@lru_cache(None)
def core(n,f,signed,mode):
    if n<=1:return 0
    if mode>=2:
        if solve_core(n,f,signed,False) is not None:return 1
    C=[tuple(cofactor1(n,f,i,v) for v in (0,1)) for i in range(n)]
    l=[max(lower(n-1,g,signed,mode) for g in c) for c in C]
    L=max(max(l),1+min(l),2 if mode>=2 else 1)
    if mode==0:return L
    best=10**9
    for i,j in combinations(range(n),2):
        c=pair_cof(n,f,i,j)
        def double():return max(lower(n-2,g,signed,mode) for g in c)
        for a,b in ((0,0),(0,1),(1,0),(1,1)) if signed else ((0,0),(1,1)):
            # x_i must be repeated if it survives absorption by x_j, and conversely.
            ri=c[2*b]!=c[2*b+1]
            rj=c[a]!=c[a+2]
            assert ri or rj, (n,f,i,j,a,b) # otherwise pair module
            v=max(L, l[i]+1 if ri else 0, l[j]+1 if rj else 0)
            if ri and rj:v=max(v,2+double())
            best=min(best,v)
    return best


def first_gate_candidates(n,f,budget,signed=False,mode=2):
    """Feasible-by-bound first gate patterns, for a fully reduced core.
    Returns tuples (i,j,absorbing_i,absorbing_j,required repeated inputs).
    """
    if reduce_table(n,f,signed)[0]!=n:raise ValueError('requires irreducible essential core')
    if n<=1:return []
    l=[max(lower(n-1,cofactor1(n,f,i,v),signed,mode) for v in (0,1)) for i in range(n)]
    if max(l)>budget:return []
    out=[]
    for i,j in combinations(range(n),2):
        c=pair_cof(n,f,i,j)
        for a,b in ((0,0),(0,1),(1,0),(1,1)) if signed else ((0,0),(1,1)):
            ri=c[2*b]!=c[2*b+1];rj=c[a]!=c[a+2]
            assert ri or rj
            if ri and l[i]+1>budget or rj and l[j]+1>budget:continue
            if ri and rj and 2+max(lower(n-2,g,signed,mode) for g in c)>budget:continue
            out.append((i,j,a,b,tuple(k for k,r in ((i,ri),(j,rj)) if r)))
    return out


def check():
    from signed_region_bounds import Bound
    start=perf_counter();rng=Random(92133)
    for signed,n,b in ((False,3,5),(False,4,5),(True,3,5),(True,4,4)):
        C=Counter()
        for f,g in brute(n,b,'free' if signed else 'mono').items():
            if not essential(n,f):continue
            a,b1,c=(lower(n,f,signed,k) for k in range(3))
            e=g-n+1
            assert a<=b1<=c<=e,(signed,n,f,e,a,b1,c)
            C.update(cases=1,first_gain=b1>a,recognizer_gain=c>b1,exact=c==e)
        print('exact',signed,n,dict(C),flush=True)
    # Compare stronger existing lower bound and first-gate candidate pruning.
    from first_gate_bound import lower as first,mono_lower
    for signed,n,fs in ((False,4,range(1<<16)),(True,4,[rng.getrandbits(16) for _ in range(600)]),(True,5,[rng.getrandbits(32) for _ in range(180)]),(False,6,[sum(1<<a for a in range(64) if any(a&t==t for t in ts)) for ts in ([rng.randrange(1,64) for _ in range(rng.randrange(3,12))] for _ in range(250))])):
        C=Counter();ex=[]
        for f in fs:
            if not signed and not raw_monotone(n,f) or not essential(n,f):continue
            if reduce_table(n,f,signed)[0]!=n:continue
            a,b,c=(lower(n,f,signed,k) for k in range(3))
            d=Bound(n,f).lower();g=(first(n,f,1) if signed else mono_lower(n,f))-n+1
            base=max(d,g);C.update(cases=1,first_gain=b>a,recognizer_gain=c>b,beats_existing=c>base,beats_regional=c>d)
            if c>base and len(ex)<3:ex.append((f,a,b,c,d,g))
            k=max(base,c)
            cand=first_gate_candidates(n,f,k,signed)
            C['candidate_total']+=(4 if signed else 2)*n*(n-1)//2;C['candidate_kept']+=len(cand)
        print('sample',signed,n,dict(C),ex,flush=True)
    # Actual circuits, verify reader degree bound on arbitrary restrictions,
    # including circuits whose input set shrinks after restriction.
    C=Counter()
    for _ in range(1800):
        n=rng.randrange(3,7);signed=bool(rng.randrange(2));V=list(vars(n));one=(1<<(1<<n))-1;g=[]
        for j in range(rng.randrange(n-1,n+6)):
            i,k=rng.sample(range(len(V)),2);a,b=V[i],V[k]
            if signed and rng.randrange(2):a^=one
            if signed and rng.randrange(2):b^=one
            V.append(a&b if rng.randrange(2) else a|b);g.append((i,k))
        f=V[-1]
        if not essential(n,f):continue
        active={len(V)-1};reads=Counter()
        for j in range(len(V)-1,n-1,-1):
            if j in active:active.update(g[j-n]);reads.update(g[j-n])
        e=len(active)-2*n+1
        assert lower(n,f,signed)<=e
        for i in range(n):
            for b in (0,1):
                L=lower(n-1,cofactor1(n,f,i,b),signed)
                assert L+reads[i]-1<=e,(n,f,i,b,L,reads[i],e)
                C['single']+=1
        for i,j in combinations(range(n),2):
            for h in pair_cof(n,f,i,j):
                assert lower(n-2,h,signed)+reads[i]+reads[j]-2<=e
                C['pair']+=1
        C['circuits']+=1
    print('generated',dict(C),'seconds',round(perf_counter()-start,3),flush=True)

if __name__=='__main__':check()
