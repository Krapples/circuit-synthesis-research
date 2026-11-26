from itertools import combinations, product, permutations
from collections import Counter
from functools import lru_cache
from random import Random
from time import perf_counter

@lru_cache(None)
def co(n,f,i,b):
    mask=(1<<i)-1
    return sum(((f>>((x&mask)|(b<<i)|((x&~mask)<<1)))&1)<<x for x in range(1<<(n-1)))
@lru_cache(None)
def support(n,f):
    return tuple(i for i in range(n) if co(n,f,i,0)!=co(n,f,i,1))
def canon(n,f):return min(f,f^((1<<(1<<n))-1))
@lru_cache(None)
def trim(n,f):
    for i in reversed(range(n)):
        if co(n,f,i,0)==co(n,f,i,1):
            f=co(n,f,i,0); n-=1
    return n,canon(n,f)
@lru_cache(None)
def ident(n,f,i,j,p):
    assert i<j
    mask=(1<<j)-1
    return sum(((f>>((x&mask)|((x&~mask)<<1)|(((x>>i&1)^p)<<j)))&1)<<x for x in range(1<<(n-1)))

def lower(n,f,mode):return solve(*trim(n,f),mode)
EXACT3 = None
@lru_cache(None)
def solve(n,f,mode):
    if n<2:return 0
    if n==2:return 3 if f==6 else 1
    if n==3 and EXACT3 is not None:return EXACT3[f]
    c=[[co(n,f,i,b) for b in (0,1)] for i in range(n)]
    t=[[lower(n-1,g,mode) for g in pair] for pair in c]
    full=(1<<(1<<(n-1)))-1
    nc=[all(g not in (0,full) for g in pair) for pair in c]
    L=max(n-1,max(t[i][b]+n-max(1,len(support(n-1,c[i][b]))) for i in range(n) for b in (0,1)))
    for i in range(n):
        if nc[i]:L=max(L,min(t[i])+2)
        if c[i][0]^c[i][1]==full:L=max(L,min(t[i])+3)
    best=10**9
    for i,j in combinations(range(n),2):
        js=[j-1 in support(n-1,g) for g in c[i]]
        ins=[i in support(n-1,g) for g in c[j]]
        eq=[lower(n-1,ident(n,f,i,j,p),mode) for p in (0,1)]
        if mode==2:
            both=max(lower(n-2,co(n-1,c[i][a],j-1,b),mode) for a,b in product((0,1),repeat=2))
        for a,b in product((0,1),repeat=2):
            # Existing repository first_gate_bound.py (mode 2 there).
            v=max(L,t[i][a]+2,t[j][b]+2,eq[a^b]+1,eq[1^a^b]+2)
            if js[a]:
                v=max(v,max(t[j])+2)
                if nc[j]:v=max(v,min(t[j])+3)
            if ins[b]:
                v=max(v,max(t[i])+2)
                if nc[i]:v=max(v,min(t[i])+3)
            if mode>=1:
                # No first-layer reapplication in a suitable minimum circuit.
                v=max(v,t[i][a]+2+ins[b],t[j][b]+2+js[a])
            if mode==2:
                # One common local reader pattern must meet all restrictions.
                local=10**9
                for A,B,AB in product((0,1),repeat=3):
                    if ins[b] and not (A or AB):continue
                    if js[a] and not (B or AB):continue
                    u=max(v,t[i][a]+2+A+AB,t[i][1-a]+1+A+AB,
                          t[j][b]+2+B+AB,t[j][1-b]+1+B+AB,
                          both+2+A+B+AB,eq[a^b]+1+AB,eq[1^a^b]+2+AB)
                    local=min(local,u)
                v=local
            best=min(best,v)
    return best

# Independent exhaustive construction; quotient by complemented truth functions.
def enumerate_aig(n,maxg):
    full=(1<<(1<<n))-1
    prim=[canon(n,sum(1<<x for x in range(1<<n) if x>>i&1)) for i in range(n)]
    states={tuple(sorted(prim))}; costs={0:0,**{x:0 for x in prim}}; hits=0
    for k in range(1,maxg+1):
        new=set()
        for st in states:
            present=set(st)
            for a,b in combinations(st,2):
                for aa,bb in product((a,a^full),(b,b^full)):
                    c=canon(n,aa&bb)
                    if c==0 or c in present:continue
                    hits+=1
                    costs.setdefault(c,k)
                    if k<maxg:new.add(tuple(sorted((*st,c))))
        states=new
    return costs,hits

def independent(n,f):
    return f and all(not (f>>(x^(1<<i))&1) for x in range(1<<n) if f>>x&1 for i in range(n))
@lru_cache(None)
def q(n,f):
    if n<=1:return 0
    cs=[co(n,f,i,b) for i in range(n) for b in (0,1)]
    qs=[q(n-1,g) for g in cs if g]
    return max(qs+([1+min(qs)] if all(cs) else []))

def main():
    start=perf_counter(); exact={}
    # Algebraic normal form: each signed consumer of a first-layer gate
    # and one original primary is a literal, constant, or signed minterm.
    prim=(0b1010,0b1100); full=15
    allowed={0,full,*prim,*(p^full for p in prim)}
    allowed.update((prim[0]^(full if a else 0))&(prim[1]^(full if b else 0)) for a,b in product((0,1),repeat=2))
    count=0
    for a,b,i,c,d in product((0,1),repeat=5):
        g=(prim[0]^(full if a else 0))&(prim[1]^(full if b else 0))
        h=(g^(full if c else 0))&(prim[i]^(full if d else 0))
        assert h in allowed; count+=1
    print('local rewrite truth tables',count,flush=True)
    for n,g in ((2,3),(3,6),(4,4)):
        costs,hits=enumerate_aig(n,g); exact[n]=costs
        for f,c in costs.items():assert lower(n,f,2)<=c,(n,hex(f),c,lower(n,f,2))
        print('enumeration',n,g,'distinct complement classes',len(costs),'candidate output hits',hits,flush=True)
    for n in (3,4,5,6):
        rng=Random(738+n); counts=Counter(); witnesses=[]; gain_max=0
        fs=range(1<<(1<<n)) if n<=4 else [rng.getrandbits(1<<n) for _ in range(300 if n==5 else 80)]
        for f in fs:
            if len(support(n,f))!=n:continue
            a,b,c=[lower(n,f,m) for m in range(3)]
            assert a<=b<=c,(n,f,a,b,c)
            counts['full_support']+=1; counts['no_reapp_gain']+=b>a; counts['pattern_gain']+=c>b;counts['total_gain']+=c>a
            if c>a and (len(witnesses)<5 or c-a>gain_max):witnesses.append((hex(f),a,b,c));gain_max=max(gain_max,c-a)
        print('full-support screen',n,dict(counts),'witnesses',witnesses,'max gain',gain_max,flush=True)
    for n in (4,5,6):
        rng=Random(421+n); cnt=Counter(); ex=[]
        fs=range(1,1<<(1<<n)) if n==4 else [sum(1<<x for x in range(1<<n) if x.bit_count()%2==0 and rng.random()<.55) for _ in range(200 if n==5 else 80)]
        for f in fs:
            if not independent(n,f):continue
            a,b,c=[lower(n,f,m) for m in range(3)];d=n-1+2*q(n,f)
            cnt['sets']+=1;cnt['pattern_over_existing_first_gate']+=c>a;cnt['pattern_over_isolation']+=c>d;cnt['pattern_over_both']+=c>max(a,d)
            if c>max(a,d) and len(ex)<6:ex.append((hex(f),a,b,c,d))
        print('isolated',n,dict(cnt),ex,flush=True)
    rng=Random(921);cnt=Counter()
    for n in range(2,7):
        full=(1<<(1<<n))-1
        for _ in range(300):
            ws=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
            G=rng.randrange(1,3*n+1)
            for _ in range(G):
                a,b=rng.choices(ws,k=2);ws.append((a^(full if rng.randrange(2) else 0))&(b^(full if rng.randrange(2) else 0)))
            f=ws[-1];assert lower(n,f,2)<=G,(n,G,f,lower(n,f,2));cnt['circuits']+=1;cnt['full_support']+=len(support(n,f))==n
    print('random circuits',dict(cnt),flush=True)
    global EXACT3
    EXACT3=exact[3]; assert len(EXACT3)==128
    solve.cache_clear()
    for n in (4,5):
        rng=Random(884+n); cnt=Counter(); ex=[]; gained=set()
        fs=range(1<<(1<<n)) if n==4 else [rng.getrandbits(1<<n) for _ in range(300)]
        for f in fs:
            if len(support(n,f))!=n:continue
            a,b,c=[lower(n,f,m) for m in range(3)]
            assert a<=b<=c
            if n==4 and canon(n,f) in exact[n]:assert c<=exact[n][canon(n,f)]
            cnt['cases']+=1;cnt['no_reapp_gain']+=b>a;cnt['pattern_gain']+=c>b;cnt['total_gain']+=c>a
            if c>a:
                gained.add(f)
                if len(ex)<6:ex.append((hex(f),a,b,c))
        print('exact three-input leaves',n,dict(cnt),ex,flush=True)
        if n==4:
            orbit=set(); f=0x07e1
            for p in permutations(range(n)):
                for mask in range(16):
                    v=sum(((f>>sum((((x^mask)>>i)&1)<<p[i] for i in range(n)))&1)<<x for x in range(16))
                    orbit.update((v,v^65535))
            assert gained==orbit
            print('exact-leaf four-input gains are one NPN orbit',len(orbit),hex(min(orbit)),flush=True)
    print('elapsed seconds',perf_counter()-start,flush=True)
if __name__=='__main__':main()
