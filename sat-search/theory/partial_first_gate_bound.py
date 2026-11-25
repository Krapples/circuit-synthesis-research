"""First-gate elimination bounds for partial monotone/free-NOT synthesis.
P,N are bitsets of assignments, disjoint. Constant outputs are free in the
relaxation (safe for constant-free synthesis). No mandatory use of all inputs.
Run for an independent n=3 partial-table test using bounded gate-set enumeration.
"""
from functools import lru_cache
from itertools import combinations, product
from collections import Counter
from time import perf_counter
from module_contraction import vars, cofactor1, brute

@lru_cache(None)
def distinctions(n,P,N,mono):
    ps=[i for i in range(1<<n) if P>>i&1];ns=[i for i in range(1<<n) if N>>i&1]
    return frozenset((a&~b) if mono else (a^b) for a in ps for b in ns)

@lru_cache(None)
def hitting(n,D):
    if 0 in D:return float('inf')
    if not D:return 0
    return min(S.bit_count() for S in range(1<<n) if all(S&d for d in D))

@lru_cache(None)
def one_gate(n,mono):
    vs=vars(n);mask=(1<<(1<<n))-1
    ss=set(vs)
    if not mono:ss.update(v^mask for v in vs)
    for a,b in combinations(vs,2):
        if mono:ss.update((a&b,a|b))
        else:
            for x,y in product((a,a^mask),(b,b^mask)):
                q=x&y;ss.update((q,q^mask))
    return tuple(ss)

def match(f,P,N):return f&P==P and f&N==0

@lru_cache(None)
def bound(n,P,N,mono=False,first=True):
    if P&N:return float('inf')
    if not P or not N:return 0
    D=distinctions(n,P,N,mono);k=hitting(n,D)
    if k==float('inf'):return k
    mask=(1<<(1<<n))-1
    if any(match(f,P,N) for f in vars(n)):return 0
    if not mono and any(match(f^mask,P,N) for f in vars(n)):return 0
    if any(match(f,P,N) for f in one_gate(n,mono)):return 1
    # Neither a literal nor a one-gate output can satisfy the labels.
    c=[[(cofactor1(n,P,i,b),cofactor1(n,N,i,b)) for b in (0,1)] for i in range(n)]
    t=[[bound(n-1,p,q,mono,first) for p,q in pair] for pair in c]
    mixed=[all(p and q for p,q in pair) for pair in c]
    L=max(2,k-1,max(max(v) for v in t))
    for i in range(n):
        if 1<<i in D:
            L=max(L,max(t[i])+1)
            if mixed[i]:L=max(L,min(t[i])+2)
    if not first:return L
    ans=float('inf')
    for i,j in combinations(range(n),2):
        surv_j=[1<<(j-1) in distinctions(n-1,*q,mono) for q in c[i]]
        surv_i=[1<<i in distinctions(n-1,*q,mono) for q in c[j]]
        for a,b in ((0,0),(1,1)) if mono else product((0,1),repeat=2):
            v=max(L,max(t[i])+1,max(t[j])+1,t[i][a]+2,t[j][b]+2)
            if surv_j[a]:
                v=max(v,max(t[j])+2)
                if mixed[j]:v=max(v,min(t[j])+3)
            if surv_i[b]:
                v=max(v,max(t[i])+2)
                if mixed[i]:v=max(v,min(t[i])+3)
            ans=min(ans,v)
    return ans

def test():
    from random import Random
    start=perf_counter();r=Random(31)
    for mono in (True,False):
        for n,budget in ((3,5),(4,4)):
            known=brute(n,budget,'mono' if mono else 'free')
            ordered=sorted(known.items(),key=lambda q:q[1]);ct=Counter();examples=[]
            rows=product(range(3),repeat=1<<n) if n==3 else (tuple(r.randrange(3) for j in range(1<<n)) for _ in range(1000))
            for labels in rows:
                P=sum(1<<i for i,v in enumerate(labels) if v==1);N=sum(1<<i for i,v in enumerate(labels) if v==2)
                if not P or not N:continue
                a=bound(n,P,N,mono,False);b=bound(n,P,N,mono,True)
                assert a<=b,(n,P,N,a,b)
                if a==float('inf'):ct['infeasible']+=1;continue
                ct['cases']+=1;ct['gain']+=b>a
                c=next((v for f,v in ordered if match(f,P,N)),None)
                if c is not None:
                    assert b<=c,(mono,n,P,N,a,b,c)
                    ct['checked']+=1;ct['exact']+=b==c
                    if b>a and len(examples)<2:examples.append((P,N,a,b,c))
                else:ct['unresolved']+=1 # no exact cost within oracle cap
            print('partial',mono,n,dict(ct),'examples',examples,flush=True)
    print('seconds',perf_counter()-start,flush=True)

if __name__=='__main__':test()
