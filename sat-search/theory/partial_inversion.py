"""Exact minimum NOT count on partial truth labels, ignoring binary cost.
Rows are (input bitmask, label). Distinct signals may be correlated.
Markov's theorem + monotone rank extension. Standard library.
"""
from functools import lru_cache
from itertools import product
from random import Random
from time import perf_counter
from collections import Counter

def ranks(rows):
    labels={}
    for a,b in rows:
        if b not in (0,1):raise ValueError('binary labels required')
        if a in labels and labels[a]!=b:raise ValueError('conflicting rows')
        labels[a]=b
    rr={}
    for a in sorted(labels,key=int.bit_count):
        b=labels[a]
        rr[a]=max([b]+[v+((v&1)!=b) for c,v in rr.items() if c&a==c])
    return rr

def inversion(rows):
    r=ranks(rows);d=max(r.values(),default=0)//2
    return d.bit_length()  # ceil(log2(d+1))

def extension(m,rows):
    r=ranks(rows)
    return sum((max((v for a,v in r.items() if a&x==a),default=0)&1)<<x for x in range(1<<m))

def boundary(cols,P,N):
    return [(sum((c>>a&1)<<i for i,c in enumerate(cols)),int(P>>a&1)) for a in range((P|N).bit_length()) if (P|N)>>a&1]

def test():
    from module_contraction import vars
    t=perf_counter();ct=Counter()
    n=3;R=1<<n
    # Independent complete-table decrease DP on full cube.
    def decrease(f):
        d=[0]*R
        for a in range(R):
            for i in range(n):
                if a>>i&1:
                    b=a^(1<<i);d[a]=max(d[a],d[b]+int((f>>b&1)>(f>>a&1)))
        return max(d)
    dd=[decrease(f) for f in range(1<<R)]
    @lru_cache(None)
    def best(P,N):
        if P|N==(1<<R)-1:return dd[P]
        a=((1<<R)-1)&~(P|N);a&=-a
        return min(best(P|a,N),best(P,N|a))
    for lab in product(range(3),repeat=R):
        P=sum(1<<i for i,x in enumerate(lab) if x==1);N=sum(1<<i for i,x in enumerate(lab) if x==2)
        rows=boundary(vars(n),P,N);g=extension(n,rows)
        assert g&P==P and not g&N and decrease(g)==best(P,N)
        assert inversion(rows)==best(P,N).bit_length();ct['partial_exact']+=1
    r=Random(744)
    for _ in range(2000):
        n=r.randrange(3,7);C=list(vars(n));full=(1<<(1<<n))-1;G=[];v=r.randrange(n)
        unused=[i for i in range(n) if i!=v];r.shuffle(unused)
        for j in range(r.randrange(n+1,n+9)):
            if r.random()<.3:
                C.append(C[v]^full);G.append(True)
            else:
                w=unused.pop() if unused else r.choice([i for i in range(len(C)) if i!=v]);C.append(C[v]&C[w] if r.randrange(2) else C[v]|C[w]);G.append(False)
            v=len(C)-1
        P=C[-1];N=full^P
        if not P or not N:continue
        q=r.randrange(len(G));u=sum(G[:q]);a=inversion(boundary(C[:n],P,N));b=inversion(boundary(C[:n+q],P,N));actual=sum(G[q:]);assert b<=actual and a<=sum(G)
        ct.update(prefixes=1,prefix_gain=b>max(0,a-u))
    print(dict(ct),'seconds',round(perf_counter()-t,3))
if __name__=='__main__':test()
