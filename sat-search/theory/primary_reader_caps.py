"""Minimum-preserving AIG primary-reader constraints, complete tables.
No explicit NOT cost, no exact nonminimum/pinned prefixes. Uses normalized
AND, OR, left difference, right difference, all-zero anchor. See test().
"""
from functools import lru_cache
from itertools import combinations, product
from collections import Counter
from random import Random
from time import perf_counter
from module_contraction import vars, essential, brute, cofactor1
from phase_budget_cnf import CNF
ABS=((0,0),(1,1),(0,1),(1,0))

def caps(n,f,B,lower):
    """Return (unconditional cap, cap if any reader absorbs at 0, cap at 1).
    Conditional caps require no reapplication and a trimmed circuit.
    lower(n,f) must be a sound free-NOT binary bound; constants cost 0.
    """
    full=(1<<(1<<(n-1)))-1
    out=[]
    for i in range(n):
        g=[cofactor1(n,f,i,a) for a in (0,1)]
        v=[lower(n-1,h) for h in g]
        d=B-max(v)
        out.append((d,*(min(d,B-l-1) if h not in (0,full) else d for h,l in zip(g,v))))
    return out

def add_caps(c,read,absorbing,C):
    """read[i] = reader indicator literals, one per binary slot.
    absorbing[i][a] = indicators of readers absorbing at a (can be conjunction
    indicators from selector/operator). c supports add, new, at_most, clauses.
    No reapplication must already be enforced for conditional caps.
    """
    for i,(d,*conditional) in enumerate(C):
        c.at_most(read[i],d)
        for a,k in enumerate(conditional):
            if k>=d or k>=len(read[i]):continue
            flag=c.new()
            for lit in absorbing[i][a]:c.add(-lit,flag)
            p=len(c.clauses);c.at_most(read[i],k)
            for j in range(p,len(c.clauses)):c.clauses[j]=(-flag,*c.clauses[j])

@lru_cache(None)
def oracle(n):return brute(n,5 if n==3 else 3,'free')
@lru_cache(None)
def lower(n,f):
    mask=(1<<(1<<n))-1
    if f in (0,mask):return 0
    for i in range(n):
        a,b=cofactor1(n,f,i,0),cofactor1(n,f,i,1)
        if a==b:return lower(n-1,a)
    if n==1:return 0
    if n<=3:return oracle(n).get(min(f,mask^f),6 if n==3 else 4)
    return n-1

def ops(a,b,m):return (a&b,a|b,a&(~b&m),(~a&m)&b)

def test():
    # Independent exhaustive topology enumeration (no caps, no symmetry
    # other than operand sorting and no reapplication). Record min witnesses.
    start=perf_counter();n=3;m=255;v=list(vars(n));seen=set();hits=Counter()
    known=oracle(n);target={min(f,m^f) for f in known if essential(n,f)}
    def rec(gates,limit):
        if gates:
            f=v[-1];canon=min(f,m^f)
            if canon in target and known[canon]==len(gates):
                d=[0]*n;absval=[set() for _ in range(n)]
                for a,b,k in gates:
                    for i,s in zip((a,b),ABS[k]):
                        if i<n:d[i]+=1;absval[i].add(s)
                C=caps(n,f,len(gates),lower)
                for i,(c,z,o) in enumerate(C):
                    assert d[i]<=c and (0 not in absval[i] or d[i]<=z) and (1 not in absval[i] or d[i]<=o),(f,gates,d,C)
                hits['min_circuits']+=1;seen.add(canon)
        if len(gates)==limit:return
        for a,b in combinations(range(len(v)),2):
            if b>=n and a in gates[b-n][:2]:continue
            if a>=n and b in gates[a-n][:2]:continue
            for k,w in enumerate(ops(v[a],v[b],m)):
                if w in (0,m) or any(w==x or w==(m^x) for x in v):continue
                v.append(w);rec(gates+[(a,b,k)],limit);v.pop()
    rec([],4)
    assert all(f in seen for f in target if known[f]<=4)
    print('three-input optimal circuits checked',hits['min_circuits'],'distinct functions',len(seen),'seconds',round(perf_counter()-start,3))
    # Count local reader restrictions, not global exclusions, for sampled
    # four-input functions at plausible budgets 7,8,9.
    rng=Random(19);fs=[]
    while len(fs)<1000:
        f=rng.getrandbits(16)
        if essential(4,f):fs.append(f)
    for B in (7,8,9):
        count=Counter()
        for f in fs:
            C=caps(4,f,B,lower)
            count['targets']+=1
            count['degree_cap_lt_3']+=sum(d<3 for d,a,b in C)
            count['targets_any_conditional']+=any(a<d or b<d for d,a,b in C)
            count['conditional_strict']+=sum((a<d)+(b<d) for d,a,b in C)
        print('four-input sample',B,dict(count))
if __name__=='__main__':test()
