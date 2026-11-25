"""Exact neutral-slice contraction for mixed listed labels.
Labels are sets of integer assignment masks. Only raw AND/OR modules.
No assumption that every listed input is essential. Standard library.
See module_contraction.py for independent gate-set enumeration.
"""
from itertools import product,permutations
from collections import Counter
from math import inf
from time import perf_counter
from module_contraction import brute

def drop(a,i):
    low=(1<<i)-1
    return (a&low)|((a>>(i+1))<<i)

def mapped(a,i,j,AND):
    x=bool(a>>i&1);y=bool(a>>j&1)
    h=int(x and y) if AND else int(x or y)
    return drop((a&~(1<<j))|(h<<j),i)

def contract(P,N,i,j,AND):
    """Return reduced and ignored-input labels if safe neutral-slice rule applies."""
    if not P or not N or i==j:return None
    Q={mapped(a,i,j,AND) for a in P};R={mapped(a,i,j,AND) for a in N}
    if Q&R:return None
    v=int(AND)
    # Every mapped label must have an original representative in the neutral slice.
    if Q!={drop(a,i) for a in P if (a>>i&1)==v}:return None
    if R!={drop(a,i) for a in N if (a>>i&1)==v}:return None
    return Q,R,{drop(a,i) for a in P},{drop(a,i) for a in N}

def mandatory(P,N,i,monotone=False):
    if monotone:return any(a&~b==1<<i for a in P for b in N)
    return any(a^b==1<<i for a in P for b in N)

def opt(known,P,N):
    p=sum(1<<a for a in P);n=sum(1<<a for a in N)
    return min((b for f,b in known.items() if f&p==p and not f&n),default=inf)

def check():
    t=perf_counter()
    for basis in ('mono','counted'):
        # Full oracle on 2-variable functions for counted up to 4 (all 16).
        T2=brute(2,4,basis);T3=brute(3,4,basis);stats=Counter()
        for labels in product((-1,0,1),repeat=8):
            P={i for i,v in enumerate(labels) if v==1};N={i for i,v in enumerate(labels) if v==0}
            if not P or not N:continue
            cf=None;seen=False
            for i,j in permutations(range(3),2):
                for AND in (False,True):
                    z=contract(P,N,i,j,AND)
                    if z is None:continue
                    if cf is None:cf=opt(T3,P,N)
                    Q,R,A,B=z;cg=opt(T2,Q,R);cd=opt(T2,A,B)
                    pred=min(cg+1,cd)
                    for b in range(5):assert (pred<=b)==(cf<=b),(basis,P,N,i,j,AND,cf,cg,cd,b)
                    stats['rule_queries']+=1;stats['mandatory_queries']+=mandatory(P,N,i,basis=='mono')
                    stats['strict_ignore_wins']+=cd<cg+1
                    if mandatory(P,N,i,basis=='mono'):
                        assert cd==inf
                        for b in range(5):assert (cg+1<=b)==(cf<=b)
                    seen=True
            stats['label_tables']+=seen
        print(basis,dict(stats),flush=True)
    print('seconds',perf_counter()-t,flush=True)
if __name__=='__main__':check()
