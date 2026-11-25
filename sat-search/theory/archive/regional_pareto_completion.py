"""Target-directed bottom-up Pareto DP for regional formula completion.
Exact all-leaf monotone/free-NOT, including repeated ports. Exponential in
leaf multiset and row width. Intended as a small, bounded portfolio backend.
No counted NOT. ResourceLimit means UNKNOWN, never UNSAT.
"""
from collections import Counter
from itertools import product
from functools import lru_cache
from time import perf_counter
from two_sharing_core import ANY,vars

class ResourceLimit(Exception):pass

def local_pareto(m,ports,pats,targets,signed,stats=None,module_filter=True,*,max_pairs=200000,max_columns=3000):
    if stats is None:stats=Counter()
    stats['local']+=1
    # Only labeled rows. Leaves of identical columns are interchangeable;
    # signed complementary columns could also be merged but are not here.
    rows=[(a,p,t>>a&1) for p,t in zip(pats,targets) if t!=ANY for a in range(1<<m)]
    U=(1<<len(rows))-1;P=sum(1<<i for i,(_,_,v) in enumerate(rows) if v);N=U^P
    ids=tuple(sorted(set(ports)));leaves=tuple(range(m))+tuple(m+i for i in ids)
    mult=(1,)*m+tuple(ports.count(i) for i in ids)
    cs=tuple(sum(1<<j for j,(a,p,t) in enumerate(rows) if ((a>>i)&1 if i<m else (p>>(i-m))&1)) for i in leaves)
    def agree(x):return U^(x^P)
    # Internally every value is the mask of correctly classified rows.
    # For AND, agreements intersect on positives and unite on negatives;
    # OR is the dual. Both operations are monotone in agreement masks.
    def and_(a,b):return ((a&b)&P)|((a|b)&N)
    def or_(a,b):return ((a|b)&P)|((a&b)&N)
    def maximal(d):
        out={}
        # All proper supersets precede their subsets. An inverted index
        # over retained masks finds a superset by intersecting candidate IDs.
        index=[0]*len(rows);k=0
        for a in sorted(d,key=int.bit_count,reverse=True):
            if not k:possible=0
            else:
                possible=(1<<k)-1;b=a
                while b and possible:
                    bit=b&-b;b^=bit;possible &= index[bit.bit_length()-1]
            if possible:continue
            out[a]=d[a];b=a
            while b:
                bit=b&-b;b^=bit;index[bit.bit_length()-1]|=1<<k
            k+=1
            if k>max_columns:raise ResourceLimit('Pareto frontier cap')
        return out
    @lru_cache(None)
    def rec(M):
        stats['rec']+=1
        if sum(M)==1:
            i=M.index(1);d={agree(cs[i]):('x',leaves[i],False)}
            if signed:d[agree(U^cs[i])]=('x',leaves[i],True)
            return maximal(d)
        d={}
        for A in product(*(range(x+1) for x in M)):
            B=tuple(x-y for x,y in zip(M,A))
            if not any(A) or not any(B) or A>B:continue
            a=rec(A);b=rec(B)
            for x,tx in a.items():
                for y,ty in b.items():
                    stats['pairs']+=1
                    if stats['pairs']>max_pairs:raise ResourceLimit('pair cap')
                    for op,z in (('&',and_(x,y)),('|',or_(x,y))):
                        if z==U and M==mult:return {z:(op,tx,ty)}
                        if z not in d:d[z]=(op,tx,ty)
            # Early Pareto pruning at each split, valid across later splits.
            if len(d)>max_columns*2:d=maximal(d)
        return maximal(d)
    try:return rec(mult).get(U) if sum(mult) else None
    finally:rec.cache_clear()

def checks():
    import regional_obligation_cache as cm
    old=cm.local;cm.local=local_pareto
    try:cm.checks()
    finally:cm.local=old
if __name__=='__main__':checks()
