"""Independent oracle for unbounded-control signed regional compatibility.
The oracle enumerates signed read-once formulas, then all their restrictions.
Needs signed_region_bounds.py in the same directory.
"""
from functools import lru_cache
from collections import defaultdict,Counter
from random import Random
from signed_region_bounds import Bound,subs

@lru_cache(None)
def oracle(k,allow_complement=True):
    full=(1<<k)-1;one=(1<<(1<<k))-1
    v=[sum(1<<a for a in range(1<<k) if a>>i&1) for i in range(k)]
    @lru_cache(None)
    def gen(S):
        if S.bit_count()==1:
            a=v[S.bit_length()-1];return {a,a^one}
        out=set()
        for A in subs(S):
            if A in (0,S) or not A&S&-S:continue
            for a in gen(A):
                for b in gen(S^A):out.update((a&b,a|b))
        return out
    fs=sorted(gen(full));possible=defaultdict(int)
    for i,f in enumerate(fs):
        possible[0]|=1<<i;possible[one]|=1<<i
        for S in subs(full):
            for a in subs(S):
                g=sum((f>>((b&~S)|a)&1)<<b for b in range(1<<k))
                possible[g]|=1<<i
                if allow_complement:possible[g^one]|=1<<i
    return (1<<len(fs))-1,possible,len(fs)

def brute_compatible(b,S,output=False):
    pos=[i for i in range(b.n) if S>>i&1];k=len(pos)
    if not k:return True
    assignments=[sum((a>>j&1)<<i for j,i in enumerate(pos)) for a in range(1<<k)]
    alive,possible,_=oracle(k,not output)
    for a in subs(b.full^S):
        f=sum(b.values[a|c]<<i for i,c in enumerate(assignments))
        alive&=possible.get(f,0)
        if not alive:return False
    return True

def check(seed=20261124):
    rng=Random(seed)
    for k in range(1,5):print('oracle',k,oracle(k)[2],flush=True)
    for n,fs in [(3,range(256)),(4,range(65536)),(5,[rng.getrandbits(32) for _ in range(1000)])]:
        c=Counter()
        for f in fs:
            try:b=Bound(n,f)
            except ValueError:continue
            c['functions']+=1
            for S in subs(b.full):
                if not 2<=S.bit_count()<=4:continue
                for out in (False,True):
                    want=brute_compatible(b,S,out);got=b.compatible(S,out)
                    assert got==want,(n,f,S,out,got,want)
                    c['queries']+=1;c['compatible']+=want
        print(n,dict(c),flush=True)

if __name__=='__main__':check()
