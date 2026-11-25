"""Free-NOT binary-gate lower bound via first gate and restrictions.
Nonconstant complete truth tables; unused inputs are projected away.
Standard library; optional signed_region_bounds and module_contraction for tests.
"""
from functools import lru_cache
from itertools import combinations
from random import Random
from collections import Counter
from time import perf_counter
from module_contraction import cofactor1, pair_cof, vars, brute

@lru_cache(None)
def support(n,f):
    return tuple(i for i in range(n) if cofactor1(n,f,i,0)!=cofactor1(n,f,i,1))

@lru_cache(None)
def trim(n,f):
    for i in reversed(range(n)):
        if cofactor1(n,f,i,0)==cofactor1(n,f,i,1):
            f=cofactor1(n,f,i,0);n-=1
    return n,min(f,((1<<(1<<n))-1)^f)

@lru_cache(None)
def identify(n,f,i,j,parity):
    """Set x_j=x_i XOR parity, retaining x_i; compact table."""
    low=(1<<j)-1
    return sum(((f>>((a&low)|((a&~low)<<1)|(((a>>i&1)^parity)<<j)))&1)<<a for a in range(1<<(n-1)))

def lower(n,f,mode=2):
    return _lower(*trim(n,f),mode)

@lru_cache(None)
def _lower(n,f,mode):
    if n<=1:return 0
    if n==2:return 3 if f in (6,9) else 1
    c=[[cofactor1(n,f,i,b) for b in (0,1)] for i in range(n)]
    t=[[lower(n-1,g,mode) for g in pair] for pair in c]
    mask=(1<<(1<<(n-1)))-1
    nonconst=[all(g not in (0,mask) for g in pair) for pair in c]
    L=max(n-1,max(max(v)+1 for v in t))
    # Restrict further semantically irrelevant inputs. Cycle rank cannot
    # increase under constant propagation; a nonconstant restriction with
    # m essential inputs costs at least n-m fewer binary gates.
    L=max(L,max(t[i][b]+n-max(1,len(support(n-1,c[i][b])))
                for i in range(n) for b in (0,1)))
    for i in range(n):
        if nonconst[i]:L=max(L,min(t[i])+2)
        if c[i][0]^c[i][1]==mask:
            L=max(L,min(t[i])+3)
    if mode==3:
        from signed_region_bounds import Bound
        L=max(L,n-1+Bound(n,f).lower())
    if mode==0:return L
    first=10**9
    for i,j in combinations(range(n),2):
        # if either variable is essential after fixing the other, its
        # first reader cannot be its only reader when that gate is fixed.
        j_survives=[j-1 in support(n-1,g) for g in c[i]]
        i_survives=[i in support(n-1,g) for g in c[j]]
        eq=[lower(n-1,identify(n,f,i,j,p),mode) for p in (0,1)] if mode==2 else [0,0]
        for a in (0,1): # absorbing value of x_i in first gate
            for b in (0,1):
                v=max(L,t[i][a]+2,t[j][b]+2)
                if j_survives[a]:
                    v=max(v,max(t[j])+2)
                    if nonconst[j]:v=max(v,min(t[j])+3)
                if i_survives[b]:
                    v=max(v,max(t[i])+2)
                    if nonconst[i]:v=max(v,min(t[i])+3)
                if mode==2:
                    v=max(v,eq[a^b]+1,eq[1^a^b]+2)
                first=min(first,v)
    return first

def test():
    from signed_region_bounds import Bound
    start=perf_counter();r=Random(1947)
    for n,budget in ((2,3),(3,5),(4,4)):
        known=brute(n,budget,'free');k=0;exact=Counter()
        for f,c in known.items():
            if len(support(n,f))!=n:continue
            a,b,d=[lower(n,f,m) for m in (0,1,2)]
            assert a<=b<=d<=c,(n,f,c,a,b,d)
            k+=1;exact.update({'base':a==c,'first':b==c,'ident':d==c})
        print('exact',n,budget,k,dict(exact),flush=True)
    for n,fs in ((3,range(256)),(4,[r.getrandbits(16) for _ in range(1200)]),(5,[r.getrandbits(32) for _ in range(300)])):
        ct=Counter();examples=[]
        for f in fs:
            if len(support(n,f))!=n:continue
            a,b,c=[lower(n,f,m) for m in (0,1,2)]
            d=n-1+Bound(n,f).lower()
            ct.update({'cases':1,'first_gain':b>a,'ident_gain':c>b,'beats_regional':c>d,'regional_beats':d>c})
            if c>d and len(examples)<3:examples.append((f,a,b,c,d))
        print('sample',n,dict(ct),examples,flush=True)
    ct=Counter()
    for _ in range(2500):
        n=r.randrange(2,7);V=list(vars(n));full=(1<<(1<<n))-1
        b=r.randrange(n-1,n+10)
        for j in range(b):
            x,y=r.sample(V,2)
            if r.randrange(2):x^=full
            if r.randrange(2):y^=full
            V.append(x&y)
        f=V[-1]
        if len(support(n,f))!=n:continue
        assert lower(n,f)<=b,(n,f,b,lower(n,f));ct['circuits']+=1
    print('generated',dict(ct),'seconds',perf_counter()-start,flush=True)

@lru_cache(None)
def mono_lower(n,f):
    """Monotone-only specialization. Requires a monotone truth table."""
    for i in reversed(range(n)):
        if cofactor1(n,f,i,0)==cofactor1(n,f,i,1):
            f=cofactor1(n,f,i,0);n-=1
    if n<=2:return max(0,n-1)
    c=[[cofactor1(n,f,i,b) for b in (0,1)] for i in range(n)]
    t=[[mono_lower(n-1,g) for g in pair] for pair in c]
    mask=(1<<(1<<(n-1)))-1
    nonconst=[all(g not in (0,mask) for g in pair) for pair in c]
    L=max(n-1,max(t[i][b]+n-max(1,len(support(n-1,c[i][b])))
                for i in range(n) for b in (0,1)))
    for i in range(n):
        if nonconst[i]:L=max(L,min(t[i])+2)
    first=10**9
    for i,j in combinations(range(n),2):
        for a in (0,1): # AND or OR have same absorbing value at both inputs.
            v=max(L,t[i][a]+2,t[j][a]+2)
            if j-1 in support(n-1,c[i][a]):
                v=max(v,max(t[j])+2)
                if nonconst[j]:v=max(v,min(t[j])+3)
            if i in support(n-1,c[j][a]):
                v=max(v,max(t[i])+2)
                if nonconst[i]:v=max(v,min(t[i])+3)
            first=min(first,v)
    return first


def test_extensions():
    from signed_region_bounds import Bound
    r=Random(455)
    for n,fs in ((3,range(256)),(4,[r.getrandbits(16) for _ in range(500)]),(5,[r.getrandbits(32) for _ in range(100)])):
        ct=Counter()
        for f in fs:
            if len(support(n,f))!=n:continue
            a=lower(n,f,1);b=n-1+Bound(n,f).lower();c=lower(n,f,3)
            assert c>=max(a,b)
            ct.update({'cases':1,'gain_over_max':c>max(a,b),'gain_over_regional':c>b})
        print('hybrid',n,dict(ct),flush=True)
    for n,b in ((3,5),(4,6),(5,5)):
        ct=Counter()
        for f,v in brute(n,b,'mono').items():
            if len(support(n,f))!=n:continue
            a=lower(n,f,1);c=mono_lower(n,f)
            assert a<=c<=v
            ct.update({'cases':1,'mono_gain':c>a,'exact':c==v})
        print('mono exact',n,dict(ct),flush=True)

if __name__=='__main__':
    test()
    test_extensions()
