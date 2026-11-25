"""Exact functional module contraction for complete Boolean tables.
Bit a of f is f(a); all inputs must be essential, target nonconstant.
Standard library; run this file for bounded independent gate-set checks.
Raw AND/OR contraction preserves binary AND/OR cost and counted total cost.
Signed AND/OR contraction preserves binary cost when NOT is free.
"""
from functools import lru_cache
from itertools import combinations, product
from collections import Counter
from time import perf_counter

@lru_cache(None)
def vars(n):
    return tuple(sum(1<<a for a in range(1<<n) if a>>i&1) for i in range(n))

def essential(n,f):
    return all(any((f>>a&1)!=(f>>(a|1<<i)&1) for a in range(1<<n) if not a>>i&1) for i in range(n))

def validate(n,f):
    if n<1 or f<0 or f.bit_length()>1<<n or not essential(n,f):
        raise ValueError('nonconstant complete truth table with essential inputs required')

@lru_cache(None)
def pair_indices(n,i,j):
    other=[k for k in range(n) if k not in (i,j)]
    base=tuple(sum((a>>l&1)<<k for l,k in enumerate(other)) for a in range(1<<(n-2)))
    return tuple(tuple(a|((p&1)<<i)|((p>>1)<<j) for a in base) for p in range(4))

def pair_cof(n,f,i,j):
    return tuple(sum((f>>a&1)<<b for b,a in enumerate(row)) for row in pair_indices(n,i,j))

@lru_cache(None)
def contract_pair(n,f,signed=False):
    """Return (i,j,exceptional pattern, reduced f), or None.
    New variable is 1 exactly on exceptional pair pattern; last coordinate.
    For raw OR, invert the new variable so it equals x_i OR x_j.
    """
    for i,j in combinations(range(n),2):
        c=pair_cof(n,f,i,j)
        if len(set(c))!=2:continue
        for p in ((0,1,2,3) if signed else (0,3)):
            o=[c[k] for k in range(4) if k!=p]
            if o[0]==o[1]==o[2] and c[p]!=o[0]:
                lo,hi=o[0],c[p]
                if p==0:lo,hi=hi,lo # raw OR instead of NOR
                return i,j,p,lo|(hi<<(1<<(n-2)))
    return None

def reduce(n,f,signed=False):
    validate(n,f);steps=[]
    while n>1:
        step=contract_pair(n,f,signed)
        if step is None:break
        steps.append(step[:3]);n-=1;f=step[3]
        assert essential(n,f)
    return n,f,steps

def lift(n,g,step):
    """Given n original inputs, expand g on n-1, new module variable last."""
    i,j,p=step;other=[k for k in range(n) if k not in (i,j)]
    f=0
    for a in range(1<<n):
        v=(a>>i&1)|((a>>j&1)<<1)
        h=int(v==p) if p else int(v!=p)
        z=sum((a>>k&1)<<l for l,k in enumerate(other))|(h<<(n-2))
        f|=(g>>z&1)<<a
    return f

@lru_cache(None)
def cofactor1(n,f,i,v):
    low=(1<<i)-1
    return sum((f>>((a&low)|((a&~low)<<1)|(v<<i))&1)<<a for a in range(1<<(n-1)))

def peel(n,f,signed=False):
    """Return (i, retained assignment, absorbing output, reduced table)."""
    one=(1<<(1<<(n-1)))-1
    for i in range(n):
        a,b=(cofactor1(n,f,i,v) for v in (0,1))
        for v,c,g in ((0,b,a),(1,a,b)):
            if c not in (0,one) or g in (0,one):continue
            if signed or (v==1 and c==0) or (v==0 and c==one):
                return i,v,int(c==one),g
    return None

def simplify(n,f,signed=False):
    """Exact at-most reduction, with a reconstruction trace in old coordinates.
    signed=True is only for free-NOT binary cost.
    """
    validate(n,f);trace=[]
    while n>1:
        p=contract_pair(n,f,signed)
        if p is not None:
            trace.append(('pair',*p[:3]));f=p[3]
        else:
            p=peel(n,f,signed)
            if p is None:break
            trace.append(('peel',*p[:3]));f=p[3]
        n-=1;assert essential(n,f)
    return n,f,trace

def expand(n,g,step):
    if step[0]=='pair':return lift(n,g,step[1:])
    _,i,v,c=step;low=(1<<i)-1
    return sum((g>>((a&low)|((a>>(i+1))<<i))&1 if (a>>i&1)==v else c)<<a for a in range(1<<n))


def flip(n,f,i):
    return sum((f>>(a^(1<<i))&1)<<a for a in range(1<<n))

def raw_monotone(n,f):
    return all((f>>a&1)<=(f>>(a|1<<i)&1) for i in range(n) for a in range(1<<n) if not a>>i&1)

def brute(n,b,basis):
    """Independent enumeration of attainable sets; no contraction or pruning."""
    one=(1<<(1<<n))-1
    if basis=='free':
        canon=lambda x:min(x,one^x)
        V=frozenset(map(canon,vars(n)))
    else: V=frozenset(vars(n))
    states={V};known={v:0 for v in V}
    for k in range(1,b+1):
        nxt=set()
        for st in states:
            vs=tuple(st);out=set()
            if basis=='counted':out.update(v^one for v in vs)
            for a,c in combinations(vs,2):
                if basis=='free':
                    out.update(canon(x&y) for x in (a,a^one) for y in (c,c^one))
                else:out.update((a&c,a|c))
            for z in out-st:
                known.setdefault(z,k)
                if k<b:nxt.add(st|{z})
        states=nxt
    if basis=='free':known.update({k^one:v for k,v in tuple(known.items())})
    return known

def test():
    t=perf_counter();totals=Counter()
    for basis in ('mono','counted','free'):
        signed=basis=='free'; budgets={1:1,2:4,3:4,4:4}
        if basis=='mono':budgets[4]=5
        tables={n:brute(n,b,basis) for n,b in budgets.items()}
        checks=0;yes=0
        for n in (2,3,4):
            # Every function within the known gate budget, and every lifted
            # reduced function whose +1 budget fits the known bound.
            fs=set(tables[n])
            for g,c in tables[n-1].items():
                if c+1>budgets[n] or not essential(n-1,g):continue
                for i,j in combinations(range(n),2):
                    for p in ((0,1,2,3) if signed else (0,3)):
                        fs.add(lift(n,g,(i,j,p)))
            for g,c in tables[n-1].items():
                if c+1>budgets[n] or not essential(n-1,g):continue
                for i in range(n):
                    for v,absorb in ((0,1),(1,0),(0,0),(1,1)) if signed else ((0,1),(1,0)):
                        fs.add(expand(n,g,('peel',i,v,absorb)))
            for f in fs:
                if not essential(n,f):continue
                if basis=='mono' and not raw_monotone(n,f):continue
                m,h,trace=simplify(n,f,signed)
                a=h
                for k,st2 in enumerate(reversed(trace),m+1):a=expand(k,a,st2)
                assert a==f
                if trace:
                    for b in range(len(trace),budgets[n]+1):
                        assert (tables[n].get(f,100)<=b)==(tables[m].get(h,100)<=b-len(trace)),(basis,n,f,b,m,h,trace)
                        totals['combined']+=1
                st=contract_pair(n,f,signed)
                if st is None:continue
                i,j,p,g=st;assert lift(n,g,(i,j,p))==f
                cf=tables[n].get(f,100);cg=tables[n-1].get(g,100)
                for b in range(1,budgets[n]+1):
                    # n-1 table supports budget b-1 in every comparison.
                    assert (cf<=b)==(cg<=b-1),(basis,n,f,b,cf,cg,st)
                    checks+=1;yes+=cf<=b
            print('oracle',basis,n,'known',len(tables[n]),'queries cumulative',checks,flush=True)
        totals[basis]=checks
    # Mixed-sign two-input module: counted bounds differ by at most one.
    tables={n:brute(n,4,'counted') for n in (1,2,3)}
    mixed=Counter()
    for n in (2,3):
        for f,cf in tables[n].items():
            if not essential(n,f):continue
            for i,j in combinations(range(n),2):
                c=pair_cof(n,f,i,j)
                for p in (1,2):
                    o=[c[k] for k in range(4) if k!=p]
                    if not(o[0]==o[1]==o[2]!=c[p]):continue
                    g=o[0]|(c[p]<<(1<<(n-2)));h=flip(n-1,g,n-2)
                    a=tables[n-1].get(g,100);b=tables[n-1].get(h,100)
                    assert 1+max(a,b)<=cf<=2+min(a,b),(n,f,p,cf,a,b)
                    mixed['checked']+=1;mixed['exact_by_polarity_gap']+=a!=b
    print('mixed',dict(mixed),flush=True)
    for n in (3,4):
        stats=Counter()
        for f in range(1,1<<(1<<n)):
            if not essential(n,f):continue
            stats['all']+=1
            a=reduce(n,f);b=reduce(n,f,True)
            stats['raw_reducible']+=bool(a[2]);stats['signed_reducible']+=bool(b[2]);stats['raw_full']+=a[0]==1;stats['signed_full']+=b[0]==1
            c=simplify(n,f);d=simplify(n,f,True)
            stats['raw_combined']+=bool(c[2]);stats['signed_combined']+=bool(d[2]);stats['raw_core_removed']+=len(c[2]);stats['signed_core_removed']+=len(d[2])
            if raw_monotone(n,f):
                stats['monotone']+=1;stats['mono_reducible']+=bool(a[2]);stats['mono_full']+=a[0]==1;stats['mono_combined']+=bool(c[2])
        print('complete distribution',n,dict(stats),flush=True)
    print('total',dict(totals),'seconds',perf_counter()-t,flush=True)

if __name__=='__main__':test()
