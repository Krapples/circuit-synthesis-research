"""Exact recognition of excess <= 1 after complete pair/canalizing reduction.
Supports monotone and free-NOT binary cost, not counted NOT.
Packed truth tables; formula leaves are ('x', i, sign), internal ('&'/'|',...).
Standard library + existing module_contraction and anchored_region prototypes.
"""
from functools import lru_cache
from time import perf_counter
from collections import Counter
from module_contraction import essential,raw_monotone,contract_pair,peel,cofactor1,brute,simplify,vars
from anchored_region import recognize,support


def project(n,f,inds):
    return sum((f>>sum((a>>j&1)<<i for j,i in enumerate(inds))&1)<<a for a in range(1<<len(inds)))


def remap(t,inds,neg):
    if isinstance(t,int):return ('x',inds[t],bool(neg>>t&1))
    return (t[0],*(remap(c,inds,neg) for c in t[1:]))


@lru_cache(None)
def tree(n,f,signed):
    """Canonical signed read-once tree on essential inputs, or None."""
    S=support(n,f);inds=tuple(i for i in range(n) if S>>i&1)
    if not inds:return None
    g=project(n,f,inds);m=len(inds);neg=0
    for i in range(m):
        d={((g>>(a|1<<i))&1)-((g>>a)&1) for a in range(1<<m) if not a>>i&1}-{0}
        if len(d)!=1:return None
        if d=={-1}:
            if not signed:return None
            neg|=1<<i
    h=sum((g>>(a^neg)&1)<<a for a in range(1<<m))
    t=recognize(m,h)
    return None if t is None else remap(t,inds,neg)


def ev(t,n):
    one=(1<<(1<<n))-1
    if isinstance(t,int):return one if t else 0
    if t[0]=='x':return vars(n)[t[1]]^(one if t[2] else 0)
    v=one if t[0]=='&' else 0
    for c in t[1:]:
        w=ev(c,n);v=(v&w) if t[0]=='&' else (v|w)
    return v


def leaves(t):
    if isinstance(t,int):return []
    if t[0]=='x':return [t[1]]
    return [i for c in t[1:] for i in leaves(c)]


def reindex(t,x):
    if t[0]=='x':return ('x',t[1]+int(t[1]>=x),t[2])
    return (t[0],*(reindex(c,x) for c in t[1:]))


def factors(t,op):
    a=list(t[1:]) if t[0]==op else [t]
    if len(a)>2:return None
    return a+[int(op=='&')]*(2-len(a))


def branch(n,x,a,b,signed):
    # a,b are trees of branch cofactors on the n-1 remaining inputs.
    g0,g1=ev(a,n-1),ev(b,n-1)
    if g0==g1:return None
    low=(1<<x)-1
    f=sum(((g1 if z>>x&1 else g0)>>((z&low)|((z>>(x+1))<<x))&1)<<z for z in range(1<<n))
    t=tree(n,f,signed)
    if t is None or x not in leaves(t):return None
    return t


def solve_core(n,f,signed=False,check_contract=True):
    """Return (binary cost, formula) if excess <=1, else None.
    Contract: essential complete target, no pair modules or canalizing peels.
    n=1 allowed. Formula has n+1 leaf occurrences for the excess-one case.
    """
    if check_contract:
        if not essential(n,f) or (not signed and not raw_monotone(n,f)) or (n>1 and (contract_pair(n,f,signed) is not None or peel(n,f,signed) is not None)):
            raise ValueError('requires fully reduced essential target')
    if n==1:return (0,('x',0,not bool(f&2)))
    for x in range(n):
        t0,t1=(tree(n-1,cofactor1(n,f,x,b),signed) for b in (0,1))
        if t0 is None or t1 is None:continue
        for op in ('&','|'):
            a,b=factors(t0,op),factors(t1,op)
            if a is None or b is None:continue
            for bb in (b,b[::-1]):
                # Branch private supports must be disjoint over BOTH slices.
                S=set(leaves(a[0])+leaves(bb[0]));T=set(leaves(a[1])+leaves(bb[1]))
                if not S or not T or S&T or len(S|T)!=n-1:continue
                u=branch(n,x,a[0],bb[0],signed);v=branch(n,x,a[1],bb[1],signed)
                if u is None or v is None:continue
                out=(op,u,v)
                assert ev(out,n)==f and len(leaves(out))==n+1
                return n,out
    return None


def check():
    t=perf_counter();counts=Counter()
    # Independent exhaustive gate-set search. All monotone n<=4 and all
    # essential signed n<=3; for signed n=4 compare all complete functions.
    # n=4 free budget 4 is tractable with the existing brute oracle.
    for signed in (False,True):
        for n in (3,4):
            known=brute(n,n,'free' if signed else 'mono')
            c=Counter()
            for f in range(1,(1<<(1<<n))-1):
                if not signed and not raw_monotone(n,f):continue
                if not essential(n,f):continue
                m,g,steps=simplify(n,f,signed)
                ans=solve_core(m,g,signed,False)
                yes=ans is not None and ans[0]+len(steps)<=n
                assert yes==(known.get(f,n+1)<=n),(signed,n,f,ans,steps,known.get(f))
                if not steps:
                    c['cores']+=1;c['yes']+=yes
                c['queries']+=1
            print('exhaustive',signed,n,dict(c),flush=True);counts.update(c)
    print('total',dict(counts),'seconds',perf_counter()-t,flush=True)



def star_candidates(n,f,signed=False):
    """All root-star formulas (one repeated input, one occurrence per branch).
    For a fully reduced core, any excess-one circuit is in this class.
    Factors on different slices are matched by common private variables.
    """
    for x in range(n):
        t0,t1=(tree(n-1,cofactor1(n,f,x,b),signed) for b in (0,1))
        if t0 is None or t1 is None:continue
        for op in ('&','|'):
            a=list(t0[1:]) if t0[0]==op else [t0]
            b=list(t1[1:]) if t1[0]==op else [t1]
            A=[set(leaves(t)) for t in a];B=[set(leaves(t)) for t in b]
            edges=[(i,j) for i,s in enumerate(A) for j,t in enumerate(B) if s&t]
            if len({i for i,j in edges})!=len(edges) or len({j for i,j in edges})!=len(edges):continue
            neutral=int(op=='&')
            pairs=[(a[i],b[j]) for i,j in edges]
            pairs.extend((t,neutral) for i,t in enumerate(a) if not any(i==u for u,v in edges))
            pairs.extend((neutral,t) for j,t in enumerate(b) if not any(j==v for u,v in edges))
            if len(pairs)<2:continue
            branches=[branch(n,x,u,v,signed) for u,v in pairs]
            if any(t is None for t in branches):continue
            out=(op,*branches);ls=leaves(out);k=len(branches)
            if len(ls)!=n-1+k or set(ls)!=set(range(n)):continue
            assert ev(out,n)==f
            yield n+k-2,out


def to_skeleton(n,t):
    gates=[]
    def go(t):
        if t[0]=='x':return t[1],int(t[2])
        op='AND' if t[0]=='&' else 'OR'
        l,a=go(t[1])
        for c in t[2:]:
            r,b=go(c)
            if l>r:l,r,a,b=r,l,b,a
            if l==r:raise ValueError('duplicate direct operands')
            gates.append((op,l,r,a,b));l=n+len(gates)-1;a=0
        return l,a
    out,p=go(t);assert out==n+len(gates)-1
    return gates,p


def counted_one(n,f):
    """Exact min NOT at binary budget n, for SIGNED-irreducible targets.
    No claim of exactness for the unrestricted total gate optimum.
    Returns (NOT cost, counted gates, output wire) or None.
    """
    from skeleton_not_opt import optimize,materialize
    if not essential(n,f) or (n>1 and (contract_pair(n,f,True) is not None or peel(n,f,True) is not None)):
        raise ValueError('requires signed irreducibility, not just raw irreducibility')
    if n==1:return (0,[],0) if f==2 else (1,[('NOT',0)],1)
    best=None
    for B,t in star_candidates(n,f,True):
        if B!=n:continue
        g,p=to_skeleton(n,t);u,ph=optimize(n,g,p)
        if best is None or u<best[0]:
            raw,out=materialize(n,g,p,ph);best=(u,raw,out)
    return best


def check_extensions():
    from phase_budget_cnf import reference,evaluate
    from random import Random
    from irreducible_region_fpt import Irreducible
    from module_contraction import vars
    t=perf_counter();c=Counter()
    for n,umax in ((3,3),(4,2)):
        refs=[reference(n,n,u) for u in range(umax+1)]
        # Only signed irreducible cores reachable with n binary gates need
        # expensive polarity optimization; all other cores cannot be SAT.
        for f in range(1,(1<<(1<<n))-1):
            if not essential(n,f) or contract_pair(n,f,True) is not None or peel(n,f,True) is not None:continue
            ans=counted_one(n,f)
            if ans:
                assert evaluate(n,ans[1],ans[2])==f
                c['witnesses']+=1
            for u,r in enumerate(refs):
                assert bool(ans is not None and ans[0]<=u)==(f in r),(n,f,u,ans)
                c['typed_queries']+=1
        print('counted through',n,dict(c),'seconds',round(perf_counter()-t,3),flush=True)
    # Generate root-star functions; after reduction, compare candidate costs
    # against known construction where the original is already irreducible.
    rng=Random(7314);cases=[];stars=Counter()
    for i in range(500):
        n=rng.randrange(4,10);k=rng.randrange(2,min(n-1,4)+1);signed=bool(i%2)
        order=list(range(n));rng.shuffle(order);x=order.pop();groups=[[v] for v in order[:k]]
        for v in order[k:]:rng.choice(groups).append(v)
        op=rng.choice('&|');children=[]
        for group in groups:
            t0=('x',x,signed and bool(rng.randrange(2)))
            for j,v in enumerate(group[::-1]):
                op1=op if (len(group)-j)%2==0 else ('|' if op=='&' else '&')
                t0=(op1,('x',v,signed and bool(rng.randrange(2))),t0)
            children.append(t0)
        f=ev((op,*children),n)
        if not essential(n,f) or contract_pair(n,f,signed) is not None or peel(n,f,signed) is not None:continue
        cand=list(star_candidates(n,f,signed));assert cand and min(z[0] for z in cand)<=n+k-2,(n,k,f)
        stars['cases']+=1;stars['signed']+=signed;stars['more_than_two_branches']+=k>2
        if k==2 and not signed and n<=7:cases.append((n,f))
    print('generated star',dict(stars),flush=True)
    # Matched timing for irreducible monotone cores at sharing one.
    # Include known satisfiable star functions and random irreducible tables.
    cases=list(dict.fromkeys(cases))[:20]
    for _ in range(100):
        n=rng.randrange(5,8);terms=[rng.randrange(1,1<<n) for _ in range(rng.randrange(3,2*n))]
        f=sum(any(a&z==z for z in terms)<<a for a in range(1<<n))
        if essential(n,f) and contract_pair(n,f) is None and peel(n,f) is None:cases.append((n,f))
        if len(cases)>=40:break
    cases=list(dict.fromkeys(cases));t=perf_counter();res=[Irreducible(n).solve(f,1) for n,f in cases];base=perf_counter()-t
    t=perf_counter();actual=[solve_core(n,f,False,False) is not None for n,f in cases];new=perf_counter()-t
    assert res==actual
    print('matched monotone',len(cases),'SAT',sum(res),'baseline seconds',round(base,4),'recognizer seconds',round(new,4),flush=True)


def certified_total(n,f):
    """Certified total optimum if the one-sharing witness meets the gap test.
    Otherwise return None (not an exclusion). Requires signed irreducibility.
    """
    from partial_inversion import inversion
    z=counted_one(n,f)
    if z is None:return None
    u,g,out=z
    if n==1:return u,g,out
    I=inversion([(a,(f>>a)&1) for a in range(1<<n)])
    return (n+u,g,out) if u<=I+1 else None

if __name__=='__main__':
    import sys
    check()
    if '--extended' in sys.argv:check_extensions()
