"""Exact complete-table recognition for binary circuits with at most one shared
internal wire, any number of repeated primary occurrences. Monotone or free-NOT.
A negative result excludes only this circuit class (not arbitrary excess >=3).
Dependencies: module_contraction, one_sharing_core, two_sharing_core.
Run this file for independent small fixed-layout and generated-circuit checks.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
from random import Random
from time import perf_counter
from module_contraction import essential, raw_monotone, vars, simplify, brute
from one_sharing_core import tree, ev
from two_sharing_core import assignments, slices, local, map_tree

ANY=-1

def subsets(V):
    for k in range(len(V)+1):yield from combinations(V,k)

def compositions(total,k):
    if k==0:
        if total==0:yield ()
    else:
        for x in range(total+1):
            for t in compositions(total-x,k-1):yield (x,)+t

def make_cofactors(f,R,S,Z):
    return tuple(slices(f,S,Z,r) for r in assignments(R))

@lru_cache(None)
def options(table,m,signed):
    """A triple: provider slice, decoder slice for h=0, decoder slice for h=1."""
    kinds=sorted(set(table));one=(1<<(1<<m))-1
    if len(kinds)>2:return ()
    if len(kinds)==1:
        a=kinds[0]
        # ANY with decoder independent of h safely covers all provider ranges.
        return ((ANY,a,a),(0,a,ANY),(one,ANY,a)) if m else ((0,a,ANY),(one,ANY,a))
    lo,hi=kinds
    h=sum((t==hi)<<a for a,t in enumerate(table))
    if tree(m,h,signed) is None:return ()
    if signed:return ((h,lo,hi),(h^one,hi,lo))
    return ((h,lo,hi),) if lo&hi==lo else ()

def consistent_monotone(a,b):
    # a <= b must hold pointwise for specified provider slices.
    return a==ANY or b==ANY or a&~b==0

def signs(m,h):
    if h==ANY:return {}
    out={}
    for i in range(m):
        ds={((h>>(a|1<<i))&1)-((h>>a)&1) for a in range(1<<m) if not a>>i&1}-{0}
        if len(ds)>1:return None
        if ds:out[i]=next(iter(ds))
    return out

def fixed(f,R,S,Z,din,dout,dH,signed=False,stats=None,prune=True,*,completion=local):
    """Exact for a specified layout. R shared primaries; S provider-private;
    Z output-private. din,dout give occurrence counts per R in each region.
    dH is the number of occurrences of the one shared internal provider.
    Returns two read-once trees, with local port indices, or None.
    """
    assert len(R)==len(din)==len(dout) and dH>=2
    if len(S)+sum(din)<2:return None
    if stats is None:stats=Counter()
    stats['layouts']+=1
    P=tuple(range(1<<len(R)));data=make_cofactors(f,R,S,Z)
    opts=tuple(options(t,len(S),signed) for t in data)
    if any(not a for a in opts):stats['cofactor_reject']+=1;return None
    pin=tuple(i for i,d in enumerate(din) for _ in range(d))
    pout=tuple(i for i,d in enumerate(dout) for _ in range(d))+(len(R),)*dH
    # If a provider ignores a port, its exact slices on those assignments must agree.
    # If the decoder ignores a shared primary, its exact slices for identical observed
    # port patterns must agree. These cheap projections avoid redundant local queries.
    pmask=sum(1<<i for i,d in enumerate(din) if d)
    dmask=sum(1<<i for i,d in enumerate(dout) if d)
    # Visible slices first, then hidden. Use consistent literal signs and monotone order.
    order=sorted(P,key=lambda p: (len(set(data[p]))<2,p))
    choose={};hs={};gs={};pol={}
    @lru_cache(None)
    def check_local(side,pats,ts):
        stats['local_'+side]+=1
        return completion(len(S) if side=='h' else len(Z),pin if side=='h' else pout,pats,ts,signed)
    def rec(i):
        if i==len(order):
            stats['profiles']+=1
            hp=tuple(sorted(hs));gp=tuple(sorted(gs))
            h=check_local('h',hp or (0,),tuple(hs[p] for p in hp) if hp else (ANY,))
            if h is None:return None
            g=check_local('g',gp,tuple(gs[p] for p in gp))
            return None if g is None else (h,g)
        p=order[i];pk=p&pmask
        for h,a,b in opts[p]:
            if prune:
                if pk in hs and h!=ANY and hs[pk]!=h:stats['projection_reject']+=1;continue
                if not signed and any((q&p==q and not consistent_monotone(v,h)) or (p&q==p and not consistent_monotone(h,v)) for q,v in choose.items()):
                    stats['order_reject']+=1;continue
                si=signs(len(S),h)
                if si is None or any(j in pol and pol[j]!=v for j,v in si.items()):stats['sign_reject']+=1;continue
            else:si={}
            # Projection and consistency are required for correctness, even if
            # extra pruning is disabled. A map stores only exact constraints.
            if pk in hs and h!=ANY and hs[pk]!=h:continue
            gpairs=[((p&dmask)|(v<<len(R)),t) for v,t in enumerate((a,b)) if t!=ANY]
            if any(k in gs and gs[k]!=t for k,t in gpairs):stats['decoder_reject']+=1;continue
            nh=pk not in hs and h!=ANY
            if nh:hs[pk]=h
            ng=[k for k,t in gpairs if k not in gs]
            for k,t in gpairs:gs[k]=t
            np=[k for k in si if k not in pol];pol.update(si);choose[p]=h
            w=rec(i+1)
            if w is not None:return w
            choose.pop(p)
            if nh:hs.pop(pk)
            for k in ng:gs.pop(k)
            for k in np:pol.pop(k)
        return None
    return rec(0)

def solve(n,f,e,signed=False,stats=None,min_excess=1,reduced_filter=False,*,completion=local):
    """Find a witness with <=e excess within the at-most-one-internal-share class."""
    if n<1 or not essential(n,f) or (not signed and not raw_monotone(n,f)):
        raise ValueError('requires essential complete target in selected basis')
    if stats is None:stats=Counter()
    V=tuple(range(n));t=tree(n,f,signed)
    if t is not None:return ('primary',(),V,t)
    # Optional structural restrictions on repeated-primary choices. The first
    # gate condition requires a fully reduced core. Restriction excess itself
    # is valid for arbitrary essential targets.
    if reduced_filter:
        from restriction_excess import lower, first_gate_candidates
        req=first_gate_candidates(n,f,e,signed)
        if not req:return None
        @lru_cache(None)
        def rest_lower(R):
            W=tuple(i for i in V if i not in R)
            return max(lower(len(W),t,signed) for t in slices(f,R,W))
        def allowed(R,d,s):
            if not any(set(t[-1])<=set(R) for t in req):return False
            if sum(x-1 for x in d)+rest_lower(R)>s:return False
            return all(x-1+rest_lower((i,))<=s for i,x in zip(R,d))
    else:
        def allowed(R,d,s):return True
    # No internally repeated wire: duplicate primary leaves only.
    for s in range(min_excess,e+1):
        for r in range(1,min(s,n)+1):
            for R in combinations(V,r):
                Z=tuple(i for i in V if i not in R);ts=slices(f,R,Z);pats=tuple(range(1<<r))
                if any(t not in (0,(1<<(1<<len(Z)))-1) and tree(len(Z),t,signed) is None for t in ts):continue
                for c in compositions(s-r,r):
                    if not allowed(R,tuple(d+2 for d in c),s):stats['restriction_reject']+=1;continue
                    ports=tuple(i for i,d in enumerate(c) for _ in range(d+2))
                    stats['primary_local']+=1
                    w=completion(len(Z),ports,pats,ts,signed)
                    if w is not None:return ('primary',R,Z,w)
    # Exactly one shared internal wire. Enumerate its read count and the
    # excess allocated to repeated primaries, then distribute their reads.
    for s in range(min_excess,e+1):
        for dH in range(2,s+2):
            sp=s-(dH-1)
            for r in range(min(sp,n)+1):
                for R in combinations(V,r):
                    W=tuple(i for i in V if i not in R)
                    for c in compositions(sp-r,r):
                        ds=tuple(i+2 for i in c)
                        if not allowed(R,ds,s):stats['restriction_reject']+=1;continue
                        for S in subsets(W):
                            Z=tuple(i for i in W if i not in S)
                            # Cache cofactor checks before allocations.
                            data=make_cofactors(f,R,S,Z)
                            if any(not options(t,len(S),signed) for t in data):continue
                            for din in product(*(range(d+1) for d in ds)):
                                dout=tuple(d-a for d,a in zip(ds,din))
                                if len(S)+sum(din)<2:continue
                                w=fixed(f,R,S,Z,din,dout,dH,signed,stats,completion=completion)
                                if w is not None:return ('internal',R,S,Z,din,dout,dH,*w)
    return None

def reconstruct(n,f,ans,e):
    """Compile the provider once, return signed DAG and independently verify."""
    V=list(vars(n));one=(1<<(1<<n))-1;gates=[]
    def neg(x):return x[0],not x[1]
    def value(x):return V[x[0]]^(one if x[1] else 0)
    def compile(t,ins):
        if t[0]=='x':return neg(ins[t[1]]) if t[2] else ins[t[1]]
        a=compile(t[1],ins)
        for c in t[2:]:
            b=compile(c,ins);x,y=value(a),value(b)
            V.append(x&y if t[0]=='&' else x|y);gates.append((t[0],a,b));a=(len(V)-1,False)
        return a
    I=tuple((i,False) for i in range(n))
    if ans[0]=='primary':
        _,R,Z,t=ans;out=compile(t,tuple(I[i] for i in Z+R))
    else:
        _,R,S,Z,din,dout,dH,h,g=ans
        outH=compile(h,tuple(I[i] for i in S+R))
        out=compile(g,tuple(I[i] for i in Z+R)+(outH,))
    assert value(out)==f and len(gates)<=n-1+e,(n,f,ans,len(gates),e)
    # Remove semantically trivial and identical-operand gates, and trim output
    # cone. This produces a distinct-operand circuit with no extra binary gates.
    vals=list(vars(n));ren=list(I);outg=[]
    def read(a):
        q=ren[a[0]];return q if not a[1] else (q^1 if isinstance(q,int) else neg(q))
    def val(a):return a*one if isinstance(a,int) else vals[a[0]]^(one if a[1] else 0)
    for op,a,b in gates:
        a,b=read(a),read(b);x,y=val(a),val(b);z=x&y if op=='&' else x|y
        if z in (0,one):w=int(z==one)
        elif z==x:w=a
        elif z==y:w=b
        else:
            assert not isinstance(a,int) and not isinstance(b,int) and a[0]!=b[0]
            outg.append((op,a,b));vals.append(z);w=(len(vals)-1,False)
        ren.append(w)
    o=read(out);assert val(o)==f and not isinstance(o,int)
    live=set()
    def visit(i):
        if i<n or i in live:return
        live.add(i);_,a,b=outg[i-n];visit(a[0]);visit(b[0])
    visit(o[0]);mapping={i:i for i in range(n)};new=[]
    for i in sorted(live):
        op,a,b=outg[i-n];mapping[i]=n+len(new);new.append((op,(mapping[a[0]],a[1]),(mapping[b[0]],b[1])))
    return new,(mapping[o[0]],o[1])

@lru_cache(None)
def formula_columns(cols,one,signed):
    """Independent exhaustive formula evaluation over specified occurrence columns."""
    if len(cols)==1:return frozenset((cols[0],cols[0]^one) if signed else cols)
    out=set()
    for mask in range(1,1<<len(cols)):
        if not mask&1 or mask==(1<<len(cols))-1:continue
        A=tuple(x for i,x in enumerate(cols) if mask>>i&1);B=tuple(x for i,x in enumerate(cols) if not mask>>i&1)
        for a in formula_columns(tuple(sorted(A)),one,signed):
            for b in formula_columns(tuple(sorted(B)),one,signed):out.update((a&b,a|b))
    return frozenset(out)

def checks():
    t=perf_counter();rng=Random(21841);C=Counter();ST=Counter()
    # All attainable truth tables for four small layouts, with randomly
    # chosen unattainable functions. The oracle enumerates full formula
    # columns independently, not conditional cofactor assignments.
    for n,R,S,Z,din,dout,dH,signed in (
        (3,(0,),(1,),(2,),(1,),(1,),2,False),
        (3,(0,),(1,),(2,),(1,),(1,),2,True),
        (4,(0,1),(2,),(3,),(1,1),(1,1),2,False),
        (4,(0,1),(2,),(3,),(2,1),(0,1),2,True),
        (4,(0,),(1,2),(3,),(1,),(2,),3,False),
        (3,(0,1),(),(2,),(1,1),(1,1),2,True)):
        v=vars(n);one=(1<<(1<<n))-1
        H=tuple(v[i] for i in S)+tuple(v[i] for i,d in zip(R,din) for _ in range(d))
        G=tuple(v[i] for i in Z)+tuple(v[i] for i,d in zip(R,dout) for _ in range(d))
        known=set()
        for h in formula_columns(tuple(sorted(H)),one,signed):known.update(formula_columns(tuple(sorted(G+(h,)*dH)),one,signed))
        pos=sorted(known);samples=pos if len(pos)<=150 else rng.sample(pos,150)
        samples+= [rng.randrange(one+1) for _ in range(150)]
        for f in samples:
            a=fixed(f,R,S,Z,din,dout,dH,signed,ST)
            assert bool(a)==(f in known),(n,R,S,Z,din,dout,dH,signed,f,a)
            if a and f not in (0,one):
                reconstruct(n,f,('internal',R,S,Z,din,dout,dH,*a),sum(i+j-1 for i,j in zip(din,dout))+dH-1)
            C['layout_checks']+=1;C['layout_yes']+=a is not None
        print('fixed layout',n,R,S,Z,din,dout,dH,signed,'attainable',len(known),'tested',len(samples),flush=True)
    # Generated circuits with a genuine provider, repeated primaries,
    # and budget 3 or 4. Check reconstruction on essential reduced targets.
    generated=[]
    for _ in range(250):
        n=5;R=(0,1);S=(2,);Z=(3,4);din=(1,1);dout=(1,1);dH=rng.choice((2,3));signed=bool(rng.randrange(2));one=(1<<(1<<n))-1;v=vars(n)
        H=[v[i] for i in S+R];G=[v[i] for i in Z+R]
        def rand_formula(A):
            A=[x^(one if signed and rng.randrange(2) else 0) for x in A]
            while len(A)>1:
                a=A.pop(rng.randrange(len(A)));b=A.pop(rng.randrange(len(A)));A.append(a&b if rng.randrange(2) else a|b)
            return A[0]
        h=rand_formula(H);f=rand_formula(G+[h]*dH)
        if not essential(n,f) or simplify(n,f,signed)[0]!=n:continue
        a=fixed(f,R,S,Z,din,dout,dH,signed,ST);assert a
        reconstruct(n,f,('internal',R,S,Z,din,dout,dH,*a),dH+1)
        C['generated']+=1;generated.append((n,f,dH+1,signed))
    print('fixed and generated',dict(C),'stats',dict(ST),'seconds',perf_counter()-t,flush=True)
    # Full recognition on a small sample. The exact independent gate-set
    # oracle is used for n=3 signed / n=4 monotone, at budget n+1. At e>=3
    # the class need not cover all circuits, so positive witness checks only.
    from two_sharing_core import solve as two
    for signed,n in ((False,4),(True,3)):
        ref=brute(n,n+1,'free' if signed else 'mono');tests=0
        for f in range(1,(1<<(1<<n))-1):
            if not essential(n,f) or (not signed and not raw_monotone(n,f)) or simplify(n,f,signed)[0]!=n:continue
            a=solve(n,f,2,signed);assert bool(a)==(f in ref),(n,f,signed,a)
            if a:reconstruct(n,f,a,2)
            tests+=1
        print('full oracle',signed,n,tests,flush=True)
    hard=[]
    for n,f,e,signed in generated:
        if not two(n,f,signed):hard.append((n,f,e,signed))
        if len(hard)>=12:break
    for n,f,e,signed in hard:
        a=solve(n,f,e,signed);assert a,(n,f,e,signed)
        reconstruct(n,f,a,e);C['beyond_two']+=1
    print('beyond excess two',len(hard),'examples',hard[:3], 'total seconds',perf_counter()-t,flush=True)
if __name__=='__main__':checks()
