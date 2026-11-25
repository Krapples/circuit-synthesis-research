"""Exact excess <=2 decision for complete, reduced monotone/free-NOT cores.
No counted-NOT claim. Returns a construction certificate, not a SAT proof.
Uses only standard library and module_contraction / one_sharing_core.
"""
from functools import lru_cache
from itertools import combinations, product
from collections import Counter
from random import Random
from time import perf_counter
from module_contraction import essential,raw_monotone,simplify,contract_pair,peel,cofactor1,vars,brute,expand
from one_sharing_core import tree,ev,leaves,solve_core
from restriction_excess import first_gate_candidates, lower as excess_lower

ANY=-1
@lru_cache(None)
def assignments(inds):
    return tuple(sum((a>>i&1)<<j for i,j in enumerate(inds)) for a in range(1<<len(inds)))

def slices(f, X, Z, fixed=0):
    return tuple(sum((f>>(fixed|a|b)&1)<<j for j,b in enumerate(assignments(Z))) for a in assignments(X))

def support(m,f):
    return sum(1<<i for i in range(m) if cofactor1(m,f,i,0)!=cofactor1(m,f,i,1))

def local(m, ports, pats, targets, signed, stats=None, module_filter=True):
    """Read-once completion with all private leaves and each port occurrence.
    Targets are compact m-primary tables. Port indices start at 0.
    Returns binary tree with duplicate occurrences mapped to the same port.
    """
    if stats is not None:stats['local']+=1
    one=(1<<(1<<m))-1;M=(1<<m)-1;cols=vars(m);q=len(ports)
    if any(t not in (0,one,ANY) and tree(m,t,signed) is None for t in targets):return None
    @lru_cache(None)
    def proj(f,S,is_and):
        A=tuple(i for i in range(m) if S>>i&1);B=tuple(i for i in range(m) if not S>>i&1)
        v=0
        for a in assignments(A):
            bits=[f>>(a|b)&1 for b in assignments(B)]
            z=any(bits) if is_and else all(bits)
            if z:
                for b in assignments(B):v|=1<<(a|b)
        return v
    @lru_cache(None)
    def exposed(j,S):
        # A subtree can have just one nonconstant cofactor, once all
        # private variables outside the subtree are fixed.
        f=targets[j]
        if f in (0,one,ANY):return None
        A=tuple(i for i in range(m) if S>>i&1);B=tuple(i for i in range(m) if not S>>i&1)
        found=None;aa=assignments(A)
        for b in assignments(B):
            h=sum((f>>(a|b)&1)<<k for k,a in enumerate(aa))
            if h in (0,(1<<len(aa))-1):continue
            if found is None:found=h
            elif found!=h:return None
        if found is None:return None
        return sum((found>>k&1)<< (a|b) for k,a in enumerate(aa) for b in assignments(B))
    @lru_cache(None)
    def rec(L,ts):
        if stats is not None:stats['rec']+=1
        if not L:return None
        if any(t!=ANY and support(m,t)&~L for t in ts):return None
        if module_filter and any(t not in (0,one,ANY) and exposed(j,L&M)!=t for j,t in enumerate(ts)):
            if stats is not None:stats['module_reject']+=1
            return None
        if L.bit_count()==1:
            i=L.bit_length()-1
            vals=(cols[i],)*len(pats) if i<m else tuple(one if p>>ports[i-m]&1 else 0 for p in pats)
            for neg in range(2 if signed else 1):
                if all(t==ANY or t==(v^(one if neg else 0)) for v,t in zip(vals,ts)):
                    return ('x',i if i<m else m+ports[i-m],bool(neg))
            return None
        # Anchor lowest leaf to one child to remove commutativity.
        bit=L&-L;rest=L^bit;a=rest
        while True:
            l=a|bit;r=L^l
            if r:
                for op in ('&','|'):
                    is_and=op=='&';absorbing=0 if is_and else one;neutral=one^absorbing
                    opts=[]
                    for t in ts:
                        if t==ANY:opts.append(((ANY,ANY),))
                        elif t==absorbing:opts.append(((absorbing,ANY),(ANY,absorbing)))
                        elif t==neutral:opts.append(((neutral,neutral),))
                        else:
                            x,y=proj(t,l&M,is_and),proj(t,r&M,is_and)
                            if (x&y if is_and else x|y)!=t:break
                            opts.append(((x,y),))
                    else:
                        for pairs in product(*opts):
                            u,v=map(tuple,zip(*pairs));x=rec(l,u)
                            if x is None:continue
                            y=rec(r,v)
                            if y is not None:return (op,x,y)
            if not a:break
            a=(a-1)&rest
        return None
    return rec((1<<(m+q))-1,tuple(targets))


def map_tree(t, mapping):
    if t[0]=='x':
        j=mapping[t[1]]
        if isinstance(j,int):return ('x',j,t[2])
        return negate(j) if t[2] else j
    return (t[0],*(map_tree(c,mapping) for c in t[1:]))

def negate(t):
    if t[0]=='x':return ('x',t[1],not t[2])
    return ('|' if t[0]=='&' else '&',*(negate(c) for c in t[1:]))

def replace_leaf(t,i,r):
    if t[0]=='x':return r if t[1]==i else t
    return (t[0],*(replace_leaf(c,i,r) for c in t[1:]))

def cost1(n,f,signed):
    """Exact excess<=1 via module reduction; return binary cost or None."""
    if n<1 or not essential(n,f):return None
    m,g,steps=simplify(n,f,signed);r=solve_core(m,g,signed,False)
    return None if r is None else r[0]+len(steps)


def solve(n,f,signed=False,stats=None,gate_filter=True,check_contract=True,*,completion=local):
    """Return a decomposition certificate if excess<=2, otherwise None.
    A certificate ('primary',R,tree) uses an explicit formula; ('module',T,Z,h,g)
    uses two <=1 synthesis problems; ('internal',x,S,Z,h,g) gives a two-region DAG.
    Local solver is exact but may be expensive for large primary count.
    """
    if check_contract:
        if n<1 or not essential(n,f) or (not signed and not raw_monotone(n,f)) or (n>1 and (contract_pair(n,f,signed) is not None or peel(n,f,signed) is not None)):
            raise ValueError('requires essential, fully reduced complete core')
    r=solve_core(n,f,signed,False)
    if r is not None:return ('one',r)
    req=first_gate_candidates(n,f,2,signed) if gate_filter else None
    if gate_filter and not req:return None
    allvars=tuple(range(n))
    def allowed(R):return req is None or any(set(v[-1])<=set(R) for v in req)
    degree=[max(excess_lower(n-1,cofactor1(n,f,x,b),signed) for b in (0,1)) for x in allvars] if gate_filter else [0]*n;
    # Case 1: all repeated wires are primaries, either 3 reads of one or
    # 2 reads each of two. After unfolding, all other inputs occur once.
    for R in [(i,) for i in allvars]+list(combinations(allvars,2)):
        if not allowed(R) or any(degree[x]+(2 if len(R)==1 else 1)>2 for x in R):continue
        Z=tuple(i for i in allvars if i not in R)
        ts=slices(f,R,Z);ps=tuple(range(1<<len(R)))
        t=completion(len(Z),(0,0,0) if len(R)==1 else (0,0,1,1),ps,ts,signed,stats)
        if t is not None:
            out=map_tree(t,Z+R);assert ev(out,n)==f
            return ('primary',R,out)
    # Case 2a: the repeated primary is used twice upstream of the repeated
    # internal wire. Its cone is a disjoint functional module of excess <=1.
    for k in range(2,n):
        for T in combinations(allvars,k):
            Z=tuple(i for i in allvars if i not in T);ts=slices(f,T,Z);types=sorted(set(ts))
            if len(types)!=2:continue
            lo,hi=types
            if not signed and lo&hi!=lo:continue
            h=sum((t==hi)<<i for i,t in enumerate(ts))
            g=lo|(hi<<(1<<len(Z))) # h last variable
            a=cost1(k,h,signed);b=cost1(n-k+1,g,signed)
            if a is not None and b is not None and a+b<=n+1:
                return ('module',T,Z,h,g,a,b)
    # Case 2b: one occurrence of x inside the provider, one outside. Its
    # one-port private cotree must be a chain. The neutral slice preserves
    # every private input and must be observed (deepest private is essential).
    for x in allvars:
        if not allowed((x,)) or degree[x]>1:continue
        rem=tuple(i for i in allvars if i!=x)
        for k in range(1,len(rem)+1):
            for S in combinations(rem,k):
                Z=tuple(i for i in rem if i not in S)
                ts=[slices(f,S,Z,b<<x) for b in (0,1)]
                ty=[sorted(set(t)) for t in ts]
                if any(len(t)>2 for t in ty):continue
                for neutral in (0,1):
                    if len(ty[neutral])!=2:continue
                    lo,hi=ty[neutral]
                    if not signed and lo&hi!=lo:continue
                    anchor=sum((t==hi)<<i for i,t in enumerate(ts[neutral]))
                    # For signed circuits we can orient h so its observed
                    # slice equals this particular labeling of the two classes.
                    if not essential(k,anchor):continue
                    t=tree(k,anchor,signed)
                    if t is None:continue
                    # Insert x at a leaf with the neutral value matching the
                    # observed slice. This contains the true deepest insertion.
                    for i in range(k):
                        # Recover literal sign from the anchor's unique leaf.
                        def getleaf(t):
                            if t[0]=='x':return t if t[1]==i else None
                            return next((v for c in t[1:] if (v:=getleaf(c)) is not None),None)
                        old=getleaf(t)
                        for op in ('&','|'):
                            neg=bool(neutral!=int(op=='&'))
                            if neg and not signed:continue
                            htree=replace_leaf(t,i,(op,old,('x',k,neg)))
                            h=ev(htree,k+1);tab={};ok=True
                            for b in (0,1):
                                for a,v in enumerate(ts[b]):
                                    p=b|((h>>(a|(b<<k))&1)<<1)
                                    if p in tab and tab[p]!=v:ok=False;break
                                    tab[p]=v
                                if not ok:break
                            if not ok:continue
                            pats=tuple(sorted(tab));targets=tuple(tab[p] for p in pats)
                            gt=completion(len(Z),(0,1,1),pats,targets,signed,stats)
                            if gt is not None:
                                H=map_tree(htree,S+(x,));G=map_tree(gt,Z+(x,H))
                                assert ev(G,n)==f
                                return ('internal',x,S,Z,htree,gt)
    return None


def reconstruct(n,f,certificate,signed=False):
    """Materialize signed binary gates and an output literal. Each internal
    shared provider is compiled once. Literal=(wire, complemented); temporary
    constants are simplified out. Validates the complete truth table and cost.
    """
    gates=[];one=(1<<(1<<n))-1;V=list(vars(n))
    def inv(a):return 1-a if isinstance(a,int) else (a[0],not a[1])
    def make(op,a,b):
        if isinstance(a,int):return a if a==int(op=='|') else b
        if isinstance(b,int):return b if b==int(op=='|') else a
        if a[0]==b[0]:return a if a==b else int(op=='|')
        u,v=(V[t[0]]^(one if t[1] else 0) for t in (a,b))
        V.append(u&v if op=='&' else u|v);gates.append((op,a,b))
        return n+len(gates)-1,False
    def compile(t,inputs):
        if t[0]=='x':return inv(inputs[t[1]]) if t[2] else inputs[t[1]]
        a=compile(t[1],inputs)
        for c in t[2:]:a=make(t[0],a,compile(c,inputs))
        return a
    def reduced(m,g,inputs):
        k,h,trace=simplify(m,g,signed);X=list(inputs);post=[]
        for step in trace:
            if step[0]=='pair':
                _,i,j,p=step;a,b=X[i],X[j]
                if p==0:w=make('|',a,b)
                else:w=make('&',a if p&1 else inv(a),b if p&2 else inv(b))
                X=[w0 for i0,w0 in enumerate(X) if i0 not in (i,j)]+[w]
            else:
                _,i,v,c=step;a=X.pop(i);post.append(('|' if c else '&',a if v!=c else inv(a)))
        ans=solve_core(k,h,signed,False);assert ans is not None
        z=compile(ans[1],X)
        for op,a in reversed(post):z=make(op,a,z)
        return z
    inputs=[(i,False) for i in range(n)];kind=certificate[0]
    if kind=='one':z=compile(certificate[1][1],inputs)
    elif kind=='primary':z=compile(certificate[2],inputs)
    elif kind=='module':
        _,T,Z,h,g,_,_=certificate
        H=reduced(len(T),h,[inputs[i] for i in T]);z=reduced(len(Z)+1,g,[inputs[i] for i in Z]+[H])
    elif kind=='internal':
        _,x,S,Z,h,g=certificate
        H=compile(h,[inputs[i] for i in S]+[inputs[x]])
        z=compile(g,[inputs[i] for i in Z]+[inputs[x],H])
    else:raise ValueError('unknown certificate')
    assert not isinstance(z,int) and V[z[0]]^(one if z[1] else 0)==f
    assert len(gates)<=n+1
    return gates,z

def check():
    from complete_sharing_fpt import Solver
    start=perf_counter();counts=Counter();stats=Counter()
    # Brute at n+1 binary gates for all monotone n<=4 and signed n<=3.
    for signed,n in ((False,3),(False,4),(True,3)):
        ref=brute(n,n+1,'free' if signed else 'mono');c=Counter()
        for f in range(1,(1<<(1<<n))-1):
            if not essential(n,f) or (not signed and not raw_monotone(n,f)):continue
            m,h,trace=simplify(n,f,signed)
            if trace:continue
            ans=solve(m,h,signed,stats)
            assert bool(ans)==(ref.get(f,n+2)<=n+1),(signed,n,f,ans,ref.get(f))
            if ans:reconstruct(m,h,ans,signed)
            c[ans[0] if ans else 'no']+=1
        counts.update(c);print('exhaustive',signed,n,dict(c),flush=True)
    # Generated n=5..7 circuits with known excess 2, deliberately choose
    # first shared primary and one shared internal node.
    rng=Random(7133);cases=[]
    for _ in range(800):
        n=rng.randrange(4,8);signed=bool(rng.randrange(2));order=list(range(n));rng.shuffle(order)
        x=order[0];k=rng.randrange(1,n-1);S=order[1:k+1];Z=order[k+1:]
        def leaf(i):return ('x',i,signed and bool(rng.randrange(2)))
        def chain(t,L):
            for i in L:t=(rng.choice('&|'),t,leaf(i))
            return t
        h=chain(leaf(x),S);c=chain(h,Z[:len(Z)//2]);d=chain(h,Z[len(Z)//2:]);d=(rng.choice('&|'),d,leaf(x));out=(rng.choice('&|'),c,d)
        f=ev(out,n)
        if not essential(n,f) or contract_pair(n,f,signed) is not None or peel(n,f,signed) is not None:continue
        ans=solve(n,f,signed,stats)
        assert ans,(n,f,signed,out)
        reconstruct(n,f,ans,signed)
        counts['generated_'+ans[0]]+=1
        if not signed and n<=6 and len(cases)<20:cases.append((n,f))
    print('counts',dict(counts),'stats',dict(stats),'seconds',perf_counter()-start,flush=True)
    # Matched small monotone benchmark, plus random irreducible exclusions.
    for _ in range(100):
        n=5;ts=[rng.randrange(1,1<<n) for _ in range(rng.randrange(4,10))];f=sum(1<<a for a in range(1<<n) if any(a&t==t for t in ts))
        if essential(n,f) and contract_pair(n,f) is None and peel(n,f) is None:cases.append((n,f))
        if len(cases)>=30:break
    t=perf_counter();answers=[bool(solve(n,f)) for n,f in cases];a=perf_counter()-t
    t=perf_counter();baseline=[Solver(n).solve(f,2) for n,f in cases];b=perf_counter()-t
    assert answers==baseline
    print('matched',len(cases),'yes',sum(answers),'direct',a,'regional',b,flush=True)
    # Force reconstruction of the disjoint-module certificate independently
    # of whether another (primary-only) solution happens to be available.
    cs=[60104,60128,60584]
    for h in cs:
        for g in cs:
            f=sum((g>>((a>>4)|((h>>(a&15)&1)<<3))&1)<<a for a in range(128))
            reconstruct(7,f,('module',(0,1,2,3),(4,5,6),h,g,4,4))
    print('verified 9 disjoint-module certificates',flush=True)

def signed_four_check():
    t=perf_counter();ref=brute(4,5,'free');rng=Random(77012)
    pos=[f for f in ref if essential(4,f) and simplify(4,f,True)[0]==4]
    neg=[f for f in range(65536) if f not in ref and essential(4,f) and simplify(4,f,True)[0]==4]
    C=Counter()
    for f in rng.sample(pos,min(500,len(pos)))+rng.sample(neg,min(500,len(neg))):
        a=solve(4,f,True);assert bool(a)==(f in ref),(f,a)
        if a:reconstruct(4,f,a,True)
        C[a[0] if a else 'no']+=1
    print('signed four-input sample',dict(C),'seconds',perf_counter()-t,flush=True)

if __name__=='__main__':
    import sys
    check()
    if '--signed-four' in sys.argv:signed_four_check()
