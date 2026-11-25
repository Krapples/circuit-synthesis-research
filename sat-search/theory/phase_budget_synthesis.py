"""Reference-row normalized signed skeletons, and lazy inversion-budget cuts.
Standard library. At-most cost, nonconstant target, fan-in two AND/OR/NOT.
Gate format as in skeleton_not_opt.py. No claims about exact-size padding.
Run this file for reproducible small oracle tests.
"""
from itertools import combinations, product
from functools import lru_cache
from collections import Counter, deque
from random import Random
from time import perf_counter
from skeleton_not_opt import generate, optimize, cost, truth
from module_contraction import brute, vars


def normalize(n, gates, out=0, anchor=0):
    """Gauge-normalize every wire to value zero at reference assignment.
    Return canonical gates, canonical target output sign, and anchor values.
    Canonical primary i represents x_i XOR anchor_i.
    """
    q=[(anchor>>i)&1 for i in range(n)]; gs=[]
    for op,l,r,a,b in gates:
        x,y=q[l]^a,q[r]^b
        p=(x&y) if op=='AND' else (x|y)
        q.append(p)
        gs.append((op if not p else ('OR' if op=='AND' else 'AND'),l,r,a^q[l]^p,b^q[r]^p))
    assert all((op,a,b) in TYPES for op,l,r,a,b in gs)
    return gs,out^q[-1],tuple(q)

# Both normalized input wires are zero at the anchor.
TYPES=(('AND',0,0),('OR',0,0),('AND',0,1),('AND',1,0))


def constraints(n, gates, out=None, anchor=0):
    """(u,v,parity,provider_group) constraints. -1 = nondeletable.
    out=None: partial skeleton, no constraint on the eventual output.
    Can use untrimmed prefixes, with no output yet.
    """
    N=n+len(gates); root=N
    edges=[(i,root,(anchor>>i)&1,-1) for i in range(n)]
    for v,(op,l,r,a,b) in enumerate(gates,n):
        assert 0<=l<r<v and a in (0,1) and b in (0,1)
        edges.extend(((l,v,a,l),(r,v,b,r)))
    if out is not None: edges.append((N-1,root,out,N-1))
    return N+1,edges


def conflict(size,edges,paid=frozenset()):
    """Return source groups of an inconsistent parity cycle, or a coloring.
    All hard constraints must be jointly consistent. paid disables a source's
    constraints, i.e. both polarities are available at that source.
    """
    adj=[[] for _ in range(size)]
    for x,y,a,g in edges:
        if g in paid:continue
        adj[x].append((y,a,g));adj[y].append((x,a,g))
    col=[None]*size;parent=[None]*size
    for root in range(size):
        if col[root] is not None:continue
        col[root]=0; queue=deque([root])
        while queue:
            x=queue.popleft()
            for y,a,g in adj[x]:
                if col[y] is None:
                    col[y]=col[x]^a;parent[y]=(x,g);queue.append(y)
                elif col[x]^col[y]!=a:
                    # recover the two paths up to their LCA, plus this edge
                    path={x:frozenset()};u=x;s=frozenset()
                    while parent[u] is not None:
                        u,h=parent[u];s=s|{h};path[u]=s
                    u=y;t={g}
                    while u not in path:
                        u,h=parent[u];t.add(h)
                    hit=frozenset((t|path[u]) - {-1})
                    assert hit, 'inconsistent hard constraints'
                    return hit,None
    p=tuple(x^col[-1] for x in col[:-1]);return None,p


def packing(size,edges):
    """Greedy disjoint provider-conflict packing: a valid NOT lower bound."""
    used=set();cuts=[]
    while True:
        hit,_=conflict(size,edges,used)
        if hit is None:return cuts
        cuts.append(hit);used.update(hit)


def min_hit(cuts, cap):
    """Exact minimum hitting set, bounded by cap. Small reference only."""
    cuts=tuple(sorted(set(cuts),key=lambda s:(len(s),tuple(sorted(s)))))
    @lru_cache(None)
    def go(cs,k):
        if not cs:return frozenset()
        if k==0:return None
        a=cs[0];freq=Counter(x for s in cs for x in s)
        for x in sorted(a,key=lambda x:(-freq[x],x)):
            r=go(tuple(s for s in cs if x not in s),k-1)
            if r is not None:return r|{x}
        return None
    for k in range(cap+1):
        r=go(cuts,k)
        if r is not None:return r
    return None


def lazy_opt(n,gates,out=None,anchor=0):
    """Exact phase optimum via source conflict clauses + hitting set.
    No external SAT dependency. Exponential reference master solver.
    """
    size,edges=constraints(n,gates,out,anchor); cuts=packing(size,edges);lb=len(cuts);rounds=0
    while True:
        paid=min_hit(cuts,size-1)
        assert paid is not None
        hit,p=conflict(size,edges,paid);rounds+=1
        if hit is None:
            assert all(p[i]==(anchor>>i)&1 for i in range(n))
            return len(paid),p,lb,rounds,cuts
        assert hit not in cuts;cuts.append(hit)


def eval_skeleton(n,gates,out,anchor=0):
    one=(1<<(1<<n))-1;vs=[v^(one if anchor>>i&1 else 0) for i,v in enumerate(vars(n))]
    for op,l,r,a,b in gates:
        x,y=vs[l]^(one if a else 0),vs[r]^(one if b else 0)
        vs.append((x&y) if op=='AND' else (x|y))
    return vs[-1]^(one if out else 0)


def brute_phase(n,gates,out=None,anchor=0):
    size,edges=constraints(n,gates,out,anchor)
    return min(len({g for x,y,a,g in edges if p[x]^p[y]!=a}) for tail in product((0,1),repeat=len(gates)) for p in [tuple((anchor>>i)&1 for i in range(n))+tail+(0,)])


def skeleton_oracle(n,bmax,totalmax):
    """Enumerate canonical signed gate sequences (untrimmed allowed).
    Final wire is output; count NOTs exactly by exhaustive phase assignment.
    """
    known={};sequences=0
    def record(gates,vs):
        nonlocal sequences
        sequences+=1
        b=len(gates);one=(1<<(1<<n))-1
        for out in (0,1):
            f=vs[-1]^(one if out else 0)
            if f in (0,one):continue
            u=brute_phase(n,gates,out)
            if b+u<=totalmax:known[f]=min(known.get(f,100),b+u)
        if b==bmax:return
        for l,r in combinations(range(len(vs)),2):
            x,y=vs[l],vs[r]
            for op,a,c in TYPES:
                v=(x|y) if op=='OR' else ((x^(one if a else 0))&(y^(one if c else 0)))
                # Retain duplicates/constant intermediate columns: no semantic pruning.
                record(gates+[(op,l,r,a,c)],vs+[v])
    # Zero binary outputs can be any literal; b>0 output last is WLOG.
    for v in vars(n):known[v]=0;known[v^((1<<(1<<n))-1)]=1
    record([],list(vars(n)))
    return known,sequences


def test():
    t=perf_counter();rng=Random(201311);stats=Counter()
    for i in range(800):
        n,g,out=generate(rng,rng.randrange(2,8),rng.randrange(1,13),i%3==0)
        old,p=optimize(n,g,out);truth(n,g,out,p)
        a=rng.randrange(1<<n);gs,o,q=normalize(n,g,out,a)
        assert eval_skeleton(n,g,out)==eval_skeleton(n,gs,o,a)
        assert old==brute_phase(n,gs,o,a)
        z,ph,lb,rounds,cuts=lazy_opt(n,gs,o,a)
        assert z==old and lb<=z
        assert len({group for x,y,s,group in constraints(n,gs,o,a)[1] if (ph+(0,))[x]^(ph+(0,))[y]!=s})==z
        stats['full']+=1;stats['packing_exact']+=lb==z;stats['packing_sum']+=lb;stats['opt_sum']+=z;stats['master_rounds']+=rounds;stats['max_rounds']=max(stats['max_rounds'],rounds)
        # All prefix constraints stay present on extension, but output absent.
        prev=0
        for k in range(len(gs)+1):
            z,_,lb,_,_=lazy_opt(n,gs[:k],None,a)
            assert z==brute_phase(n,gs[:k],None,a) and prev<=z<=old
            stats['prefix']+=1;stats['prefix_nonzero']+=z>0;stats['prefix_packing_exact']+=lb==z;prev=z
    print('phase tests',dict(stats),'seconds',round(perf_counter()-t,3),flush=True)
    for n,bmax in ((2,3),(3,3),(4,2)):
        t=perf_counter();known,seq=skeleton_oracle(n,bmax,bmax);ref=brute(n,bmax,'counted');one=(1<<(1<<n))-1
        ref={f:v for f,v in ref.items() if f not in (0,one)}
        assert known==ref,(n,bmax,set(known.items())^set(ref.items()))
        print('counted synthesis',n,bmax,'sequences',seq,'nonconstant functions',len(ref),'seconds',round(perf_counter()-t,3),flush=True)

if __name__=='__main__':test()
