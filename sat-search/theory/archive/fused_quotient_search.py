"""Interleave region ownership and quotient reconstruction. Complete reduced
monotone/free-NOT cores, at one allocated excess. Experimental, no counted NOT.
Uses the same class coverage as layout_projection.search_exact. No claim of
exact-size padding. Run --bench for a bounded matched comparison.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations
from time import perf_counter
from conditional_provider import options, signs, consistent_monotone
from layout_projection import Projection, port_patterns, masks
from module_contraction import essential, raw_monotone, simplify
from restriction_excess import first_gate_candidates, lower
from two_sharing_core import slices
from ordered_quotient_core import reconstruct
from regional_obligation_cache import ObligationCache
ANY=-1

@lru_cache(maxsize=100000)
def split_residual(t,W,S):
    """Compact residual in canonical W order, split into S then W\\S."""
    A=tuple(W.index(i) for i in S);B=tuple(i for i in range(len(W)) if i not in A)
    return slices(t,A,B)

def search(n,f,e,signed=False,stats=None,cache=None,internal_first=False,check_contract=True,lookahead=True):
    if check_contract and (n<2 or not essential(n,f) or (not signed and not raw_monotone(n,f)) or simplify(n,f,signed)[0]!=n):
        raise ValueError('requires a complete essential fully reduced core')
    if stats is None:stats=Counter()
    if cache is None:cache=ObligationCache()
    V=tuple(range(n));req=first_gate_candidates(n,f,e,signed)
    if not req:return None
    @lru_cache(None)
    def rest_lower(R):
        W=tuple(i for i in V if i not in R)
        return max(lower(len(W),t,signed) for t in slices(f,R,W))
    classes=[(r,k) for k in range(e) for r in range(1,min(n,e-k)+1)]
    if internal_first:classes.sort(key=lambda a:-a[1])
    for r,k in classes:
        for R in combinations(V,r):
            if not any(set(t[-1])<=set(R) for t in req):continue
            proj=Projection(n,f,R,signed);W0=tuple(i for i in V if i not in R)
            try:
                for P in port_patterns(r,k,e):
                    stats['patterns']+=1
                    d=Counter(x for Q in P for x in Q)
                    if sum(d[i]-1 for i in range(r))+rest_lower(R)>e or any(d[i]-1+rest_lower((R[i],))>e for i in range(r)):
                        stats['restriction_reject']+=1;continue
                    live=[set(x for Q in P[j:] for x in Q if x<r+j) for j in range(k+1)]
                    lm=[sum(1<<x for x in A) for A in live]
                    pm=[sum(1<<x for x in set(Q)) for Q in P]
                    cutargs=[(tuple(R[x] for x in sorted(A) if x<r),sum(x>=r for x in A)) for A in live]
                    inargs=[(tuple(R[x] for x in sorted(set(A)) if x<r),sum(x>=r for x in set(A))) for A in P]
                    start=tuple(enumerate(slices(f,R,W0))) # each repeated primary live initially
                    @lru_cache(None)
                    def viable(j,W):
                        X=tuple(i for i in V if i not in W)
                        if not proj.cut(X,*cutargs[j]):return ()
                        choices=[]
                        for S in ((W,) if j==k else masks(W)):
                            if len(S)+len(P[j])<2:continue
                            if not proj.step(X,S,*inargs[j],j==k):continue
                            W2=tuple(i for i in W if i not in S)
                            if j==k or viable(j+1,W2):choices.append(S)
                        return tuple(choices)
                    @lru_cache(None)
                    def go(j,W,state):
                        stats['states']+=1
                        X=tuple(i for i in V if i not in W)
                        if not proj.cut(X,*cutargs[j]):stats['cut_reject']+=1;return None
                        for S in (viable(j,W) if lookahead else ((W,) if j==k else masks(W))):
                            if len(S)+len(P[j])<2:continue
                            if not proj.step(X,S,*inargs[j],j==k):stats['step_reject']+=1;continue
                            if j==k:
                                reqs={}
                                for p,t in state:
                                    a=p&pm[j]
                                    if a in reqs and reqs[a]!=t:break
                                    reqs[a]=t
                                else:
                                    ps=tuple(sorted(reqs));ts=tuple(reqs[p] for p in ps)
                                    h=cache(len(S),P[j],ps,ts,signed);stats['local']+=1
                                    if h is not None:return ((S,),(h,))
                                continue
                            W2=tuple(i for i in W if i not in S);m=len(S)
                            opts={p:options(split_residual(t,W,S),m,signed) for p,t in state}
                            if any(not o for o in opts.values()):stats['cofactor_reject']+=1;continue
                            order=sorted(opts,key=lambda p:(opts[p][0][0]==ANY,p));hreq={};new={};pol={}
                            def choose(i):
                                if i==len(order):
                                    stats['profiles']+=1
                                    ps=tuple(sorted(hreq)) or (0,);ts=tuple(hreq[p] for p in ps) if hreq else (ANY,)
                                    h=cache(m,P[j],ps,ts,signed);stats['local']+=1
                                    if h is None:return None
                                    ans=go(j+1,W2,tuple(sorted(new.items())))
                                    if ans is not None:return ((S,)+ans[0],(h,)+ans[1])
                                    return None
                                p=order[i];pk=p&pm[j]
                                for h,a,b in opts[p]:
                                    if pk in hreq and h!=ANY and hreq[pk]!=h:continue
                                    si=signs(m,h)
                                    if si is None or any(v in pol and pol[v]!=sg for v,sg in si.items()):continue
                                    if not signed and any((q&pk==q and not consistent_monotone(t,h)) or (pk&q==pk and not consistent_monotone(h,t)) for q,t in hreq.items()):continue
                                    add={};ok=True
                                    for v,t in enumerate((a,b)):
                                        if t==ANY:continue
                                        key=(p|(v<<(r+j)))&lm[j+1]
                                        if (key in new and new[key]!=t) or (key in add and add[key]!=t):ok=False;break
                                        add[key]=t
                                    if not ok:continue
                                    nh=h!=ANY and pk not in hreq
                                    if nh:hreq[pk]=h
                                    nn=[q for q in add if q not in new];new.update(add)
                                    np=[q for q in si if q not in pol];pol.update(si)
                                    ans=choose(i+1)
                                    if ans is not None:return ans
                                    if nh:del hreq[pk]
                                    for q in nn:del new[q]
                                    for q in np:del pol[q]
                                return None
                            ans=choose(0)
                            if ans is not None:return ans
                        return None
                    ans=go(0,W0,start);stats['state_hits']+=go.cache_info().hits;stats['viability_states']+=viable.cache_info().misses;go.cache_clear();viable.cache_clear()
                    if ans is not None:return R,ans[0],P,ans[1]
            finally:
                proj.cut.cache_clear();proj.step.cache_clear();proj.bound.compatible.cache_clear()
    return None

def check():
    from module_contraction import brute
    t=perf_counter();count=Counter()
    for n,signed in ((3,True),(4,False)):
        ref=brute(n,n+2,'free' if signed else 'mono')
        for f in range(1,(1<<(1<<n))-1):
            if not essential(n,f) or (not signed and not raw_monotone(n,f)) or simplify(n,f,signed)[0]!=n:continue
            a=next((a for e in range(1,4) if (a:=search(n,f,e,signed)) is not None),None)
            assert bool(a)==(f in ref),(n,f,signed,a)
            if a:reconstruct(n,f,*a,3)
            count['queries']+=1;count['yes']+=bool(a)
    print('oracle',dict(count),'seconds',perf_counter()-t,flush=True)

def bench():
    import ordered_quotient_core as oq
    from layout_projection import search_exact
    from layout_projection_bench import cases
    fs=[a for a in cases() if not a[2]][:6];expected=[]
    for mode in ('cached layout','fused'):
        T=perf_counter();C=Counter();cache=ObligationCache();old=oq.local;oq.local=cache
        try:
            for j,(n,f,signed) in enumerate(fs):
                t=perf_counter();a=search_exact(n,f,3,signed,C) if mode=='cached layout' else search(n,f,3,signed,C,cache)
                if a:reconstruct(n,f,*a,3)
                if mode=='cached layout':expected.append(bool(a))
                else:assert bool(a)==expected[j]
                print(mode,j,bool(a),round(perf_counter()-t,4),flush=True)
        finally:oq.local=old
        print(mode,'seconds',perf_counter()-T,'stats',dict(C),'cache',cache.solve.cache_info(),'local',dict(cache.stats),flush=True)
if __name__=='__main__':
    import sys
    check()
    if '--bench' in sys.argv:bench()
