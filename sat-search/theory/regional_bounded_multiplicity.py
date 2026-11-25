"""Optional-leaf, bounded-multiplicity regional synthesis. Free-NOT or monotone.
Exact at-most leaf multiset solver, plus exact-occurrence wrapper with fallback.
A timeout must propagate. Repo version: production helpers, bounded memo, lazy splits; opt-in completion mode.
Uses flat specified rows.
Run --bench for small Unix deadline comparisons.
"""
from collections import Counter
from functools import lru_cache
from itertools import product
from time import perf_counter
from random import Random
from regional_padding import columns, combine, graft, evaluate as value      # production helpers (same semantics)
from regional_production_adapter import check_tree, local_cover               # production local_blocks
from conditional_provider import formula_columns
from regional_phase_first import phase_first, phase_problem, phase_domains, adaptive_completion
from two_sharing_core import ANY

MEMO = 1 << 15            # bounded memoization per query (repo adaptation; prototype used unbounded caches)


def lazy_splits(c):
    """Bipartitions (a, c - a) of a capacity vector, one per unordered pair, smaller side first, generated lazily
    (repo adaptation of the prototype's sorted materialized list; same set, order within a size class may differ)."""
    total = sum(c)

    def comps(i, s):
        if i == len(c):
            if s == 0:
                yield ()
            return
        for k in range(min(c[i], s) + 1):
            for rest in comps(i + 1, s - k):
                yield (k,) + rest
    for s in range(1, total // 2 + 1):
        for a in comps(0, s):
            b = tuple(n - k for n, k in zip(c, a))
            if sum(b) > s or a <= b:
                yield a


def optional(m, ports, pats, targets, signed, stats=None, quotient=True):
    """Exact optional multiset solver. No mandatory leaves, no constants.
    Flat row obligations P,N. Return formula using a nonempty submultiset.
    """
    if stats is None: stats=Counter()
    cs,f,one=columns(m,ports,pats,targets)
    count=Counter(tuple(range(m))+tuple(m+i for i in ports));ids=tuple(sorted(count));cap=tuple(count[i] for i in ids)
    C=tuple(cs[i] for i in ids);D=len(ids)
    def bits(v):
        while v:
            b=v&-v;v^=b;yield b.bit_length()-1
    # Precompute input pattern of every specified row.
    rows=tuple(sum((c>>j&1)<<i for i,c in enumerate(C)) for j in range(one.bit_length()))
    # For each row, group other rows by distinguishing mask; bitset tests
    # then compute the maximal opposite-label subset a child can separate.
    @lru_cache(MEMO)
    def compatible(S):
        if signed:
            groups={}
            for j,r in enumerate(rows):groups[r&S]=groups.get(r&S,0)|(1<<j)
            a=tuple(groups[r&S] for r in rows)
            return a,a
        a=[];b=[]
        for r in rows:
            a.append(sum(1<<j for j,t in enumerate(rows) if not ((r^t if signed else t&~r)&S))) # positive t cannot distinguish negative r
            b.append(sum(1<<j for j,t in enumerate(rows) if not ((r^t if signed else r&~t)&S))) # negative t cannot distinguish positive r
        return tuple(a),tuple(b)
    def mask(c):return sum(1<<i for i,n in enumerate(c) if n)
    def leaf(i,phase):return ('x',ids[i],bool(phase))
    @lru_cache(MEMO)
    def val(t):return value(t,cs,one)
    @lru_cache(MEMO)
    def one_side(c,R,want):
        if not any(c):return None
        if not R:return leaf(next(i for i,n in enumerate(c) if n),0)
        available=[i for i,n in enumerate(c) if n]
        if signed:
            for i in available:
                if c[i]>=2:return ('|' if want else '&',leaf(i,0),leaf(i,1))
            seen={sum((C[i]>>j&1)<<k for k,i in enumerate(available)) for j in bits(R)}
            if len(seen)==1<<len(available):return None
            p=next(k for k in range(len(seen)+1) if k not in seen)
            return combine('|' if want else '&',[leaf(i,(p>>k&1)^int(not want)) for k,i in enumerate(available)])
        t=combine('|' if want else '&',[leaf(i,0) for i in available]);v=val(t)
        return t if not (R&(one^v if want else v)) else None
    def splits(c):
        return lazy_splits(c)
    @lru_cache(MEMO)
    def canonical(S,P,N):
        # Identical projected rows impose the same obligation on this child.
        a,b=compatible(S)
        def collapse(R):
            result=0
            while R:
                j=(R&-R).bit_length()-1
                g=a[j] if signed else a[j]&b[j]
                result|=g&-g;R&=~g
            return result
        P,N=collapse(P),collapse(N)
        if not signed:
            P=sum(1<<j for j in bits(P) if not (a[j]&P&~(1<<j)))
            N=sum(1<<j for j in bits(N) if not (b[j]&N&~(1<<j)))
        return P,N
    def rec(c,P,N):
        if quotient:P,N=canonical(mask(c),P,N)
        return solve(c,P,N)
    @lru_cache(MEMO)
    def solve(c,P,N):
        stats['optional_states']+=1
        if not any(c):return None
        if not P or not N:return one_side(c,P or N,bool(P))
        S=mask(c);a,b=compatible(S)
        if any(a[j]&P for j in bits(N)):return None
        for i,n in enumerate(c):
            if n:
                for p in range(2 if signed else 1):
                    v=C[i]^(one if p else 0)
                    if not (P&~v or N&v):return leaf(i,p)
        if sum(c)<2:return None
        for l in splits(c):
            r=tuple(n-k for n,k in zip(c,l));sl,sr=mask(l),mask(r)
            al,bl=compatible(sl);ar,br=compatible(sr)
            for op in ('&','|'):
                fixed,absorb,lc,rc=(P,N,al,ar) if op=='&' else (N,P,bl,br)
                # These children cannot cover an absorbing row if it
                # collides with a required neutral row after projection.
                badl=sum(1<<j for j in bits(absorb) if lc[j]&fixed)
                badr=sum(1<<j for j in bits(absorb) if rc[j]&fixed)
                if badl&badr:continue
                free=absorb&~(badl|badr)
                def sub(c,Q):return rec(c,fixed,Q) if op=='&' else rec(c,Q,fixed)
                visited=set()
                def cover(extra):
                    if extra in visited:return None
                    visited.add(extra)
                    x=sub(l,badr|extra)
                    if x is None:return None
                    covered=(one^val(x)) if op=='&' else val(x)
                    rem=free&~covered
                    y=sub(r,badl|rem)
                    if y is not None:return (op,x,y)
                    for j in bits(rem):
                        t=cover(extra|1<<j)
                        if t is not None:return t
                    return None
                t=cover(0)
                if t is not None:return t
        return None
    return rec(cap,f,one^f)


def exact(m, ports, pats, targets, signed, stats=None, fallback=None, quotient=True):
    """Sound complete wrapper: optional UNSAT proves exact UNSAT; successful
    padding proves SAT; otherwise exact solver. Never infer UNSAT from failed graft.
    """
    if stats is None:stats=Counter()
    if fallback is None:
        # repo: the integrated adaptive phase-first mode (production local_blocks underneath)
        fallback=lambda: adaptive_completion(m,ports,pats,targets,signed,stats)
    if signed:
        _,_,dom,clauses=phase_problem(m,ports,pats,targets)
        if next(phase_domains(dom,clauses),None) is None:
            stats['phase_prescreen']+=1;return None
    t=optional(m,ports,pats,targets,signed,stats,quotient)
    if t is None:stats['optional_unsat']+=1;return None
    counts=Counter(tuple(range(m))+tuple(m+i for i in ports));used=Counter()
    def walk(u):
        if u[0]=='x':used[u[1]]+=1
        else:walk(u[1]);walk(u[2])
    walk(t);spare=tuple((counts-used).elements());cs,f,one=columns(m,ports,pats,targets)
    assert not used-counts and value(t,cs,one)==f
    w=graft(t,spare,cs,one,signed)
    if w is not None:
        stats['optional_lift']+=1;check_tree(w,m,ports,pats,targets,signed);return w
    stats['fallback']+=1;return fallback()



def completion(m, ports, pats, targets, signed, stats=None, module_filter=True):
    """Completion-solver contract of ordered_quotient_core.make_completion ('bounded-multiplicity' mode): optional-leaf
    solver, padded by graft; failed padding falls back to the exact adaptive phase-first / production solver."""
    if m + len(ports) == 0:
        return None
    return exact(m, ports, pats, targets, signed, stats)

def checks(n=600):
    rng=Random(118226);stats=Counter();start=perf_counter()
    for j in range(n):
        m=rng.randrange(3);q=rng.randrange(1,7-m);r=rng.randrange(1,q+1);p=tuple(rng.randrange(r) for _ in range(q));ps=tuple(i for i in range(1<<r) if rng.random()<.7) or (0,);sg=bool(j%2)
        cs,_,one=columns(m,p,ps,(0,)*len(ps));cols=tuple(cs[i] for i in tuple(range(m))+tuple(m+i for i in p));L=len(cols)
        full=formula_columns(tuple(sorted(cols)),one,sg)
        allf=set().union(*(formula_columns(tuple(sorted(cols[i] for i in range(L) if S>>i&1)),one,sg) for S in range(1,1<<L)))
        f=rng.choice(sorted(allf)) if j%3 else rng.randrange(one+1);sm=(1<<(1<<m))-1;ts=tuple(f>>(i*(1<<m))&sm for i in range(len(ps)))
        w=optional(m,p,ps,ts,sg,stats);assert bool(w)==(f in allf),(m,p,ps,ts,sg)
        if w:assert value(w,cs,one)==f
        w=exact(m,p,ps,ts,sg,stats);assert bool(w)==(f in full),(m,p,ps,ts,sg)
        if w:check_tree(w,m,p,ps,ts,sg)
    print('checks',n,'seconds',round(perf_counter()-start,3),dict(stats),flush=True)


def bench(cap=.2):
    import signal
    from regional_root_bench import instances,Deadline,alarm
    from regional_phase_extra_bench import cases
    old=signal.signal(signal.SIGALRM,alarm);C=Counter();T=Counter();changes=[]
    jobs=[(m,p,ps,ts,sg,k) for m,p,ps,ts,sg,k in instances() if sg]+[(m,p,ps,ts,True,k) for m,p,ps,ts,k in cases()]
    try:
        for j,(m,p,ps,ts,sg,k) in enumerate(jobs):
            result={}
            for mode in ('phase','optional'):
                stats=Counter();start=perf_counter();signal.setitimer(signal.ITIMER_REAL,cap)
                try:
                    w=phase_first(m,p,ps,ts,stats) if mode=='phase' else exact(m,p,ps,ts,sg,stats)
                    status='sat' if w else 'unsat'
                    if w:check_tree(w,m,p,ps,ts,sg)
                    if k:assert w
                except Deadline:status='timeout'
                finally:signal.setitimer(signal.ITIMER_REAL,0)
                dt=perf_counter()-start;result[mode]=(status,round(dt,5));C[mode,status]+=1;T[mode]+=dt
                for a,b in stats.items():C[mode,a]+=b
            assert len({x[0] for x in result.values() if x[0]!='timeout'})<=1
            if result['phase'][0]!=result['optional'][0]:changes.append((j,result))
        print('bench',dict(T),dict(C),'changes',changes,flush=True)
    finally:signal.signal(signal.SIGALRM,old)
if __name__=='__main__':
    import sys
    checks()
    if '--bench' in sys.argv:bench()
