"""Exact promotion of independently observed singleton ports to private inputs.
Complete slices or ANY, exact leaf multiplicities, monotone or free NOT.
Uses existing packed port-first solver; optionally phase-first for signed.
"""
from collections import Counter
from functools import reduce
from time import perf_counter
from random import Random
from regional_production_adapter import local_cover  # production local_blocks (was prototype regional_order_completion)
from regional_phase_first import phase_first
from regional_production_adapter import check_tree
from regional_padding import columns
from conditional_provider import formula_columns
from two_sharing_core import tree,support,ANY

def lift_axes(m,ports,pats,targets,signed,stats=None,solver=None,max_private=10):
    if stats is None:stats=Counter()
    if solver is None:solver=lambda m,p,ps,t,s:local_cover(m,p,ps,t,s,stats,port_first=True)
    mask=sum(1<<i for i in set(ports));rows={}
    for p,t in zip(pats,targets):
        if t==ANY:continue
        p&=mask
        if p in rows and rows[p]!=t:return None
        rows[p]=t
    if not rows:return solver(m,ports,pats,targets,signed)
    axes=tuple(i for i,c in sorted(Counter(ports).items()) if c==1 and all(p^(1<<i) in rows for p in rows))[:max(0,max_private-m)]
    if not axes:return solver(m,ports,pats,targets,signed)
    A=sum(1<<i for i in axes);q=len(axes);mm=m+q;pp=tuple(i for i in ports if not A>>i&1);ps=tuple(sorted({p&~A for p in rows}));W=1<<m
    ts=tuple(sum(rows[p|sum(((a>>j)&1)<<i for j,i in enumerate(axes))]<<(a*W) for a in range(1<<q)) for p in ps)
    stats['lift_queries']+=1;stats['axes']+=q
    if not pp:
        assert len(ts)==1
        stats['direct']+=1
        if support(mm,ts[0])!=(1<<mm)-1:return None
        w=tree(mm,ts[0],signed)
        if w is not None:
            def binary(t):
                if t[0]=='x':return t
                return reduce(lambda a,b:(t[0],a,b),map(binary,t[1:]))
            w=binary(w)
    else:w=solver(mm,pp,ps,ts,signed)
    if w is None:return None
    def restore(t):
        if t[0]=='x':
            i=t[1];return ('x',i if i<m else m+axes[i-m] if i<mm else m+i-mm,t[2])
        return (t[0],*(restore(c) for c in t[1:]))
    out=restore(w);check_tree(out,m,ports,pats,targets,signed);return out

def checks(n=600):
    rng=Random(5723);C=Counter();T=perf_counter()
    for j in range(n):
        m=rng.randrange(3);q=rng.randrange(1,7-m);r=rng.randrange(1,q+1);signed=bool(j%2)
        ports=tuple(rng.randrange(r)*2+1 for _ in range(q));ids=tuple(sorted(set(ports)))
        # Half are full cubes, others arbitrary observed rows.
        pats=tuple(sum((a>>i&1)<<k for i,k in enumerate(ids)) for a in range(1<<len(ids)) if j%4<2 or rng.random()<.75) or (0,)
        cs,_,one=columns(m,ports,pats,(0,)*len(pats));fs=formula_columns(tuple(sorted(cs[i] for i in tuple(range(m))+tuple(m+i for i in ports))),one,signed)
        f=rng.choice(sorted(fs)) if j%3 else rng.randrange(one+1);sm=(1<<(1<<m))-1
        ts=tuple(f>>(i*(1<<m))&sm if j%4<2 or rng.random()<.85 else ANY for i in range(len(pats)))
        yes=any(all(t==ANY or (v>>(i*(1<<m))&sm)==t for i,t in enumerate(ts)) for v in fs)
        w=lift_axes(m,ports,pats,ts,signed,C);assert (w is not None)==yes,(m,ports,pats,ts,signed)
        if w:check_tree(w,m,ports,pats,ts,signed)
    print('axis oracle',n,dict(C),'seconds',round(perf_counter()-T,3),flush=True)

def bench(cap=.3):
    import signal
    from regional_root_bench import instances,Deadline,alarm
    old=signal.signal(signal.SIGALRM,alarm);C=Counter();times=Counter();changes=[]
    try:
        for j,(m,p,ps,ts,sg,known) in enumerate(instances()):
            result={}
            for mode in ('base','lift','lift-phase') if sg else ('base','lift'):
                st=Counter();T=perf_counter();signal.setitimer(signal.ITIMER_REAL,cap)
                try:
                    def base(m,p,ps,t,s):return local_cover(m,p,ps,t,s,st,port_first=True)
                    def combined(m,p,ps,t,s):return phase_first(m,p,ps,t,st) if s else base(m,p,ps,t,s)
                    w=base(m,p,ps,ts,sg) if mode=='base' else lift_axes(m,p,ps,ts,sg,st,combined if mode=='lift-phase' else base)
                    if w:check_tree(w,m,p,ps,ts,sg)
                    if known:assert w
                    status='sat' if w else 'unsat'
                except Deadline:status='timeout'
                finally:signal.setitimer(signal.ITIMER_REAL,0)
                dt=perf_counter()-T;C[sg,mode,status]+=1;times[sg,mode]+=dt;C[sg,mode,'lift_queries']+=st['lift_queries'];C[sg,mode,'axes']+=st['axes'];C[sg,mode,'direct']+=st['direct'];result[mode]=(status,round(dt,5),st['axes'])
            assert len({v[0] for v in result.values() if v[0]!='timeout'})<=1
            if len({v[0] for v in result.values()})>1:changes.append((j,result))
        for key,t in times.items():print(key,round(t,4),{k[2]:v for k,v in C.items() if k[:2]==key},flush=True)
        print('changed decisions',changes,flush=True)
    finally:signal.signal(signal.SIGALRM,old)

if __name__=='__main__':
    import sys
    checks()
    if '--bench' in sys.argv:bench()
