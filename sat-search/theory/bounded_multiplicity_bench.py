"""Fresh seeded regional bounded-multiplicity benchmark and extra oracle tests.
Unix deadlines; use separate workers on Windows. No production code.
"""
from regional_bounded_multiplicity import *
try:
    from regional_root_bench import Deadline,alarm
except ImportError:  # prototype bench driver not in the repo; oracle checks still run
    class Deadline(Exception):pass
    def alarm(*a):raise Deadline()
import signal

def extra_checks(n=800):
    rng=Random(20261126);stats=Counter();start=perf_counter()
    for j in range(n):
        m=rng.randrange(3);q=rng.randrange(1,7-m);r=rng.randrange(1,q+1);p=tuple(rng.randrange(r)*2+1 for _ in range(q));ids=sorted(set(p));ps=tuple(sum((i>>k&1)<<a for k,a in enumerate(ids)) for i in range(1<<len(ids)) if rng.random()<.75) or (0,);sg=bool(j%2)
        ps=list(ps);rng.shuffle(ps);ps=tuple(ps);ts0=tuple(ANY if rng.random()<.3 else 0 for _ in ps)
        cs,_,one=columns(m,p,ps,ts0);cols=tuple(cs[i] for i in tuple(range(m))+tuple(m+i for i in p));L=len(cols)
        full=formula_columns(tuple(sorted(cols)),one,sg)
        allf=set().union(*(formula_columns(tuple(sorted(cols[i] for i in range(L) if S>>i&1)),one,sg) for S in range(1,1<<L)))
        f=rng.choice(sorted(allf)) if j%3 else rng.randrange(one+1);sm=(1<<(1<<m))-1;it=iter(range(sum(t!=ANY for t in ts0)));ts=tuple(ANY if t==ANY else (f>>(next(it)*(1<<m)))&sm for t in ts0)
        w=optional(m,p,ps,ts,sg,stats);assert bool(w)==(f in allf),(m,p,ps,ts,sg)
        if w:assert value(w,cs,one)==f
        w=exact(m,p,ps,ts,sg,stats);assert bool(w)==(f in full),(m,p,ps,ts,sg)
        if w:check_tree(w,m,p,ps,ts,sg)
    print('extra oracle',n,round(perf_counter()-start,3),dict(stats),flush=True)

def cases(n=80):
    rng=Random(4917632)
    for j in range(n):
        m=j%3;q=6+j%7;r=max(2,q-(j%5));p=tuple(range(r))+tuple(rng.randrange(r) for _ in range(q-r));ps=tuple(sorted(rng.sample(range(1<<r),min(64,1<<r))))
        # all signed, diverse random generated trees, half perturbed
        cs,_,one=columns(m,p,ps,(0,)*len(ps));cols=[cs[i]^(one if rng.randrange(2) else 0) for i in tuple(range(m))+tuple(m+i for i in p)]
        while len(cols)>1:
            a=cols.pop(rng.randrange(len(cols)));b=cols.pop(rng.randrange(len(cols)));cols.append(a&b if rng.randrange(2) else a|b)
        f=cols[0];known=bool(j%2)
        if not known:f^=1<<rng.randrange(len(ps)*(1<<m))
        sm=(1<<(1<<m))-1;ts=tuple(f>>(i*(1<<m))&sm for i in range(len(ps)))
        yield m,p,ps,ts,known

def fresh(cap=.2,n=80):
    old=signal.signal(signal.SIGALRM,alarm);C=Counter();T=Counter();changes=[];matched=Counter();matched_times=Counter()
    try:
        for j,(m,p,ps,ts,known) in enumerate(cases(n)):
            result={}
            for mode in ('phase','optional'):
                stats=Counter();start=perf_counter();signal.setitimer(signal.ITIMER_REAL,cap)
                try:
                    w=phase_first(m,p,ps,ts,stats) if mode=='phase' else exact(m,p,ps,ts,True,stats)
                    status='sat' if w else 'unsat'
                    if w:check_tree(w,m,p,ps,ts,True)
                    if known:assert w
                except Deadline:status='timeout'
                finally:signal.setitimer(signal.ITIMER_REAL,0)
                dt=perf_counter()-start;result[mode]=(status,round(dt,5));C[mode,status]+=1;T[mode]+=dt
                for a,b in stats.items():C[mode,a]+=b
            assert len({x[0] for x in result.values() if x[0]!='timeout'})<=1
            if result['phase'][0]!=result['optional'][0]:changes.append((j,result))
            if all(v[0]!='timeout' for v in result.values()):
                matched['count']+=1
                for mode,(_,dt) in result.items():matched_times[mode]+=dt
        print('fresh',dict(T),dict(C),'matched',dict(matched),dict(matched_times),'changes',changes,flush=True)
    finally:signal.signal(signal.SIGALRM,old)
if __name__=='__main__':
    extra_checks();fresh()

def capacity_checks(n=500):
    """For mixed labels, cap each raw provider by number of opposite-label
    pairs it distinguishes (directional for monotone). Independent oracle.
    If a repeated signed provider's cap shrinks, any reduced witness pads.
    """
    rng=Random(28716);S=Counter();start=perf_counter()
    for j in range(n):
        L=rng.randrange(2,7);r=rng.randrange(1,L+1);p=tuple(rng.randrange(r) for _ in range(L));ps=tuple(i for i in range(1<<r) if rng.random()<.65) or (0,);sg=bool(j%2)
        cs,_,one=columns(0,p,ps,(0,)*len(ps));cols=tuple(cs[i] for i in p)
        if one<3:continue
        full=formula_columns(tuple(sorted(cols)),one,sg)
        f=rng.choice(sorted(full)) if j%3 else rng.randrange(one+1)
        if f in (0,one):continue
        cnt=Counter(p);cap={i:min(c,(f&cs[i]).bit_count()*((one^f)&(one^cs[i])).bit_count()+( (f&(one^cs[i])).bit_count()*((one^f)&cs[i]).bit_count() if sg else 0)) for i,c in cnt.items()}
        def optset(p):
            return set().union(*(formula_columns(tuple(sorted(cs[p[i]] for i in range(len(p)) if z>>i&1)),one,sg) for z in range(1,1<<len(p))))
        new=tuple(i for i,c in cap.items() for _ in range(c))
        assert (f in optset(p))==(f in optset(new))
        shrunk=any(cap[i]<c for i,c in cnt.items());S['checked']+=1;S['shrunk']+=shrunk
        if sg and any(c>=2 and cap[i]<c for i,c in cnt.items()):
            assert (f in optset(new))==(f in full)
            S['exact_equivalence']+=1
    print('capacity oracle',dict(S),'seconds',round(perf_counter()-start,3),flush=True)
