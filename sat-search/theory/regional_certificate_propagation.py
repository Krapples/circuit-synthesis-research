"""Necessary certificate constraints for fixed literal phases. Passing is unknown.
Repo version: production local_blocks underneath; certificate_completion() is the opt-in
'phase-certificate' completion mode (adaptive phase-first with this prescreen on each monotone query).
Uses occurrence columns, including duplicates. Experimental phase-first wrapper.
"""
from collections import Counter
from random import Random
from time import perf_counter
from regional_padding import columns
from regional_phase_first import phase_first
from regional_production_adapter import local_cover  # production local_blocks (was prototype regional_order_completion)
from conditional_provider import formula_columns
from regional_production_adapter import check_tree

def bits(x):
    while x:
        b=x&-x;x^=b;yield b.bit_length()-1

def compatible(A,O,L):
    def components(G,S):
        out=[]
        while S:
            b=S&-S;C=b;todo=b
            while todo:
                i=(todo&-todo).bit_length()-1;todo^=1<<i
                d=G[i]&S&~C;C|=d;todo|=d
            out.append(C);S^=C
        return out
    def rec(S):
        if S.bit_count()<2:return True
        for G in (A,O):
            cs=components(G,S)
            if len(cs)>1:return all(rec(c) for c in cs)
        return False
    return rec((1<<L)-1)

def prescreen(cols,f,one,reduce_rows=True):
    n=len(cols);full=(1<<n)-1;P=set();N=set()
    for j in bits(one):
        mask=sum((1<<i) for i,c in enumerate(cols) if c>>j&1)
        if f>>j&1:P.add(mask)
        else:N.add(full^mask)
    if 0 in P or 0 in N:return False
    if not P or not N:return True
    def minimal(S):
        out=[]
        for a in sorted(S,key=lambda b:(b.bit_count(),b)):
            if not any(b&a==b for b in out):out.append(a)
        return out
    P=minimal(P) if reduce_rows else list(P);N=minimal(N) if reduce_rows else list(N);fp=[0]*len(P);fn=[0]*len(N);A=[0]*n;O=[0]*n
    while True:
        changed=False
        for i,p in enumerate(P):
            for j,q in enumerate(N):
                D=p&q
                if not D:return False
                F=fp[i]&fn[j]
                if F.bit_count()>1:return False
                if D&(D-1)==0:
                    if fp[i]&D==0:fp[i]|=D;changed=True
                    if fn[j]&D==0:fn[j]|=D;changed=True
                elif F:
                    pp=P[i]&~(fn[j]^F);qq=N[j]&~(fp[i]^F)
                    if pp!=P[i]:P[i]=pp;p=pp;changed=True
                    if qq!=N[j]:N[j]=qq;changed=True
        for forced,allowed,G,H in ((fp,P,A,O),(fn,N,O,A)):
            for k,F in enumerate(forced):
                if F&~allowed[k]:return False
                for i in bits(F):
                    if H[i]&F:return False
                    new=G[i]|(F^(1<<i))
                    if new!=G[i]:G[i]=new;changed=True
                    a=allowed[k]&~H[i]
                    if a!=allowed[k]:allowed[k]=a;changed=True
        if not changed:break
    return compatible(A,O,n)

def screen_query(m,p,ps,ts):
    cs,f,one=columns(m,p,ps,ts)
    return prescreen(tuple(cs[i] for i in tuple(range(m))+tuple(m+j for j in p)),f,one)

def solve(m,p,ps,ts,stats=None):
    if stats is None:stats=Counter()
    def local(m,p,ps,ts):
        stats['certificate_queries']+=1
        if not screen_query(m,p,ps,ts):
            stats['certificate_rejections']+=1;return None
        return local_cover(m,p,ps,ts,False,stats,port_first=True,method='witness')
    return phase_first(m,p,ps,ts,stats,solver=local)

def exclusion_cases(n=60):
    # Monotone targets made using additional repeated leaves, then ask for
    # signed read-once completion on the smaller allocation. Not all UNSAT.
    r=Random(63971)
    for j in range(n):
        k=5+j%4;m=j%3;p=tuple(range(k))+tuple(r.randrange(k) for _ in range(j%3))
        ps=tuple(sorted(r.sample(range(1<<k),min(64,1<<k))))
        cs,_,one=columns(m,p,ps,(0,)*len(ps))
        # Monotone DNF with 3-6 terms, each 2-4 independent literals.
        f=0;ids=tuple(cs)
        for _ in range(3+j%4):
            term=one
            for i in r.sample(ids,min(len(ids),2+r.randrange(3))):term&=cs[i]
            f|=term
        # Random input phases preserve structure but make phase inference relevant.
        # For partial observed patterns, transforming the observations suffices.
        flip=r.randrange(1<<k);ps=tuple(v^flip for v in ps)
        sm=(1<<(1<<m))-1;ts=tuple((f>>(i*(1<<m)))&sm for i in range(len(ps)))
        yield m,p,ps,ts,False

def checks():
    r=Random(1773);S=Counter();T=perf_counter()
    for j in range(1200):
        n=r.randrange(1,7);R=r.randrange(1,15);one=(1<<R)-1
        cs=tuple(sorted(r.randrange(one+1) for _ in range(n)))
        fs=formula_columns(cs,one,False)
        f=r.choice(sorted(fs)) if j%2==0 else r.randrange(one+1)
        yes=f in fs;ok=prescreen(cs,f,one)
        assert ok or not yes,(cs,f)
        P=list(bits(f));N=list(bits(one^f))
        base=all(any(c>>a&1 and not c>>b&1 for c in cs) for a in P for b in N) and all(any(c>>a&1 for c in cs) for a in P) and all(any(not c>>b&1 for c in cs) for b in N)
        S['cases']+=1;S['sat']+=yes;S['base_reject']+=not base;S['new_reject']+=base and not ok
    # All monotone functions on four independent leaves, with some rows
    # removed. Known answer from exhaustive formula enumeration.
    cs=(0xaaaa,0xcccc,0xf0f0,0xff00);one=65535;fs=formula_columns(cs,one,False)
    for f in range(one+1):
        if any((f & (one^c)) << (1<<i) & ~f for i,c in enumerate(cs)):continue
        for mask in (one,r.randrange(one+1)):
            cols=tuple(c&mask for c in cs);target=f&mask
            yes=any(g&mask==target for g in fs);ok=prescreen(cols,target,mask)
            assert ok or not yes
            base=all(any(c>>a&1 and not c>>b&1 for c in cols) for a in bits(target) for b in bits(mask^target)) and all(any(c>>a&1 for c in cols) for a in bits(target)) and all(any(not c>>b&1 for c in cols) for b in bits(mask^target))
            S['structured']+=1;S['structured_new_reject']+=base and not ok
    print('checks',dict(S),'seconds',round(perf_counter()-T,3),flush=True)

def bench(cap=.25,data=None):
    import signal
    from regional_root_bench import instances,Deadline,alarm
    from regional_phase_extra_bench import cases
    if data is None:data=[(m,p,ps,ts,k) for m,p,ps,ts,sg,k in instances() if sg]+list(cases())
    old=signal.signal(signal.SIGALRM,alarm);C=Counter();times=Counter();matched=Counter();change=[]
    try:
        for j,(m,p,ps,ts,known) in enumerate(data):
            res={};dts={}
            for mode,fn in [('base',phase_first),('certificate',solve)]:
                S=Counter();T=perf_counter();signal.setitimer(signal.ITIMER_REAL,cap)
                try:
                    w=fn(m,p,ps,ts,S)
                    if w:check_tree(w,m,p,ps,ts,True)
                    assert w or not known
                    status='sat' if w else 'unsat'
                except Deadline:status='timeout'
                finally:signal.setitimer(signal.ITIMER_REAL,0)
                dt=perf_counter()-T;res[mode]=status;dts[mode]=dt;times[mode]+=dt;C[mode,status]+=1
                for k,v in S.items():C[mode,k]+=v
            assert len(set(res.values())-{'timeout'})<=1
            if 'timeout' not in res.values():matched.update(dts)
            if res['base']!=res['certificate']:change.append((j,res))
        for mode in times:print(mode,dict((k[1],v) for k,v in C.items() if k[0]==mode),'elapsed',round(times[mode],4),'matched',round(matched[mode],4),flush=True)
        print('changed',change,flush=True)
    finally:signal.signal(signal.SIGALRM,old)

if __name__=='__main__':
    import sys
    checks()
    if '--bench' in sys.argv:bench()
    if '--fresh' in sys.argv:
        from bounded_multiplicity_bench import cases
        bench(.2,list(cases()))
    if '--exclusions' in sys.argv:bench(.2,list(exclusion_cases()))


# ---------------------------------------------------------------- production completion mode
PRESCREEN_LABEL_CAP = 1024    # propagation is quadratic in reduced positive x negative rows; skip it above this


def certificate_completion(m, ports, pats, targets, signed, stats=None, module_filter=True):
    """Completion-solver contract of ordered_quotient_core.make_completion ('phase-certificate' mode). Same routing as
    regional_phase_first.adaptive_completion; each monotone phase-class query is first screened by the necessary
    certificate test (a rejection is sound UNSAT for that class; passing means unknown) and only then sent to the
    production local_blocks."""
    from regional_block_completion import local_blocks
    from regional_phase_first import phase_rule, PRODUCTION_FLAGS
    from two_sharing_core import ANY
    if signed and m + len(ports) > 0 and phase_rule(m, ports, targets):
        if stats is not None:
            stats['phase_first_calls'] += 1

        def mono(mm, p, ps, ts):
            labels = sum(1 for t in ts if t != ANY) << mm
            if labels <= PRESCREEN_LABEL_CAP and mm + len(p) > 0:
                if stats is not None:
                    stats['certificate_queries'] += 1
                if not screen_query(mm, p, ps, ts):
                    if stats is not None:
                        stats['certificate_rejections'] += 1
                    return None
            return local_blocks(mm, p, ps, ts, False, stats, module_filter, **PRODUCTION_FLAGS)
        return phase_first(m, ports, pats, targets, stats, mono)
    return local_blocks(m, ports, pats, targets, signed, stats, module_filter, **PRODUCTION_FLAGS)
