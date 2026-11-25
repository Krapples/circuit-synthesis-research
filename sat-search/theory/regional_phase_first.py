"""Exact phase-first signed regional completion, optional experimental backend.
All allocated leaves are used exactly once (port multiplicities allowed).
Free NOT only. Input slices exact or ANY. No production source required.
Run --bench for bounded Unix stress comparison; use worker deadlines on Windows.
"""
from collections import Counter
from itertools import product
from time import perf_counter
from random import Random
from regional_production_adapter import local_cover  # production local_blocks (was prototype regional_order_completion)
from regional_production_adapter import check_tree
from regional_padding import columns
from conditional_provider import formula_columns
from two_sharing_core import ANY

# Three sign-availability classes: 1=positive, 2=negative, 4=both.
# A positive literal can distinguish row a from row b when a_i=1,b_i=0.
# A mixed-phase repeated provider can distinguish in either direction.

def phase_problem(m, ports, pats, targets):
    ids=tuple(range(m))+tuple(m+i for i in sorted(set(ports)))
    cnt=Counter(tuple(range(m))+tuple(m+i for i in ports))
    cs,f,one=columns(m,ports,pats,targets)
    counts=tuple(cnt[i] for i in ids)
    dom=tuple(7 if n>1 else 3 for n in counts)
    pos=[];neg=[]
    for j in range(one.bit_length()):
        a=sum(((cs[i]>>j)&1)<<k for k,i in enumerate(ids))
        (pos if f>>j&1 else neg).append(a)
    pos=set(pos);neg=set(neg);full=(1<<len(ids))-1
    # Clause (a,b): at least one positive-capable class in a OR
    # negative-capable class in b. Endpoint clauses ensure no constant leaves.
    clauses={(a&~b,b&~a) for a in pos for b in neg}
    clauses.update((a,full^a) for a in pos)
    clauses.update((full^b,b) for b in neg)
    # Subsumption reduces clauses (same class may satisfy either polarity).
    minimal=[]
    for a,b in sorted(clauses,key=lambda t:(t[0].bit_count()+t[1].bit_count(),t)):
        if not any((u&~a)==0 and (v&~b)==0 for u,v in minimal):minimal.append((a,b))
    return ids,counts,dom,tuple(minimal)

def phase_domains(dom,clauses,stats=None):
    """Enumerate exactly the feasible sign-availability classes. Domain masks
    encode allowed values among 1,2,4; unit propagation is finite-domain SAT.
    """
    D=len(dom)
    compiled=[]
    for a,b in clauses:
        compiled.append(tuple((j,(5 if a>>j&1 else 0)|(6 if b>>j&1 else 0)) for j in range(D) if (a|b)>>j&1))
    def rec(d):
        d=list(d)
        while True:
            changed=False;active=[]
            for cl in compiled:
                live=[]
                for j,mask in cl:
                    if not d[j]&~mask:break # clause always satisfied
                    if d[j]&mask:live.append((j,mask))
                else:
                    if not live:return
                    if len(live)==1:
                        j,mask=live[0];d[j]&=mask;changed=True
                    else:active.append(live)
            if not changed:break
        if stats is not None:stats['phase_nodes']+=1
        if not active:
            yield from product(*(tuple(v for v in (4,1,2) if v&mask) for mask in d));return
        weight=Counter(j for cl in active for j,_ in cl)
        j=max((j for j in weight if d[j].bit_count()>1),key=lambda j:(weight[j],-d[j].bit_count()))
        for v in (4,1,2):
            if d[j]&v:
                dd=d.copy();dd[j]=v;yield from rec(dd)
    yield from rec(dom)

def phase_first(m,ports,pats,targets,stats=None,solver=None):
    """Exact: all satisfying phase-count vectors, then monotone local solve.
    The solver callback must be exact, use all allocated occurrences, and
    return a tree or None. Exceptions/timeouts must propagate, not become UNSAT.
    """
    if stats is None:stats=Counter()
    if solver is None:
        def solver(m,ports,pats,targets):
            return local_cover(m,ports,pats,targets,False,stats,port_first=True,method='witness')
    if m+len(ports)==0:return None
    ids,counts,dom,clauses=phase_problem(m,ports,pats,targets)
    stats['phase_clauses']+=len(clauses)
    before=stats['monotone_calls']
    for state in phase_domains(dom,clauses,stats):
        stats['phase_classes']+=1
        flip=sum((state[i]==2)<<i for i in range(m))
        ts=tuple(t if t==ANY or not flip else sum(((t>>(a^flip))&1)<<a for a in range(1<<m)) for t in targets)
        # Recode positive and negative occurrences as distinct virtual ports.
        # For mixed-phase groups the exact multiplicity remains to be chosen.
        for ns in product(*( (0,) if s==1 else (c,) if s==2 else range(1,c) for s,c in zip(state[m:],counts[m:]))):
            refs=[];pp=[]
            for i,c,n in zip(ids[m:],counts[m:],ns):
                for phase,k in ((0,c-n),(1,n)):
                    if k:pp.extend([len(refs)]*k);refs.append((i-m,phase))
            ps=tuple(sum((((p>>i)&1)^phase)<<j for j,(i,phase) in enumerate(refs)) for p in pats)
            stats['monotone_calls']+=1
            w=solver(m,tuple(pp),ps,ts)
            if w is not None:
                def lift(t):
                    if t[0]=='x':
                        assert not t[2]
                        i=t[1]
                        if i<m:return ('x',i,bool(flip>>i&1))
                        j,phase=refs[i-m];return ('x',m+j,bool(phase))
                    return (t[0],*(lift(c) for c in t[1:]))
                out=lift(w);check_tree(out,m,ports,pats,targets,True);return out
    if stats['monotone_calls']==before:stats['phase_reject']+=1
    return None

def checks(n=600):
    rng=Random(20261125);T=perf_counter();C=Counter()
    for j in range(n):
        m=rng.randrange(3);q=rng.randrange(1,7-m);r=rng.randrange(1,q+1)
        ports=tuple(rng.randrange(r)*2+1 for _ in range(q));ids=tuple(sorted(set(ports)))
        pats=tuple(sum((b>>i&1)<<k for i,k in enumerate(ids)) for b in range(1<<len(ids)) if rng.random()<.7) or (0,)
        cs,_,one=columns(m,ports,pats,(0,)*len(pats));fs=formula_columns(tuple(sorted(cs[i] for i in tuple(range(m))+tuple(m+i for i in ports))),one,True)
        f=rng.choice(sorted(fs)) if j%2==0 else rng.randrange(one+1)
        sm=(1<<(1<<m))-1;ts=tuple(f>>(i*(1<<m))&sm if rng.random()<.85 else ANY for i in range(len(pats)))
        yes=any(all(t==ANY or (v>>(i*(1<<m))&sm)==t for i,t in enumerate(ts)) for v in fs)
        ids,counts,dom,clauses=phase_problem(m,ports,pats,ts)
        # Direct enumeration independent of propagation.
        want={s for s in product(*( (1,2,4) if c>1 else (1,2) for c in counts)) if all(any((v&5 and a>>i&1) or (v&6 and b>>i&1) for i,v in enumerate(s)) for a,b in clauses)}
        got=list(phase_domains(dom,clauses));assert len(got)==len(set(got)) and set(got)==want
        st=Counter();w=phase_first(m,ports,pats,ts,st);assert (w is not None)==yes,(m,ports,pats,ts,yes,st)
        C.update(st);C['queries']+=1;C['sat']+=yes
    print('oracle checks',dict(C),'seconds',round(perf_counter()-T,3),flush=True)

def bench(cap=.3):
    import signal
    from regional_root_bench import instances,Deadline,alarm
    old=signal.signal(signal.SIGALRM,alarm);C=Counter();times=Counter();changes=[]
    try:
        for j,(m,p,ps,ts,sg,known) in enumerate(instances()):
            if not sg:continue
            result={}
            for mode in ('signed','phase-first'):
                st=Counter();T=perf_counter();signal.setitimer(signal.ITIMER_REAL,cap)
                try:
                    w=phase_first(m,p,ps,ts,st) if mode=='phase-first' else local_cover(m,p,ps,ts,True,st,port_first=True,method='witness')
                    if w:check_tree(w,m,p,ps,ts,True)
                    if known:assert w
                    status='sat' if w else 'unsat'
                except Deadline:status='timeout'
                finally:signal.setitimer(signal.ITIMER_REAL,0)
                dt=perf_counter()-T;C[mode,status]+=1;times[mode]+=dt
                for k,v in st.items():C[mode,k]+=v
                result[mode]=(status,round(dt,5),st['monotone_calls'])
            assert len({v[0] for v in result.values() if v[0]!='timeout'})<=1
            if result['signed'][0]!=result['phase-first'][0]:changes.append((j,result))
        for mode,t in times.items():print(mode,round(t,4),{k[1]:v for k,v in C.items() if k[0]==mode},flush=True)
        print('changed decisions',changes,flush=True)
    finally:signal.signal(signal.SIGALRM,old)

if __name__=='__main__':
    import sys
    checks()
    if '--bench' in sys.argv:bench()


# ---------------------------------------------------------------- production completion mode
PRODUCTION_FLAGS = dict(port_first=True, witness_cover=True, row_quotient=True)
PHASE_LABEL_CAP = 4096      # distinction clauses are quadratic in labelled rows; fall back above this


def phase_rule(m, ports, targets):
    """Activation rule (experiments/phase_first_production.py): phase-first unless the query is wide (m >= 4) with no
    repeated provider, and only while the labelled table is small enough for the clause build."""
    labels = sum(1 for t in targets if t != ANY) << m
    repeats = len(ports) - len(set(ports))
    return labels <= PHASE_LABEL_CAP and not (repeats == 0 and m >= 4)


def adaptive_completion(m, ports, pats, targets, signed, stats=None, module_filter=True):
    """Completion-solver contract of ordered_quotient_core.make_completion: signed queries passing phase_rule go to
    phase-first over the production monotone solver; everything else goes to the production solver directly."""
    from regional_block_completion import local_blocks
    if signed and m + len(ports) > 0 and phase_rule(m, ports, targets):
        if stats is not None:
            stats['phase_first_calls'] += 1
        mono = lambda mm, p, ps, ts: local_blocks(mm, p, ps, ts, False, stats, module_filter, **PRODUCTION_FLAGS)
        return phase_first(m, ports, pats, targets, stats, mono)
    return local_blocks(m, ports, pats, targets, signed, stats, module_filter, **PRODUCTION_FLAGS)
