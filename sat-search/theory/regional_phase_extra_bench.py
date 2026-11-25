"""Second signed stress workload, heavier provider repetition. Unix deadlines.
Run from the directory with the other research prototypes.
"""
from regional_phase_first import phase_first
from regional_production_adapter import local_cover  # production local_blocks (was prototype regional_order_completion)
from regional_production_adapter import check_tree
from regional_padding import columns
try:
    from regional_root_bench import Deadline,alarm
except ImportError:  # prototype bench driver not in the repo; cases() is still importable
    class Deadline(Exception):pass
    def alarm(*a):raise Deadline()
from random import Random
from time import perf_counter
from collections import Counter
import signal

def cases():
    r=Random(35719)
    for j in range(36):
        m=j%3;q=8+j%5;d=2+j%3;k=q-d
        p=tuple(range(k))+tuple(r.randrange(k) for _ in range(d))
        ps=tuple(sorted(r.sample(range(1<<k),min(64,1<<k))))
        cs,_,one=columns(m,p,ps,(0,)*len(ps));cols=[cs[i]^(one if r.randrange(2) else 0) for i in tuple(range(m))+tuple(m+i for i in p)]
        while len(cols)>1:
            a=cols.pop(r.randrange(len(cols)));b=cols.pop(r.randrange(len(cols)));cols.append(a&b if r.randrange(2) else a|b)
        f=cols[0];known=j%3!=2
        if not known:f^=1<<r.randrange(len(ps)*(1<<m))
        sm=(1<<(1<<m))-1;ts=tuple(f>>(i*(1<<m))&sm for i in range(len(ps)))
        yield m,p,ps,ts,known

def run(cap=.2):
    old=signal.signal(signal.SIGALRM,alarm);out=Counter();times=Counter();changes=[]
    try:
        for j,(m,p,ps,ts,known) in enumerate(cases()):
            res={}
            for mode in ('base','phase'):
                st=Counter();T=perf_counter();signal.setitimer(signal.ITIMER_REAL,cap)
                try:
                    w=phase_first(m,p,ps,ts,st) if mode=='phase' else local_cover(m,p,ps,ts,True,st,port_first=True)
                    if w:check_tree(w,m,p,ps,ts,True)
                    if known:assert w
                    v='sat' if w else 'unsat'
                except Deadline:v='timeout'
                finally:signal.setitimer(signal.ITIMER_REAL,0)
                dt=perf_counter()-T;out[mode,v]+=1;times[mode]+=dt;res[mode]=(v,round(dt,5));out[mode,'phase_reject']+=st['phase_reject'];out[mode,'rec']+=st['rec']
            assert len({v[0] for v in res.values() if v[0]!='timeout'})<=1
            if res['base'][0]!=res['phase'][0]:changes.append((j,res))
        print('extra',dict(out),dict(times),'changes',changes,flush=True)
    finally:signal.signal(signal.SIGALRM,old)
if __name__=='__main__':run()
