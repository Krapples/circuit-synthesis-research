"""Compare existing FPT solver with exact module preprocessing.
Keep module_contraction.py and previous FPT modules beside this script.
"""
from collections import Counter
from time import perf_counter
from fast_readonce_fpt import FullPortFastSolver
from module_contraction import simplify,expand,essential,brute

class ReducedSolver:
    def __init__(self):self.solvers={};self.stats=Counter()
    def solve(self,n,f,s):
        m,g,trace=simplify(n,f)
        self.stats['queries']+=1;self.stats['reduced_queries']+=bool(trace);self.stats['eliminated_inputs']+=len(trace)
        if m not in self.solvers:self.solvers[m]=FullPortFastSolver(m)
        return self.solvers[m].solve(g,s)


def run(jobs):
    solvers={};t=perf_counter();base=[]
    for n,f,s in jobs:
        if n not in solvers:solvers[n]=FullPortFastSolver(n)
        base.append(solvers[n].solve(f,s))
    btime=perf_counter()-t;st=Counter()
    for sol in solvers.values():st.update(sol.stats)
    red=ReducedSolver();t=perf_counter();new=[red.solve(*j) for j in jobs];rtime=perf_counter()-t
    assert base==new
    newst=Counter()
    for sol in red.solvers.values():newst.update(sol.stats)
    print('jobs',len(jobs),'sat',sum(base),'baseline',btime,dict(st),'reduced',rtime,dict(newst),dict(red.stats),flush=True)
    return new

if __name__=='__main__':
    jobs=[];want=[]
    for n,b in ((2,4),(3,4)):
        known=brute(n,b,'counted')
        for f in range(1,1<<(1<<n)):
            if not essential(n,f):continue
            for s in range(b-n+2):jobs.append((n,f,s));want.append(known.get(f,100)<=n-1+s)
    assert run(jobs)==want
    jobs=[]
    for core in (0xe8,0x96,0xca,0x16):
        for step in (('pair',0,1,3),('peel',0,1,0)):
            f=expand(4,core,step)
            for s in range(3):jobs.append((4,f,s))
    run(jobs)
