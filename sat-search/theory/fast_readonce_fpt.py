"""Plug-in exact no-port local solver and NOT-budget prescreen.
Run alongside readonce_not_cost.py and compressed_signed_fpt.py.
"""
from collections import Counter
from time import perf_counter
from math import inf
from compressed_signed_fpt import CompressedSolver
from complete_signed_fpt import ANY,NC,brute,essential
from readonce_not_cost import costs

class FastReadOnceSolver(CompressedSolver):
    full_port_fast = False
    def local(self,S,ports,patterns,targets,notbudget):
        exact=set(targets)-{ANY,NC,0,self.ONE}
        if not ports:
            self.stats['fast_local']+=1
            if not S or 0 in targets or self.ONE in targets or len(exact)>1:return False
            if not exact:return True
            f=next(iter(exact))
            active=sum(1<<i for i in range(self.n) if self.res(f,1<<i,0)!=self.res(f,1<<i,1<<i))
            return active==S and costs(self.n,f)[0]<=notbudget
        if self.full_port_fast and len(set(ports))==len(ports):
            # Treat distinct port inputs as independent variables whenever the
            # reachable patterns supply the entire exact local truth table.
            q=len(ports);table={};valid=True
            for pat,t in zip(patterns,targets):
                a=sum((pat>>i&1)<<j for j,i in enumerate(ports))
                if t in (ANY,NC):continue
                if a in table and table[a]!=t:return False
                table[a]=t
            if len(table)==1<<q:
                for pat,t in zip(patterns,targets):
                    a=sum((pat>>i&1)<<j for j,i in enumerate(ports))
                    if t==NC and table[a] in (0,self.ONE):return False
                pos=[i for i in range(self.n) if S>>i&1];u=len(pos)
                f=sum((table[a>>u]>>sum((a>>j&1)<<i for j,i in enumerate(pos))&1)<<a for a in range(1<<(u+q)))
                self.stats['full_port_fast']+=1
                full=(1<<(u+q))-1
                if not all(any((f>>a&1)!=(f>>(a|1<<i)&1) for a in range(full+1) if not a>>i&1) for i in range(u+q)):return False
                return costs(u+q,f)[0]<=notbudget
        if any(costs(self.n,f)[0]>notbudget for f in exact):
            self.stats['not_cost_reject']+=1;return False
        return super().local(S,ports,patterns,targets,notbudget)

class FullPortFastSolver(FastReadOnceSolver):
    full_port_fast=True

def check():
    jobs=[]
    for n,b in ((2,4),(3,4)):
        known=brute(n,b);orig=CompressedSolver(n)
        for f in range(1,orig.ONE):
            if essential(f,orig):
                for s in range(b-n+2):jobs.append((n,f,s,known.get(f,100)<=n-1+s))
    for cls in (CompressedSolver,FastReadOnceSolver,FullPortFastSolver):
        stats=Counter();t=perf_counter();sols={}
        for n,f,s,want in jobs:
            if n not in sols:sols[n]=cls(n)
            got=sols[n].solve(f,s)
            assert got==want,(cls.__name__,n,f,s,got,want)
        for sol in sols.values():stats.update(sol.stats)
        print(cls.__name__,len(jobs),dict(stats),'seconds',perf_counter()-t,flush=True)

if __name__=='__main__':check()
