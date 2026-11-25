"""Experimental improvements to complete_signed_fpt.Solver.
Dead-provider projection; orientation components; bounded port endpoint profiles.
Run from same directory as complete_signed_fpt.py. Standard library.
"""
from functools import lru_cache
from itertools import product
from collections import Counter
from complete_signed_fpt import Solver, ANY, NC, essential, brute
from time import monotonic

@lru_cache(None)
def endpoint_columns(ports,pats):
    """All signed read-once functions on subsets of occurrence slots, and constants."""
    ones=(1<<len(pats))-1
    leaves=[sum((p>>j&1)<<i for i,p in enumerate(pats)) for j in ports]
    @lru_cache(None)
    def rec(S):
        if S.bit_count()==1:
            v=leaves[S.bit_length()-1];return frozenset((v,v^ones))
        low=S&-S;sub=(S-1)&S;out=set()
        while sub:
            if sub&low:
                for a in rec(sub):
                    for b in rec(S^sub):
                        out.update((a&b,a|b,(a&b)^ones,(a|b)^ones))
            sub=(sub-1)&S
        return frozenset(out)
    out={0,ones}
    for S in range(1,1<<len(ports)):out.update(rec(S))
    return frozenset(out)

def profiles(ports,pats,forced):
    """Superset of attainable range profiles; 0,1,2 mean constant 0, constant 1, nonconstant."""
    C=endpoint_columns(ports,pats);ones=(1<<len(pats))-1
    for lo in C:
        if lo&forced:continue
        for hi in C:
            if lo&~hi or forced&~hi:continue
            yield tuple(1 if lo>>i&1 else 2 if hi>>i&1 else 0 for i in range(len(pats)))

class CompressedSolver(Solver):
    force_endpoints = False
    def orientations(self,S,options,q):
        """options[j]=(v,lo,hi) for forced nonconstant slices, None otherwise."""
        signs={};adj={j:[] for j,o in enumerate(options) if o is not None}
        for j,o in enumerate(options):
            if o is None:continue
            v=o[0]
            for i in range(self.n):
                if not S>>i&1:continue
                a=self.res(v,1<<i,0);b=self.res(v,1<<i,1<<i)
                if a==b:continue
                if a&~b and b&~a:return
                neg=int(bool(a&~b))
                if i in signs:
                    k,t=signs[i];adj[j].append((k,t^neg));adj[k].append((j,t^neg))
                else:signs[i]=j,neg
        bits={};parts=[]
        for j in adj:
            if j in bits:continue
            bits[j]=0;todo=[j];part=[]
            while todo:
                k=todo.pop();part.append(k)
                for l,p in adj[k]:
                    v=bits[k]^p
                    if l in bits:
                        if bits[l]!=v:return
                    else:bits[l]=v;todo.append(l)
            parts.append(part)
        if len(parts)>max(1,q):return
        for flips in product((0,1),repeat=len(parts)):
            z=bits.copy()
            for part,flip in zip(parts,flips):
                for j in part:z[j]^=flip
            yield z
    def solve(self,f,s):
        if not essential(f,self):raise ValueError('essential inputs required')
        for deg in self.degrees(s):
            r=len(deg)
            @lru_cache(None)
            def go(X,k,rem,state,left):
                self.stats['states']+=1
                un=self.M^X
                if len(self.cof(f,X))>1<<len(rem):return False
                pats=tuple(t for t,v in enumerate(state) if v!=ANY)
                if k==r:
                    ports=tuple(i for i,d in enumerate(rem) for _ in range(d))
                    return self.local(un,ports,pats,tuple(state[t] for t in pats),left)
                for S in self.subsets(un):
                    newX=X|S;opts=[];free={};forced=0
                    for j,t in enumerate(pats):
                        g=state[t];c=self.cof(g,S)
                        if len(c)>2:break
                        if len(c)==1:
                            free[j]=next(iter(c));opts.append(None)
                        else:
                            lo,hi=sorted(c)
                            v=sum((self.res(g,S,a&S)==hi)<<a for a in range(1<<self.n))
                            opts.append((v,lo,hi));forced|=1<<j
                    else:
                        for take in product(*(range(d+1) for d in rem)):
                            ports=tuple(i for i,d in enumerate(take) for _ in range(d))
                            if not(S or ports):continue
                            keep=tuple(i for i,d in enumerate(rem) if d>take[i]);newrem=tuple(rem[i]-take[i] for i in keep)+(deg[k],)
                            if len(self.cof(f,newX))>1<<len(newrem):continue
                            # Small profiles use direct enumeration. Larger ones with few
                            # ports use endpoint columns; larger q falls back for this prototype.
                            if self.force_endpoints or (len(free)>4 and len(ports)<=5):
                                ps=list(profiles(ports,pats,forced));self.stats['endpoint_calls']+=1
                            else:
                                ps=[]
                                for a in product(range(3),repeat=len(free)):
                                    z=[2]*len(pats)
                                    for j,v in zip(free,a):z[j]=v
                                    ps.append(tuple(z))
                            if not S:ps=[p for p in ps if 2 not in p]
                            for orient in self.orientations(S,opts,len(ports)):
                                for p in ps:
                                    self.stats['profiles']+=1
                                    targets=[];ns=[ANY]*(1<<len(newrem));ok=True
                                    for j,t in enumerate(pats):
                                        if j in free:
                                            h=free[j];v=p[j];target=(0,self.ONE,NC)[v]
                                            out=(h,ANY) if v==0 else (ANY,h) if v==1 else (h,h)
                                        else:
                                            v,lo,hi=opts[j]
                                            if orient[j]:v^=self.ONE;lo,hi=hi,lo
                                            target=v;out=(lo,hi)
                                        targets.append(target)
                                        base=sum((t>>i&1)<<a for a,i in enumerate(keep))
                                        for bit,g in enumerate(out):
                                            if g==ANY:continue
                                            idx=base|(bit<<len(keep))
                                            if ns[idx]!=ANY and ns[idx]!=g:ok=False;break
                                            ns[idx]=g
                                        if not ok:break
                                    if not ok:self.stats['projection_rejects']+=1;continue
                                    for used in range(left+1):
                                        if self.local(S,ports,pats,tuple(targets),used) and go(newX,k+1,newrem,tuple(ns),left-used):return True
                return False
            if go(0,0,(),(f,),s-sum(d-1 for d in deg)):return True
        return False

def check():
    from random import Random
    from signed_region_bounds import subs
    # Exact range coverage for every signed read-once formula on 2 primary + q port occurrences.
    for q in range(4):
        n=2+q;leaves=tuple(sum(((a>>i)&1)<<a for a in range(1<<n)) for i in range(n));one=(1<<(1<<n))-1
        @lru_cache(None)
        def gen(S):
            if S.bit_count()==1:
                a=leaves[S.bit_length()-1];return frozenset((a,a^one))
            out=set();low=S&-S
            for A in subs(S):
                if A in (0,S) or not A&low:continue
                for a in gen(A):
                    for b in gen(S^A):out.update((a&b,a|b))
            return frozenset(out)
        pats=tuple(range(1<<q));ports=tuple(range(q));C=endpoint_columns(ports,pats)
        possible=set(profiles(ports,pats,0));actual=set();fs=gen((1<<n)-1)
        for f in fs:
            v=[]
            for p in pats:
                s=sum(f>>(p<<2|x)&1 for x in range(4));v.append(0 if s==0 else 1 if s==4 else 2)
            v=tuple(v);actual.add(v);assert v in possible
        print('range coverage',q,'formulas',len(fs),'endpoint columns',len(C),'profiles',len(possible),'actual',len(actual),'naive',3**len(pats),flush=True)
    # Compare both original and modified solver with gate-set oracle.
    t=monotonic();total=0;old=Counter();new=Counter()
    for n,budget in ((2,4),(3,4)):
        known=brute(n,budget);orig=Solver(n);comp=CompressedSolver(n)
        for f in range(1,orig.ONE):
            if not essential(f,orig):continue
            for s in range(budget-n+2):
                want=known.get(f,100)<=n-1+s
                a=orig.solve(f,s);b=comp.solve(f,s)
                assert a==b==want,(n,f,s,a,b,want);total+=1
        old.update(orig.stats);new.update(comp.stats)
    print('queries',total,'original',old,'compressed',new,'seconds',monotonic()-t,flush=True)
    # q=4 sample of sparse control patterns
    pats=tuple(range(16));ports=(0,1,2,3)
    C=endpoint_columns(ports,pats);num=sum(1 for _ in profiles(ports,pats,0))
    print('q4 columns',len(C),'profiles',num,'naive',3**len(pats),flush=True)

if __name__=='__main__':check()
