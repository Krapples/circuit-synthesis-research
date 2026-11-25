"""Monotone regional FPT restriction on complete pair-irreducible targets.
Derived from complete_sharing_fpt.py. At-most budget, essential inputs.
No counted-NOT or partial-function generalization claimed.
"""
from functools import lru_cache
from itertools import product
from collections import Counter
from time import perf_counter
from complete_sharing_fpt import Solver, ANY, NC, brute
from module_contraction import contract_pair, essential, raw_monotone

class Baseline(Solver):
 def local(self,S,ports,patterns,targets):
  self.stats['local']+=1
  L=S|(((1<<len(ports))-1)<<self.n)
  if not L:return False
  one=self.ONE
  @lru_cache(None)
  def canon(j,A):
   f=targets[j]
   if f in (ANY,NC,0,one):return None
   c=self.cof(f,S&~A)-{0,one}
   return next(iter(c)) if len(c)==1 else None
  def ok(j,A,t):return t in (ANY,NC,0,one) or canon(j,A)==t
  @lru_cache(None)
  def rec(L,ts):
   self.stats["local_rec"]+=1
   if L.bit_count()==1:
    i=L.bit_length()-1
    for j,t in enumerate(ts):
     v=self.var[i] if i<self.n else (one if patterns[j]>>ports[i-self.n]&1 else 0)
     if t==NC:
      if v in (0,one):return False
     elif t!=ANY and v!=t:return False
    return True
   A=L&-L
   for l in self.subsets(L^A):
    l|=A;r=L^l
    if not r:continue
    x=l&self.M;y=r&self.M
    for AND in (False,True):
     absorbing=0 if AND else one;neutral=one^absorbing
     opts=[]
     for j,t in enumerate(ts):
      if t==ANY:o=[(ANY,ANY)]
      elif t==absorbing:o=[(absorbing,ANY),(ANY,absorbing)]
      elif t==neutral:o=[(neutral,neutral)]
      elif t==NC:o=[(NC,NC),(NC,neutral),(neutral,NC)]
      else:
       a=self.res(t,y,y if AND else 0);b=self.res(t,x,x if AND else 0)
       if (a&b if AND else a|b)!=t or not ok(j,x,a) or not ok(j,y,b):break
       o=[(a,b)]
      opts.append(o)
     else:
      for pairs in product(*opts):
       a,b=map(tuple,zip(*pairs))
       if rec(l,a) and rec(r,b):return True
   return False
  return rec(L,targets)

class Irreducible(Baseline):
 def local(self,S,ports,patterns,targets):
  self.stats['local']+=1
  L=S|(((1<<len(ports))-1)<<self.n)
  if not L:return False
  one=self.ONE
  @lru_cache(None)
  def canon(j,A):
   f=targets[j]
   if f in (ANY,NC,0,one):return None
   c=self.cof(f,S&~A)-{0,one}
   return next(iter(c)) if len(c)==1 else None
  def ok(j,A,t):return t in (ANY,NC,0,one) or canon(j,A)==t
  @lru_cache(None)
  def rec(L,ts):
   self.stats["local_rec"]+=1
   if L.bit_count()>1 and not (L&~self.M):
    self.stats["pure_primary_reject"]+=1;return False
   if L.bit_count()==1:
    i=L.bit_length()-1
    for j,t in enumerate(ts):
     v=self.var[i] if i<self.n else (one if patterns[j]>>ports[i-self.n]&1 else 0)
     if t==NC:
      if v in (0,one):return False
     elif t!=ANY and v!=t:return False
    return True
   A=L&-L
   for l in self.subsets(L^A):
    l|=A;r=L^l
    if not r:continue
    x=l&self.M;y=r&self.M
    for AND in (False,True):
     absorbing=0 if AND else one;neutral=one^absorbing
     opts=[]
     for j,t in enumerate(ts):
      if t==ANY:o=[(ANY,ANY)]
      elif t==absorbing:o=[(absorbing,ANY),(ANY,absorbing)]
      elif t==neutral:o=[(neutral,neutral)]
      elif t==NC:o=[(NC,NC),(NC,neutral),(neutral,NC)]
      else:
       a=self.res(t,y,y if AND else 0);b=self.res(t,x,x if AND else 0)
       if (a&b if AND else a|b)!=t or not ok(j,x,a) or not ok(j,y,b):break
       o=[(a,b)]
      opts.append(o)
     else:
      for pairs in product(*opts):
       a,b=map(tuple,zip(*pairs))
       if rec(l,a) and rec(r,b):return True
   return False
  return rec(L,targets)
 def solve(self,f,s):
  if contract_pair(self.n,f) is not None:raise ValueError("pair-irreducible target required")
  for deg in self.degrees(s):
   r=len(deg)
   @lru_cache(None)
   def go(X,rem,state):
    self.stats['states']+=1
    k=len(rem);un=self.M^X
    if len(self.cof(f,X))>1<<k:return False
    pats=tuple(t for t,v in enumerate(state) if v!=ANY)
    if k==r:
     ports=tuple(i for i,d in enumerate(rem) for _ in range(d))
     return self.local(un,ports,pats,tuple(state[t] for t in pats))
    for S in self.subsets(un):
     newX=X|S
     if len(self.cof(f,newX))>1<<(k+1):continue
     opt=[]
     for t in pats:
      g=state[t];c=self.cof(g,S)
      if len(c)>2:break
      if len(c)==1:
       h=next(iter(c));opt.append([(0,h,ANY),(self.ONE,ANY,h),(NC,h,h)])
      else:
       lo=self.res(g,S,0);hi=self.res(g,S,S)
       if lo==hi:break
       v=sum((self.res(g,S,a&S)==hi)<<a for a in range(1<<self.n))
       opt.append([(v,lo,hi)])
     else:
      for take in product(*(range(d+1) for d in rem)):
       ports=tuple(i for i,d in enumerate(take) for _ in range(d))
       if not (S or ports):continue
       if not ports and S.bit_count()>1:
        self.stats["empty_port_reject"]+=1;continue
       newrem=tuple(d-c for d,c in zip(rem,take))+(deg[k],)
       for choice in product(*opt):
        targets=tuple(x[0] for x in choice)
        # Avoid known impossible range of no-primary slices.
        if not S and NC in targets:continue
        ns=[ANY]*(1<<(k+1))
        for t,(_,a,b) in zip(pats,choice):ns[t]=a;ns[t|(1<<k)]=b
        if go(newX,newrem,tuple(ns)) and self.local(S,ports,pats,targets):return True
    return False
   if go(0,(),(f,)):return True
  return False


def test():
    jobs=[]
    for n,b in ((3,4),(4,5)):
        known=brute(n,b)
        for f in range(1,(1<<(1<<n))-1):
            if raw_monotone(n,f) and essential(n,f) and contract_pair(n,f) is None:
                for s in range(b-n+2):jobs.append((n,f,s,known.get(f,100)<=n-1+s))
    for cls in (Baseline,Irreducible):
        t=perf_counter();sols={};stats=Counter()
        for n,f,s,want in jobs:
            if n not in sols:sols[n]=cls(n)
            assert sols[n].solve(f,s)==want,(n,f,s,cls)
        for so in sols.values():stats.update(so.stats)
        print(cls.__name__,len(jobs),dict(stats),'seconds',perf_counter()-t,flush=True)

if __name__=='__main__':test()
