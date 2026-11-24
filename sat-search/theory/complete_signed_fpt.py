"""Small exact decision prototype for complete AND/OR/NOT synthesis, parameterized by total gates above the support bound.
Run directly for exhaustive small cross-checks. Uses only the Python standard library.
This is a decision prototype, not a production solver or proof-certificate generator.

Provenance: supplied by the independent theory audit (ChatGPT), 2026-11-24; contracts added in this
repository (verify/AUDIT.md). Status: provisional decision prototype, independently tested on small
cases (verify/theory_audit_checks.py), not proved and not a production pruning rule.
Contract of solve(f, s): f is a truth-table bitmask over the 2^n rows, nonconstant, with every input
essential; s is a nonnegative integer (gates above the support bound
n - 1). Violations raise ValueError instead of returning an unfounded answer.
"""
from functools import lru_cache
from itertools import product
from collections import Counter
import time
ANY=-1; NC=-2
class Solver:
 def __init__(self,n):
  self.n=n;self.M=(1<<n)-1;self.ONE=(1<<(1<<n))-1
  self.var=[sum(1<<a for a in range(1<<n) if a>>i&1) for i in range(n)]
  self.stats=Counter()
 @lru_cache(None)
 def subsets(self,S):
  a=S; out=[]
  while True:
   out.append(a)
   if not a:return tuple(out)
   a=(a-1)&S
 @lru_cache(None)
 def res(self,f,S,a):
  return sum(((f>>((i&~S)|a))&1)<<i for i in range(1<<self.n))
 @lru_cache(None)
 def cof(self,f,S):return frozenset(self.res(f,S,a) for a in self.subsets(S))
 def local(self,S,ports,patterns,targets,notbudget):
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
  def ok(j,A,t):
   if t in (ANY,NC,0,one):return True
   c=canon(j,A)
   return c is not None and t in (c,c^one)
  def complement(t):return t if t in (ANY,NC) else t^one
  def proj(t,mask,AND):
   v=0 if AND else one
   for a in self.subsets(mask):
    k=self.res(t,mask,a);v=(v|k) if AND else (v&k)
   return v
  @lru_cache(None)
  def rec(L,ts,left):
   if left and rec(L,tuple(complement(t) for t in ts),left-1):return True
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
       a=proj(t,y,AND);b=proj(t,x,AND)
       if (a&b if AND else a|b)!=t or not ok(j,x,a) or not ok(j,y,b):break
       o=[(a,b)]
      opts.append(o)
     else:
      for pairs in product(*opts):
       a,b=map(tuple,zip(*pairs))
       if any(rec(l,a,j) and rec(r,b,left-j) for j in range(left+1)):return True
   return False
  return rec(L,targets,notbudget)
 @staticmethod
 def degrees(s):
  yield ()
  def rec(left,p):
   for x in range(1,left+1):
    q=p+(x+1,);yield q;yield from rec(left-x,q)
  yield from rec(s,())
 def check_target(self,f,s):
  if not isinstance(f,int) or not 0<f<self.ONE:raise ValueError(f'target must be a nonconstant truth table over {self.n} inputs')
  if not all(self.res(f,1<<i,0)!=self.res(f,1<<i,1<<i) for i in range(self.n)):raise ValueError('every input must be essential')
  if not isinstance(s,int) or s<0:raise ValueError('s must be a nonnegative integer')
 def solve(self,f,s):
  self.check_target(f,s)
  for deg in self.degrees(s):
   r=len(deg)
   @lru_cache(None)
   def go(X,rem,state,left):
    self.stats['states']+=1
    k=len(rem);un=self.M^X
    if len(self.cof(f,X))>1<<k:return False
    pats=tuple(t for t,v in enumerate(state) if v!=ANY)
    if k==r:
     ports=tuple(i for i,d in enumerate(rem) for _ in range(d))
     return self.local(un,ports,pats,tuple(state[t] for t in pats),left)
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
       lo,hi=sorted(c)
       v=sum((self.res(g,S,a&S)==hi)<<a for a in range(1<<self.n))
       opt.append([(v,lo,hi),(v^self.ONE,hi,lo)])
     else:
      for take in product(*(range(d+1) for d in rem)):
       ports=tuple(i for i,d in enumerate(take) for _ in range(d))
       if not (S or ports):continue
       newrem=tuple(d-c for d,c in zip(rem,take))+(deg[k],)
       for choice in product(*opt):
        targets=tuple(x[0] for x in choice)
        # Avoid known impossible range of no-primary slices.
        if not S and NC in targets:continue
        ns=[ANY]*(1<<(k+1))
        for t,(_,a,b) in zip(pats,choice):ns[t]=a;ns[t|(1<<k)]=b
        for used in range(left+1):
         if self.local(S,ports,pats,targets,used) and go(newX,newrem,tuple(ns),left-used):return True
    return False
   if go(0,(),(f,),s-sum(d-1 for d in deg)):return True
  return False

def brute(n,b):
 sol=Solver(n);known={v:0 for v in sol.var};states={frozenset(sol.var)}
 for i in range(1,b+1):
  nxt=set()
  for st in states:
   l=sorted(st)
   for x in l:
    z=x^sol.ONE
    if z not in st:known.setdefault(z,i);nxt.add(st|{z})
   for j,x in enumerate(l):
    for y in l[j+1:]:
     for z in (x&y,x|y):
      if z not in st:
       known.setdefault(z,i);nxt.add(st|{z})
  states=nxt
  print('brute',n,i,len(states),len(known),flush=True)
 return known

def essential(f,sol):return all(sol.res(f,1<<i,0)!=sol.res(f,1<<i,1<<i) for i in range(sol.n))
if __name__=='__main__':
 t=time.monotonic();count=0
 for n,b in [(2,4),(3,4)]:
  known=brute(n,b);sol=Solver(n);cases=[]
  for f in range(1,sol.ONE):
   if not essential(f,sol):continue
   cases.append(f)
  print('cases',n,len(cases),flush=True)
  for f in cases:
   for s in range(b-n+2):
    got=sol.solve(f,s);want=known.get(f,100)<=n-1+s
    assert got==want,(n,f,s,got,want)
    count+=1
  print('checked',n,sol.stats,'elapsed',time.monotonic()-t,flush=True)
 print('TOTAL',count,'elapsed',time.monotonic()-t)
