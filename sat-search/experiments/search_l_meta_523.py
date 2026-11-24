"""Search for the witness in pequalnp.com gap L-meta-523.

Install python-sat, then run: python search_l_meta_523.py cadical195 100000
The optional second argument sets a solver conflict limit. A None status means
the search reached its limit without deciding satisfiability.

Check monotone truth tables at the minimal true and maximal false inputs.
For an eligible lift, the Boolean output is unchanged: when h is false the
OR replacement agrees with the original, and when h is true the new output
is true. The lift only removes circuit dependencies, so requiring the count
not to decrease is equivalent to preserving each original AND-to-AND path
pair. The SAT model checks that preservation and the script checks any
returned circuit independently on all 256 assignments.
"""


import sys
from pathlib import Path
local_packages = Path(__file__).with_name('.scratch-sat')
if local_packages.is_dir():
 sys.path.insert(0, str(local_packages))
from pysat.formula import IDPool
from pysat.solvers import Solver
from pysat.card import CardEnc
E=[3,6,12,24,48,33,65,130]
good=lambda x:any(x&e==e for e in E)
bad=[x for x in range(256) if not good(x) and all(good(x|1<<i) for i in range(8) if not x>>i&1)]
v=IDPool()
C=[]
def add(*x):C.append(list(x))
A=lambda j:v.id(('and',j))
S=lambda j,k,i:v.id(('select',j,k,i))
U=lambda j:v.id(('under',j))
for j in range(8,19):
 for k in range(2):
  C.extend(CardEnc.equals([S(j,k,i) for i in range(j)],1,vpool=v).clauses)
 for i in range(j):
  for l in range(i):add(-S(j,0,i),-S(j,1,l))
 terms=[]
 for k in range(2):
  for i in range(8,j):
   w=v.id(('nest',j,k,i))
   add(-w,S(j,k,i));add(-w,U(i));add(-S(j,k,i),-U(i),w)
   terms.append(w)
 add(-A(j),U(j))
 for w in terms:add(-w,U(j))
 add(-U(j),A(j),*terms)
add(*(v.id(('witness',j)) for j in range(8,19)))
for j in range(8,19):
 w=v.id(('witness',j))
 add(-w,A(j))
 add(-w,*(v.id(('nest',j,k,i)) for k in range(2) for i in range(8,j)))
for x in E+bad:
 t=lambda j:v.id(('val',x,j))
 for j in range(8):add(t(j) if x>>j&1 else -t(j))
 for j in range(8,19):
  l,r=[v.id(('arg',x,j,k)) for k in range(2)]
  for k,arg in enumerate((l,r)):
   for i in range(j):
    add(-S(j,k,i),-arg,t(i));add(-S(j,k,i),arg,-t(i))
  f=t(j);a=A(j)
  add(-a,-l,-r,f);add(-a,l,-f);add(-a,r,-f)
  add(a,l,r,-f);add(a,-l,f);add(a,-r,f)
 add(t(18) if good(x) else -t(18))
def evaluate(g,x,mod=None):
 vals=[bool(x>>i&1) for i in range(8)]
 for j,(a,b,c) in enumerate(g,8):
  if mod is not None and j == mod[0]:
   b = c = mod[1]
  vals.append((vals[b] and vals[c]) if a else (vals[b] or vals[c]))
 return vals
def pairs(g,mod=None):
 deps=[set() for _ in range(8)]
 n=0
 for j,(a,b,c) in enumerate(g,8):
  if mod is not None and j==mod[0]:b=c=mod[1]
  dep=deps[b]|deps[c]|{b,c}
  n+=sum(i>=8 and g[i-8][0] for i in dep) if a else 0
  deps.append(dep)
 return n
def both(a,b,key):
 w=v.id(key)
 add(-w,a);add(-w,b);add(-a,-b,w)
 return w
def reach(skip,slot):
 R={}
 for j in range(8,19):
  for i in range(8,j):
   via=[]
   for k in range(2):
    if (j,k)==(skip,slot):continue
    via.append(S(j,k,i))
    for m in range(i+1,j):
     via.append(both(S(j,k,m),R[m,i],('path',skip,slot,j,i,k,m)))
   w=R[j,i]=v.id(('reach',skip,slot,j,i))
   for q in via:add(-q,w)
   add(-w,*via)
 return R
org=reach(0,0)
for j in range(9,18):
 for k in range(2):
  R=reach(j,k)
  no=v.id(('ineligible',j,k))
  for i in range(8,j):
   add(-no,-S(j,k,i),*(v.id(('val',x,i)) for x in bad))
  for (u,b),w in org.items():
   if b>=j or u<=j:continue
   add(A(j),no,-A(u),-A(b),-w,R[u,b])
for j in range(8,17):
 for i in range(j):
  for l in range(i):
   add(-S(j,1,i),-S(j+1,1,l))
  for a in range(i):
   for b in range(a):
    add(-S(j,1,i),-S(j+1,1,i),-S(j,0,a),-S(j+1,0,b))
print('CNF',len(C),v.top,len(E+bad),flush=True)
with Solver(name=sys.argv[1] if len(sys.argv)>1 else 'cadical195', bootstrap_with=C) as solver:
 count=0
 solver.conf_budget(int(sys.argv[2]) if len(sys.argv) > 2 else -1)
 while solver.solve_limited():
  m=set(solver.get_model())
  g=[(A(j) in m,*(next(i for i in range(j) if S(j,k,i) in m) for k in range(2))) for j in range(8,19)]
  vals=[evaluate(g,x) for x in range(256)]
  assert pairs(g)>0 and all(vals[x][-1]==good(x) for x in range(256))
  orig=pairs(g)
  lifts=[]
  for j,(a,b,c) in enumerate(g[:-1],8):
   if a:continue
   for p,h in [(b,c),(c,b)]:
    if any(vals[x][h] and not good(x) for x in range(256)):continue
    if pairs(g,(j,p))>=orig:continue
    if all((evaluate(g,x,(j,p))[-1] or vals[x][h])==good(x) for x in range(256)):
     lifts.append((j,p,h))
  if not lifts:
   print('WITNESS',g,flush=True);break
  count+=1
  if count==1 or count%100==0:print('Rejected liftable models',count,g,flush=True)
  solver.add_clause([(-A(j) if a else A(j)) for j,(a,b,c) in enumerate(g,8)]+[-S(j,k,i) for j,(_,b,c) in enumerate(g,8) for k,i in enumerate((b,c))])
 else:print('SEARCH ENDED',solver.get_status(),count,solver.accum_stats(),flush=True)








