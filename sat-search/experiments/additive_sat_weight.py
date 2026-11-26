"""Additive gate-elimination weight and the all-copy SAT composition certificates (ChatGPT handoff 2026-11-26,
README(2).md, reference code verbatim apart from this docstring). w gives C(AND_j f_j) >= sum_j w(f_j) - 1 for nonzero
complete f_j on disjoint inputs (paper proof reviewed in NOTES_SAT_ENCODING_BOUNDS.md). Independent checks:
experiments/additive_weight_check.py.
"""
from functools import lru_cache
from itertools import combinations,product

def cof(f,n,i,b):
 return sum(((f>>((r&((1<<i)-1))|(b<<i)|((r>>i)<<(i+1))))&1)<<r for r in range(1<<(n-1)))

def trim(f,n):
 for i in range(n-1,-1,-1):
  a,b=cof(f,n,i,0),cof(f,n,i,1)
  if a==b:f,n=a,n-1
 return f,n

def module(f,n,i,j,a,b):
 # new var in position 0; other inputs in increasing order
 rem=[k for k in range(n) if k not in (i,j)]; vals={}
 for r in range(1<<n):
  h=int((r>>i&1)==a and (r>>j&1)==b)
  s=h+sum((r>>k&1)<<(t+1) for t,k in enumerate(rem));v=f>>r&1
  if s in vals and vals[s]!=v:return None
  vals[s]=v
 return sum(v<<s for s,v in vals.items())

@lru_cache(None)
def weight(f,n):
 assert f>0, "zero factors are outside the theorem"
 f,n=trim(f,n)
 if n==0:return 0
 if n==1:return 1
 # remove literal factors first
 for i in range(n):
  for b in range(2):
   if cof(f,n,i,1-b)==0:return 1+weight(cof(f,n,i,b),n-1)
 # gate using cross-block variables: for any repeated operand and phase
 v=min(repeated(f,n,i,a) for i in range(n) for a in range(2))
 for i,j in combinations(range(n),2):
  for a,b in product(range(2),repeat=2):
   g=module(f,n,i,j,a,b)
   if g is not None:v=min(v,1+weight(g,n-1))
 return v

def repeated(f,n,i,a):
 return max(3+weight(cof(f,n,i,1-a),n-1),2+weight(cof(f,n,i,a),n-1))

START=('B',False,False,False,False); U='uncertified'
def step(state,tok):
 phase,last0,nonempty,haspos,pol=state
 if phase=='B':
  if tok==0:return None if not nonempty else START if haspos else U
  if tok==1:return None
  return ('P',False,nonempty,haspos,tok==3)
 if tok==0:return None
 if tok==1:return None if phase=='D' and last0 else ('B',False,True,haspos or pol,False)
 return ('D',tok==2,nonempty,haspos,pol)
def run(st,w,L):
 for i in range(L-2,-1,-2):
  st=step(st,(w>>i)&3)
  if st is None or st==U:return st
 return st

def certificate(tmp,n,f):
 assert trim(f,n)==(f,n)
 R={START};todo=[START];count=0
 while todo:
  st=todo.pop()
  for r in range(1<<n):
   word=''.join(str((r>>(ord(ch)-97))&1) if ch.isalpha() else ch for ch in tmp)
   nxt=run(st,int(word,2),len(tmp));count+=1
   assert nxt!=U and (nxt is not None)==bool((f>>r)&1)
   if nxt is not None and nxt not in R:R.add(nxt);todo.append(nxt)
 assert all(run(st,int('110100',2),6)==START for st in R)
 return len(R),count

if __name__=='__main__':
 assert weight(0x9,2)==4
 assert weight(0xe8e4,4)==6
 cases=[('11a1bcd1',4,0xedc4,7),
        ('11a1bcd1efg1',7,0xedc4ed00edc400c4edc4000000c40000,12)]
 for tmp,n,f,w in cases:
  assert weight(f,n)==w
  assert certificate(tmp,n,f)==(7,7*(1<<n))
  print(tmp,hex(f),w,'certificate OK')
