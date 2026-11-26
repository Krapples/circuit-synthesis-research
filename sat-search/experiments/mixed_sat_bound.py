"""Mixed-block SAT composition, all-even-length full support, and the floor(17n/12)-4 arithmetic.

Handoff reference (README(3), 2026-11-26), kept verbatim apart from this docstring.
Finite checking only: the padding argument and mixed-state induction in
NOTES_SAT_ENCODING_BOUNDS.md establish the unbounded claims.
Run from sat-search/experiments:  python -I mixed_sat_bound.py
"""
import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))  # sibling import under python -I
from additive_sat_weight import weight, trim, START, U, run
from itertools import product
from random import Random

BLOCKS=[('11a10b',2,0x9,4),('11a1bcd1',4,0xedc4,7),
 ('11abcde1fg',7,0xe8e4e040e8e40000e8e4e0400000e040,10),
 ('11a1bcd1efg1',7,0xedc4ed00edc400c4edc4000000c40000,12)]
PAD='100100'
BASE={12:[PAD*2],16:['1001001001100100','1001001001110100','1001001010110100'],
 20:[PAD*2+'10110100','10110100'+PAD*2]}

def fill(tmp,r):
 return ''.join(str(r>>(ord(c)-97)&1) if c.isalpha() else c for c in tmp)

def sat(s):
 if len(s)%2:return False
 ts=[s[i:i+2] for i in range(0,len(s),2)];i=0;cs=[];cl=[]
 while i<len(ts):
  h=ts[i];i+=1
  if h=='00':cs.append(cl);cl=[];continue
  if h not in ('10','11'):return False
  ds=[]
  while i<len(ts) and ts[i] in ('10','11'):
   ds.append(int(ts[i][1]));i+=1
  if i==len(ts) or ts[i]!='01' or (ds and ds[-1]==0):return False
  i+=1;cl.append((sum(d<<j for j,d in enumerate(ds)),h=='11'))
 if cl or any(not c for c in cs):return False
 if all(any(b for _,b in c) for c in cs):return True
 def rec(cs):
  if not cs:return True
  if any(not c for c in cs):return False
  v=cs[0][0][0]
  return any(rec([[(u,b) for u,b in c if u!=v] for c in cs if (v,a) not in c]) for a in (False,True))
 return rec(cs)

def flip(w,i):return w[:i]+str(1-int(w[i]))+w[i+1:]

def mixed_cert():
 R=[START];count=0
 for st in R:
  for tmp,m,f,w in BLOCKS:
   for r in range(1<<m):
    z=run(st,int(fill(tmp,r),2),len(tmp));count+=1
    assert z!=U and (z is not None)==bool(f>>r&1)
    if z is not None and z not in R:R.append(z)
 assert all(run(s,52,6)==START for s in R)
 return len(R),count

def support_cert():
 cover={};tests=0
 for n,words in BASE.items():
  cv={}
  for w in words:
   assert len(w)==n and sat(w) and sat(w+PAD);tests+=2
   for i in range(n):
    a,b=sat(flip(w,i)),sat(flip(w,i)+PAD);tests+=2
    if not a and not b:cv[i]=w
  assert len(cv)==n
  cover[n]=cv
 return cover,tests

def choose(n):
 assert n>=16 and n%2==0
 k,r=divmod(n,12)
 return [3]*(k if r==6 else k-1)+{0:[0],2:[1],4:[2],6:[],8:[0,1],10:[1,1]}[r]

def bound(n):
 b=choose(n);assert sum(len(BLOCKS[i][0]) for i in b)+6==n
 return n-1+sum(BLOCKS[i][3]-BLOCKS[i][1] for i in b)

if __name__=='__main__':
 for tmp,m,f,w in BLOCKS:assert trim(f,m)==(f,m) and weight(f,m)==w
 assert mixed_cert()==(11,3036)
 cv,t=support_cert();assert t==212
 count=0
 for n in range(16,122,2):
  base={0:12,2:20,4:16}[n%6];k=(n-base)//6
  for i in range(n):
   j=min(i//6,k);local=i-6*j;w=cv[base][local];padded=PAD*j+w+PAD*(k-j)
   assert sat(padded) and not sat(flip(padded,i));count+=1
 assert count==3604
 pairs=0
 for tmp,m,f,w in BLOCKS:
  for tmp2,m2,f2,w2 in BLOCKS:
   for r,s in product(range(1<<m),range(1<<m2)):
    assert sat(fill(tmp,r)+fill(tmp2,s)+'110100')==bool((f>>r&1) and (f2>>s&1));pairs+=1
 assert pairs==76176
 rng=Random(20261126)
 for _ in range(5000):
  b=rng.choices(BLOCKS,k=rng.randrange(3,13));rows=[rng.choice([r for r in range(1<<m) if f>>r&1]) for tmp,m,f,w in b]
  if rng.randrange(2):
   j=rng.randrange(len(b));tmp,m,f,w=b[j];rows[j]=rng.choice([r for r in range(1<<m) if not f>>r&1])
  assert sat(''.join(fill(tmp,r) for (tmp,m,f,w),r in zip(b,rows))+'110100')==all(f>>r&1 for (tmp,m,f,w),r in zip(b,rows))
 for n in range(16,10002,2):assert bound(n)>=17*n//12-4 and bound(n)>=4*n//3-3
 print('PASS: 3036 transitions, 212 base checks, 3604 padded sensitivities, 76176 block pairs, 5000 mixed sequences, 4993 arithmetic checks')
