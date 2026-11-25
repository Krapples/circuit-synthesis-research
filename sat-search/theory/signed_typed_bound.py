"""Combine regional exact read-once NOT costs with ordered excess bounds.
Requires signed_region_bounds.py and readonce_not_cost.py.
"""
from functools import lru_cache
from collections import Counter
from random import Random
from math import inf
from signed_region_bounds import Bound,subs,circuit
from readonce_not_cost import costs,brute_formulas

class TypedBound(Bound):
    @lru_cache(None)
    def not_cost(self,S,output=False):
        v=0;pos=[i for i in range(self.n) if S>>i&1];k=len(pos)
        if not k:return 0
        aa=[sum((a>>j&1)<<i for j,i in enumerate(pos)) for a in range(1<<k)]
        one=(1<<(1<<k))-1
        for x in subs(self.full^S):
            g=sum(self.values[x|a]<<j for j,a in enumerate(aa))
            if g not in (0,one):
                cc=costs(k,g);v=max(v,cc[0] if output else min(cc))
        return v
    def typed_lower(self):
        # state: nonempty private groups, required empty providers, port cost -> min NOT
        dp=[{} for _ in range(self.full+1)];dp[0][0,0,0]=0;best=inf;mk=self.not_lower()
        for X in range(self.full+1):
            if not dp[X]:continue
            left=self.full^X
            if self.compatible(left,True,2):
                p=self.cost(X,left,True);nc=self.not_cost(left,True)
                for (k,t,a),b in dp[X].items():
                    best=min(best,max(k+max(t,p-k),a+p-k)+max(mk,b+nc))
            for S in subs(left):
                if not S or not self.compatible(S,False,2):continue
                p=self.cost(X,S)
                if p==inf:continue
                nc=self.not_cost(S);Y=X|S;d=self.diversity(Y)
                for (k,t,a),b in dp[X].items():
                    u=max(t,p-k,d-(k+1));key=k+1,u,a+p
                    if k+1+u+max(mk,b+nc)>=best:continue
                    dp[Y][key]=min(dp[Y].get(key,inf),b+nc)
        return best

def check(seed=20261124):
    r=Random(seed)
    for n,fs in [(3,range(256)),(4,[r.getrandbits(16) for _ in range(600)]),(5,[r.getrandbits(32) for _ in range(300)]),(5,r.sample(list(brute_formulas(5)),600))]:
        c=Counter();ex=None
        for f in fs:
            try:b=TypedBound(n,f)
            except ValueError:continue
            old=b.lower()+b.not_lower();new=b.typed_lower();assert new>=old
            c['functions']+=1;c['global_gain']+=new>old
            if new>old and ex is None:ex=(n,f,old,new)
        print(n,dict(c),'example',ex,flush=True)
    c=Counter()
    for _ in range(3000):
        n=r.randrange(2,7);g=[]
        for j in range(r.randrange(n-1,n+9)):
            op=r.choice('AAOON');x=r.randrange(n+j);y=r.randrange(n+j-1);y+=y>=x;g.append((op,x,y))
        z=circuit(n,g)
        if z is None:continue
        f,B,N,act,reads=z
        try:b=TypedBound(n,f)
        except ValueError:continue
        assert b.typed_lower()<=B-n+1+N,(n,g,B,N,b.typed_lower())
        c['circuits']+=1;c['gain']+=b.typed_lower()>b.lower()+b.not_lower()
    print(dict(c),flush=True)

if __name__=='__main__':check()
