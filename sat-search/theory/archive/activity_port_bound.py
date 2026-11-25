"""Activity-antichain port lower bound. Standalone check uses signed_region_bounds.py."""
from functools import lru_cache
from collections import Counter
from random import Random
from math import inf
from signed_region_bounds import Bound,subs,circuit

def width(profiles):
    """Dilworth via maximum matching in strict-subset DAG."""
    a=list(set(profiles)); n=len(a)
    edges=[[j for j,y in enumerate(a) if x!=y and x&y==x] for x in a]
    match={}
    def aug(i,seen):
        for j in edges[i]:
            if j in seen:continue
            seen.add(j)
            if j not in match or aug(match[j],seen):
                match[j]=i;return True
        return False
    return n-sum(aug(i,set()) for i in range(n))

class ActivityBound(Bound):
    @lru_cache(None)
    def profiles(self,S):
        outside=subs(self.full^S);inside=subs(S)
        return tuple(sum(int(any(self.values[a|b]!=self.values[a|b|1<<i] for b in inside if not b>>i&1))<<j for j,a in enumerate(outside)) for i in range(self.n) if S>>i&1)
    @lru_cache(None)
    def activity_cost(self,S):
        p=set(self.profiles(S))
        return 0 if len(p)<=1 else width(p)
    def lower_activity(self):
        # Existing DP, but distinguish number of distinct providers from occurrences.
        dp=[{} for _ in range(self.full+1)];dp[0][0,0]=0;best=inf
        for X in range(self.full+1):
            if not dp[X]:continue
            left=self.full^X
            if self.compatible(left,True,2):
                p=self.cost(X,left,True);v=max(p,self.activity_cost(left))
                for (k,t),a in dp[X].items():
                    best=min(best,max(k+max(t,p-k),a+v-k))
            for S in subs(left):
                if not S or not self.compatible(S,False,2):continue
                p=self.cost(X,S)
                if p==inf:continue
                v=max(p,self.activity_cost(S));Y=X|S;d=self.diversity(Y)
                for (k,t),a in dp[X].items():
                    u=max(t,p-k,d-(k+1));key=k+1,u
                    if k+1+u>=best:continue
                    dp[Y][key]=min(dp[Y].get(key,inf),a+v)
        return best

def check(seed=20261124):
    rng=Random(seed)
    for n,fs in [(3,range(256)),(4,[rng.getrandbits(16) for _ in range(600)]),(5,[rng.getrandbits(32) for _ in range(300)])]:
        c=Counter();ex=None
        for f in fs:
            try:b=ActivityBound(n,f)
            except ValueError:continue
            old=b.lower();new=b.lower_activity();assert new>=old
            c['functions']+=1;c['global_gain']+=new>old
            if new>old and ex is None:ex=(n,f,old,new)
            for S in subs(b.full):
                if not S or not b.compatible(S):continue
                for X in subs(b.full^S):
                    p=b.cost(X,S,X|S==b.full)
                    if p==inf:continue
                    c['regional_queries']+=1;c['local_gain']+=b.activity_cost(S)>p
        print(n,dict(c),'example',ex,flush=True)
    c=Counter()
    for _ in range(3000):
        n=rng.randrange(2,7);g=[]
        for j in range(rng.randrange(n-1,n+9)):
            op=rng.choice('AAOON');x=rng.randrange(n+j);y=rng.randrange(n+j-1);y+=y>=x;g.append((op,x,y))
        z=circuit(n,g)
        if z is None:continue
        f,B,N,act,reads=z
        try:b=ActivityBound(n,f)
        except ValueError:continue
        assert b.lower_activity()<=B-n+1,(n,g,B,b.lower_activity())
        readers={};out=n+len(g)-1
        for j in act:
            if j<n:continue
            op,x,y=g[j-n]
            for i in ((x,) if op=='N' else (x,y)):readers.setdefault(i,[]).append(j)
        def owner(i):
            while i!=out and reads[i]==1:i=readers[i][0]
            return i
        groups={};ports=Counter()
        for i in range(n):groups[owner(i)]=groups.get(owner(i),0)|(1<<i)
        for i,rr in readers.items():
            if len(rr)>1:
                for j in rr:ports[owner(j)]+=1
        for j,S in groups.items():
            assert b.activity_cost(S)<=ports[j],(n,g,j,S,ports[j],b.activity_cost(S))
            c['regions']+=1
        c['circuits']+=1;c['shared']+=B-n+1>0
    print(dict(c),flush=True)

if __name__=='__main__':check()
