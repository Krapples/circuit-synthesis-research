"""Complete Boolean-function lower bounds using signed regional restrictions.
Masks use assignment bits indexed by the integer encoding of input values.
Run directly for reproducible small tests (standard library only).
"""
from functools import lru_cache
from itertools import combinations
from random import Random
from collections import Counter
from math import inf

@lru_cache(None)
def subs(s):
    a=s; r=[]
    while True:
        r.append(a)
        if not a:return tuple(r)
        a=(a-1)&s

def logceil(n):return (max(1,n)-1).bit_length()

def components(S,adj):
    out=[]
    while S:
        seen=S&-S; todo=seen
        while todo:
            v=todo&-todo;todo^=v
            new=adj[v.bit_length()-1]&S&~seen
            seen|=new;todo|=new
        out.append(seen);S^=seen
    return out

def sandwich(S,A,O):
    if S.bit_count()<=1:return True
    for adj in (A,O):
        parts=components(S,adj)
        if len(parts)>1:return all(sandwich(p,A,O) for p in parts)
    return False

class Bound:
    def __init__(self,n,f):
        assert n>=1 and 0<=f<1<<(1<<n)
        self.n=n;self.f=f;self.full=(1<<n)-1;self.values=tuple(f>>a&1 for a in range(1<<n))
        self.sign=[];self.binate=0
        for i in range(n):
            d={self.values[a|1<<i]-self.values[a] for a in subs(self.full^(1<<i))}-{0}
            if not d:raise ValueError('all inputs must be essential')
            self.sign.append(1 if d=={1} else 0 if d=={-1} else None)
            if len(d)==2:self.binate|=1<<i
        self.pairs={};self.xor=[0]*n;self.bad=[0]*n
        for i,j in combinations(range(n),2):
            I,J=1<<i,1<<j; codes=set();xor=False
            for a in subs(self.full^I^J):
                v=[self.values[a|b] for b in (0,I,J,I|J)]
                if (v[0]==v[1] and v[2]==v[3]) or (v[0]==v[2] and v[1]==v[3]):continue
                if sum(v)==2:xor=True
                else:codes.add(v.index(int(sum(v)==1)))
            if xor:self.xor[i]|=J;self.xor[j]|=I
            if xor or len(codes)>1:self.bad[i]|=J;self.bad[j]|=I
            elif codes:self.pairs[i,j]=next(iter(codes))
    @lru_cache(None)
    def compatible(self,S,output=False,level=2):
        if output and S&self.binate:return False
        adj=self.xor if level==0 else self.bad
        if any(adj[i]&S for i in range(self.n) if S>>i&1):return False
        if level<2:return True
        edges=[(i,j,c) for (i,j),c in self.pairs.items() if S>>i&1 and S>>j&1]
        graph=[[] for _ in range(self.n)]
        for i,j,c in edges:
            p=(c&1)^(c>>1);graph[i].append((j,p));graph[j].append((i,p))
        signs={i:self.sign[i] for i in range(self.n) if output and S>>i&1}
        for i in range(self.n):
            if not S>>i&1:continue
            if i not in signs:signs[i]=1
            todo=[i];visited=set()
            while todo:
                u=todo.pop()
                if u in visited:continue
                visited.add(u)
                for v,p in graph[u]:
                    z=signs[u]^p
                    if v in signs and signs[v]!=z:return False
                    signs[v]=z;todo.append(v)
        A=[0]*self.n;O=[0]*self.n
        for i,j,c in edges:
            adj=A if signs[i]==(c&1) else O
            adj[i]|=1<<j;adj[j]|=1<<i
        return sandwich(S,A,O)
    @lru_cache(None)
    def slice(self,X,a):
        # compact cofactor indexed by descending assignments of remaining variables
        return sum(self.values[a|b]<<i for i,b in enumerate(subs(self.full^X)))
    @lru_cache(None)
    def diversity(self,X):
        return logceil(len({self.slice(X,a) for a in subs(X)}))
    @lru_cache(None)
    def cost(self,X,S,output=False):
        if output:
            assert X|S==self.full and not X&S
            return self.diversity(X)
        req=set();V=self.values;Z=self.full^X^S
        ss=subs(S);zz=subs(Z);ones=(1<<len(ss))-1
        for a in subs(X):
            rows=[sum(V[a|b|c]<<j for j,c in enumerate(zz)) for b in ss]
            types=set(rows)
            if len(types)>2:return inf
            if len(types)==2:
                v=sum((r==rows[0])<<i for i,r in enumerate(rows))
                req.add(min(v,v^ones))
        return logceil(len(req))
    def lower(self,level=2,ordered=True):
        # number of private nonempty groups, required empty providers, sum port costs
        dp=[{} for _ in range(self.full+1)];dp[0][0,0]=0
        best=inf
        for X in range(self.full+1):
            if not dp[X]:continue
            left=self.full^X
            if self.compatible(left,True,level):
                p=self.cost(X,left,True) if ordered else 0
                for (k,t),a in dp[X].items():
                    best=min(best,max(k+max(t,p-k),a+p-k))
            for S in subs(left):
                if not S or not self.compatible(S,False,level):continue
                p=self.cost(X,S) if ordered else 0
                if p==inf:continue
                Y=X|S;d=self.diversity(Y) if ordered else 0
                for (k,t),a in dp[X].items():
                    u=max(t,p-k,d-(k+1));key=k+1,u
                    if k+1+u>=best:continue
                    dp[Y][key]=min(dp[Y].get(key,inf),a+p)
        return best
    def not_lower(self):
        # Maximum number of downward transitions on any increasing chain.
        d=[0]*(1<<self.n)
        for a in range(1,1<<self.n):
            d[a]=max(d[a^(1<<i)]+(self.values[a^(1<<i)]>self.values[a]) for i in range(self.n) if a>>i&1)
        return logceil(d[-1]+1)

def circuit(n,gates):
    one=(1<<(1<<n))-1
    sig=[sum(1<<a for a in range(1<<n) if a>>i&1) for i in range(n)]
    for op,x,y in gates:
        sig.append(sig[x]^one if op=='N' else sig[x]&sig[y] if op=='A' else sig[x]|sig[y])
    active={len(sig)-1};reads=Counter()
    for i in range(len(sig)-1,n-1,-1):
        if i in active:
            op,x,y=gates[i-n];args=(x,) if op=='N' else (x,y)
            active.update(args);reads.update(args)
    if not all(i in active for i in range(n)):return None
    B=sum(i>=n and gates[i-n][0]!='N' for i in active)
    N=sum(i>=n and gates[i-n][0]=='N' for i in active)
    return sig[-1],B,N,active,reads

def check(seed=20261124):
    rng=Random(seed);counts=Counter(); examples={}
    for n,functions in [(2,range(16)),(3,range(256)),(4,[rng.getrandbits(16) for _ in range(600)]),(5,[rng.getrandbits(32) for _ in range(300)])]:
        c=Counter()
        for f in functions:
            try:b=Bound(n,f)
            except ValueError:continue
            a=b.lower(0,False);p=b.lower(1,False);s=b.lower(2,False);o=b.lower(2,True)
            assert a<=p<=s<=o<inf,(n,f,a,p,s,o)
            c['cases']+=1;c['pattern']+=p>a;c['sandwich']+=s>p;c['ordered']+=o>s
            for name,x,y in [('pattern',a,p),('sandwich',p,s),('ordered',s,o)]:
                if y>x:examples.setdefault(name,(n,f,a,p,s,o))
        print('truth tables',n,dict(c),flush=True)
    for _ in range(2500):
        n=rng.randrange(2,7);g=[]
        for j in range(rng.randrange(n-1,n+9)):
            op=rng.choice('AAOON');x=rng.randrange(n+j);y=rng.randrange(n+j-1);y+=y>=x;g.append((op,x,y))
        z=circuit(n,g)
        if z is None:continue
        f,B,N,act,reads=z
        try:b=Bound(n,f)
        except ValueError:continue
        e=B-n+1;l=b.lower()
        assert l<=e and b.not_lower()<=N,(n,g,e,l,N,b.not_lower())
        # independently obtain actual region of each input by following unique reader.
        readers={}
        for j in act:
            if j<n:continue
            op,x,y=g[j-n]
            for i in ((x,) if op=='N' else (x,y)):readers.setdefault(i,[]).append(j)
        groups={};out=n+len(g)-1
        for i in range(n):
            j=i
            while j!=out and reads[j]==1:j=readers[j][0]
            groups[j]=groups.get(j,0)|(1<<i)
        for j,S in groups.items():
            assert b.compatible(S,j==out),(n,g,j,S)
            counts['regions']+=1
        counts['circuits']+=1;counts['shared']+=e>0;counts['nonmonotone']+=N>0 and b.not_lower()>0
    print('circuits',dict(counts),'examples',examples,flush=True)
    # Separate independent gate-set enumeration, free NOT unavailable here.
    from complete_signed_fpt import brute
    for n,budget in ((2,4),(3,4)):
        known=brute(n,budget);c=0;maxgap=0
        for f,g in known.items():
            try:b=Bound(n,f)
            except ValueError:continue
            v=n-1+b.lower()+b.not_lower()
            assert v<=g,(n,f,v,g)
            c+=1;maxgap=max(maxgap,g-v)
        print('exact gate-set',n,c,'max gap',maxgap,flush=True)

if __name__=='__main__':check()
