"""At-most binary suffix bounds for a pinned AND/OR or free-NOT prefix.
Columns are bitsets on labeled rows, P,N disjoint. U is a bitmask of
boundary wires that MUST occur in the suffix output cone. In exact
all-wires-read synthesis these are the currently unread wires (provided
there is at least one suffix gate). Distinct wires may have equal columns.
NOTs, if counted, are ignored by this binary lower bound.
No claim of exact-size preservation. Constant outputs outside mixed labels
are relaxed. All restrictions act on suffix formal inputs, not the prefix.
"""
from functools import lru_cache
from itertools import combinations, product
from random import Random
from time import perf_counter
from collections import Counter
INF=float('inf')

def bits(x):
    while x:
        b=x&-x;yield b.bit_length()-1;x-=b

def minimal(ds):
    out=[]
    for d in sorted(set(ds),key=int.bit_count):
        if not any(x&d==x for x in out):out.append(d)
    return tuple(sorted(out))

@lru_cache(maxsize=100000)
def hit(ds):
    if not ds:return 0
    if 0 in ds:return INF
    d=min(ds,key=int.bit_count)
    return 1+min(hit(tuple(x for x in ds if not x>>i&1)) for i in bits(d))

class Bound:
    def __init__(self, cols,P,N,mono=False):
        assert P&N==0 and P and N
        self.C=tuple(c&(P|N) for c in cols);self.P=P;self.N=N;self.mono=mono
        self.all=(1<<len(cols))-1
        self.pairs=[]
        for a in bits(P):
            for b in bits(N):
                d=0
                for i,c in enumerate(self.C):
                    if (c>>a&1)>(c>>b&1) or (not mono and (c>>a&1)!=(c>>b&1)):d|=1<<i
                self.pairs.append(((1<<a)|(1<<b),d))
        self._memo={}
        self._data={}

    def data(self,R):
        if R in self._data:return self._data[R]
        const=sum(1<<i for i,c in enumerate(self.C) if c&R in (0,R))
        ds=minimal(d for mask,d in self.pairs if mask&R==mask)
        mandatory=0
        for d in ds:
            if d and d&(d-1)==0:mandatory|=d
        self._data[R]=(const,ds,mandatory)
        return self._data[R]

    def base(self,R,U=0):
        if not R&self.P or not R&self.N:return 0
        const,ds,mandatory=self.data(R)
        if 0 in ds:return INF
        U|=mandatory
        L=max(0,U.bit_count()+hit(minimal(d for d in ds if not d&U))-1)
        if L>=2:return L
        # Explicit zero/one-binary-gate completion, respecting mandatory wires.
        p=self.P&R;n=self.N&R
        def ok(c):return c&p==p and not c&n or (not self.mono and c&n==n and not c&p)
        for i,c in enumerate(self.C):
            if not U&~(1<<i) and ok(c):return L
        for i,j in combinations(range(len(self.C)),2):
            if U&~((1<<i)|(1<<j)):continue
            a,b=self.C[i]&R,self.C[j]&R
            vals=(a&b,a|b) if self.mono else (x&y for x,y in product((a,a^R),(b,b^R)))
            if any(ok(c) for c in vals):return max(1,L)
        return max(2,L)

    def lower(self,R=None,U=0,depth=1):
        if R is None:R=self.P|self.N
        if not R&self.P or not R&self.N:return 0
        key=(R,U,depth)
        if key in self._memo:return self._memo[key]
        const,ds,mandatory=self.data(R)
        U|=mandatory
        L=self.base(R,U)
        if depth and L!=INF:
            # Restrict any boundary signal. Constants already present in the
            # parent are not counted twice by recursion: child U is empty,
            # and only semantically mandatory wires are reintroduced there.
            for i,c in enumerate(self.C):
                if const>>i&1:continue
                slices=(R&~c,R&c)
                mixed=tuple(bool(s&self.P and s&self.N) for s in slices)
                v=[]
                for s,m in zip(slices,mixed):
                    if m:
                        a=self.lower(s,0,depth-1);v.append(a)
                        removed=(U&self.data(s)[0]).bit_count()
                        L=max(L,a+removed)
                    else:v.append(0)
                if U>>i&1 and all(mixed):L=max(L,2+min(v))
        self._memo[key]=L
        return L

    def first(self,U=0,depth=1):
        """One-step lookahead: condition on first binary gate. Unary NOTs
        are free in signed mode. Only valid for suffix with >=1 binary gate;
        literal solutions are handled conservatively by returning base bound.
        """
        R=self.P|self.N;L=self.lower(R,U,depth)
        if L<1 or L==INF:return L
        ans=INF
        for i,j in combinations(range(len(self.C)),2):
            a,b=self.C[i],self.C[j]
            vals=(a&b,a|b) if self.mono else tuple(x&y for x,y in product((a,a^R),(b,b^R)))
            for c in set(vals):
                V=(U&~((1<<i)|(1<<j)))|(1<<len(self.C))
                # If the first binary gate is final, the mandatory new wire
                # may itself serve as output: remaining bound zero.
                B=Bound(self.C+(c,),self.P,self.N,self.mono)
                ans=min(ans,1+B.lower(U=V,depth=depth))
                if ans<=L:return L
        return max(L,ans)

def generate(r,n,b,mono):
    # Construct a trimmed circuit backward, with distinct operands.
    # First build a random forward chain using all n primaries, then add
    # arbitrary reads; keep the previous output as an operand to trim gates.
    from module_contraction import vars
    C=list(vars(n));mask=(1<<(1<<n))-1;G=[]
    order=list(range(n));r.shuffle(order);v=order.pop()
    for _ in range(b):
        w=order.pop() if order else r.choice([i for i in range(len(C)) if i!=v])
        a,c=C[v],C[w];op=r.randrange(2)
        if not mono:
            if r.randrange(2):a^=mask
            if r.randrange(2):c^=mask
        C.append(a&c if op==0 else a|c);G.append((v,w));v=len(C)-1
    return C,G

def test():
    r=Random(20261124);t=perf_counter();counts=Counter();example=None
    for mono in (True,False):
        ct=Counter()
        for _ in range(700):
            n=r.randrange(3,6);b=r.randrange(n-1,n+5);C,G=generate(r,n,b,mono)
            mask=(1<<(1<<n))-1;P=C[-1];N=mask^P
            if not P or not N:continue
            # one random prefix, and optionally omit some labels
            q=r.randrange(b);U=(1<<(n+q))-1
            for i,j in G[:q]:U&=~((1<<i)|(1<<j))
            if r.randrange(2):
                P&=r.getrandbits(1<<n);N&=r.getrandbits(1<<n)
            if not P or not N:continue
            A=Bound(C[:n+q],P,N,mono);a=A.base(P|N,U);v=A.lower(U=U,depth=1);w=A.lower(U=U,depth=2)
            assert a<=v<=w<=b-q,(mono,n,b,q,U,a,v,w)
            ct.update(cases=1,depth1_gain=v>a,depth2_gain=w>v,exact_base=a==b-q,exact_depth2=w==b-q)
            if ct['cases']<=80:
                z=A.first(U,0);zz=A.first(U,1)
                assert a<=z<=zz<=b-q and v<=zz,(mono,n,b,q,U,a,v,z,zz)
                ct.update(lookahead_cases=1,lookahead_gain=z>a,combined_gain=zz>max(z,v))
            if v>a and example is None:example=(mono,n,b,q,tuple(C[:n+q]),P,N,U,a,v,w)
        print('monotone',mono,dict(ct),flush=True);counts.update(ct)
    print('total',dict(counts),'example',example,'seconds',round(perf_counter()-t,3),flush=True)
if __name__=='__main__':test()


def exact_small_test():
    """Independent exhaustive 0/1/2-gate circuits on random 4-row columns.
    Track structural input use, even when columns are equal/constant.
    """
    r=Random(614);ct=Counter();t=perf_counter();mask=15
    for mono in (True,False):
        for _ in range(60):
            m=r.randrange(2,5);C=tuple(r.randrange(16) for _ in range(m));allU=(1<<m)-1
            known={}
            def add(f,u,k):
                for g in (f,) if mono else (f,f^mask):
                    for s in range(1<<m):
                        if s&~u==0:known[g,s]=min(k,known.get((g,s),INF))
            def gates(V):
                for i,j in combinations(range(len(V)),2):
                    a,u=V[i];b,v=V[j]
                    vals=(a&b,a|b) if mono else tuple(x&y for x,y in product((a,a^mask),(b,b^mask)))
                    for z in vals:yield i,j,z,u|v
            V=tuple((c,1<<i) for i,c in enumerate(C))
            for f,u in V:add(f,u,0)
            for _,_,f,u in gates(V):
                add(f,u,1)
                for i,j,g,v in gates(V+((f,u),)):
                    if j==m:add(g,v,2)
            for labels in product(range(3),repeat=4):
                P=sum(1<<i for i,x in enumerate(labels) if x==1);N=sum(1<<i for i,x in enumerate(labels) if x==2)
                if not P or not N:continue
                A=Bound(C,P,N,mono)
                for U in range(1<<m):
                    opt=min((k for (f,s),k in known.items() if s==U and f&P==P and not f&N),default=INF)
                    if opt==INF:continue
                    a=A.base(P|N,U);b=A.lower(U=U,depth=2)
                    assert a<=b<=opt,(mono,C,P,N,U,a,b,opt)
                    ct.update(exact_cases=1,gain=b>a)
                    if opt and ct['exact_cases']%13==0:
                        z=A.first(U,1);assert b<=z<=opt,(mono,C,P,N,U,b,z,opt);ct['lookahead_checked']+=1
    print('independent small suffix oracle',dict(ct),'seconds',round(perf_counter()-t,3),flush=True)

if __name__=='__main__':exact_small_test()
