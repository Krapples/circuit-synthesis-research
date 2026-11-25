"""Exact NOT minimization on a fixed signed AND/OR DAG (standard library).
Gate (op,l,r,a,b) computes op(value[l]^a,value[r]^b), a,b in {0,1}.
All binary gates and inputs belong to the output cone. Output phase out in {0,1}.
No binary rewiring, merging, or reassociation; only De Morgan phase choices
and at most one shared inverter per source. Returns optimum and phase witness.
"""
from itertools import product
from random import Random
from time import perf_counter
from collections import Counter, deque
INF=10**9

def structure(n,gates,out):
    if n<1 or out not in (0,1):raise ValueError('invalid inputs or output')
    N=n+len(gates);reads=[[] for _ in range(N)]
    for v,(op,l,r,a,b) in enumerate(gates,n):
        if op not in ('AND','OR') or not 0<=l<r<v or a not in (0,1) or b not in (0,1):raise ValueError('invalid gate')
        reads[l].append((v,a));reads[r].append((v,b))
    reads[-1].append((N,out)) # dummy output consumer, phase 0
    if any(not x for x in reads):raise ValueError('trimmed output cone required')
    return reads

def cost(n,gates,out,phases):
    reads=structure(n,gates,out);N=len(reads)
    if len(phases)!=N or any(phases[:n]) or any(p not in (0,1) for p in phases):raise ValueError('invalid phases')
    p=tuple(phases)+(0,)
    return sum(any(p[u] != (p[v]^a) for v,a in rr) for u,rr in enumerate(reads))

def optimize(n,gates,out=0):
    reads=structure(n,gates,out);N=len(reads)
    shared=[u for u in range(N) if len(reads[u])>1]
    states=[(0,2) if u<n else (0,1,2) for u in shared]
    best=INF;bestph=None
    # d[v][p] = private-subtree cost delivering phase p to its single reader.
    # raw[v][p] = cost of computing phase p before an optional inverter at v.
    for ss in product(*states):
        state=dict(zip(shared,ss));d=[];raw=[];extra=0;rootphase={}
        for v in range(N):
            if v<n:c=(0,INF)
            else:
                _,l,r,a,b=gates[v-n]
                c=tuple(d[l][a^p]+d[r][b^p] for p in (0,1))
            raw.append(c)
            if v in state:
                s=state[v]
                if s==2:
                    p=int(c[1]<c[0]);extra+=1+c[p];rootphase[v]=p;d.append((0,0))
                else:
                    extra+=c[s];rootphase[v]=s;d.append((0,INF) if s==0 else (INF,0))
            else:d.append(tuple(min(c[p],1+c[1-p]) for p in (0,1)))
        total=extra+d[-1][out]
        if total>=best:continue
        phases=[None]*N
        def trace(v,req,root=False):
            if v in state and not root:return
            p=rootphase[v] if root else (req if raw[v][req]<=1+raw[v][1-req] else 1-req)
            phases[v]=p
            if v>=n:
                _,l,r,a,b=gates[v-n];trace(l,a^p);trace(r,b^p)
        for v in shared:trace(v,0,True)
        trace(N-1,out)
        assert all(p is not None for p in phases)
        assert cost(n,gates,out,phases)<=total
        best=cost(n,gates,out,phases);bestph=tuple(phases)
    assert bestph is not None
    return best,bestph

def brute(n,gates,out=0):
    return min((cost(n,gates,out,(0,)*n+p), (0,)*n+p) for p in product((0,1),repeat=len(gates)))

def balance_gauge(n,gates,out=0):
    reads=structure(n,gates,out);N=len(reads);adj=[[] for _ in range(N+1)]
    for u,rr in enumerate(reads):
        for v,a in rr:adj[u].append((v,a));adj[v].append((u,a))
    q=[None]*(N+1)
    for v in range(N+1):
        if q[v] is not None:continue
        q[v]=0;stack=[v]
        while stack:
            x=stack.pop()
            for y,a in adj[x]:
                t=q[x]^a
                if q[y] is None:q[y]=t;stack.append(y)
                elif q[y]!=t:return None
    return q

def balanced_optimize(n,gates,out=0):
    """Polynomial min-cut for balanced signed graphs. None if unbalanced."""
    reads=structure(n,gates,out);N=len(reads);q=balance_gauge(n,gates,out)
    if q is None:return None
    S=3*N+1;T=S+1;adj=[{} for _ in range(T+1)]
    def arc(u,v,c):
        adj[u][v]=adj[u].get(v,0)+c;adj[v].setdefault(u,0)
    for u,rr in enumerate(reads):
        a=N+1+2*u;b=a+1;arc(a,b,1)
        for v in {u,*[v for v,_ in rr]}:arc(v,a,N+1);arc(b,v,N+1)
    for u in [*range(n),N]:
        if q[u]:arc(S,u,N+1)
        else:arc(u,T,N+1)
    flow=0
    while True:
        parent={S:None};queue=deque([S])
        while queue and T not in parent:
            u=queue.popleft()
            for v,c in adj[u].items():
                if c and v not in parent:parent[v]=u;queue.append(v)
        if T not in parent:break
        v=T;amount=INF
        while v!=S:u=parent[v];amount=min(amount,adj[u][v]);v=u
        v=T
        while v!=S:u=parent[v];adj[u][v]-=amount;adj[v][u]+=amount;v=u
        flow+=amount
    phases=tuple(int(v in parent)^q[v] for v in range(N))
    assert cost(n,gates,out,phases)==flow
    return flow,phases

def generate(rng,n,B,balanced=False):
    # Build backwards from output, choosing either an input or a previous gate.
    # Simpler rejection: random forward DAG then trim and renumber all nodes.
    raw=[]
    for v in range(n,n+B):
        l,r=sorted(rng.sample(range(v),2));raw.append((rng.choice(('AND','OR')),l,r,rng.randrange(2),rng.randrange(2)))
    live={n+B-1}
    for v in range(n+B-1,n-1,-1):
        if v in live:live.update(raw[v-n][1:3])
    ins=sorted(v for v in live if v<n);m=len(ins);ids={v:i for i,v in enumerate(sorted(live))}
    gs=[(op,ids[l],ids[r],a,b) for v,(op,l,r,a,b) in enumerate(raw,n) if v in live]
    out=rng.randrange(2)
    if balanced:
        q=[rng.randrange(2) for _ in live];gs=[(op,l,r,q[l]^q[v],q[r]^q[v]) for v,(op,l,r,_,_) in enumerate(gs,m)]
    return m,gs,out

def test():
    rng=Random(291);t=perf_counter();stats=Counter()
    for i in range(600):
        n,g,out=generate(rng,rng.randrange(2,7),rng.randrange(1,10),i%2==0)
        expected=brute(n,g,out)[0];actual,ph=optimize(n,g,out)
        assert actual==expected,(n,g,out,actual,expected)
        mc=balanced_optimize(n,g,out)
        if mc is not None:assert mc[0]==expected;stats['balanced']+=1
        naive=cost(n,g,out,(0,)*(n+len(g)))
        stats['checks']+=1;stats['naive_NOT']+=naive;stats['optimal_NOT']+=actual;stats['improved']+=actual<naive
        stats['shared']+=any(len(x)>1 for x in structure(n,g,out))
    print(dict(stats),'seconds',round(perf_counter()-t,3))
    # Large balanced graphs: polynomial mode, no exponential oracle.
    t=perf_counter();large=[]
    for i in range(20):
        n,g,out=generate(rng,12,200,True);actual,ph=balanced_optimize(n,g,out);large.append((len(g),actual))
    print('large balanced checks',len(large),'binary gates',sum(x for x,_ in large),'max gates',max(x for x,_ in large),'seconds',round(perf_counter()-t,3))

def materialize(n,gates,out,phases):
    """Produce counted AND/OR/NOT gate list and output index."""
    cost(n,gates,out,phases)
    result=[];wire=list(range(n));neg={}
    def get(u,req):
        if phases[u]==req:return wire[u]
        if u not in neg:
            neg[u]=n+len(result);result.append(('NOT',wire[u]))
        return neg[u]
    for v,(op,l,r,a,b) in enumerate(gates,n):
        p=phases[v];x=get(l,a^p);y=get(r,b^p)
        wire.append(n+len(result));result.append((op if not p else ('OR' if op=='AND' else 'AND'),x,y))
    output=get(len(wire)-1,out)
    assert sum(g[0]=='NOT' for g in result)==cost(n,gates,out,phases)
    return result,output

def oct_graph(n,gates,out=0):
    """Ordinary graph, allowed deletion vertices indexed n+B+2+u.
    All remaining vertices are protected. Equalities become two-edge paths.
    Removing the vertex for provider u permits its shared inverter.
    """
    reads=structure(n,gates,out);N=len(reads);anchor=N+1;allowed=tuple(range(N+2,2*N+2));adj=[set() for _ in range(2*N+2)]
    def edge(u,v):adj[u].add(v);adj[v].add(u)
    def parity(u,v,a):
        if a:edge(u,v)
        else:
            x=len(adj);adj.append(set());edge(u,x);edge(x,v)
    for u,rr in enumerate(reads):
        t=allowed[u];parity(u,t,0)
        for v,a in rr:parity(t,v,a)
    for v in [*range(n),N]:parity(anchor,v,0)
    return adj,allowed,anchor

def oct_coloring(adj,removed):
    col={}
    for v in range(len(adj)):
        if v in removed or v in col:continue
        col[v]=0;queue=[v]
        for u in queue:
            for x in adj[u]:
                if x in removed:continue
                if x in col:
                    if col[x]==col[u]:return None
                else:col[x]=1-col[u];queue.append(x)
    return col

def oct_brute(n,gates,out=0):
    from itertools import combinations
    adj,allowed,anchor=oct_graph(n,gates,out)
    for k in range(len(allowed)+1):
        for sub in combinations(allowed,k):
            c=oct_coloring(adj,set(sub))
            if c is not None:
                ph=tuple(c[v]^c[anchor] for v in range(n+len(gates)))
                assert cost(n,gates,out,ph)==k
                return k,ph
    raise AssertionError('all groups removed must be consistent')

def truth(n,gates,out,ph):
    values=[sum(1<<a for a in range(1<<n) if a>>i&1) for i in range(n)];one=(1<<(1<<n))-1
    for op,l,r,a,b in gates:
        x=values[l]^(one if a else 0);y=values[r]^(one if b else 0)
        values.append(x&y if op=='AND' else x|y)
    expected=values[-1]^(one if out else 0)
    raw,idx=materialize(n,gates,out,ph);values=values[:n]
    for g in raw:
        if g[0]=='NOT':values.append(one^values[g[1]])
        elif g[0]=='AND':values.append(values[g[1]]&values[g[2]])
        else:values.append(values[g[1]]|values[g[2]])
    assert expected==values[idx]

def extended_test():
    rng=Random(292);t=perf_counter();stats=Counter()
    for i in range(300):
        n,g,out=generate(rng,rng.randrange(2,6),rng.randrange(1,8),i%2==0)
        a,p=optimize(n,g,out);b,q=oct_brute(n,g,out)
        assert a==b
        truth(n,g,out,p);truth(n,g,out,q)
        stats['OCT comparisons']+=1;stats['truth-table witness comparisons']+=2
    print(dict(stats),'seconds',round(perf_counter()-t,3))

if __name__=="__main__":
    test();extended_test()
