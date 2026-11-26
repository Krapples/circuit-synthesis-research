from collections import Counter, defaultdict
from itertools import product
from random import Random

# Independent baseline: choose one available vertex per group.
def transversal(groups, edges, available):
    adj=defaultdict(set)
    for a,b in edges: adj[a].add(b); adj[b].add(a)
    def go(opts):
        if not opts: return True
        i=min(range(len(opts)),key=lambda i:len(opts[i]))
        return any(go([o-adj[v] for j,o in enumerate(opts) if j!=i]) for v in opts[i])
    return go([set(g)&available for g in groups])

def background(vertices, edges, private):
    """Connected components and deficient labels in a resource multigraph."""
    vertices=set(vertices); adj={v:[] for v in vertices}
    for a,b in edges: adj[a].append(b); adj[b].append(a)
    label={}; sizes=Counter()
    for r in sorted(vertices):
        if r in label: continue
        label[r]=r; stack=[r]
        while stack:
            v=stack.pop(); sizes[r]+=1
            for w in adj[v]:
                if w not in label: label[w]=r; stack.append(w)
    counts=Counter(label[a] for a,b in edges)
    supplied={label[v] for v in private}
    deficient={r for r,n in sizes.items() if counts[r]<n and r not in supplied}
    assert all(counts[r]==sizes[r]-1 for r in deficient)
    return label,deficient

def first_stage(groups,matching,forks,available):
    owner={v:i for i,g in enumerate(groups) for v in g}
    used={v for e in matching for v in e}|{v for f in forks for v in f}
    private={owner[v] for v in available-used}; edges=[]
    for a,b in matching:
        u,v=owner[a],owner[b]
        if a in available and b in available and u!=v: edges.append((u,v))
        else:
            if a in available: private.add(u)
            if b in available: private.add(v)
    labels,D=background(range(len(groups)),edges,private)
    records=[tuple(labels[owner[v]] if v in available and labels[owner[v]] in D else None for v in f) for f in forks]
    return D,records

def kernel(D,records):
    clauses={c:[] for c in D}
    for i,(c,a,b) in enumerate(records,1):
        for v,l in ((c,i),(a,-i),(b,-i)):
            if v is not None: clauses[v].append(l)
    cs=list(clauses.values())
    counts=Counter(l for cl in cs for l in cl)
    assert sum(map(len,cs))<=3*len(records)
    assert all(counts[i]<=1 and counts[-i]<=2 for i in range(1,len(records)+1))
    return cs

def brute_cnf(cs,k):
    return any(all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs) for x in range(1<<k))

def mode_eval(D,records):
    """Independent set-cover interpretation, not the CNF evaluator."""
    for x in range(1<<len(records)):
        covered=set()
        for i,(c,a,b) in enumerate(records): covered.update((c,) if x>>i&1 else (a,b))
        if D<=covered: return True
    return False

def simplify(D,records):
    """Reduce dominated modes and two-choice resources, then contract again."""
    private=set(); edges=[]; genuine=[]
    for c,a,b in records:
        C={c}-{None}; L={a,b}-{None}
        if C<=L: private.update(L)
        elif L<=C: private.update(C)
        elif len(L)==1: edges.append((c,next(iter(L))))
        else:
            assert c is not None and len(L)==2 and c not in L
            genuine.append((c,a,b))
    lab,D2=background(D,edges,private)
    reduced=[tuple(lab[v] if lab[v] in D2 else None for v in f) for f in genuine]
    return D2,reduced

# AIG: 0/1 constants, primary/gate i represented by 2*i, complement ^1.
class AIG:
    def __init__(self,n): self.n=n; self.g=[]; self.memo={}
    def And(self,a,b):
        if a==0 or b==0 or a==b^1:return 0
        if a==1:return b
        if b==1 or a==b:return a
        a,b=sorted((a,b));key=(a,b)
        if key not in self.memo:
            self.g.append(key);self.memo[key]=2*(self.n+len(self.g))
        return self.memo[key]
    def Or(self,a,b):return self.And(a^1,b^1)^1
    def XOR(self,a,b):return self.Or(self.And(a,b^1),self.And(a^1,b))
    def all(self,ls):
        r=1
        for l in ls:r=self.And(r,l)
        return r
    def any(self,ls):return self.all(l^1 for l in ls)^1
    def eval_batch(self,inputs,out):
        mask=(1<<len(inputs))-1
        val=[0]+[sum(((row>>i)&1)<<j for j,row in enumerate(inputs)) for i in range(self.n)]
        def get(l):return val[l//2]^(mask if l&1 else 0)
        for a,b in self.g:val.append(get(a)&get(b))
        return get(out)

def core_circuit(k,w):
    """Inputs: uncovered flag, then for each of 3k slots (active, w-bit label).
    Active means available in a deficient component. Uncovered means some deficient
    component has no active endpoint. This is the post-background circuit only.
    """
    a=AIG(1+3*k*(w+1)); reject=2
    active=[]; labels=[]
    for j in range(3*k):
        off=1+j*(w+1);active.append(2*(off+1));labels.append([2*(off+2+i) for i in range(w)])
    # Compute clauses for every slot, including duplicates and inactive slots.
    # All clause truth vectors use the same lexicographic mode assignment order.
    joint=[1]*(1<<k)
    for j in range(3*k):
        related=[a.And(active[t],a.all(a.XOR(u,v)^1 for u,v in zip(labels[j],labels[t]))) for t in range(3*k)]
        vals=[active[j]^1]
        for i in range(k):
            p=related[3*i];n=a.Or(related[3*i+1],related[3*i+2])
            vals=[a.Or(v,l) for v in vals for l in (n,p)]
        joint=[a.And(u,v) for u,v in zip(joint,vals)]
    return a,a.And(reject^1,a.any(joint))

def encode_metadata(D,records,w):
    flat=[v for f in records for v in f]; r=int(not D<=set(flat))
    for j,v in enumerate(flat):
        if v is not None:r|=(1|(v<<1))<<(1+j*(w+1))
    return r

def partitions(vs):
    if not vs:yield [];return
    v,*rest=vs
    for p in partitions(rest):
        yield [(v,)]+p
        for j,g in enumerate(p):
            if len(g)<3:yield p[:j]+[(v,)+g]+p[j+1:]

def main():
    rng=Random(261126); counts=Counter(); batches=defaultdict(list); stats=Counter()
    def check(gs,match,forks,A,kind):
        edges=match+[(c,v) for c,a,b in forks for v in (a,b)]
        expected=transversal(gs,edges,A)
        D,R=first_stage(gs,match,forks,A);cs=kernel(D,R)
        assert brute_cnf(cs,len(R))==expected
        assert mode_eval(D,R)==expected
        assert not expected or len(D)<=2*len(R)
        D2,R2=simplify(D,R)
        assert brute_cnf(kernel(D2,R2),len(R2))==expected
        assert mode_eval(D2,R2)==expected
        assert len(R2)<=len(R)
        counts[kind]+=1;stats['forks']+=len(R);stats['genuine']+=len(R2)
        stats['no_genuine']+=not R2;stats['uncovered']+=any(not c for c in cs)
        stats['budget_reject']+=len(D)>2*len(R)
        stats['simplified']+=len(R2)<len(R)
        # Actual gate-level core circuit batch, both before and after simplification.
        w=max(1,(len(gs)-1).bit_length())
        for DD,RR in ((D,R),(D2,R2)):
            if len(RR)<=7:batches[len(RR),w].append((encode_metadata(DD,RR,w),expected))
    for n,match,forks in [(3,[],[(0,1,2)]),(5,[(3,4)],[(0,1,2)]),(6,[],[(0,1,2),(3,4,5)]),(6,[(3,4)],[(0,1,2)])]:
        for gs in partitions(list(range(n))):
            for mask in range(1<<n):
                check(gs,match,forks,{i for i in range(n) if mask>>i&1},'exhaustive')
    for _ in range(3500):
        n=rng.randrange(1,27);p=list(range(n));rng.shuffle(p);gs=[]
        while p:
            s=rng.randrange(1,4);gs.append(tuple(p[:s]));p=p[s:]
        p=list(range(n));rng.shuffle(p);k=rng.randrange(n//3+1)
        forks=[tuple(p[3*i:3*i+3]) for i in range(k)];p=p[3*k:];j=rng.randrange(len(p)//2+1)
        matching=[tuple(p[2*i:2*i+2]) for i in range(j)]
        A={v for v in range(n) if rng.random()<rng.choice((.35,.65,.95))}
        check(gs,matching,forks,A,'random')
    print('semantic checks',dict(counts));print('statistics',dict(stats))
    total=0
    for (k,w),rows in sorted(batches.items()):
        a,out=core_circuit(k,w)
        for start in range(0,len(rows),256):
            b=rows[start:start+256];v=a.eval_batch([x for x,y in b],out)
            assert v==sum(int(y)<<j for j,(x,y) in enumerate(b));total+=len(b)
    print('core AIG evaluations',total,'distinct circuit parameter pairs',len(batches))
    print('sample constructed core sizes (w=10):',[(k,len(core_circuit(k,10)[0].g)) for k in range(1,11)])
if __name__=='__main__':main()
