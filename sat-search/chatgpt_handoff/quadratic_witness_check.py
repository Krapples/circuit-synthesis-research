"""Quadratic packed SAT, exact Walsh image, and affine compression regression."""
from itertools import product
from random import Random
from permutable_andreev_check import params, build, parse, encode_clause, balance, unit_decide


def packed(k, h, x, order, labels):
    M, ell, J, r, P, B, A, Q = params(k)
    m = k*J
    assert len(labels)==m and all(0<=u<=m for pair in labels for u in pair)
    Q2 = 1 << (max(4*P,A+3*m+1)-1).bit_length()
    old,_,_ = build(k,h,x,order)
    def rename(l):
        v=abs(l)+(Q2-Q if abs(l)>Q else 0)
        return v if l>0 else -v
    F=[[rename(l) for l in C] for C in parse(old)]
    def e(u): return Q2+A+2*m+u+1
    out=F[:P]+[[-e(0)]]
    for i,(u,v) in enumerate(labels):
        a,b=F[P+2*i:P+2*i+2]; z=b[0]
        t=Q2+A+i+1; p=Q2+A+m+i+1
        out.extend([[-t,a[1]],[t,b[1]],[-p,e(u)],[-p,e(v)],[p,-e(u),-e(v)]])
        for X,Y in product((0,1),repeat=2):
            out.append([l if not bit else -l for l,bit in zip((t,p,z),(X,Y,1^X^Y))])
    out.extend(F[P+2*m:])
    w=[v for C in out for v in encode_clause(C)]
    assert parse(w)==out and all(abs(l)-1<2*Q2 for C in out for l in C)
    return w,{u:e(u) for u in sorted({v for p in labels for v in p if v})}


def toggle(D,m,v):
    if v:
        D[m]=D.get(m,0)^v
        if not D[m]: del D[m]


def polynomial(k,x,order,labels,ids):
    M,ell,J,r,P,B,A,Q=params(k)
    idx={u:i for i,u in enumerate(ids)}; D={}
    for i,(j,(u,v)) in enumerate(zip(order,labels)):
        bit=1<<(j//J)
        if sum(x[i*ell:(i+1)*ell])%2: toggle(D,0,bit)
        if u and v: toggle(D,(1<<idx[u])|(1<<idx[v]),bit)
    return D


def evaluate(D,z):
    a=0
    for m,v in D.items():
        if z&m==m: a^=v
    return a


def multiply(L,R):
    P=set()
    for l in L:
        for r in R: P.symmetric_difference_update({l|r})
    return P


def scalar(D,lam):
    return {m for m,v in D.items() if (v&lam).bit_count()%2}


def character(P,d):
    """Exact sum of (-1)^P over d bits, eliminating a quadratic pair at a time."""
    P=set(P); t=0
    while True:
        pair=next((m for m in P if m.bit_count()==2),None)
        if pair is None: break
        a=pair&-pair; b=pair^a; P.remove(pair)
        L={m^a for m in P if m&a}; R={m^b for m in P if m&b}
        P={m for m in P if not m&pair} ^ multiply(L,R)
        t+=1
    return 0 if P-{0} else (-1 if 0 in P else 1)*(1<<(d-t))


def polar_rank(P,d):
    rows=[0]*d
    for m in P:
        if m.bit_count()==2:
            a=m&-m; b=m^a
            rows[a.bit_length()-1]^=b; rows[b.bit_length()-1]^=a
    piv={}
    for v in rows:
        while v:
            i=v.bit_length()-1
            if i not in piv: piv[i]=v; break
            v^=piv[i]
    return len(piv)


def histogram(D,k,d):
    a=[character(scalar(D,lam),d) for lam in range(1<<k)]
    step=1
    while step<len(a):
        for i in range(0,len(a),2*step):
            for j in range(i,i+step):
                x,y=a[j],a[j+step]; a[j],a[j+step]=x+y,x-y
        step*=2
    assert all(x>=0 and x%(1<<k)==0 for x in a)
    a=[x>>k for x in a]; assert sum(a)==1<<d
    return a


def restrict(D,forms):
    """Each original variable is an affine polynomial in new variables."""
    E={}
    for m,v in D.items():
        P={0}
        for i,L in enumerate(forms):
            if m>>i&1: P=multiply(P,L)
        for p in P: toggle(E,p,v)
    return E


def random_forms(q,d,rng):
    return [{m for m in [0]+[1<<i for i in range(d)] if rng.randrange(2)} for _ in range(q)]


def brute(D,k,q):
    H=[0]*(1<<k)
    for z in range(1<<q): H[evaluate(D,z)]+=1
    return H


def defeat_fixed_sketches(rng):
    """Construct a nonzero linear annihilator of all affine sketches, then multiply by a fresh bit."""
    for _ in range(128):
        t=rng.randrange(1,5); d=rng.randrange(1,8); J=t*(d+1)+1
        sketches=[random_forms(J+1,d,rng) for _ in range(t)]
        piv={}; relation=0
        for i in range(J):
            v=sum(1<<(j*(d+1)+m.bit_length()) for j,L in enumerate(sketches) for m in L[i])
            mask=1<<i
            while v:
                b=v.bit_length()-1
                if b not in piv: piv[b]=(v,mask); break
                w,c=piv[b]; v^=w; mask^=c
            if not v: relation=mask; break
        assert relation
        D={(1<<J)|(1<<i):1 for i in range(J) if relation>>i&1}
        assert evaluate(D,(relation&-relation)|(1<<J))==1
        assert all(not restrict(D,S) for S in sketches)
    return 128


def main():
    rng=Random(870009); stats=dict(cases=0,pinned_sat=0,balanced_sat=0,coordinate_probes=0,
        rank_checks=0,exact_histograms=0,restriction_checks=0,compression_trials=0,compression_misses=0,
        rare_trials=0,rare_misses=0,high_rank_checks=0,missing_address_cases=0)
    for k in range(1,8):
        M,ell,J,r,P,B,A,Q=params(k); m=k*J
        for trial in range(12):
            h=[rng.randrange(2) for _ in range(M)]; x=[rng.randrange(2) for _ in range(k*r)]
            order=list(range(m)); rng.shuffle(order); limit=min(m,4)
            labels=[(rng.randrange(limit+1),rng.randrange(limit+1)) for _ in range(m)]
            w,ids=packed(k,h,x,order,labels); F=parse(w); G=parse(balance(w)); q=len(ids)
            D=polynomial(k,x,order,labels,ids); H=brute(D,k,q)
            assert histogram(D,k,q)==H; stats['exact_histograms']+=1
            for z in range(1<<q):
                pins=[[v if z>>i&1 else -v] for i,v in enumerate(ids.values())]
                want=bool(h[evaluate(D,z)])
                assert unit_decide(F+pins)==want and unit_decide(G+pins)==want
                stats['pinned_sat']+=1; stats['balanced_sat']+=1
            if trial<2:
                order2=order[::-1]; labels2=[(0,0)]*m
                w2,_=packed(k,h,x,order2,labels2)
                for data,size,copies in [(False,len(x),2),(True,M,1)]:
                    i=rng.randrange(size); X=x[:]; T=h[:]; (T if data else X)[i]^=1
                    w3,_=packed(k,T,X,order,labels); w4,_=packed(k,T,X,order2,labels2)
                    assert len(w)==len(w2)==len(w3)==len(w4)
                    a={j for j,(u,v) in enumerate(zip(w,w3)) if u!=v}
                    b={j for j,(u,v) in enumerate(zip(w2,w4)) if u!=v}
                    assert a==b and len(a)==copies; stats['coordinate_probes']+=1
            for lam in range(1,M):
                S=scalar(D,lam); rank=polar_rank(S,q); bias=character(S,q)
                assert rank%2==0 and abs(bias) in (0,1<<(q-rank//2))
                stats['rank_checks']+=1
            if 0 in H:
                assert any(character(scalar(D,l),q) and polar_rank(scalar(D,l),q)<=2*k-2 for l in range(1,M))
                stats['missing_address_cases']+=1
            assert all(not a or a*(1<<(2*k))>=1<<q for a in H)
            for d in (min(q+1,5),3*k+2):
                forms=random_forms(q,d,rng); E=restrict(D,forms); K=histogram(E,k,d)
                for z in range(min(1<<d,32)):
                    old=sum((sum(z&m==m for m in L)%2)<<i for i,L in enumerate(forms))
                    assert evaluate(E,z)==evaluate(D,old); stats['restriction_checks']+=1
                assert all(not a or b for a,b in zip(K,H))
                if d<=5: assert K==brute(E,k,d); stats['exact_histograms']+=1
                if d==3*k+2:
                    stats['compression_trials']+=1
                    stats['compression_misses']+=any(b and not a for a,b in zip(K,H))
            stats['cases']+=1
    # Sharp density example: k independent ANDs, target all ones has density 2^(-2k).
    for k in range(1,5):
        q=2*k; D={(3<<(2*i)):1<<i for i in range(k)}
        H=histogram(D,k,q); assert H[-1]==1
        for _ in range(64):
            d=2*k+2; E=restrict(D,random_forms(q,d,rng)); K=histogram(E,k,d)
            stats['rare_trials']+=1; stats['rare_misses']+=K[-1]==0
        # Disjoint blocks of k pairs per output guarantee polar rank >=2k.
        D={(3<<(2*(i*k+j))):1<<i for i in range(k) for j in range(k)}; q=2*k*k
        for lam in range(1,1<<k):
            assert polar_rank(scalar(D,lam),q)>=2*k; stats['high_rank_checks']+=1
        assert all(histogram(D,k,q))
    stats['fixed_sketch_counterexamples']=defeat_fixed_sketches(rng)
    print(stats); print('all assertions passed')

if __name__=='__main__': main()
