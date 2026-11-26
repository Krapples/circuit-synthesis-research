"""Deterministic image compression via simultaneous orthogonal blocks.
Sparse-rank merge reference; Python operations are not synthesized gates.
"""
from random import Random
from quadratic_witness_check import histogram, brute, restrict, evaluate, toggle, packed, polynomial
from permutable_andreev_check import params


def bits(x):
    while x:
        b=x&-x; yield b.bit_length()-1; x^=b


def independent(items, limit=None):
    piv={}; out=[]
    for tag,v in items:
        while v:
            i=v.bit_length()-1
            if i not in piv:
                piv[i]=v; out.append(tag); break
            v^=piv[i]
        if limit is not None and len(out)>=limit: break
    return out


def kernel(rows, indices):
    """Pivot coordinate indices and a kernel basis on given coordinates."""
    piv={}; cols=[]; ker=[]
    for j in indices:
        v=sum(((r>>j)&1)<<i for i,r in enumerate(rows)); x=1<<j
        while v:
            i=v.bit_length()-1
            if i not in piv:
                piv[i]=(v,x); cols.append(j); break
            w,y=piv[i]; v^=w; x^=y
        if not v: ker.append(x)
    return cols,ker


def certificate(rows, limit):
    """Truncated row basis with same-size nonsingular column minor."""
    assert limit>0
    def merge(ids):
        cols={}
        for i,r in enumerate(ids):
            for j in bits(rows[r]): cols[j]=cols.get(j,0)|(1<<i)
        C=independent(sorted(cols.items()),limit)
        R=independent((r,sum(((rows[r]>>c)&1)<<j for j,c in enumerate(C))) for r in ids)
        assert len(R)==len(C)
        return R,C
    level=[([i],[]) for i,v in enumerate(rows) if v]
    if not level:return [],[]
    while len(level)>1:
        level=[merge(level[i][0]+(level[i+1][0] if i+1<len(level) else [])) for i in range(0,len(level),2)]
    return merge(level[0][0])


def polar(D,x,y):
    ans=0
    for m,v in D.items():
        if m.bit_count()==2:
            a=m&-m; b=m^a
            if (bool(x&a)*bool(y&b))^(bool(x&b)*bool(y&a)): ans^=v
    return ans


def polar_rows(D,q,lam):
    rows=[0]*q
    for m,v in D.items():
        if m.bit_count()==2 and (lam&v).bit_count()%2:
            i,j=bits(m); rows[i]^=1<<j; rows[j]^=1<<i
    return rows


def constraints(D,k,q,W):
    L=[]
    for w in W:
        rows=[0]*k
        for m,v in D.items():
            if m.bit_count()!=2:continue
            a=m&-m; b=m^a; t=(b if w&a else 0)^(a if w&b else 0)
            for j in bits(v):rows[j]^=t
        L.extend(rows)
    return L


def witness(D,q,L,I,lam):
    B=polar_rows(D,q,lam); r=len(I)
    aug=[v|sum(((l>>j)&1)<<(q+i) for i,l in enumerate(L)) for j,v in enumerate(B)]+L
    R,C=certificate(aug,2*r+1)
    if len(R)<=2*r:return None
    S=sorted(set(I)|{j for j in R+C if j<q})
    _,K=kernel(L,S)
    for i,x in enumerate(K):
        for y in K[i+1:]:
            v=polar(D,x,y)
            if (v&lam).bit_count()%2:return x,y,v
    raise AssertionError('augmented rank certificate did not yield a pair')


def label_span(D,k,q,L,I):
    U=[]; pairs=[]
    while True:
        _,ann=kernel(U,range(k))
        for lam in ann:
            hit=witness(D,q,L,I,lam)
            if hit:
                x,y,v=hit; U.append(v); pairs.extend([x,y]); break
        else:return U,pairs
        assert len(U)<=k


def compression(D,k,q):
    W=[]; L=[]; I=[]
    for _ in range(2*k):
        U,block=label_span(D,k,q,L,I)
        if not block:break
        W.extend(block); L=constraints(D,k,q,W); I,_=kernel(L,range(q))
    U,_=label_span(D,k,q,L,I); _,ann=kernel(U,range(k))
    _,K=kernel(L,range(q))
    def project(v):return sum(((v&a).bit_count()%2)<<j for j,a in enumerate(ann))
    S=[1<<i for i in I]; t=len(ann)
    def signature(v):
        return project(evaluate(D,v)^evaluate(D,0)) | sum(project(polar(D,s,v))<<(t*(i+1)) for i,s in enumerate(S))
    Z=independent((v,signature(v)) for v in K)
    E=independent((w,w) for w in W+S+Z)
    forms=[{1<<j for j,w in enumerate(E) if w>>i&1} for i in range(q)]
    Q=restrict(D,forms)
    assert len(E)<=4*k*k+4*k**3+k*(1+4*k**3)
    return Q,E,ann,len(W),len(I),len(Z)


def check(D,k,q,stats):
    Q,E,ann,w,r,z=compression(D,k,q)
    H=histogram(D,k,q); K=histogram(Q,k,len(E))
    assert [bool(a) for a in H]==[bool(a) for a in K]
    if q<=10:assert H==brute(D,k,q); stats['brute']+=1
    for lam in range(1,1<<k):
        in_low=len(independent((a,a) for a in ann+[lam]))==len(ann)
        if not in_low:
            rows=polar_rows(Q,len(E),lam)
            assert len(independent(enumerate(rows)))>=4*k
            stats['high_rank']+=1
    stats['maps']+=1; stats['image_bits']+=1<<k; stats['compressed']+=len(E)<q
    stats['mixed']+=0<len(ann)<k; stats['max_q']=max(stats['max_q'],q)
    stats['max_d']=max(stats['max_d'],len(E)); stats['max_removed']=max(stats['max_removed'],q-len(E))
    return len(E),len(ann)


def main():
    rng=Random(870010)
    stats=dict(rank_certificates=0, maps=0, brute=0,image_bits=0,high_rank=0,compressed=0,mixed=0,max_q=0,max_d=0,max_removed=0,packed_maps=0)
    for _ in range(1000):
        n=rng.randrange(0,40); m=rng.randrange(1,45); T=rng.randrange(1,12)
        rows=[sum(1<<j for j in range(m) if rng.randrange(7)==0) for i in range(n)]
        R,C=certificate(rows,T)
        assert len(R)==len(C)==min(T,len(independent(enumerate(rows))))
        assert len(independent((i,sum(((rows[r]>>c)&1)<<j for j,c in enumerate(C))) for i,r in enumerate(R)))==len(R)
        stats['rank_certificates']+=1
    for k in range(1,6):
        for _ in range(36):
            q=rng.randrange(0,11); D={0:rng.randrange(1<<k)}
            for i in range(q):
                if rng.randrange(3)==0:toggle(D,1<<i,rng.randrange(1<<k))
                for j in range(i):
                    if rng.randrange(4)==0:toggle(D,(1<<i)|(1<<j),rng.randrange(1<<k))
            check(D,k,q,stats)
        # Mixed high-rank forms plus low-rank dense star and affine dependence.
        if k>=2:
            q=2*(k-1)*4*k+20; D={0:1}
            for i in range(k-1):
                for j in range(4*k):toggle(D,3<<(2*(4*k*i+j)),1<<i)
            a=2*(k-1)*4*k
            for j in range(a+1,q):toggle(D,(1<<a)|(1<<j),1<<(k-1))
            toggle(D,1<<(q-1),1<<(k-1))
            assert check(D,k,q,stats)[1]==1
    for k in range(1,7):
        M,ell,J,r,P,B,A,Q=params(k); m=k*J
        for _ in range(8):
            h=[rng.randrange(2) for _ in range(M)]; x=[rng.randrange(2) for _ in range(k*r)]
            order=list(range(m)); rng.shuffle(order); labels=[(rng.randrange(min(m,9)+1),rng.randrange(min(m,9)+1)) for i in range(m)]
            word,ids=packed(k,h,x,order,labels); D=polynomial(k,x,order,labels,ids)
            check(D,k,len(ids),stats); stats['packed_maps']+=1
    print(stats);print('all assertions passed')

if __name__=='__main__':main()
