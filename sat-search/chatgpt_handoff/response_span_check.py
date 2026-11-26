"""Finite regression for joint response-span certificates and shared-witness SAT.
No SAT solver required. Run with Python 3 and networkx.
"""
from itertools import product
from collections import Counter
import json, random
import networkx as nx

class AIG:
    def __init__(self,n): self.n=n; self.g=[]
    def AND(self,a,b):
        v=2*(self.n+len(self.g)); self.g.append((a,b)); return v
    def OR(self,a,b): return self.AND(a^1,b^1)^1
    def XOR(self,a,b): return self.OR(self.AND(a,b^1),self.AND(a^1,b))
    def mux(self,q,a,b): return self.OR(self.AND(q,b),self.AND(q^1,a))

def specialize_all(C,d,k,ports):
    # Constants -2/-1, signed representative IDs >=0. A shared affine
    # hash recognizes XOR macros by their actual two child ANDs.
    M=1<<k; nodes=[None]*d; forms={}; ah={0:-2,1:-1}; sh={}
    for i in range(d):
        f=1<<(i+1); forms[i]=f; ah[f]=2*i; ah[f^1]=2*i+1
    A=[[2*i for i in range(d)]+[-2+((h>>j)&1) for j in range(k)] for h in range(M)]
    F=[[1<<(i+1) for i in range(d)]+[(h>>j)&1 for j in range(k)] for h in range(M)]
    def lit(v,l): return v[l>>1]^(l&1)
    def form(v,l):
        a=v[l>>1]; return None if a is None else a^(l&1)
    for j,(u,w) in enumerate(C.g):
        for h in range(M):
            x,y=lit(A[h],u),lit(A[h],w); a,b=form(F[h],u),form(F[h],w); z=None
            if a==0 or b==0: z=0
            elif a==1: z=b
            elif b==1: z=a
            elif a is not None and b is not None:
                if a==b: z=a
                elif a^b==1: z=0
            if u&1 and w&1 and min(u>>1,w>>1)>=C.n:
                p,q=C.g[(u>>1)-C.n]; other=C.g[(w>>1)-C.n]
                if sorted(other)==sorted([p^1,q^1]):
                    a,b=form(F[h],p),form(F[h],q)
                    if a is not None and b is not None: z=a^b
            if z is not None and z in ah: r=ah[z]
            elif x==-2 or y==-2 or x==(y^1): r=-2
            elif x==-1 or x==y: r=y
            elif y==-1: r=x
            else:
                key=tuple(sorted((x,y)))
                if key not in sh:
                    sh[key]=2*len(nodes); nodes.append(key)
                r=sh[key]
            if z is not None:
                assert z not in ah or ah[z]==r
                ah[z]=r; ah[z^1]=r^1
            A[h].append(r); F[h].append(z)
    outs=[[lit(a,l) for l in ports] for a in A]
    coeff=[[form(f,l) for l in ports] for f in F]
    return nodes,outs,coeff

def rank(rows):
    B={}
    for a in rows:
        while a:
            j=a.bit_length()-1
            if j in B:a^=B[j]
            else:B[j]=a;break
    return len(B)

def flow(nodes,outs,d,allowed=None):
    live=set(); todo=list(set(l>>1 for l in outs if l>=0))
    while todo:
        v=todo.pop()
        if v in live:continue
        live.add(v)
        if nodes[v]:todo.extend(l>>1 for l in nodes[v])
    G=nx.DiGraph(); s='s';t='t'; G.add_nodes_from([s,t])
    for v in live:
        G.add_edge((v,0),(v,1),capacity=1)
        if v<d:
            if allowed is None or v in allowed:G.add_edge(s,(v,0),capacity=1)
        else:
            for l in nodes[v]:G.add_edge((l>>1,1),(v,0),capacity=d+1)
    for v in set(l>>1 for l in outs if l>=0):G.add_edge((v,1),t,capacity=d+1)
    return nx.maximum_flow_value(G,s,t),len(live)

def candidate(k,rng):
    M=1<<k;d=M*M+M;C=AIG(d+k);rows=[]
    for j in range(M):
        V=[2*(j*M+(i^j)) for i in range(M)]
        for t in range(k):V=[C.mux(2*(d+t),v,V[i^(1<<t)]) for i,v in enumerate(V)]
        rows.append(V)
    outputs=[]
    for i in range(M):
        p=C.XOR(rows[i][i],2*(M*M+i))
        for j in range(M):
            if j!=i:p=C.XOR(p,rows[j][i])
        outputs.append(p)
    ports=outputs+[2*(M*M+i) for i in range(M)]
    nodes,outs,coef=specialize_all(C,d,k,ports)
    assert all(a is not None for row in coef for a in row)
    assert all(rank([a>>1 for a in row])==2*M for row in coef)
    assert len(set(a>>1 for row in coef for a in row[:M]))==M*M
    R=rank([a>>1 for row in coef for a in row]);assert R==2*M
    fl,live=flow(nodes,[l for row in outs for l in row],d);assert fl==d,(M,fl,d)
    checks=0
    minor_checks=0
    if M<=8:
        flat_out=[l for row in outs for l in row];flat_c=[a>>1 for row in coef for a in row]
        for _ in range(30):
            I={i for i in range(d) if rng.randrange(3)==0};J=[j for j in range(len(flat_out)) if rng.randrange(3)==0]
            mask=sum(1<<i for i in I);r=rank([flat_c[j]&mask for j in J])
            f,_=flow(nodes,[flat_out[j] for j in J],d,I);assert r<=f;minor_checks+=1
    for _ in range(100):
        x=rng.getrandbits(d);q=rng.randrange(M);V=[(x>>i)&1 for i in range(d)]+[(q>>j)&1 for j in range(k)]
        for a,b in C.g:V.append((V[a>>1]^(a&1))&(V[b>>1]^(b&1)))
        W=[(x>>i)&1 for i in range(d)]
        def l(v):return v+2 if v<0 else W[v>>1]^(v&1)
        for a,b in nodes[d:]:W.append(l(a)&l(b))
        for i,o in enumerate(ports):
            y=V[o>>1]^(o&1);z=l(outs[q][i]);c=coef[q][i]
            want=((c>>1&x).bit_count()^(c&1))&1
            assert y==z==want
            if i<M:
                p=(x>>(M*M+i))&1
                for j in range(M):p^=x>>(j*M+(q^i^j))&1
                assert y==p
            checks+=1
    return dict(M=M,data=d,original_ANDs=len(C.g),distinct_nondirect_responses=M*M,per_history_rank=2*M,quotient_flow=fl,span_rank=R,live_quotient_vertices=live,comparisons=checks,rank_minor_flow_checks=minor_checks)

# Shared-witness grammar, single-copy pattern digits. Zero-based variable IDs.
def enc(F):
    w=[]
    for C in F:
        for v,s in C:
            w.extend([1,s]);a=v
            while a:w.extend([1,a&1]);a>>=1
            w.extend([0,1])
        w.extend([0,0])
    return w

def parse(w):
    F=[];C=[];i=0
    while i<len(w):
        a,b=w[i:i+2];i+=2
        if a==0 and b==0:F.append(C);C=[];continue
        assert a==1;v=0;shift=0;last=1
        while True:
            a,z=w[i:i+2];i+=2
            if a==0:assert z==1 and last==1;break
            v|=z<<shift;shift+=1;last=z
        C.append((v,b))
    assert not C;return F

def packed(H,S,Q):
    m=len(H);ell=len(H[0]);k=(ell-1).bit_length();P=1<<ell
    assert ell==1<<k
    base=1<<((2*P+k-1).bit_length())
    # active and parking namespaces. Active dictionary uses witness bits;
    # parking dictionary variables are forced true.
    F=[];data=[];meta=[];w=[];width=base.bit_length()
    a=[base+2*P+j for j in range(k)]
    def emit(C):
        off=len(w);F.append(C);w.extend(enc([C]));return off
    for p in range(P):
        for t in range(ell):emit([(v,1-((t>>j)&1)) for j,v in enumerate(a)]+[(base+p,(p>>t)&1)])
        emit([(base+P+p,1)])
    emit([(base+Q,1)])
    for i,row in enumerate(H):
        p=sum(v<<j for j,v in enumerate(row));v=base+p+(0 if S>>i&1 else P)
        off=emit([(v,1)]);data.extend(off+3+2*j for j in range(ell));meta.append(off+3+2*ell)
    assert len(set(data+meta))==len(data+meta)
    return F,w,data,meta,a

def solve_witness(F,a,ell):
    # A witness assignment pins every dictionary variable by its unique
    # active clause; unit propagation detects a clash if any selected unit fails.
    for q in range(ell):
        vals={v:(q>>j)&1 for j,v in enumerate(a)}
        while True:
            pending=[];changed=False;bad=False
            for C in F:
                if any(vals.get(v)==s for v,s in C):continue
                U=[(v,s) for v,s in C if v not in vals]
                if not U:bad=True;break
                if len(U)==1:
                    v,s=U[0];vals[v]=s;changed=True
                else:pending.append(C)
            if bad:break
            if not changed:
                assert not pending
                return True
    return False

def witness_checks(rng):
    checks=coord=meta=qprobe=0;maxlen=0
    for m,ell in [(2,2),(3,2),(5,4),(8,8)]:
        for _ in range(32):
            H=[[rng.randrange(2) for _ in range(ell)] for _ in range(m)];S=rng.randrange(1<<m);Q=rng.randrange(1<<ell)
            F,w,D,B,a=packed(H,S,Q);assert parse(w)==F
            want=any(Q>>t&1 and all(not(S>>i&1) or H[i][t] for i in range(m)) for t in range(ell))
            assert solve_witness(F,a,ell)==want;checks+=1;maxlen=max(maxlen,len(w))
            i=rng.randrange(m);j=rng.randrange(ell);H[i][j]^=1
            _,w2,D2,B2,_=packed(H,S,Q);assert len(w)==len(w2) and D==D2 and B==B2
            assert [t for t,(v,z) in enumerate(zip(w,w2)) if v!=z]==[D[i*ell+j]];coord+=1
            H[i][j]^=1;_,w3,_,_,_=packed(H,S^(1<<i),Q)
            assert [t for t,(v,z) in enumerate(zip(w,w3)) if v!=z]==[B[i]];meta+=1
            t=rng.randrange(ell);_,w4,_,_,_=packed(H,S,Q^(1<<t))
            # Selector mask is in the unit clause just before the m payload units.
            qoff=len(w)-(m+1)*(2*(len(bin(a[0]))-2)+6)
            # a[0] exists for all tested ell>=2; IDs have the same width.
            assert [z for z,(v,y) in enumerate(zip(w,w4)) if v!=y]==[qoff+3+2*t];qprobe+=1
    return dict(cases=checks,single_copy_data_mutations=coord,single_copy_selection_mutations=meta,single_copy_query_mask_mutations=qprobe,max_word_bits=maxlen)

def matrix_checks():
    # Rank of shared-witness query matrix over GF(2). Empty selected set:
    # constant one for nonempty mask; empty mask always false.
    stats=[]
    for m,ell in [(1,2),(2,2),(3,2),(2,4),(3,4)]:
        cols=[];d=m*ell
        for S in range(1<<m):
            for Q in range(1<<ell):
                c=0
                for x in range(1<<d):
                    f=any(Q>>t&1 and all(not(S>>i&1) or x>>(i*ell+t)&1 for i in range(m)) for t in range(ell))
                    if f:c|=1<<x
                cols.append(c)
        R=rank(cols);want=1+((1<<m)-1)*((1<<ell)-1);assert R==want
        rows={tuple(c>>x&1 for c in cols) for x in range(1<<d)};assert len(rows)==1<<d
        
        # Mobius transform of the all-rows/all-columns query truth table.
        coeff=[(cols[-1]>>x)&1 for x in range(1<<d)]
        for i in range(d):
            for x in range(1<<d):
                if x>>i&1:coeff[x]^=coeff[x^(1<<i)]
        degree=max(x.bit_count() for x,a in enumerate(coeff) if a);assert degree==d
        stats.append(dict(rows=m,columns=ell,data_bits=d,query_columns=len(cols),rank=R,distinct_residuals=len(rows),full_query_degree=degree))
    return stats

if __name__=='__main__':
    rng=random.Random(870027)
    print(json.dumps(dict(span_examples=[candidate(k,rng) for k in range(1,5)],packed_witness=witness_checks(rng),matrix=matrix_checks()),indent=2))
    print('all assertions passed')