"""Exact monotone cut decomposition when D=2**k distinct cofactors.
Only for complete monotone functions, and circuits respecting the specified cut.
Standard library. k<=3 enumeration by default; boolean-poset fast path for any k.
Columns use packed truth tables, local variables in increasing index order.
"""
from itertools import permutations, combinations
from collections import Counter
from random import Random
from time import perf_counter
from math import comb


def scatter(a, xs):
    return sum(((a>>j)&1)<<i for j,i in enumerate(xs))


def cofactors(n,f,X):
    xs=[i for i in range(n) if X>>i&1]; zs=[i for i in range(n) if not X>>i&1]
    xp=[scatter(a,xs) for a in range(1<<len(xs))];zp=[scatter(b,zs) for b in range(1<<len(zs))]
    return tuple(sum(((f>>(a|b))&1)<<j for j,b in enumerate(zp)) for a in xp)


def orders(cs):
    vals=sorted(set(cs));idx={c:i for i,c in enumerate(vals)};d=len(vals)
    ids=tuple(idx[c] for c in cs)
    Q=tuple(sum(1<<j for j,b in enumerate(vals) if a&~b==0) for a in vals)
    P=[1<<i for i in range(d)]
    for a,i in enumerate(ids):
        for bit in range((len(cs)-1).bit_length()):
            if not a>>bit&1:P[i]|=1<<ids[a|1<<bit]
    for i in range(d):
        for j in range(d):
            if P[j]>>i&1:P[j]|=P[i]
    if any(p&~q for p,q in zip(P,Q)):raise ValueError('monotone table required')
    return vals,ids,tuple(P),Q


def codes_ok(code,P,Q):
    for i,a in enumerate(code):
        for j,b in enumerate(code):
            le=a&~b==0
            if P[i]>>j&1 and not le:return False
            if le and not Q[i]>>j&1:return False
    return True


def columns(code,ids,k):
    return tuple(sorted(sum(((code[i]>>b)&1)<<a for a,i in enumerate(ids)) for b in range(k)))


def boolean_order_code(O,k):
    d=len(O);bot=next((i for i,v in enumerate(O) if v==(1<<d)-1),None)
    if bot is None:return None
    pred=[sum(1<<i for i,v in enumerate(O) if v>>j&1) for j in range(d)]
    atoms=[i for i,p in enumerate(pred) if p==((1<<bot)|(1<<i)) and i!=bot]
    if len(atoms)!=k:return None
    code=tuple(sum(((p>>a)&1)<<b for b,a in enumerate(atoms)) for p in pred)
    if len(set(code))!=d:return None
    if not codes_ok(code,O,O):return None
    return code


def embeddings(cs,max_k=3):
    """Return (status, set of unordered provider-column tuples).
    status: exact, impossible, not_saturated, or skipped (large nontrivial case).
    Necessary and sufficient for monotone encoder/decoder with k live bits,
    not a claim about circuit gate budget. Exact if D=2**k and processed.
    """
    vals,ids,P,Q=orders(cs);d=len(vals);k=(d-1).bit_length()
    if d!=1<<k:return 'not_saturated',set()
    if sum(p.bit_count() for p in P)>3**k or sum(q.bit_count() for q in Q)<3**k:return 'impossible',set()
    for O in (P,Q):
        if sum(o.bit_count() for o in O)==3**k:
            code=boolean_order_code(O,k)
            if code is None or not codes_ok(code,P,Q):return 'impossible',set()
            return 'exact',{columns(code,ids,k)}
    if k>max_k:return 'skipped',set()
    # Bottom/top pinned because monotone input has least/greatest assignment.
    bottom,top=ids[0],ids[-1]
    middle=[i for i in range(d) if i not in (bottom,top)]
    out=set()
    for p in permutations(range(1,d-1)):
        code=[0]*d;code[top]=d-1
        for i,x in zip(middle,p):code[i]=x
        if codes_ok(code,P,Q):out.add(columns(code,ids,k))
    return ('exact' if out else 'impossible'),out


def reconstruct_decoder(cs,cols):
    """Return decoder cofactor tuple indexed by provider pattern; saturated only."""
    v={}
    for a,c in enumerate(cs):
        p=sum(((x>>a)&1)<<b for b,x in enumerate(cols))
        if p in v:assert v[p]==c
        v[p]=c
    assert len(v)==1<<len(cols)
    return tuple(v[i] for i in range(len(v)))


def monotone_columns(n):
    return [f for f in range(1,(1<<(1<<n))-1) if all(not(f>>a&1) or f>>(a|1<<i)&1 for a in range(1<<n) for i in range(n))]


def brute_encoders(cs,k,cols):
    out=set()
    for C in combinations(cols,k):
        by={};ok=True
        for a,c in enumerate(cs):
            p=sum(((v>>a)&1)<<j for j,v in enumerate(C))
            if p in by and by[p]!=c:ok=False;break
            by[p]=c
        if ok and all(not(p&~q==0) or c&~d==0 for p,c in by.items() for q,d in by.items()):out.add(C)
    return out


def essential(n,f):
    return all(any((f>>a&1)!=(f>>(a^(1<<i))&1) for a in range(1<<n)) for i in range(n))


def support_components(m,cols):
    parent=list(range(m))
    def root(x):
        while parent[x]!=x:x=parent[x]
        return x
    for col in cols:
        S=[i for i in range(m) if any((col>>a&1)!=(col>>(a^(1<<i))&1) for a in range(1<<m))]
        for i in S[1:]:parent[root(i)]=root(S[0])
    return len({root(i) for i in range(m)})


def test():
    from monotone_frontier_order import OrderBound
    from backward_column_synthesis import multi_slack
    rng=Random(21481);start=perf_counter();ct=Counter();examples={}
    m3=monotone_columns(3)
    # Exhaustively enumerate all monotone targets for up to four inputs.
    cases=[(n,f) for n in (3,4) for f in monotone_columns(n) if essential(n,f)]
    for n in (5,6,7):
        for k in range(1,n+1):cases.append((n,sum((a.bit_count()>=k)<<a for a in range(1<<n))))
        for _ in range(160):
            terms=[rng.randrange(1,1<<n) for _ in range(rng.randint(2,2*n))]
            f=sum(any(a&t==t for t in terms)<<a for a in range(1<<n))
            if essential(n,f):cases.append((n,f))
    cases=list(dict.fromkeys(cases))
    for n,f in cases:
        ob=OrderBound(n,f)
        for X in range(1,(1<<n)-1):
            cs=cofactors(n,f,X);d=len(set(cs));k=(d-1).bit_length();m=X.bit_count()
            if k<2 or d!=1<<k or k>=m:continue
            status,E=embeddings(cs);ct['nontrivial_saturated']+=1
            ct[status]+=1
            if status=='skipped':continue
            if status=='impossible':
                if ob.details(X)[-1]==k:
                    ct['stronger_than_order']+=1;examples.setdefault('rejected',(n,f,X,k))
            else:
                ct['unique']+=len(E)==1
                forced=set.intersection(*(set(c) for c in E));ct['some_forced']+=bool(forced)
                ct['total_forced_columns']+=len(forced)
                A=frozenset(sum(((a>>i)&1)<<a for a in range(1<<m)) for i in range(m))
                ct['nonprimary_forced']+=len(forced-A)>0
                lower=min(max(m-support_components(m,C),len(set(C)-A)) for C in E)
                ct['prefix_connectivity_gain']+=lower>m-k
                if m<=4:
                    opt=None
                    for g in range(lower,m+2):
                        if any(multi_slack(1<<m,A,C,g,True)[0] is not None for C in E):
                            opt=g;break
                    ct['prefix_bounded_search']+=1
                    ct['prefix_cost_established']+=opt is not None
                    ct['prefix_stronger_than_support']+=opt is not None and opt>lower
                    ct['prefix_proved_above_support']+=opt is None

                if len(E)==1 and len(forced-A)>0:
                    examples.setdefault('forced',(n,f,X,k,sorted(forced)))
                for C in E:
                    decoder=reconstruct_decoder(cs,C)
                    assert all(p&~q or a&~b==0 for p,a in enumerate(decoder) for q,b in enumerate(decoder))
            if m==3:
                brute=brute_encoders(cs,k,m3);assert E==brute,(n,f,X,E,brute)
                ct['independent_brute']+=1
    print('corpus',len(cases),dict(ct),'examples',examples,'seconds',perf_counter()-start,flush=True)
    # Construct independent-selector targets with surjective monotone providers.
    generated=Counter()
    for _ in range(100):
        # Three independent nonconstant blocks, each AND or OR on 1-2 inputs.
        sizes=[rng.randint(1,2) for _ in range(3)];m=sum(sizes);off=0;cols=[]
        for sz in sizes:
            mask=((1<<sz)-1)<<off;off+=sz;isand=rng.randrange(2)
            cols.append(sum((a&mask==mask if isand else bool(a&mask))<<a for a in range(1<<m)))
        # Residual functions are ORs of independent selector variables.
        cs=tuple(sum(bool(any((c>>a&1) and (z>>i&1) for i,c in enumerate(cols)))<<z for z in range(8)) for a in range(1<<m))
        status,E=embeddings(cs);assert status=='exact' and E=={tuple(sorted(cols))}
        A=frozenset(sum(((a>>i)&1)<<a for a in range(1<<m)) for i in range(m))
        w,_=multi_slack(1<<m,A,set(cols),m-3,True);assert w is not None and len(w)==m-3
        generated['unique_cuts']+=1;generated['prefix_gates']+=len(w)
    print('constructed',dict(generated),'seconds',perf_counter()-start,flush=True)
    # Nonunique saturated embedding: a 4-cube's middle antichain gives
    # six separate classes; the residuals form a chain of eight functions.
    middle=[a for a in range(16) if a.bit_count()==2]
    residual=[sum((z.bit_count()>=7-i)<<z for z in range(128)) for i in range(8)]
    cs=tuple(residual[0 if a.bit_count()<2 else 7 if a.bit_count()>2 else 1+middle.index(a)] for a in range(16))
    status,E=embeddings(cs);assert status=='exact' and len(E)>1
    print('nonunique example embeddings',len(E),flush=True)

if __name__=='__main__':test()
