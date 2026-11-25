"""Exact minimum counted-NOT cost of a signed read-once Boolean formula.
A nonconstant complete table is encoded as an integer, bit a is f(a).
Run this file for independent binary-formula enumeration tests.
"""
from functools import lru_cache
from itertools import combinations
from collections import Counter
from math import inf

def subs(S):
    a=S
    while True:
        yield a
        if not a:return
        a=(a-1)&S

def components(S,adj):
    out=[]
    while S:
        seen=S&-S;todo=seen
        while todo:
            v=todo&-todo;todo^=v
            new=adj[v.bit_length()-1]&S&~seen
            todo|=new;seen|=new
        S^=seen;out.append(seen)
    return out

@lru_cache(None)
def costs(n,f):
    """Return (min NOT for f, min NOT for ~f), ignoring inessential inputs.
    (inf,inf) means no read-once formula on essential inputs, or a constant.
    """
    one=(1<<(1<<n))-1;full=(1<<n)-1
    if f in (0,one):return inf,inf
    neg=0;active=0
    for i in range(n):
        d={((f>>(a|1<<i))&1)-((f>>a)&1) for a in subs(full^(1<<i))}-{0}
        if len(d)>1:return inf,inf
        if d:active|=1<<i
        if d=={-1}:neg|=1<<i
    g=sum((f>>(a^neg)&1)<<a for a in range(1<<n))
    # co-occurrence graph on minimal one-certificates
    A=[0]*n
    for a in subs(active):
        if not g>>a&1:continue
        if any(g>>(a^(1<<i))&1 for i in range(n) if a>>i&1):continue
        for i in range(n):
            if a>>i&1:A[i]|=a^(1<<i)
    O=[active&~(A[i]|1<<i) for i in range(n)]
    def rec(S):
        if S.bit_count()==1:
            v=sum(1<<a for a in range(1<<n) if a&S)
            return (v,(1,0) if S&neg else (0,1))
        p=components(S,A);AND=False
        if len(p)==1:p=components(S,O);AND=True
        if len(p)==1:return None
        children=[rec(C) for C in p]
        if any(c is None for c in children):return None
        v=one if AND else 0;cc=[]
        for a,c in children:v=v&a if AND else v|a;cc.append(c)
        M=sum(min(c) for c in cc)
        return v,tuple(min(sum(c[t] for c in cc),1+M) for t in (0,1))
    out=rec(active)
    if out is None or out[0]!=g:return inf,inf
    return out[1]

# Independent enumeration: binary splits, AND/OR, then optional output NOT.
def brute_formulas(n):
    one=(1<<(1<<n))-1;full=(1<<n)-1
    v=[sum(1<<a for a in range(1<<n) if a>>i&1) for i in range(n)]
    @lru_cache(None)
    def gen(S):
        if S.bit_count()==1:
            a=v[S.bit_length()-1];return {a:0,a^one:1}
        out={}
        for A in subs(S):
            if A in (0,S) or not A&(S&-S):continue
            for a,p in gen(A).items():
                for b,q in gen(S^A).items():
                    for f in (a&b,a|b):
                        out[f]=min(out.get(f,inf),p+q)
                        out[f^one]=min(out.get(f^one,inf),p+q+1)
        return out
    return gen(full)

def check():
    for n in range(1,6):
        known=brute_formulas(n);one=(1<<(1<<n))-1
        for f,c in known.items():assert costs(n,f)==(c,known[f^one]),(n,f,c,costs(n,f))
        if n<=4:
            for f in range(1,one):
                if not all(any((f>>a&1)!=(f>>(a|1<<i)&1) for a in subs(((1<<n)-1)^(1<<i))) for i in range(n)):continue
                assert costs(n,f)[0]==known.get(f,inf),(n,f,costs(n,f),known.get(f,inf))
        print('formula oracle',n,len(known),dict(Counter(known.values())),flush=True)

if __name__=='__main__':check()
