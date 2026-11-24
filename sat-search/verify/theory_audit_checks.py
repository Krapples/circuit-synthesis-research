"""Independent targeted checks for the circuit theory audit.
Requires complete_signed_fpt.py and complete_sharing_fpt.py (sat-search/theory) only
for the solver comparison. The rank witness generator is independent.
Provenance: supplied by the independent theory audit (ChatGPT), 2026-11-24; only this docstring and the
import path below were changed. Run: python verify/theory_audit_checks.py [--expanded-fpt]
"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))), 'theory'))
from itertools import combinations, product
from collections import Counter
import random, time, sys

def rank2(rows):
    piv={}
    for v in rows:
        while v:
            k=v.bit_length()-1
            if k in piv: v ^= piv[k]
            else: piv[k]=v; break
    return len(piv)

def make_rank_witnesses(e, positive):
    # Private guard triples are L_0..L_(e-1), R, C_0..C_(e-2).
    # C_i supplies v_i from v_(i+1). x is primary zero.
    allmask=(1<<(6*e+1))-1
    def cert(root, selected_L, selected_R, selected_C):
        # root = -1 for the positive R branch, -2 for positive AND,
        # or a negative choice of the unique false AND child.
        active_L=set(range(e)) if root==-2 else ({root} if root>=0 else set())
        active_R=root!=-2
        reach=set(); cmask=0; features=0
        def wrap(index, select):
            nonlocal cmask
            a,b,c=(1<<(1+3*index+j) for j in range(3))
            cmask |= (a if select else b) if positive else (b|c if select else a|b)
        def read(i, slot):
            nonlocal features
            reach.add(i);features|=(1<<(3*i+slot))|(1<<(3*i+2))
        for i in active_L:
            use=i in selected_L;wrap(i,use)
            if use:read(i,0 if i==0 else 1)
        if active_R:
            wrap(e,selected_R)
            if selected_R:read(0,1)
        for i in range(e-1):
            if i in reach:
                use=i in selected_C;wrap(e+1+i,use)
                if use:read(i+1,0)
        if e-1 in reach:cmask|=1
        return cmask,features
    out=[]
    if positive:
        out += [cert(-2,{0},False,set()),cert(-1,set(),True,set())]
    else:
        out += [cert(0,{0} if l else set(),bool(r),set()) for l,r in product(range(2),repeat=2)]
    for i in range(1,e):
        for a,b in product(range(2),repeat=2):
            if positive:
                out.append(cert(-2,{i-1}|({i} if b else set()),False,{i-1} if a else set()))
            else:
                out.append(cert(i,{i} if b else set(),True,set(range(i-1))|({i-1} if a else set())))
    def evalf(x):
        def w(i,p):
            a,b,c=(bool(x>>(1+3*i+j)&1) for j in range(3))
            return ((p or c) and a) or b
        v=[False]*e;v[-1]=bool(x&1)
        for i in range(e-2,-1,-1):v[i]=w(e+1+i,v[i+1])
        return w(e,v[0]) or all(w(i,v[i]) for i in range(e))
    for mask,feat in out:
        x=mask if positive else allmask^mask
        assert evalf(x)==positive,(e,positive,mask)
        for i in range(6*e+1):
            if mask>>i&1:assert evalf(x^(1<<i))!=positive,(e,positive,mask,i)
    return out

def rank_audit():
    total=0
    for e in range(1,31):
        P=make_rank_witnesses(e,True);N=make_rank_witnesses(e,False)
        a=rank2(v for _,v in P);b=rank2(v for _,v in N)
        H=rank2(sum((((p&q).bit_count()-1)&1)<<j for j,(q,_) in enumerate(N)) for p,_ in P)
        assert (a,b,H)==(3*e-1,3*e,3*e-1),(e,a,b,H)
        total+=len(P)+len(N)
    print('rank witness sets checked: e=1..30; rows (including repeats):',total,flush=True)

def exact_padding_audit():
    # Enumerate every legal program of 0..3 gates on 1..3 inputs, both bases.
    # Check every trimmed program and every nonempty pinned prefix thereof.
    count=0;edge=0;prefix=0
    for n in (1,2,3):
        for signed in (False,True):
            var=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
            one=(1<<(1<<n))-1
            def rec(gs,vs,read):
                nonlocal count,edge,prefix
                out=len(vs)-1
                if read == (1<<out)-1:
                    if out==0:edge+=1
                    else:
                        a,b=out,0
                        p=vs[a]&vs[b];q=vs[a]|p
                        assert a!=b and q==vs[a]
                        newread=read|(1<<a)|(1<<b)|(1<<(out+1))
                        assert newread==(1<<(out+2))-1
                        padded=gs+((0,b,a),(1,a,out+1))
                        for k in range(len(gs)+1):
                            assert padded[:k]==gs[:k];prefix+=1
                        count+=1
                if len(gs)==3:return
                for a,b in combinations(range(len(vs)),2):
                    for op,z in enumerate((vs[a]&vs[b],vs[a]|vs[b])):
                        rec(gs+((op,a,b),),vs+[z],read|(1<<a)|(1<<b))
                if signed:
                    for a,z in enumerate(vs):rec(gs+((2,a),),vs+[one^z],read|(1<<a))
            rec((),var,0)
    print('padding:',count,'trimmed circuits;',prefix,'prefix checks;',edge,'one-wire cases',flush=True)

def independent_oracle(n,b,signed):
    one=(1<<(1<<n))-1
    var=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
    states={frozenset(var)};known=dict.fromkeys(var,0)
    for depth in range(1,b+1):
        nxt=set()
        for st in states:
            outputs={z for a,c in combinations(st,2) for z in (a&c,a|c)}
            if signed:outputs.update(one^a for a in st)
            for z in outputs-st:
                known.setdefault(z,depth);nxt.add(st|{z})
        states=nxt
    return known

def additional_solver_audit():
    from complete_signed_fpt import Solver as Signed
    from complete_sharing_fpt import Solver as Mono
    n=3;sol=Signed(n);known=independent_oracle(n,5,True)
    count=0
    for f in range(1,255):
        if not all(any(((f>>x)^(f>>(x^(1<<i))))&1 for x in range(8)) for i in range(n)):continue
        assert sol.solve(f,3)==(known.get(f,99)<=5),(f,known.get(f))
        count+=1
    print('new signed depth-5 queries:',count,flush=True)
    rng=random.Random(20261124);counts=Counter()
    for cls,signed in [(Mono,False),(Signed,True)]:
        sol=cls(4);n=4
        for _ in range(200):
            vals=list(sol.var)
            b=rng.randint(3,6)
            for j in range(b):
                if signed and rng.randrange(4)==0:vals.append(vals[rng.randrange(len(vals))]^sol.ONE)
                else:
                    a,c=rng.sample(vals,2);vals.append(a&c if rng.randrange(2) else a|c)
            f=vals[-1]
            if not all(any(((f>>x)^(f>>(x^(1<<i))))&1 for x in range(16)) for i in range(n)):continue
            assert sol.solve(f,b-n+1),(signed,f,b)
            counts[signed]+=1
    print('generated 4-input witness checks:',dict(counts),flush=True)

if __name__=='__main__':
    t=time.monotonic();rank_audit();exact_padding_audit()
    if '--expanded-fpt' in sys.argv:additional_solver_audit()
    print('elapsed',time.monotonic()-t)
