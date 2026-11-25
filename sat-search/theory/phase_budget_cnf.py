"""Compact counted-NOT SAT encoding via normalized signed binary skeletons.
Uses phase_budget_synthesis.py. Mixed partial labels, arbitrary reference row
chosen from labels. Fixed binary slots b>=1 or at-most slots with activation variables.
Optional joint budget on binary activations and inverter sources. No padding assumption.
Standard library. Tiny DPLL included solely for known-answer checks.
"""
from itertools import combinations
from functools import lru_cache
from collections import Counter
from random import Random
from time import perf_counter
from phase_budget_synthesis import TYPES
from module_contraction import vars

class CNF:
    def __init__(self):self.n=0;self.clauses=[];self.selectors=[]
    def new(self):self.n+=1;return self.n
    def add(self,*lits):
        s=set(lits)
        if any(-v in s for v in s):return
        self.clauses.append(tuple(dict.fromkeys(lits)))
    def exactly_one(self,vs):
        self.add(*vs)
        # Sequential at-most-one.
        if len(vs)<2:return
        prev=self.new();self.add(-vs[0],prev)
        for x in vs[1:-1]:
            cur=self.new();self.add(-x,cur);self.add(-prev,cur);self.add(-x,-prev);prev=cur
        self.add(-vs[-1],-prev)
    def at_most(self,vs,k):
        if k<0:self.add();return
        if k>=len(vs):return
        if not k:
            for v in vs:self.add(-v)
            return
        # Implications into threshold counters. No false negative possible:
        # actual threshold indicators satisfy all clauses, and induction
        # forces a threshold when at least that many inputs have been set.
        prev=[]
        for x in vs:
            cur=[self.new() for _ in range(min(k,len(prev)+1))]
            self.add(-x,cur[0])
            for j,p in enumerate(prev):
                self.add(-p,cur[j])
                if j+1<len(cur):self.add(-x,-p,cur[j+1])
                else:self.add(-x,-p)
            prev=cur
    def dimacs(self):
        return 'p cnf %d %d\n'%(self.n,len(self.clauses))+''.join(' '.join(map(str,c))+' 0\n' for c in self.clauses)


def encode(n,b,u,P,N,anchor=None,atmost=False,total=None):
    if n<1 or b<0 or (not atmost and b<1) or u<0 or not P or not N or P&N or (P|N).bit_length()>1<<n:
        raise ValueError('mixed disjoint labels, b>=1, u>=0 required')
    if anchor is None:anchor=((P|N)&-(P|N)).bit_length()-1
    if not ((P|N)>>anchor&1):raise ValueError('reference row must be labeled')
    rows=[a for a in range(1<<n) if a!=anchor and (P|N)>>a&1];out=P>>anchor&1
    c=CNF();true=c.new();c.add(true)
    phase=[c.new() for _ in range(n+b)];z=[c.new() for _ in phase]
    for i in range(n):c.add(phase[i] if anchor>>i&1 else -phase[i])
    c.at_most(z,u)
    active=[c.new() for _ in range(b)] if atmost else []
    if atmost:
        for x,y in zip(active,active[1:]):c.add(-y,x)
        if total is not None:c.at_most(active+z,total)
    elif total is not None:c.at_most(z,total-b)
    tab=[{a:(true if (a^anchor)>>i&1 else -true) for a in rows} for i in range(n)]
    gates=[]
    for v in range(n,n+b):
        vals={a:c.new() for a in rows};tab.append(vals);choices={}
        for l,r in combinations(range(v),2):
            for op,sa,sb in TYPES:
                sel=c.new();choices[sel]=(op,l,r,sa,sb);c.selectors.append(sel)
                for src,s in ((l,sa),(r,sb)):
                    x,y=phase[src],phase[v]
                    c.add(-sel,z[src],-x,-y if s else y)
                    c.add(-sel,z[src],x,y if s else -y)
                for a in rows:
                    x=tab[l][a]*(-1 if sa else 1);y=tab[r][a]*(-1 if sb else 1);o=vals[a]
                    if op=='AND':
                        c.add(-sel,-x,-y,o);c.add(-sel,x,-o);c.add(-sel,y,-o)
                    else:
                        c.add(-sel,x,y,-o);c.add(-sel,-x,o);c.add(-sel,-y,o)
        if atmost:
            # Active gate chooses one operation; inactive gate chooses none.
            # A dummy choice acts as the unique choice exactly when inactive.
            off=c.new();c.add(-off,-active[v-n]);c.add(off,active[v-n]);c.exactly_one([off,*choices])
        else:c.exactly_one(list(choices))
        gates.append(choices)
    output={}
    if atmost:
        # Output is last active gate, or any primary if no binary gate active.
        for v in range(n+b):
            sel=c.new();output[sel]=v
            if v<n:
                if active:c.add(-sel,-active[0])
            else:
                c.add(-sel,active[v-n])
                if v-n+1<b:c.add(-sel,-active[v-n+1])
            c.add(-sel,z[v],phase[v] if out else -phase[v])
            for a in rows:c.add(-sel,tab[v][a] if ((P>>a&1)^out) else -tab[v][a])
        c.exactly_one(list(output))
        c.selectors=list(output)+c.selectors
    else:
        c.add(z[-1],phase[-1] if out else -phase[-1])
        for a in rows:c.add(tab[-1][a] if ((P>>a&1)^out) else -tab[-1][a])
    return c,{'phase':phase,'inverters':z,'gates':gates,'out':out,'anchor':anchor,'output':output,'active':active}


def dpll(c):
    """Small independent CNF search; not a production solver."""
    order=c.selectors
    def go(clauses,assigned):
        while True:
            if not clauses:return assigned
            units=[cl[0] for cl in clauses if len(cl)==1]
            if any(not cl for cl in clauses):return None
            if not units:break
            s=set(units)
            if any(-x in s or -x in assigned for x in s):return None
            assigned=assigned|s
            clauses=[tuple(x for x in cl if -x not in s) for cl in clauses if not any(x in s for x in cl)]
        # Branch on selector in a remaining clause, else a shortest clause.
        used={abs(x) for cl in clauses for x in cl}
        x=next((x for x in order if x in used),None)
        if x is None:x=min(clauses,key=len)[0]
        for v in (x,-x):
            result=go(clauses+[(v,)],assigned)
            if result is not None:return result
        return None
    return go(c.clauses,set())


def decode(n,meta,assignment):
    """Independently materialize counted circuit and output, any anchor."""
    anchor=meta['anchor'];p=[x in assignment for x in meta['phase']]
    assert p[:n]==[bool(anchor>>i&1) for i in range(n)]
    g=[g for choices in meta['gates'] for x,g in choices.items() if x in assignment]
    assert not meta['active'] or len(g)==sum(x in assignment for x in meta['active'])
    result=[];wire=list(range(n));neg={}
    def get(src,req):
        if p[src]==req:return wire[src]
        assert meta['inverters'][src] in assignment
        if src not in neg:
            neg[src]=n+len(result);result.append(('NOT',wire[src]))
        return neg[src]
    for v,(op,l,r,a,b) in enumerate(g,n):
        x,y=get(l,a^p[v]),get(r,b^p[v]);wire.append(n+len(result))
        result.append((op if not p[v] else ('OR' if op=='AND' else 'AND'),x,y))
    v=next(v for x,v in meta['output'].items() if x in assignment) if meta['output'] else len(wire)-1
    out=get(v,meta['out'])
    return result,out


def evaluate(n,g,out):
    vs=list(vars(n));one=(1<<(1<<n))-1
    for op,*a in g:
        if op=='NOT':vs.append(vs[a[0]]^one)
        elif op=='AND':vs.append(vs[a[0]]&vs[a[1]])
        else:vs.append(vs[a[0]]|vs[a[1]])
    return vs[out]


@lru_cache(None)
def reference(n,B,U):
    """Independent available-function-set enumeration with separate budgets."""
    V=frozenset(vars(n));one=(1<<(1<<n))-1;states={(0,0):{V}};out=set(V)
    for b in range(B+1):
        for u in range(U+1):
            for st in states.get((b,u),()):
                if b<B:
                    cand={z for x,y in combinations(st,2) for z in (x&y,x|y)}-st
                    out.update(cand)
                    if b+1<B or u<U:states.setdefault((b+1,u),set()).update(st|{z} for z in cand)
                if u<U:
                    cand={x^one for x in st}-st;out.update(cand)
                    if b<B or u+1<U:states.setdefault((b,u+1),set()).update(st|{z} for z in cand)
    return frozenset(out)


def solve_small(n,B,U,P,N,anchor=None):
    one=(1<<(1<<n))-1
    for x in vars(n):
        for f in (x,x^one) if U else (x,):
            if f&P==P and not f&N:return True
    for b in range(1,B+1):
        c,meta=encode(n,b,U,P,N,anchor);a=dpll(c)
        if a is not None:
            g,out=decode(n,meta,a);f=evaluate(n,g,out)
            assert f&P==P and not f&N
            assert sum(x[0]=='NOT' for x in g)<=U and sum(x[0]!='NOT' for x in g)<=B
            return True
    return False


def test():
    t=perf_counter();r=Random(1242);ct=Counter()
    for n in (2,3):
        one=(1<<(1<<n))-1
        labels=[(f,one^f) for f in range(1,one)] if n==2 else [(f,one^f) for f in r.sample(range(1,one),24)]
        for _ in range(24):
            a=[r.randrange(3) for _ in range(1<<n)];P=sum(1<<i for i,v in enumerate(a) if v==1);N=sum(1<<i for i,v in enumerate(a) if v==2)
            if P and N:labels.append((P,N))
        for B in (1,2):
            for U in (0,1,2):
                ref=reference(n,B,U)
                for P,N in labels:
                    anchor=r.choice([i for i in range(1<<n) if (P|N)>>i&1]);expected=any(f&P==P and not f&N for f in ref)
                    actual=solve_small(n,B,U,P,N,anchor)
                    assert actual==expected,(n,B,U,P,N,anchor,actual,expected)
                    ct['queries']+=1;ct['SAT']+=actual;ct['partial']+=(P|N)!=one
                    c,meta=encode(n,B,U,P,N,anchor,atmost=True);ass=dpll(c)
                    assert (ass is not None)==expected
                    if ass is not None:
                        g,v=decode(n,meta,ass);f=evaluate(n,g,v)
                        assert f&P==P and not f&N and sum(x[0]=='NOT' for x in g)<=U and sum(x[0]!='NOT' for x in g)<=B
                    ct['activation_queries']+=1
        for G in range(4 if n==2 else 3):
            # Total budget oracle is union of all split-budget oracles.
            ref=set().union(*(reference(n,b,G-b) for b in range(G+1)))
            for P,N in labels:
                expected=any(f&P==P and not f&N for f in ref)
                c,meta=encode(n,G,G,P,N,atmost=True,total=G);ass=dpll(c)
                assert (ass is not None)==expected,(n,G,P,N)
                if ass is not None:
                    g,v=decode(n,meta,ass);f=evaluate(n,g,v);assert f&P==P and not f&N and len(g)<=G
                ct['total_queries']+=1
    print('CNF vs independent counted-gate oracle',dict(ct),'seconds',round(perf_counter()-t,3))

if __name__=='__main__':test()
