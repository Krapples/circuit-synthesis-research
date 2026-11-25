"""Exact ordered quotient reconstruction for fixed repeated-primary and
shared-internal layouts; exhaustive <=3 excess recognition for complete,
fully reduced monotone / free-NOT cores. Not a counted-NOT algorithm.
Dependencies: conditional_provider, two_sharing_core, module_contraction.
"""
from collections import Counter
from functools import lru_cache, partial
from itertools import product
from time import perf_counter
from random import Random
from module_contraction import vars, essential, raw_monotone, simplify, brute, contract_pair, peel
from conditional_provider import options, signs, consistent_monotone, compositions, solve as one_internal, reconstruct as reconstruct_one, formula_columns
from two_sharing_core import assignments, slices, local, solve as two, reconstruct as reconstruct_two
from restriction_excess import first_gate_candidates, lower
from regional_block_completion import CompletionWorkLimit, local_blocks
from regional_obligation_cache import ObligationCache
ANY=-1


def make_completion(mode='dominance-branches', *, cache_size=4096, table_factory=None):
    if mode == 'reference':
        return local
    if mode == 'cached':
        return ObligationCache(maxsize=cache_size)
    if mode in ('certificate-cnf', 'certificate-lazy', 'certificate-rows', 'certificate-anchored',
                'certificate-absorption', 'certificate-fallback'):
        from regional_certificate_cnf import local_cnf

        anchored = mode in ('certificate-anchored', 'certificate-absorption')
        cnf = partial(local_cnf, eager=mode == 'certificate-cnf', lazy_rows=mode == 'certificate-rows' or anchored,
                      anchored=anchored, absorb=mode == 'certificate-absorption')
        if mode == 'certificate-fallback':
            cnf = completion_portfolio(partial(local_cnf, eager=False, lazy_rows=True), 'certificate')
        return ObligationCache(maxsize=cache_size, solver=cnf)
    if mode == 'root-portfolio':
        root = partial(local_blocks, port_first=True, witness_cover=True, row_quotient=True, root_relaxation=True)
        return ObligationCache(maxsize=cache_size, solver=completion_portfolio(root, 'root'))
    modes = {
        'blocks': dict(row_filter=False),
        'row-bounds': dict(endpoint_branches=False),
        'endpoint-branches': dict(dominance_branches=False),
        'dominance-branches': {},
        'port-first': dict(port_first=True),
        'witness-cover': dict(witness_cover=True),
        'port-first-witness': dict(port_first=True, witness_cover=True),
        'ordered-block': dict(port_first=True, witness_cover=True, block_order=True),
        'row-quotient': dict(port_first=True, witness_cover=True, row_quotient=True),
        'root-relaxation': dict(port_first=True, witness_cover=True, row_quotient=True, root_relaxation=True),
    }
    if mode not in modes:
        raise ValueError(f'unknown completion mode {mode!r}')
    options = modes[mode]
    if table_factory is not None:
        options['table_factory'] = table_factory
    return ObligationCache(maxsize=cache_size, solver=partial(local_blocks, **options))


def completion_portfolio(fallback, stage):
    def solve(m, ports, patterns, targets, signed, stats=None, module_filter=True):
        args = (m, ports, patterns, targets, signed, stats, module_filter)
        port_heavy = m <= 2 and len(patterns) >= 16
        wide_signed = stage == 'certificate' and signed and m <= 8 and len(patterns) >= 8
        options = dict(port_first=True, witness_cover=True, row_quotient=True)
        if not (port_heavy or wide_signed):
            return local_blocks(*args, **options)
        try:
            return local_blocks(*args, **options, work_limit=256)
        except CompletionWorkLimit:
            if stats is not None:
                stats[f'{stage}_fallbacks'] += 1
            return fallback(*args)

    return solve


@lru_cache(None)
def split_table(f,m,z):
    return tuple(sum((f>>(a|(b<<m))&1)<<b for b in range(1<<z)) for a in range(1<<m))

def fixed(n,f,R,groups,ports,signed=False,stats=None,projection=True,*,completion=None):
    """R: repeated primary indices; groups: ordered tuple of disjoint private
    groups (last is output). ports[j]: global provider ids read in region j,
    including repeats; ids 0..len(R)-1 are primaries, len(R)+j earlier region
    outputs. Every non-output region must have >=2 leaf occurrences. Returns
    local trees or None. For fixed layout, exact, including serial providers.
    """
    if stats is None:stats=Counter()
    if completion is None:completion=make_completion()
    r=len(R);k=len(groups)-1;W=tuple(i for S in groups for i in S)
    assert sorted(R+W)==list(range(n)) and len(ports)==len(groups)
    assert all(all(0<=p<r+j for p in P) for j,P in enumerate(ports))
    if any(len(S)+len(P)<2 for S,P in zip(groups[:-1],ports[:-1])):return None
    if not groups[-1] and not ports[-1]:return None
    stats['layouts']+=1
    # Mask of providers still read by this or a subsequent region.
    live=[sum(1<<v for v in set(p for P in ports[j:] for p in P)) for j in range(k+1)]
    def project(p,mask):return p&mask if projection else p
    start={}
    for p,t in enumerate(slices(f,R,W)):
        a=project(p,live[0]);
        if a in start and start[a]!=t:return None
        start[a]=t
    @lru_cache(None)
    def check(j,req):
        stats['local']+=1
        pats,ts=zip(*req) if req else ((0,),(ANY,))
        return completion(len(groups[j]),ports[j],pats,ts,signed)
    @lru_cache(None)
    def go(j,state):
        stats['states']+=1
        m=len(groups[j]);z=sum(map(len,groups[j+1:]));pmask=sum(1<<v for v in set(ports[j]))
        if j==k:
            w={}
            for p,t in state:
                a=p&pmask
                if a in w and w[a]!=t:return None
                w[a]=t
            a=check(j,tuple(sorted(w.items())))
            return (a,) if a is not None else None
        opts={p:options(split_table(t,m,z),m,signed) for p,t in state}
        if any(not o for o in opts.values()):stats['cofactor_reject']+=1;return None
        order=sorted(opts,key=lambda p:(opts[p][0][0]==ANY,p))
        hreq={};new={};pol={}
        def choose(i):
            if i==len(order):
                stats['profiles']+=1
                h=check(j,tuple(sorted(hreq.items())))
                if h is None:return None
                ans=go(j+1,tuple(sorted(new.items())))
                return None if ans is None else (h,)+ans
            p=order[i];pk=p&pmask
            for h,a,b in opts[p]:
                if pk in hreq and h!=ANY and hreq[pk]!=h:stats['projection_reject']+=1;continue
                si=signs(m,h)
                if si is None or any(v in pol and pol[v]!=sg for v,sg in si.items()):stats['sign_reject']+=1;continue
                if not signed and any((q&pk==q and not consistent_monotone(t,h)) or (pk&q==pk and not consistent_monotone(h,t)) for q,t in hreq.items()):stats['order_reject']+=1;continue
                add={};ok=True
                for v,t in enumerate((a,b)):
                    if t==ANY:continue
                    key=project(p|(v<<(r+j)),live[j+1])
                    if (key in new and new[key]!=t) or (key in add and add[key]!=t):ok=False;break
                    add[key]=t
                if not ok:stats['projection_reject']+=1;continue
                nh=h!=ANY and pk not in hreq
                if nh:hreq[pk]=h
                nn=[q for q in add if q not in new];new.update(add)
                np=[q for q in si if q not in pol];pol.update(si)
                w=choose(i+1)
                if w is not None:return w
                if nh:del hreq[pk]
                for q in nn:del new[q]
                for q in np:del pol[q]
            return None
        return choose(0)
    return go(0,tuple(sorted(start.items())))

def reconstruct(n,f,R,groups,ports,trees,e):
    """Compile each region once, simplify constants / repeated operands, trim.
    Returns a signed binary DAG, independently checked against the target.
    """
    one=(1<<(1<<n))-1;V=list(vars(n));gates=[]
    def neg(a):return a^1 if isinstance(a,int) else (a[0],not a[1])
    def val(a):return a*one if isinstance(a,int) else V[a[0]]^(one if a[1] else 0)
    def make(op,a,b):
        x,y=val(a),val(b);z=x&y if op=='&' else x|y
        if z in (0,one):return int(z==one)
        if z==x:return a
        if z==y:return b
        assert not isinstance(a,int) and not isinstance(b,int) and a[0]!=b[0]
        gates.append((op,a,b));V.append(z);return len(V)-1,False
    def compile(t,I):
        if t[0]=='x':return neg(I[t[1]]) if t[2] else I[t[1]]
        a=compile(t[1],I)
        for c in t[2:]:a=make(t[0],a,compile(c,I))
        return a
    avail=tuple((i,False) for i in R)
    for j,(S,t) in enumerate(zip(groups,trees)):
        I=tuple((i,False) for i in S)+avail
        out=compile(t,I);avail+=(out,)
    assert val(out)==f and not isinstance(out,int)
    live=set()
    def visit(i):
        if i<n or i in live:return
        live.add(i);_,a,b=gates[i-n];visit(a[0]);visit(b[0])
    visit(out[0]);ren={i:i for i in range(n)};G=[]
    for i in sorted(live):
        op,a,b=gates[i-n];ren[i]=n+len(G);G.append((op,(ren[a[0]],a[1]),(ren[b[0]],b[1])))
    out=(ren[out[0]],out[1]);assert len(G)<=n-1+e
    vals=list(vars(n))
    for op,a,b in G:
        x,y=(vals[i]^(one if p else 0) for i,p in (a,b));vals.append(x&y if op=='&' else x|y)
    assert vals[out[0]]^(one if out[1] else 0)==f
    return G,out

def two_internal(n,f,signed=False,stats=None,*,completion=None):
    """The two-internal-wire class at excess three, for reduced cores."""
    if stats is None:stats=Counter()
    if completion is None:completion=make_completion()
    req=first_gate_candidates(n,f,3,signed)
    V=tuple(range(n))
    for x in V:
        if not any(set(t[-1])<={x} for t in req):continue
        W=tuple(i for i in V if i!=x)
        for owners in product(range(3),repeat=len(W)):
            groups=tuple(tuple(i for i,o in zip(W,owners) if o==j) for j in range(3))
            for d in compositions(2,3):
                if d[0]==0 or len(groups[0])+d[0]<2:continue
                for h in range(3):
                    P=((0,)*d[0],(0,)*d[1]+(1,)*h,(0,)*d[2]+(1,)*(2-h)+(2,)*2)
                    if not P[1] or len(groups[1])+len(P[1])<2:continue
                    a=fixed(n,f,(x,),groups,P,signed,stats,completion=completion)
                    if a is not None:return ('two_internal',(x,),groups,P,a)
    return None

def solve3(n,f,signed=False,stats=None,check_contract=True,internal_first=False,*,completion=None):
    """Exact <=3 excess decision on fully reduced essential complete cores.
    At excess three the only new class beyond <=1 shared internal wire is
    two shared internal wires plus one repeated primary, each read twice.
    internal_first changes only search order.
    """
    if check_contract and (n<1 or not essential(n,f) or (not signed and not raw_monotone(n,f)) or simplify(n,f,signed)[0]!=n):
        raise ValueError('requires fully reduced essential complete core')
    if stats is None:stats=Counter()
    if completion is None:completion=make_completion()
    a=two(n,f,signed,check_contract=False,completion=completion)
    if a is not None:return ('two',a)
    if internal_first:
        a=two_internal(n,f,signed,stats,completion=completion)
        if a is not None:return a
    a=one_internal(n,f,3,signed,stats,min_excess=3,reduced_filter=True,completion=completion)
    if a is not None:return ('one_internal',a)
    if not internal_first:return two_internal(n,f,signed,stats,completion=completion)
    return None

def materialize3(n,f,ans,signed=False):
    if ans[0]=='two':return reconstruct_two(n,f,ans[1],signed)
    if ans[0]=='one_internal':return reconstruct_one(n,f,ans[1],3)
    return reconstruct(n,f,*ans[1:],3)

def checks():
    rng=Random(41923);T=perf_counter();C=Counter();stats=Counter()
    # Independent full formula-column enumeration on specified layouts.
    # Two independent providers, then serial and hybrid dependencies.
    for n,R,groups,P,signed in (
        (4,(0,),((1,),(2,),(3,)),((0,),(0,),(1,1,2,2)),False),
        (4,(0,),((1,),(2,),(3,)),((0,),(0,),(1,1,2,2)),True),
        (4,(0,),((1,),(2,),(3,)),((0,),(0,1),(1,2,2)),False),
        (4,(0,),((1,),(2,),(3,)),((0,),(0,1),(1,2,2)),True),
        (4,(0,),((1,),(2,),(3,)),((0,0),(1,1),(2,2)),True),
        (5,(0,),((1,2),(3,),(4,)),((0,),(1,),(0,1,2,2)),True)):
        v=vars(n);one=(1<<(1<<n))-1;known=set()
        def gen(j,avail):
            c=tuple(v[i] for i in groups[j])+tuple(avail[i] for i in P[j])
            fs=formula_columns(tuple(sorted(c)),one,signed)
            if j==len(groups)-1:known.update(fs);return
            for h in fs:gen(j+1,avail+(h,))
        gen(0,tuple(v[i] for i in R))
        pos=sorted(known);sample=pos if len(pos)<=100 else rng.sample(pos,100)
        sample += [rng.randrange(one+1) for _ in range(120)]
        for f in sample:
            a=fixed(n,f,R,groups,P,signed,stats)
            assert (a is not None)==(f in known),(n,R,groups,P,signed,f,a)
            if a and f not in (0,one):reconstruct(n,f,R,groups,P,a,3)
            C['layout']+=1;C['layout_yes']+=a is not None
        print('layout',n,P,signed,len(known),len(sample),flush=True)
    # Exhaustive essential reduced functions with independent gate-set oracle.
    for signed,n in ((False,4),(True,3)):
        ref=brute(n,n+2,'free' if signed else 'mono');c=Counter()
        for f in range(1,(1<<(1<<n))-1):
            if not essential(n,f) or (not signed and not raw_monotone(n,f)) or simplify(n,f,signed)[0]!=n:continue
            a=solve3(n,f,signed,stats);assert bool(a)==(f in ref),(n,f,signed,a)
            if a:materialize3(n,f,a,signed)
            c[a[0] if a else 'no']+=1
        print('full oracle',signed,n,dict(c),flush=True);C['oracle']+=sum(c.values())
    # Construct random serial / parallel shared internal circuits on 5,6
    # inputs and retain only essential fully reduced cores. Class membership
    # is known from construction; optimum checked by lower-excess recognizer.
    generated=[]
    for _ in range(1200):
        n=rng.choice((5,6));R=(0,);signed=bool(rng.randrange(2));W=list(range(1,n));rng.shuffle(W)
        i=rng.randrange(1,n-1);j=rng.randrange(i,n);groups=(tuple(W[:i]),tuple(W[i:j]),tuple(W[j:]))
        P=rng.choice((((0,),(0,),(1,1,2,2)),((0,),(0,1),(1,2,2)),((0,),(1,),(0,1,2,2)),((0,),(1,1),(0,2,2)),((0,0),(1,),(1,2,2))))
        if any(len(S)+len(p)<2 for S,p in zip(groups[:-1],P[:-1])):continue
        v=vars(n);one=(1<<(1<<n))-1;avail=(v[0],)
        for S,p in zip(groups,P):
            A=[v[i] for i in S]+[avail[i] for i in p];A=[a^(one if signed and rng.randrange(2) else 0) for a in A]
            while len(A)>1:
                a=A.pop(rng.randrange(len(A)));b=A.pop(rng.randrange(len(A)));A.append(a&b if rng.randrange(2) else a|b)
            avail+=(A[0],)
        f=avail[-1]
        if not essential(n,f) or simplify(n,f,signed)[0]!=n:continue
        a=fixed(n,f,R,groups,P,signed,stats);assert a;reconstruct(n,f,R,groups,P,a,3);C['generated']+=1
        if two(n,f,signed) is None:generated.append((n,f,signed))
        if len(generated)>=8:break
    for n,f,signed in generated:
        a=solve3(n,f,signed,stats);assert a;materialize3(n,f,a,signed);C[a[0]]+=1
    print('generated beyond two',len(generated),'examples',generated[:3],flush=True)
    print('total',dict(C),'stats',dict(stats),'seconds',perf_counter()-T,flush=True)
if __name__=='__main__':checks()
