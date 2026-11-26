"""Finite regression for coupled existential packed lookup (stdlib only)."""
from itertools import product
from random import Random
from permutable_andreev_check import params, build, parse, encode_clause, balance, unit_decide


def coupled(k, h, x, order, labels):
    M, ell, J, r, P, B, A, Q = params(k)
    m = k * J
    assert len(labels) == m and all(0 <= u <= m for u in labels)
    Q2 = 1 << (max(4*P, A+2*m+1)-1).bit_length()
    old, _, _ = build(k, h, x, order)
    def rename(l):
        v = abs(l)
        if v > Q:
            v += Q2-Q
        return v if l > 0 else -v
    F = [[rename(l) for l in C] for C in parse(old)]
    def e(u): return Q2+A+m+u+1
    out = F[:P] + [[-e(0)]]
    for i,u in enumerate(labels):
        a,b = F[P+2*i:P+2*i+2]
        z = b[0]
        t = Q2+A+i+1
        out.extend([[-t,a[1]], [t,b[1]]])
        for v,w in product((0,1), repeat=2):
            bad = (v,w,1^v^w)
            out.append([l if not bit else -l for l,bit in zip((t,e(u),z),bad)])
    out.extend(F[P+2*m:])
    word = [v for C in out for v in encode_clause(C)]
    assert parse(word) == out
    assert all(abs(l)-1 < 2*Q2 for C in out for l in C)
    return word, {u:e(u) for u in set(labels) if u}


def columns(k, x, order, labels):
    M, ell, J, r, P, B, A, Q = params(k)
    b, cols = 0, {u:0 for u in set(labels) if u}
    for i,(j,u) in enumerate(zip(order,labels)):
        bit = 1 << (j//J)
        if sum(x[i*ell:(i+1)*ell]) % 2: b ^= bit
        if u: cols[u] ^= bit
    return b, cols


def basis(cols):
    piv = {}
    for a in cols:
        while a:
            j = a.bit_length()-1
            if j not in piv:
                piv[j] = a
                break
            a ^= piv[j]
    return piv


def in_span(a, piv):
    while a:
        j = a.bit_length()-1
        if j not in piv: return False
        a ^= piv[j]
    return True


def diffs(a,b):
    assert len(a)==len(b)
    return {i for i,(x,y) in enumerate(zip(a,b)) if x!=y}


def main():
    rng = Random(870008)
    cases = assignments = balanced = probes = address_checks = 0
    multiple = cross = 0
    for k in range(1,9):
        M, ell, J, r, P, B, A, Q = params(k)
        m = k*J
        for case in range(24):
            h = [rng.randrange(2) for _ in range(M)]
            x = [rng.randrange(2) for _ in range(k*r)]
            order = list(range(m)); rng.shuffle(order)
            q = min(m,4)
            labels = [rng.randrange(q+1) for _ in range(m)]
            word, ids = coupled(k,h,x,order,labels)
            F = parse(word); G = parse(balance(word))
            assert len(balance(word)) == 3*len(word)+12
            assert sum(balance(word)) == 2*len(word)+5
            b, cols = columns(k,x,order,labels)
            piv = basis(cols.values())
            seen = set(); count = 0
            for bits in product((0,1),repeat=len(ids)):
                a=b; pins=[]
                for u,v in zip(sorted(ids),bits):
                    if v: a ^= cols[u]
                    pins.append([ids[u] if v else -ids[u]])
                seen.add(a)
                expected = bool(h[a]); count += expected
                assert unit_decide(F+pins) == expected
                assert unit_decide(G+pins) == expected
                assignments += 1; balanced += 1
            pred = {a for a in range(M) if in_span(a^b,piv)}
            assert seen == pred
            assert count == sum(h[a] for a in pred) * (1 << (len(ids)-len(piv)))
            address_checks += M
            multiple += count>1
            cross += any(sum(1 for j in range(k) if any(u==v and z//J==j for z,v in zip(order,labels)))>1 for u in ids)
            if case < 3:
                order2=order[::-1]; labels2=[0]*m
                word2,_=coupled(k,h,x,order2,labels2)
                for data, size, copies in [(False,len(x),2),(True,len(h),1)]:
                    i=rng.randrange(size); H=h[:]; X=x[:]
                    (H if data else X)[i]^=1
                    flip,_=coupled(k,H,X,order,labels)
                    flip2,_=coupled(k,H,X,order2,labels2)
                    assert len(diffs(word,flip))==copies
                    assert diffs(word,flip)==diffs(word2,flip2)
                    probes+=1
            cases+=1
    print(dict(cases=cases, pinned_sat_checks=assignments, balanced_checks=balanced,
               address_membership_checks=address_checks, coordinate_probes=probes,
               multiple_witness_cases=multiple, cross_row_label_cases=cross))
    print('all assertions passed')

if __name__ == '__main__': main()
