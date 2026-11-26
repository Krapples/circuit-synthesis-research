"""Independent finite replay of a permutable packed Andreev SAT projection.
No external dependencies. IDs are zero-based; signed literals use ID+1.
Physical selector slots are indexed by slot, then by low-to-high bit.
The permutation maps physical slots to logical (row, chunk) numbers.
"""
from collections import defaultdict, deque
from itertools import product
from random import Random


def params(k):
    assert k >= 1
    M = 1 << k
    ell = 1 << (max(1, k // 2).bit_length() - 1)
    J = M // (k * ell)
    r = J * ell
    P, B = 1 << ell, M // ell
    A = k * (2 * J - 1) + 2 * B - 1
    Q = 1 << (max(4 * P, A) - 1).bit_length()
    return M, ell, J, r, P, B, A, Q


def encode_clause(c):
    out = []
    for lit in c:
        out += [1, int(lit > 0)]
        v = abs(lit) - 1
        while v:
            out += [1, v % 2]
            v //= 2
        out += [0, 1]
    return out + [0, 0]


def parse(w):
    assert len(w) % 2 == 0
    tokens = iter(zip(w[::2], w[1::2]))
    clauses, clause = [], []
    for tag, sign in tokens:
        if (tag, sign) == (0, 0):
            clauses.append(clause)
            clause = []
            continue
        assert tag == 1
        v, bit, last = 0, 1, 1
        for a, d in tokens:
            if a == 0:
                assert d == 1 and last == 1
                break
            v += d * bit
            bit *= 2
            last = d
        else:
            raise AssertionError('unfinished literal')
        clause.append((v + 1) * (1 if sign else -1))
    assert not clause
    return clauses


def balance(w):
    assert w[-2:] == [0, 0]
    return w + [1,0,0,1,1,1,0,1,1,0] + [b for v in w[:-2] for b in (1,1-v)] + [1,1,0,1,0,0]


def build(k, h, x, order):
    M, ell, J, r, P, B, A, Q = params(k)
    assert len(h) == M and len(x) == k*r
    assert sorted(order) == list(range(k*J))
    lo = ell.bit_length() - 1
    nxt = Q + 1  # signed literal for zero-based ID Q
    def fresh():
        nonlocal nxt
        v = nxt
        nxt += 1
        return v
    def pattern(bits):
        return sum(bit << i for i, bit in enumerate(bits))
    def U(p): return P + p + 1
    def V(p): return 2*P + p + 1
    w, clauses = [], []
    xcoords = [[] for _ in x]
    hcoords = [[] for _ in h]
    def emit(c):
        clauses.append(c)
        w.extend(encode_clause(c))
    for p in range(P):
        emit([U(p) if p.bit_count() % 2 else -U(p)])
    zs = [fresh() for _ in order]
    start = len(w)
    width = Q.bit_length()
    blocklen = 20 + 4*width + 4*(ell+1)
    for slot, logical in enumerate(order):
        z = zs[logical]
        p = pattern(x[slot*ell:(slot+1)*ell])
        for phase in (-1, 1):
            base = len(w) + len(encode_clause([phase*z])) - 2
            emit([phase*z, -phase*U(p)])
            for t in range(ell):
                xcoords[slot*ell+t].append(base+3+2*t)
        assert len(w) == start+(slot+1)*blocklen
    addr = []
    for j in range(k):
        a = zs[j*J]
        for b in zs[j*J+1:(j+1)*J]:
            c = fresh()
            for v1, v2 in product((0,1), repeat=2):
                v3 = 1 ^ v1 ^ v2
                emit([v if bit == 0 else -v for v, bit in zip((a,b,c),(v1,v2,v3))])
            a = c
        addr.append(a)
    for p in range(P):
        for q in range(ell):
            emit([(-a if q >> i & 1 else a) for i,a in enumerate(addr[:lo])] + [V(p) if p >> q & 1 else -V(p)])
    root = fresh()
    emit([root])
    guards = [root]
    for a in reversed(addr[lo:]):
        children = []
        for g in guards:
            for b in (-a,a):
                v = fresh()
                emit([-v,g]); emit([-v,b]); emit([v,-g,-b])
                children.append(v)
        guards = children
    for i,g in enumerate(guards):
        p = pattern(h[i*ell:(i+1)*ell])
        base = len(w) + len(encode_clause([-g])) - 2
        emit([-g,V(p)])
        for t in range(ell):
            hcoords[i*ell+t].append(base+3+2*t)
    assert nxt == Q+A+1 and nxt-2 < 2*Q
    assert parse(w) == clauses
    return w, xcoords, hcoords


def unit_decide(clauses):
    """Unit propagation; assert no unresolved non-tautological clauses."""
    pos = defaultdict(set)
    rows = []
    for c in clauses:
        c = set(c)
        if any(-l in c for l in c):
            continue
        if not c:
            return False
        i = len(rows)
        rows.append(c)
        for l in c:
            pos[l].add(i)
    queue = deque(next(iter(c)) for c in rows if len(c) == 1)
    live = set(range(len(rows)))
    values = set()
    while queue:
        l = queue.popleft()
        if -l in values:
            return False
        if l in values:
            continue
        values.add(l)
        live.difference_update(pos[l])
        for i in pos[-l] & live:
            c = rows[i]
            c.remove(-l)
            if not c:
                return False
            if len(c) == 1:
                queue.append(next(iter(c)))
    assert not live, 'unexpected unresolved clauses'
    return True


def lookup(k, h, x, order):
    M, ell, J, r, P, B, A, Q = params(k)
    parity = [0]*k
    for slot, logical in enumerate(order):
        parity[logical//J] ^= sum(x[slot*ell:(slot+1)*ell]) % 2
    return bool(h[sum(v<<i for i,v in enumerate(parity))])


def balanced_order(counts, k, J):
    """Rank by light-bit count; give rank j*k+i to row i, chunk j."""
    assert len(counts) == k*J
    physical = sorted(range(k*J), key=lambda i: -counts[i])
    order = [0]*(k*J)
    for rank, slot in enumerate(physical):
        j, i = divmod(rank,k)
        order[slot] = i*J+j
    totals = [0]*k
    for slot, logical in enumerate(order):
        totals[logical//J] += counts[slot]
    assert sorted(order) == list(range(k*J))
    assert max(totals)-min(totals) <= max(counts)-min(counts)
    return order, totals


def reader_transfer_tests(rng):
    tests, unfold_tests, positive = 0, 0, 0
    for trial in range(3000):
        m = rng.randrange(1,30)
        s = rng.randrange(1,11) if trial < 1000 else rng.randrange(1,100)
        edges = [tuple(rng.randrange(m+j) for _ in range(2)) for j in range(s)]
        p = [0]*(m+s); p[-1] = 1
        readers = [[] for _ in range(m)]
        for j in reversed(range(s)):
            g=m+j
            for v in edges[j]:
                p[v]+=p[g]
                if v<m: readers[v].append(g)
        if trial < 1000:
            leaves = [0]*m
            def unfold(v):
                if v<m: leaves[v]+=1
                else:
                    for u in edges[v-m]: unfold(u)
            unfold(m+s-1)
            assert leaves==p[:m]
            unfold_tests += 1
        assert all(p[i] == sum(p[g] for g in readers[i]) for i in range(m))
        tau = rng.randrange(1,max(p[:m])+1)
        H=[i for i in range(m) if p[i]>=tau]; h=len(H)
        assert h>0
        low=[i for i in H if h*len(readers[i])<=4*s]
        assert 2*len(low)>=h
        chosen={max(readers[i],key=lambda g:p[g]) for i in low}
        assert all(4*s*p[g]>=tau*h for g in chosen)
        assert 4*len(chosen)>=h
        assert len({g for g in range(m,m+s) if 4*s*p[g]>=tau*h})>=len(chosen)
        tests += 1
        positive += len(chosen)>1
    return tests, unfold_tests, positive


def padding_tests():
    checks=0
    for delta in range(48,1000,2):
        b=next(i for i in range(5) if (delta-14*i)%10==0)
        a=(delta-14*b)//10
        assert a>=0 and b>=0
        w=encode_clause([1,-1])*a + encode_clause([2,-2])*b
        assert len(w)==delta and unit_decide(parse(w))
        checks+=1
    return checks


def main():
    rng = Random(870_007)
    semantics = balanced = copies = permutations = selected = 0
    for k in range(1, 10):
        M, ell, J, r, P, B, A, Q = params(k)
        order0 = list(range(k*J))
        z = [0]*(k*r)
        h0 = [0]*M
        w0, xc0, hc0 = build(k,h0,z,order0)
        trials = 40 if k <= 5 else 12
        for _ in range(trials):
            order = rng.sample(order0,len(order0))
            h = rng.choices((0,1),k=M)
            x = rng.choices((0,1),k=k*r)
            w, xc, hc = build(k,h,x,order)
            assert len(w) == len(w0) and xc == xc0 and hc == hc0
            mask = set()
            for coords, bits, mult in ((xc,x,2),(hc,h,1)):
                for group, bit in zip(coords,bits):
                    assert len(group) == mult and not mask.intersection(group)
                    assert all(w[i] == bit for i in group)
                    mask.update(group)
            w_const, _, _ = build(k,h0,z,order)
            assert all((w[i] ^ w_const[i]) == (i in mask and w[i]) for i in range(len(w)))
            assert all(w_const[i] == w0[i] for i in mask)
            assert unit_decide(parse(w)) == lookup(k,h,x,order)
            semantics += 1
            b = balance(w)
            assert len(b) == 3*len(w)+12 and sum(b) == 2*len(w)+5
            assert unit_decide(parse(b)) == lookup(k,h,x,order)
            balanced += 1
            permutations += 1
        # Single source bit flips against all-zero source, permuted constants fixed.
        order = rng.sample(order0,len(order0))
        w, xc, hc = build(k,h0,z,order)
        probes = list(range(M+k*r)) if k <= 5 else rng.sample(range(M+k*r),16)
        for i in probes:
            h, x = h0.copy(), z.copy()
            if i < M:
                h[i] = 1; expect = hc[i]
            else:
                x[i-M] = 1; expect = xc[i-M]
            v, _, _ = build(k,h,x,order)
            assert [j for j,(a,b) in enumerate(zip(w,v)) if a != b] == expect
            bv,bw=balance(v),balance(w)
            assert [j for j,(a,b) in enumerate(zip(bw,bv)) if a!=b] == expect + [len(w)+11+2*j for j in expect]
            copies += 1
        # Construct an actual restriction from a light-mask, then verify lookup.
        if J >= 6:
            for _ in range(3):
                light = set(rng.sample(range(k*r), (k*r+1)//2))
                counts = [sum(t in light for t in range(s*ell,(s+1)*ell)) for s in range(k*J)]
                order, totals = balanced_order(counts,k,J)
                R = r//3
                assert min(totals) >= R
                keep = [[t for t in sorted(light) if order[t//ell]//J == row][:R] for row in range(k)]
                assert all(len(row) == R for row in keep)
                h = rng.choices((0,1),k=M)
                for _ in range(4):
                    x = [0]*(k*r); target = 0
                    for row, indices in enumerate(keep):
                        for t in indices: x[t] = rng.randrange(2)
                        target |= (sum(x[t] for t in indices)%2)<<row
                    w, _, _ = build(k,h,x,order)
                    assert unit_decide(parse(w)) == bool(h[target])
                    selected += 1
        print(f'k={k:2} M={M:4} ell={ell:2} J={J:3} r={r:3} n={len(w0):7} n/M={len(w0)/M:.3f}')
    # Exhaustive small balancing profiles and randomized large/adversarial masks.
    profiles = 0
    for k,J,ell in ((2,3,2),(3,2,2),(3,3,1)):
        for counts in product(range(ell+1), repeat=k*J):
            _, totals = balanced_order(counts,k,J)
            assert min(totals)*k >= sum(counts)-k*ell
            profiles += 1
    for _ in range(2000):
        k,J,ell = rng.randrange(2,25),rng.randrange(6,40),rng.randrange(1,33)
        counts = [rng.randrange(ell+1) for _ in range(k*J)]
        # include extreme all-or-nothing chunks
        if rng.randrange(2): counts = [rng.choice((0,ell)) for _ in counts]
        _, totals = balanced_order(counts,k,J)
        assert min(totals)*k >= sum(counts)-k*ell
        if 2*sum(counts) >= k*J*ell:
            assert min(totals) >= J*ell//3
        profiles += 1
    print(dict(semantic=semantics, balanced=balanced, permutations=permutations,
               source_flip_probes=copies, selected_row_sat=selected, balancing_profiles=profiles))
    print("reader_transfer, explicit_unfolding, multiple_witnesses",reader_transfer_tests(rng))
    print("padding_checks",padding_tests())

if __name__ == '__main__':
    main()
