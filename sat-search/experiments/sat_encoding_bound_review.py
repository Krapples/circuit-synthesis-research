"""Independent finite checks for the six-bit / even-length SAT encoding lower-bound notes.

The decoder is written from PEqualNP/Defs/Search.lean (encodeLiteral/encodeClause/encodeCNF), not copied
from the bundle scripts. Literal (v, b): [1,b] ++ flatMap (fun d => [1,d]) (Nat.bits v) ++ [0,1];
Nat.bits is LSB first with no trailing zero (bits 0 = []). Clause: literals ++ [0,0]. b = true is positive.
"""
from itertools import combinations, product
import random
import sys


def parse(s):
    """Unique CNF with encodeCNF = s, or None. Tokens are bit pairs."""
    if len(s) % 2:
        return None
    toks = [s[i:i + 2] for i in range(0, len(s), 2)]
    cnf, clause, i = [], [], 0
    while i < len(toks):
        t = toks[i]
        if t == '00':
            cnf.append(tuple(clause)); clause = []; i += 1; continue
        if t[0] != '1':  # '01' cannot start a literal
            return None
        pol = t[1] == '1'; i += 1
        bits = []
        while i < len(toks) and toks[i][0] == '1':
            bits.append(int(toks[i][1])); i += 1
        if i == len(toks) or toks[i] != '01':
            return None
        if bits and bits[-1] == 0:  # Nat.bits has no trailing zero
            return None
        clause.append((sum(b << j for j, b in enumerate(bits)), pol)); i += 1
    return tuple(cnf) if not clause else None


def encode(cnf):
    out = []
    for c in cnf:
        for v, p in c:
            out.append('1' + ('1' if p else '0'))
            while v:
                out.append('1' + str(v & 1)); v >>= 1
            out.append('01')
        out.append('00')
    return ''.join(out)


def satisfiable(cnf):
    if cnf is None:
        return False
    vs = sorted({v for c in cnf for v, _ in c})
    for a in product((False, True), repeat=len(vs)):
        s = dict(zip(vs, a))
        if all(any(s[v] == p for v, p in c) for c in cnf):
            return True
    return False


def sat(s):
    return satisfiable(parse(s))


def fill(template, row, names):
    return ''.join(str(row >> names.index(c) & 1) if c in names else c for c in template)


def truth(template, names):
    return sum(sat(fill(template, r, names)) << r for r in range(1 << len(names)))


# ---- Boolean function helpers (tt as int over n vars, row bit i = var i) ----
def cof(n, f, i, b):
    out = 0
    for r in range(1 << (n - 1)):
        lo = r & ((1 << i) - 1); hi = r >> i
        out |= (f >> (lo | (b << i) | (hi << (i + 1))) & 1) << r
    return out


def support(n, f):
    return [i for i in range(n) if cof(n, f, i, 0) != cof(n, f, i, 1)]


def pair_funnel(n, f):
    for i, j in combinations(range(n), 2):
        cs = [cof(n - 1, cof(n, f, j, b), i, a) for b in (0, 1) for a in (0, 1)]
        if any(cs.count(c) >= 3 for c in cs):
            return True
    return False


def full(n):
    return (1 << (1 << n)) - 1


def is_xor2(n, f):
    sup = support(n, f)
    if len(sup) != 2:
        return False
    i, j = sup
    vals = {}
    for r in range(1 << n):
        vals[(r >> i & 1) ^ (r >> j & 1)] = vals.get((r >> i & 1) ^ (r >> j & 1), set()) | {f >> r & 1}
    return all(len(v) == 1 for v in vals.values()) and vals[0] != vals[1]


def main():
    rng = random.Random(1125)
    # 0. decoder round trip and independence from the bundle decoder: every even string up to 14 bits.
    roundtrip = 0
    for L in range(2, 15, 2):
        for a in range(1 << L):
            s = format(a, f'0{L}b'); c = parse(s)
            if c is not None:
                assert encode(c) == s; roundtrip += 1
    for _ in range(3000):
        cnf = tuple(tuple((rng.randrange(40), rng.random() < .5) for _ in range(rng.randrange(4)))
                    for _ in range(rng.randrange(1, 5)))
        assert parse(encode(cnf)) == cnf
    print('decoder: legal strings up to 14 bits', roundtrip, 'random round trips 3000')

    T = lambda x, y: f'11{x}10{y}'
    # 1. six-bit identity, exhaustive through q=6
    checks = 0
    for q in range(1, 7):
        for bits in product((0, 1), repeat=2 * q):
            s = ''.join(T(bits[2 * i], bits[2 * i + 1]) for i in range(q)) + '110100'
            assert sat(s) == all(bits[2 * i] == bits[2 * i + 1] for i in range(q)); checks += 1
    print('six-bit F_q identity checks', checks)

    # 2/3. tails: truth tables and prefix composition (both positive fragments and arbitrary valid prefixes)
    mux, h14 = '11zy1x0100', '11u1zyx1110100'
    assert truth(mux, 'xyz') == 0xac, hex(truth(mux, 'xyz'))
    assert truth(h14, 'xyzu') == 0xe8f2, hex(truth(h14, 'xyzu'))
    comp = 0
    for tail, names, f in ((mux, 'xyz', 0xac), (h14, 'xyzu', 0xe8f2)):
        for q in range(0, 5):
            for bits in product((0, 1), repeat=2 * q):
                pre = ''.join(T(bits[2 * i], bits[2 * i + 1]) for i in range(q))
                ok = all(bits[2 * i] == bits[2 * i + 1] for i in range(q))
                for r in range(1 << len(names)):
                    assert sat(pre + fill(tail, r, names)) == (ok and bool(f >> r & 1)); comp += 1
        # stronger: an arbitrary legal satisfiable-by-all-true prefix with an open positive clause
        for _ in range(300):
            cl = [tuple((rng.randrange(6), True) for _ in range(rng.randrange(1, 3))) for _ in range(rng.randrange(3))]
            openc = encode([tuple((rng.randrange(6), True) for _ in range(rng.randrange(1, 3)))])[:-2]
            pre = encode(cl) + openc
            for r in range(1 << len(names)):
                assert sat(pre + fill(tail, r, names)) == bool(f >> r & 1); comp += 1
    # the 12-bit gadget is unsafe after a negative fragment (regression from the notes)
    assert not sat('100100' + '110100') and sat('101101' + '110100') is True
    print('tail composition checks', comp)

    # 4. structural premises
    assert not pair_funnel(3, 0xac) and all(cof(3, 0xac, i, b) not in (0, full(2)) for i in range(3) for b in (0, 1))
    H = 0xe8f2
    assert support(4, H) == [0, 1, 2, 3] and not pair_funnel(4, H)
    assert all(cof(4, H, i, b) not in (0, full(3)) for i in range(4) for b in (0, 1))
    strong = {0: 1, 1: 0, 2: 0, 3: 1}  # x=1, y=0, z=0, u=1
    expected = {0: 0xed, 1: 0x8e, 2: 0x82, 3: 0xe8}
    for i, b in strong.items():
        g = cof(4, H, i, b)
        assert g == expected[i], (i, hex(g))
        assert support(3, g) == [0, 1, 2]
        case_a = any(is_xor2(2, cof(3, g, j, c)) for j in range(3) for c in (0, 1))
        case_b = (not pair_funnel(3, g)) and all(len(support(2, cof(3, g, j, c))) == 2 for j in range(3) for c in (0, 1))
        assert case_a or case_b, (i, hex(g))
        print(f'  H strong cofactor var{i}={b}: {g:#04x} case_a={case_a} case_b={case_b}')
    # mux unary cofactors are nonconstant (one essential input at least)
    assert all(support(2, cof(3, 0xac, i, b)) for i in range(3) for b in (0, 1))
    print('structural premises ok')

    # 5. full essential support at even lengths
    U, ess = '100100', 0
    def sensitive(w):
        return {i for i in range(len(w)) if sat(w) != sat(w[:i] + str(1 - int(w[i])) + w[i + 1:])}
    for n in range(12, 61, 2):
        k, rmd = divmod(n, 6)
        if rmd == 0:
            words = [U * k]
        elif rmd == 2:
            if k < 3:
                continue
            words = [U * (k - 1) + '10110100', '10110100' + U * (k - 1)]
        else:
            words = [U * (k - 1) + '1001100100', '1001100100' + U * (k - 1)] if k >= 2 else []
            if n == 16:
                words = ['1001001001100100', '1001001001110100', '1001001010110100']
        assert all(sat(w) and len(w) == n for w in words), n
        cov = set().union(*(sensitive(w) for w in words))
        assert cov == set(range(n)), (n, sorted(set(range(n)) - cov)); ess += 1
    print('full-support lengths checked (even 12..60 except 14)', ess)

    # 6. bound arithmetic
    for n in range(16, 2001, 2):
        k, rmd = divmod(n, 6)
        if rmd == 0:
            q, m, c = k - 1, 2 * (k - 1), 4 * (k - 1) - 1
        elif rmd == 2:
            q, m, c = k - 2, 2 * (k - 2) + 4, 4 * (k - 2) + 6
        else:
            q, m, c = k - 1, 2 * (k - 1) + 3, 4 * (k - 1) + 3
        assert n - m + c >= (4 * n) // 3 - 3, n
    print('bound arithmetic: n-m+C >= floor(4n/3)-3 for even 16..2000')

    # 7. truth tables for exact percy checks (row bit r: var i = bit i of r)
    def conj(n1, f1, n2, f2):
        return sum((f1 >> (r & ((1 << n1) - 1)) & 1 & (f2 >> (r >> n1) & 1)) << r for r in range(1 << (n1 + n2)))
    xnor = 0b1001
    tabs = {'F2': (4, conj(2, xnor, 2, xnor)), 'F1_mux': (5, conj(2, xnor, 3, 0xac)), 'H': (4, H)}
    for i, b in strong.items():
        tabs[f'F1_g{i}'] = (5, conj(2, xnor, 3, expected[i]))
    for name, (n, f) in tabs.items():
        print('percy', name, n, format(f, f'0{(1 << n) // 4}x'))


if __name__ == '__main__':
    main()
