# Finite threshold of the PS_d block-product route for B(SAT_n).
# Bound: B(SAT_n) >= n + q*(2r - 3d + 3), q = floor(n/(2r+8)) - 2^r - 1 (h <= 2^r helpers).
# d(r): least d with union bound C(r,d) 2^(r-d) * 2 d(d-1) * 2^(-2^(d-2)) < 1 (PS_d exists),
# versus README d = ceil(log2(4r)) + 2.
from math import comb, ceil, log2
from fractions import Fraction
def d_union(r):
    for d in range(2, r + 1):
        if Fraction(comb(r, d) * 2**(r - d) * 2 * d * (d - 1), 2**(2**(d - 2))) < 1:
            return d
    return None
def d_readme(r):
    return ceil(log2(4 * r)) + 2
def best(n, dfun):
    b = 0
    for r in range(2, 40):
        d = dfun(r)
        if d is None or d > r: continue
        q = n // (2 * r + 8) - 2**r - 1
        if q >= 1: b = max(b, n + q * (2 * r - 3 * d + 3))
    return b
for r in range(8, 33, 4): print('r', r, 'd_union', d_union(r), 'd_readme', d_readme(r))
for name, df in (('union', d_union), ('readme', d_readme)):
    lo = None
    for e in range(10, 80):
        n = 2**e
        if best(n, df) > 17 * n // 12 - 4:
            lo = e; break
    print(name, 'first power of two beating floor(17n/12)-4: 2^%s' % lo)
