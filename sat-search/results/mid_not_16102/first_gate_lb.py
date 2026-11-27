"""First-gate recursion lower bound for free-NOT AIG complexity (L-meta-16102, 2026-11-26).

In a minimal AIG the first gate reads two distinct inputs i, j. Either
  (B) input i (or j) has at least two readers: fixing it to either constant deletes them,
      so C(g) >= 2 + C(g|x_i=b) for both b; or
  (A) both have exactly one reader: g = Psi(x_i^a AND x_j^c, rest), and contracting the
      gate gives C(g) >= 1 + C(g') where g' has the gate output as a new input.
LB(g) = min over pairs {i,j} of min(B_i, B_j, A over factorizing polarities), with the
connectivity floor #essential - 1. This is a sound recursion only if each case is sound;
the Lean side would formalize exactly these three steps.
"""
import sys
from functools import lru_cache

CASCADE = 2


def var_mask(n, i):
    m = 0
    for x in range(1 << n):
        if x >> i & 1:
            m |= 1 << x
    return m


def cofactor(n, tt, i, b):
    """Truth table on n-1 vars (var i removed)."""
    out = 0
    k = 0
    for x in range(1 << n):
        if (x >> i & 1) != b:
            continue
        if tt >> x & 1:
            # index without bit i
            lo = x & ((1 << i) - 1)
            hi = x >> (i + 1)
            out |= 1 << (lo | (hi << i))
    return out


def nonconst(n, tt):
    return tt not in (0, (1 << (1 << n)) - 1)


def essential(n, tt):
    return [i for i in range(n) if cofactor(n, tt, i, 0) != cofactor(n, tt, i, 1)]


def reduce_fn(n, tt):
    """Drop inessential variables (largest index first)."""
    for i in reversed(range(n)):
        c0 = cofactor(n, tt, i, 0)
        if c0 == cofactor(n, tt, i, 1):
            n, tt = n - 1, c0
    return n, tt


def canon(n, tt):
    n, tt = reduce_fn(n, tt)
    full = (1 << (1 << n)) - 1
    return n, min(tt, tt ^ full)  # output negation is free


def factor(n, tt, i, j, a, c):
    """If tt = Psi(x_i==a AND x_j==c, rest), return g' on n-1 vars: rest + new var last."""
    rest = [k for k in range(n) if k not in (i, j)]
    m = len(rest)
    out = 0
    for r in range(1 << m):
        base = 0
        for t, k in enumerate(rest):
            if r >> t & 1:
                base |= 1 << k
        vals = {}
        for vi in (0, 1):
            for vj in (0, 1):
                x = base | (vi << i) | (vj << j)
                vals[(vi, vj)] = tt >> x & 1
        one = vals[(a, c)]
        zeros = {vals[p] for p in vals if p != (a, c)}
        if len(zeros) != 1:
            return None
        z = zeros.pop()
        if z:
            out |= 1 << r
        if one:
            out |= 1 << (r | (1 << m))
    return out


@lru_cache(maxsize=None)
def LB(n, tt, cascade=CASCADE):
    ess = essential(n, tt)
    if len(ess) <= 1:
        return 0
    floor = len(ess) - 1
    if len(ess) == 2:
        return 1
    sub = lambda v, b: LB(*canon(n - 1, cofactor(n, tt, v, b)), cascade)
    best = None
    for p in range(len(ess)):
        for q in range(p + 1, len(ess)):
            i, j = ess[p], ess[q]
            opts = []
            # Case 2: some first-gate input v has >= 2 readers.
            case2 = []
            for v in (i, j):
                C = [sub(v, b) for b in (0, 1)]
                lo, hi = sorted(C)
                val = 2 + hi
                if cascade:
                    # controlling value of the first gate kills R(v) and R(g1), and
                    # minimality gives R(g1) not inside R(v): >= 3 gates for some b.
                    val = max(val, 3 + lo)
                if cascade and cascade >= 2:
                    nc = [nonconst(n - 1, cofactor(n, tt, v, b)) for b in (0, 1)]
                    # >= 3 readers: fixing v either way deletes them.
                    three = 3 + hi
                    # exactly 2 readers g1, g2; b0 = value making g1 constant.
                    two = None
                    for b0 in (0, 1):
                        o = 1 - b0
                        alt = []
                        # g2 constant at o != b0: g1, g2 and R(g2) (nonempty unless f|v=o const)
                        alt.append((3 if nc[o] else 2) + C[o])
                        # g2 constant at b0 too: {g1,g2} u R(g1) u R(g2) >= 4 by minimality
                        alt.append((4 if nc[b0] else 3) + C[b0])
                        cand = max(3 + C[b0], min(alt))
                        two = cand if two is None else min(two, cand)
                    val = max(val, min(three, two))
                case2.append(val)
            opts.append(min(case2))
            # Case 1: both inputs have one reader; the gate is x_i^a AND x_j^c.
            for a in (0, 1):
                for c in (0, 1):
                    g = factor(n, tt, i, j, a, c)
                    if g is None:
                        continue
                    val = 1 + LB(*canon(n - 1, g), cascade)
                    if cascade:
                        # x_i := not a makes g1 constant: g1 and its reader(s) go.
                        val = max(val, 2 + sub(i, 1 - a), 2 + sub(j, 1 - c))
                    opts.append(val)
            val = min(opts)
            best = val if best is None else min(best, val)
    return max(floor, best)


def table_16102():
    bits = [0]*19 + [1, 0] + [1]*11 + [0, 0] + [1]*14 + [0, 0] + [1]*14
    assert len(bits) == 64
    return sum(b << k for k, b in enumerate(bits))


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    tt = table_16102()
    print("LB(f16102) without cascades =", LB(*canon(6, tt), False))
    print("LB(f16102) with first-level cascades =", LB(*canon(6, tt), 1))
    print("LB(f16102) with two-reader cascades =", LB(*canon(6, tt), 2))
    for v in range(6):
        for b in (0, 1):
            print(f"  x{v}={b}: LB =", LB(*canon(5, cofactor(6, tt, v, b))))
    print("states:", LB.cache_info().currsize)
