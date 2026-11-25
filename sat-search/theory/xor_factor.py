"""Exact XOR-factor preprocessing in the free-NOT basis (binary AND/OR gates counted, NOT gates free).

If f(x) = x_i XOR h(rest) with h nonconstant and independent of x_i, then C(f) = C(h) + 3 (supplied by the
independent theory audit; independently tested here against gate-set enumeration, verify/test_xor_factor.py).
Only this exact factor form is used: f|x_i=1 == NOT f|x_i=0. The unrestricted XOR-input-module conjecture
(an arbitrary XOR of input groups) is NOT assumed. This applies to the free-NOT binary count only, not to
the counted-NOT total.
Truth tables: bit a of f is f(a); all inputs essential."""
from module_contraction import cofactor1


def xor_factor(n, f):
    """(i, h) for the first input with f = x_i XOR h, h = f|x_i=0 nonconstant; None if there is none."""
    if n < 2:
        return None
    one = (1 << (1 << (n - 1))) - 1
    for i in range(n):
        a, b = cofactor1(n, f, i, 0), cofactor1(n, f, i, 1)
        if b == a ^ one and a not in (0, one):
            return i, a
    return None


def strip_xor(n, f):
    """Remove XOR factors repeatedly. Returns (core_n, core_f, factors) with
    C_free(f) = C_free(core) + 3 * factors."""
    k = 0
    while True:
        s = xor_factor(n, f)
        if s is None:
            return n, f, k
        n, f = n - 1, s[1]
        k += 1
