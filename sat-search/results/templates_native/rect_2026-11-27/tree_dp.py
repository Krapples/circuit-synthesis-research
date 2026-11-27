"""Exact tree-decomposition DP for monotone AND/OR circuits on cared rows, excess s <= 1.

A minimum circuit has no unread non-output gate and no gate constant on the cared rows. Let H be its gates
read at least twice (p = |H|). Every other non-output gate has one reader, so the gates split into binary
trees rooted at H and the output; leaves are input reads and H reads, and a tree with L leaves has L-1 gates.
Hence k = (total leaf occurrences) - (p + 1). Gates act bitwise, so a tree using leaf h computes
lo | (hi & h) per bit: it is carried as the pair (lo, hi) = (value at h=0, value at h=1).

With every input essential (read at least once) and k <= n (excess s = k + 1 - n <= 1):
  k = n-1: p = 0, each input once (read-once formula).
  k = n:   p = 0 with one input read twice, or p = 1, f = 2, each input once
           (h = tree on S_h; output tree on the rest plus two h leaves).
usage: python tree_dp.py LINES_FILE [index ...]   (LINES: native template input format)
prints per unit: minimum k in {n-1, n} if found, else '>n'."""
import itertools, sys


def unit(line):
    f = line.split()
    n = int(f[1])
    rows = [(int(h, 16), int(t)) for h, t in (x.split(':') for x in f[5].split(','))]
    T = sum(t << j for j, (_, t) in enumerate(rows))
    wire = [sum(((r >> i) & 1) << j for j, (r, _) in enumerate(rows)) for i in range(n)]
    return f[0], n, T, wire, (1 << len(rows)) - 1


def all_essential(n, T, wire, FULL):
    """Monotone partial label: input i is essential iff some T=1 row a and T=0 row b have a minus i inside b."""
    rows = [sum(((wire[i] >> j) & 1) << i for i in range(n)) for j in range(FULL.bit_length())]
    one = [r for j, r in enumerate(rows) if T >> j & 1]
    zero = [r for j, r in enumerate(rows) if not T >> j & 1]
    return all(any((a & ~(1 << i)) & ~b == 0 for a in one for b in zero) for i in range(n))


def solve(line):
    uid, n, T, wire, FULL = unit(line)
    ALL = (1 << n) - 1
    if not all_essential(n, T, wire, FULL):
        return uid, 'skip'

    def ok(v):
        return v != 0 and v != FULL

    # R0[A]: read-once trees over input set A (bitmask)
    R0 = [set() for _ in range(1 << n)]
    for i in range(n):
        R0[1 << i] = {wire[i]}
    for A in sorted(range(1, 1 << n), key=lambda x: bin(x).count('1')):
        if A & (A - 1) == 0:
            continue
        out = set()
        B = (A - 1) & A
        while B:
            C = A ^ B
            if B < C:
                for p in R0[B]:
                    for q in R0[C]:
                        out.add(p & q); out.add(p | q)
            B = (B - 1) & A
        R0[A] = {v for v in out if ok(v)}
    if T in R0[ALL]:
        return uid, n - 1
    # p = 0, one input doubled: multiset DP with input i allowed twice
    for i in range(n):
        Rd = {}  # (A, has_extra) -> set ; extra copy of i
        def get(A, e):
            return R0[A] if not e else Rd[A]
        for A in sorted(range(0, 1 << n), key=lambda x: bin(x).count('1')):
            # multiset = A plus one extra copy of i (A may or may not contain i)
            out = set()
            if A == 0:
                Rd[A] = {wire[i]}
                continue
            # split: extra copy goes to one side
            B = A
            while True:
                C = A ^ B
                # side1 = (B, extra), side2 = (C, no extra); both nonempty as multisets
                if C:
                    for p in Rd[B]:
                        for q in R0[C]:
                            out.add(p & q); out.add(p | q)
                if B == 0:
                    break
                B = (B - 1) & A
            Rd[A] = {v for v in out if ok(v)}
        if T in Rd[ALL]:
            return uid, n
    # p = 1, f = 2, each input once. Rs[A][j]: pairs (lo, hi) for trees on A plus j copies of h.
    Rs = [[None, None, None] for _ in range(1 << n)]
    for A in range(1 << n):
        Rs[A][0] = {(v, v) for v in R0[A]}
    Rs[0][1] = {(0, FULL)}
    Rs[0][2] = {(0, FULL)}  # h & h = h | h = h (redundant gate, kept for completeness)
    for j in (1, 2):
        for A in sorted(range(0, 1 << n), key=lambda x: bin(x).count('1')):
            if A == 0:
                continue
            out = set()
            B = A
            while True:
                C = A ^ B
                for j1 in range(0, j + 1):
                    j2 = j - j1
                    if (B == 0 and j1 == 0) or (C == 0 and j2 == 0):
                        continue
                    if (B, j1) > (C, j2) and j1 == 0 and j2 == 0:
                        continue
                    if B == 0 and j1 > 0 and Rs[0][j1] is None:
                        continue
                    for a in Rs[B][j1]:
                        for b in Rs[C][j2]:
                            out.add((a[0] & b[0], a[1] & b[1])); out.add((a[0] | b[0], a[1] | b[1]))
                if B == 0:
                    break
                B = (B - 1) & A
            Rs[A][j] = {x for x in out if x != (0, 0) and x != (FULL, FULL)}
    for Sh in range(1, 1 << n):
        if Sh & (Sh - 1) == 0:
            continue
        C = ALL ^ Sh
        Ds = {hi & ~lo for lo, hi in Rs[C][2] if lo & ~T == 0 and T & ~hi == 0}
        if not Ds:
            continue
        for h in R0[Sh]:
            x = h ^ T
            if any(x & D == 0 for D in Ds):
                return uid, n
    return uid, '>n'


if __name__ == '__main__':
    lines = [l for l in open(sys.argv[1]).read().split('\n') if l.strip()]
    idx = [int(x) for x in sys.argv[2:]] or range(len(lines))
    for i in idx:
        print(*solve(lines[i]), flush=True)
