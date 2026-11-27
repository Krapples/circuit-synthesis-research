"""Exhaustive free-NOT AIG check: does a function of n inputs have an AIG with <= s gates?

Exploration aid (2026-11-26) for the first-gate recursion in first_gate_lb.py. Gates are
x^p AND y^q over earlier wires, output negation free. Prefix gates are enumerated with a
nondecreasing larger-operand index (any DAG has such a topological order), degenerate
gates (constant or equal to an earlier wire up to complement) are skipped, and the last
gate is matched against the target directly.
Usage: python aig_exact_small.py <n> <hex truth table> <s>
"""
import sys


def has_aig(n, tt, s):
    N = 1 << n
    full = (1 << N) - 1
    targets = {tt, tt ^ full}
    wires = []
    for i in range(n):
        m = 0
        for x in range(N):
            if x >> i & 1:
                m |= 1 << x
        wires.append(m)
    if tt in (0, full) or any(w in targets for w in wires):
        return True  # needs 0 gates
    if s == 0:
        return False

    def last(ws):
        k = len(ws)
        for b in range(k):
            wb = ws[b]
            nb = wb ^ full
            for a in range(b):
                wa = ws[a]
                na = wa ^ full
                for v in (wa & wb, wa & nb, na & wb, na & nb):
                    if v in targets:
                        return True
        return False

    def rec(ws, depth, minb):
        if depth == s - 1:
            return last(ws)
        if last(ws):
            return True
        k = len(ws)
        seen = set(ws) | {w ^ full for w in ws} | {0, full}
        for b in range(minb, k):
            wb = ws[b]
            nb = wb ^ full
            for a in range(b):
                wa = ws[a]
                na = wa ^ full
                for v in (wa & wb, wa & nb, na & wb, na & nb):
                    if v in seen:
                        continue
                    if rec(ws + [v], depth + 1, b):
                        return True
        return False

    return rec(wires, 0, 0)


if __name__ == "__main__":
    n, tt, s = int(sys.argv[1]), int(sys.argv[2], 16), int(sys.argv[3])
    print(f"n={n} tt={tt:x} s={s}: {'FOUND' if has_aig(n, tt, s) else 'NONE'}", flush=True)
