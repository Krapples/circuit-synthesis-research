"""Prototype: chain open-goat L107 (fan-out step) with exact small counted-NOT minima.

L107 (proved upstream, counted-NOT fan-in-2 AND/OR/NOT, every gate counted): if f depends on some
input, every restriction f|x_p=b at a dependent input p is nonconstant (RestrNC), and no two
dependent inputs form a pair funnel (three of the four (p,q)-restrictions equal), then a minimum
circuit of size s yields a restriction f|y=0 of size <= s-3 or f|y=1 of size <= s-4.  At s = m(f)
the input y must be dependent (otherwise f itself would have size < m(f)).  Hence

    m(f) >= min( min_p m(f|p=0) + 3, min_p m(f|p=1) + 4 )      (p over dependent inputs)

Lower bounds for the restrictions may replace m.  Base: exact counted-NOT minima of all 3-input
functions by set-BFS to size CAP (unseen functions get CAP+1, a valid lower bound).  Recursion:
LB_n(f) = max(support-1, L107 bound) for n >= 4.  Soundness check: LB_4 <= exact m_4 for every
4-input function whose exact minimum is found by set-BFS up to size CAP4.
This bound is for the counted-NOT basis and therefore also the monotone basis; it does NOT
apply to free-NOT (AIG) sizes.
Usage: python -I experiments/pequalnp_fanout_check.py [--cap 7] [--cap4 5]
"""
import argparse
import json
import os
import time
from functools import lru_cache

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def var(n, i):
    return sum(1 << r for r in range(1 << n) if r >> i & 1)


def exact_table(n, cap):
    """Counted-NOT minima (gates) of n-input functions found with <= cap gates."""
    full = (1 << (1 << n)) - 1
    xs = [var(n, i) for i in range(n)]
    best = {x: 0 for x in xs}
    best[0] = 0                      # missing wire reads false
    level = {frozenset()}
    for k in range(1, cap + 1):
        nxt = set()
        for st in level:
            w = xs + list(st)
            have = set(w)
            cand = set()
            for i, a in enumerate(w):
                cand.add(full ^ a)
                for b in w[i + 1:]:
                    cand.add(a & b)
                    cand.add(a | b)
            for g in cand:
                if g in have:
                    continue
                if g not in best:
                    best[g] = k
                if g not in (0, full):   # constants never help a minimum circuit
                    nxt.add(st | {g})
        level = nxt
    return best


def restrict(n, f, i, b):
    """f with input i fixed to b, as an (n-1)-input table (input i removed)."""
    out, r = 0, 0
    for x in range(1 << n):
        if (x >> i & 1) != b:
            continue
        lo, hi = x & ((1 << i) - 1), x >> (i + 1)
        if f >> x & 1:
            out |= 1 << (lo | (hi << i))
    return out


def depends(n, f, i):
    return restrict(n, f, i, 0) != restrict(n, f, i, 1)


def hypotheses(n, f):
    full = (1 << (1 << (n - 1))) - 1
    dep = [i for i in range(n) if depends(n, f, i)]
    if not dep:
        return dep, False
    for p in dep:
        for b in (0, 1):
            if restrict(n, f, p, b) in (0, full):
                return dep, False
    for p in dep:
        for q in dep:
            if p >= q:
                continue
            # q has index q-1 after removing p (q > p)
            sub = {(a, b): restrict(n - 1, restrict(n, f, p, a), q - 1, b) for a in (0, 1) for b in (0, 1)}
            for a in (0, 1):
                for b in (0, 1):
                    others = [sub[(a2, b2)] for a2 in (0, 1) for b2 in (0, 1) if (a2, b2) != (a, b)]
                    if others[0] == others[1] == others[2]:
                        return dep, False
    return dep, True


def make_lb(base_n, base, base_cap):
    @lru_cache(maxsize=None)
    def lb(n, f):
        if n == base_n:
            return base.get(f, base_cap + 1)
        dep, ok = hypotheses(n, f)
        support = max(0, len(dep) - 1)
        if not ok:
            return support
        step = min(min(lb(n - 1, restrict(n, f, p, 0)) + 3 for p in dep),
                   min(lb(n - 1, restrict(n, f, p, 1)) + 4 for p in dep))
        return max(support, step)
    return lb


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cap', type=int, default=7)
    ap.add_argument('--cap4', type=int, default=5)
    args = ap.parse_args()
    t = time.time()
    m3 = exact_table(3, args.cap)
    print(f'm3: {len(m3)} functions with min <= {args.cap} ({time.time() - t:.1f}s)')
    lb = make_lb(3, m3, args.cap)
    t = time.time()
    m4 = exact_table(4, args.cap4)
    print(f'm4: {len(m4)} functions with min <= {args.cap4} ({time.time() - t:.1f}s)')
    # cross-check the set-BFS tables against exact values proved in Lean upstream
    v3 = [var(3, i) for i in range(3)]
    v4 = [var(4, i) for i in range(4)]
    maj3 = (v3[0] & v3[1]) | (v3[0] & v3[2]) | (v3[1] & v3[2])
    path4 = (v4[0] & v4[1]) | (v4[1] & v4[2]) | (v4[2] & v4[3])
    c4 = path4 | (v4[3] & v4[0])
    assert m3[maj3] == 4, 'L100: majority of three has size 4'
    assert m4[path4] == 4, 'L102: path on 4 inputs has size 4 + 2 - 2'
    assert m4[c4] == 3, 'L112: the 4-cycle edge function has size 3'
    assert m4[v4[0] | v4[1] | v4[2] | v4[3]] == 3, 'L012: OR of 4 inputs has size 3'
    print('cross-checks vs L012/L100/L102/L112: ok')
    bad = gains = applicable = 0
    for f, m in m4.items():
        b = lb(4, f)
        bad += b > m
    for f in range(1 << 16):
        dep, ok = hypotheses(4, f)
        if ok:
            applicable += 1
            gains += lb(4, f) > max(0, len(dep) - 1)
    print(f'n=4: soundness violations {bad} (over {len(m4)} exact minima); '
          f'L107 applicable to {applicable}/65536, beats support on {gains}')
    # 4-input distribution of the bound among applicable functions
    dist = {}
    for f in range(1 << 16):
        dep, ok = hypotheses(4, f)
        if ok:
            dist[lb(4, f)] = dist.get(lb(4, f), 0) + 1
    print('n=4 L107 bound histogram (applicable functions):', dict(sorted(dist.items())))
    # corpus complete functions with n = 5 and 6
    seen = set()
    for path in ('results/synthesis_cases.json', 'results/synthesis_signed_cases.json'):
        for c in json.load(open(os.path.join(HERE, path), encoding='utf-8')):
            n, truth = int(c['n']), int(c['truth'])
            if c['name'] in seen or n not in (5, 6) or int(c['known']) != (1 << (1 << n)) - 1:
                continue
            seen.add(c['name'])
            dep, ok = hypotheses(n, truth)
            print(f"  {c['name']:22s} n={n} support-1={max(0, len(dep) - 1)} L107_ok={ok} chain_lb={lb(n, truth)}")


if __name__ == '__main__':
    main()
