"""Prototype: signal-network test for the tight fan-out case (monotone circuits).

At excess e with k = e + 1 nonempty terminal groups there are no empty regions and every repeated terminal
(all but the output, which is the last group) has exactly two readers. For an ordered partition S_1..S_k:
 * terminal h_i depends only on S_i and earlier groups' inputs P_i; wherever f restricted to S_i (under some
   completion) is non-constant, h_i equals that restriction (monotone downstream is the identity);
 * region j needs >= p(S_j) incoming connections (output region: pout), from earlier terminals only;
 * for contexts a, b of region j with f_a(S_j) not <= f_b(S_j), some incoming terminal must be 1 at a and
   0 at b; a terminal is excluded if it is known equal at a and b, known 0 at a or 1 at b, or if a <= b on
   its inputs (monotone);
 * every non-output terminal sends exactly 2 connections.
If no ordered partition passes, B >= n + e (one more than the tight bound).
Usage: python signal_network.py  (L-meta-1343 at e = 7)"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import cube_search as cs
from functools import lru_cache
from itertools import product

E = [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9),
     (6, 7), (6, 10), (7, 9), (8, 9)]
n = 11
T = cs._anti([(1 << u) | (1 << v) for u, v in E])
SUP = cs.rterms_support(T)
f = lambda y: any(y & t == t for t in T)


def restriction(S, y):
    """f restricted to S under outside assignment y (bits of S ignored): antichain over S, or None if
    constant."""
    o = y & ~S
    if any((t & S) == 0 and (t & ~o) == 0 for t in T):
        return None
    surv = [t & S for t in T if (t & ~S & ~o) == 0 and t & S]
    return cs._anti(surv) if surv else None


def terminal_value(i, groups, y):
    """Known value of terminal h_i at full assignment y: 1, 0, or None (unknown). h_i depends on S_i and
    P_i = earlier groups. Look for a completion of the bits outside S_i and P_i that makes f|S_i
    non-constant; then h_i(y) = that restriction evaluated at y's S_i bits."""
    S = groups[i]
    P = 0
    for g in groups[:i]:
        P |= g
    free = SUP & ~S & ~P
    base = y & P
    bits = [b for b in range(n) if free >> b & 1]
    for k in range(1 << len(bits)):
        comp = base | sum(1 << bits[t] for t in range(len(bits)) if k >> t & 1)
        r = restriction(S, comp)
        if r is not None:
            ys = y & S
            return int(any((t & ys) == t for t in r))
    return None


def demands_for(j, groups):
    """Separation demands of region j: list of bitmasks of possible provider terminals (i < j)."""
    S = groups[j]
    ctx = cs.port_contexts(T, S)
    zs = list(ctx)
    dom = []
    for i in range(j):
        d = groups[i]
        for g in groups[:i]:
            d |= g
        dom.append(d)
    out = []
    for a in zs:
        for b in zs:
            if a == b or cs.terms_imply(ctx[a], ctx[b]):
                continue
            mask = 0
            for i in range(j):
                if (a & dom[i] & ~b) == 0:          # a <= b on h_i's inputs: h_i(a) <= h_i(b)
                    continue
                va, vb = terminal_value(i, groups, a), terminal_value(i, groups, b)
                if va == 0 or vb == 1 or (va is not None and va == vb):
                    continue
                mask |= 1 << i
            out.append(mask)
    return out


def network_feasible(needs, demands):
    k = len(needs)

    @lru_cache(None)
    def dp(j, caps):
        if j == k:
            return not any(caps)
        for v in product(*(range(c + 1) for c in caps)):
            if sum(v) < needs[j]:
                continue
            used = sum(1 << i for i, c in enumerate(v) if c)
            if any(not (m & used) for m in demands[j]):
                continue
            rem = tuple(c - u for c, u in zip(caps, v)) + ((2,) if j < k - 1 else ())
            if dp(j + 1, rem):
                return True
        return False
    return dp(0, ())


COSTS = cs.port_costs(T, mono=True, separation=True, profile=True, formula=True, output=True)


def enumerate_partitions(e):
    """Ordered partitions S_1..S_k (k = e + 1) passing the port-cost and eligibility tests."""
    k = e + 1
    costs = COSTS
    pout = costs.pout or {}
    ctxs = {S: cs.port_contexts(T, S) for S in costs}

    def eligible(S, P):
        seen = {}
        for z, sig in ctxs[S].items():
            kk = z & P
            if kk in seen and seen[kk] != sig:
                return False
            seen[kk] = sig
        return True
    found = []

    def dfs(P, groups, total):
        if total > e + k - 1:
            return
        if len(groups) == k:
            if P == SUP:
                found.append(tuple(groups))
            return
        rest = SUP & ~P
        S = rest
        while S:
            if S in costs and eligible(S, P):
                last = (P | S) == SUP
                if last and len(groups) == k - 1:
                    c = pout.get(S, costs[S])
                    if total + c <= e + k - 1:
                        found.append(tuple(groups + [S]))
                elif not last:
                    dfs(P | S, groups + [S], total + costs[S])
            S = (S - 1) & rest
    dfs(0, [], 0)
    return found


if __name__ == '__main__':
    e = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    k = e + 1
    costs, pout = COSTS, COSTS.pout or {}
    t0 = time.time()
    found = enumerate_partitions(e)
    print(f'e={e}, k={k}: {len(found)} ordered partitions pass the port/eligibility test ({time.time() - t0:.0f}s)', flush=True)
    passing = 0
    for idx, groups in enumerate(found):
        needs = [costs[S] for S in groups[:-1]] + [pout.get(groups[-1], costs[groups[-1]])]
        dem = [demands_for(j, list(groups)) for j in range(k)]
        if any(0 in d for d in dem):
            continue
        if network_feasible(needs, dem):
            passing += 1
            if passing <= 3:
                print('  feasible network for groups', [bin(S) for S in groups], flush=True)
        if idx % 200 == 0 and idx:
            print(f'  checked {idx}/{len(found)} ({time.time() - t0:.0f}s), {passing} feasible so far', flush=True)
    print(f'RESULT: {passing}/{len(found)} ordered partitions have a feasible signal network'
          f'{" -> bound rises to B >= " + str(n + e) if passing == 0 and found else ""} ({time.time() - t0:.0f}s)')
