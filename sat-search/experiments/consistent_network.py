"""Consistent signal-network test (tight fan-out case, monotone circuits).

Same regional model as signal_network.py (k = e + 1 nonempty groups S_1..S_k in order, inputs read once,
every non-output terminal read exactly twice by later regions, the last region is the output), but each
terminal i now has ONE truth table h_i on a row set R, shared by all its readers:
 * h_i depends monotonically on its domain D_i = S_1 u ... u S_i:  a <= b on D_i  =>  h_i(a) <= h_i(b);
 * region j:  a <= b on S_j  and  h_i(a) <= h_i(b) for every provider i  =>  h_j(a) <= h_j(b),
   i.e.  h_j(a) & ~h_j(b)  =>  OR_i [conn(i, j) & h_i(a) & ~h_i(b)];
 * the output terminal equals f on R; region j receives >= needs[j] wires; each terminal sends 2.
With R = all rows these conditions are exactly realizability by monotone local functions (positive rows
are upward-closed images, see the monotone-extension argument), so UNSAT on ANY row subset R is a valid
proof that no circuit with this region structure exists. SAT is not a circuit witness.

Usage: python consistent_network.py [e] [limit] [rows: minmax|false|all]    (L-meta-1343; default e=7)"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import cube_search as cs  # noqa: F401  (puts the vendored pysat on sys.path)
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver


def minmax_rows(n, f, sup):
    """Minimal true points and maximal false points of monotone f (restricted to the support)."""
    bits = [b for b in range(n) if sup >> b & 1]
    R = []
    S = sup
    while True:
        v = f(S)
        if v and all(not f(S & ~(1 << b)) for b in bits if S >> b & 1):
            R.append(S)
        if not v and all(f(S | (1 << b)) for b in bits if not S >> b & 1):
            R.append(S)
        if S == 0:
            break
        S = (S - 1) & sup
    return sorted(R)


def all_rows(sup):
    R, S = [], sup
    while True:
        R.append(S)
        if S == 0:
            return sorted(R)
        S = (S - 1) & sup


def consistent_feasible(groups, needs, R, f, solver='g4', budget=None):
    """True if the consistent network SAT is satisfiable, False if UNSAT, None if the budget ran out."""
    k = len(groups)
    pool = IDPool()
    cl = []
    D, acc = [], 0
    for g in groups:
        acc |= g
        D.append(acc)
    h = {(i, r): pool.id(('h', i, r)) for i in range(k) for r in R}
    for r in R:                                   # output terminal = f
        cl.append([h[k - 1, r] if f(r) else -h[k - 1, r]])
    for i in range(k):                            # monotone in own domain
        for a in R:
            da = a & D[i]
            for b in R:
                if a != b and da & ~b == 0:
                    cl.append([-h[i, a], h[i, b]])
    # wire slots: terminal i (non-output) sends slots 0 and 1 to later regions, slot0 <= slot1
    slot = {}
    for i in range(k - 1):
        for s in (0, 1):
            vs = [pool.id(('t', i, s, j)) for j in range(i + 1, k)]
            for j in range(i + 1, k):
                slot[i, s, j] = pool.id(('t', i, s, j))
            cl.extend(CardEnc.equals(vs, 1, vpool=pool, encoding=EncType.pairwise).clauses)
        for j0 in range(i + 1, k):                # symmetry: slot1's target >= slot0's target
            for j1 in range(i + 1, j0):
                cl.append([-slot[i, 0, j0], -slot[i, 1, j1]])
    conn = {}
    for j in range(1, k):
        ins = [slot[i, s, j] for i in range(j) for s in (0, 1)]
        if needs[j] > 0:
            cl.extend(CardEnc.atleast(ins, needs[j], vpool=pool, encoding=EncType.seqcounter).clauses)
        for i in range(j):
            c = pool.id(('c', i, j))
            conn[i, j] = c
            cl.append([-c, slot[i, 0, j], slot[i, 1, j]])
            cl.append([c, -slot[i, 0, j]])
            cl.append([c, -slot[i, 1, j]])
    if needs[0] > 0:
        return False                               # the first region has no earlier terminals
    sep = {}

    def sepv(i, a, b):
        key = (i, a, b)
        if key not in sep:
            v = pool.id(('s',) + key)
            sep[key] = v
            cl.append([-v, h[i, a]])
            cl.append([-v, -h[i, b]])
        return sep[key]
    for j in range(1, k):
        S = groups[j]
        for a in R:
            sa = a & S
            for b in R:
                if a == b or sa & ~b or (a & D[j]) & ~b == 0:
                    continue                       # not ordered on S_j, or already a domain-monotone pair
                lits = [-h[j, a], h[j, b]]
                for i in range(j):
                    if (a & D[i]) & ~b == 0:
                        continue                   # h_i(a) <= h_i(b) forced
                    u = pool.id(('u', i, j, a, b))
                    cl.append([-u, conn[i, j]])
                    cl.append([-u, sepv(i, a, b)])
                    lits.append(u)
                cl.append(lits)
    with Solver(name=solver, bootstrap_with=cl) as s:
        if budget:
            s.conf_budget(budget)
            r = s.solve_limited()
        else:
            r = s.solve()
    return r


if __name__ == '__main__':
    import signal_network as sn
    e = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    rowmode = sys.argv[3] if len(sys.argv) > 3 else 'minmax'
    k = e + 1
    t0 = time.time()
    if rowmode == 'minmax':
        R = minmax_rows(sn.n, sn.f, sn.SUP)
    elif rowmode == 'false':          # every false point plus the minimal true points
        R = sorted(set(r for r in all_rows(sn.SUP) if not sn.f(r)) | set(sn.T))
    else:
        R = all_rows(sn.SUP)
    print(f'{len(R)} rows ({rowmode})', flush=True)
    found = sn.enumerate_partitions(e)
    print(f'e={e}, k={k}: {len(found)} ordered partitions ({time.time() - t0:.0f}s); testing {min(limit, len(found))}',
          flush=True)
    costs, pout = sn.COSTS, sn.COSTS.pout or {}
    jobs = [(g, [costs[S] for S in g[:-1]] + [pout.get(g[-1], costs[g[-1]])]) for g in found[:limit]]
    sat = 0
    t1 = time.time()
    for g, needs in jobs:
        r = consistent_feasible(list(g), needs, R, sn.f)
        sat += bool(r)
    print(f'RESULT: {sat}/{len(jobs)} feasible under consistent truth tables ({time.time() - t1:.1f}s, '
          f'{(time.time() - t1) / max(1, len(jobs)) * 1000:.0f} ms each)')
