"""L-meta-612 probe: for small C4-free graphs, how few AND gates / OR gates can a monotone
fan-in-2 circuit for the edge function have, and is the total ever below |E| + tau - 1?

Encoding as in mono_shard.py: exactly S gates, each AND/OR of two different earlier wires,
output = last gate (a smaller circuit pads by OR-ing the output with an input... no: we let
the output be any gate). Rows: edges (=1) and maximal independent sets (=0), enough for a
monotone circuit. Every model is re-checked on all 2^n inputs.

Queries per graph (S = size cap):
  total : size <= E + tau - 2                       (the step itself; expect UNSAT)
  and   : #AND <= tau - 1 with size <= S            (cut half A: expect UNSAT?)
  or    : #OR  <= E - 2   with size <= S            (cut half B: expect UNSAT?)
Usage: python l612_counts.py [--extra 3]
"""
import argparse, itertools, os, sys, time
sys.path.insert(0, r"C:\Users\Carson\Documents\ChatGPT\P=NP\.scratch-sat")
from multiprocessing import Pool
from pysat.formula import IDPool
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType


def c4free(n, E):
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v); adj[v].add(u)
    for a, c in itertools.combinations(range(n), 2):
        if len(adj[a] & adj[c]) >= 2:
            return False
    return True


def tau(n, E):
    for k in range(n + 1):
        for S in itertools.combinations(range(n), k):
            s = set(S)
            if all(u in s or v in s for u, v in E):
                return k


def rows(n, E):
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v); adj[v].add(u)
    ones = [(1 << u) | (1 << v) for u, v in E]
    zeros = []
    for m in range(1 << n):
        if any(m >> u & 1 and m >> v & 1 for u, v in E):
            continue
        if all(m >> w & 1 or any(m >> z & 1 for z in adj[w]) for w in range(n)):
            zeros.append(m)
    return ones, zeros


def solve(n, E, S, max_and=None, max_or=None):
    ones, zeros = rows(n, E)
    R = [(m, 1) for m in ones] + [(m, 0) for m in zeros]
    pool = IDPool()
    W = n + S
    sel = {}
    isand = {g: pool.id(('a', g)) for g in range(n, W)}
    val = {}
    cl = []
    for w in range(W):
        for r, (m, _) in enumerate(R):
            val[w, r] = pool.id(('v', w, r))
    for w in range(n):
        for r, (m, _) in enumerate(R):
            cl.append([val[w, r]] if m >> w & 1 else [-val[w, r]])
    for g in range(n, W):
        prs = list(itertools.combinations(range(g), 2))
        lits = [pool.id(('s', g, i, j)) for i, j in prs]
        for (i, j), s in zip(prs, lits):
            sel[g, i, j] = s
        cl.append(lits)
        cl += CardEnc.atmost(lits, 1, vpool=pool, encoding=EncType.seqcounter).clauses
        for (i, j), s in zip(prs, lits):
            a = isand[g]
            for r in range(len(R)):
                v, x, y = val[g, r], val[i, r], val[j, r]
                # AND
                cl += [[-s, -a, -v, x], [-s, -a, -v, y], [-s, -a, v, -x, -y]]
                # OR
                cl += [[-s, a, v, -x], [-s, a, v, -y], [-s, a, -v, x, y]]
    out = {g: pool.id(('o', g)) for g in range(n, W)}
    cl.append(list(out.values()))
    for g in range(n, W):
        for r, (m, t) in enumerate(R):
            cl.append([-out[g], val[g, r] if t else -val[g, r]])
    ands = list(isand.values())
    if max_and is not None:
        cl += CardEnc.atmost(ands, max_and, vpool=pool, encoding=EncType.seqcounter).clauses
    if max_or is not None:
        cl += CardEnc.atmost([-a for a in ands], max_or, vpool=pool,
                             encoding=EncType.seqcounter).clauses
    with Solver(name='maplechrono', bootstrap_with=cl) as s:
        ok = s.solve()
        if not ok:
            return None
        md = set(l for l in s.get_model() if l > 0)
    gates = []
    for g in range(n, W):
        for i, j in itertools.combinations(range(g), 2):
            if sel[g, i, j] in md:
                gates.append(('AND' if isand[g] in md else 'OR', i, j))
    o = next(g for g in range(n, W) if out[g] in md)
    # recheck on all inputs
    for m in range(1 << n):
        w = [m >> i & 1 for i in range(n)]
        for op, i, j in gates:
            w.append(w[i] & w[j] if op == 'AND' else w[i] | w[j])
        want = int(any(m >> u & 1 and m >> v & 1 for u, v in E))
        assert w[o] == want, 'model fails recheck'
    return gates, o


GRAPHS = {
    'P4': (4, [(0, 1), (1, 2), (2, 3)]),
    'K3': (3, [(0, 1), (1, 2), (0, 2)]),
    'P5': (5, [(0, 1), (1, 2), (2, 3), (3, 4)]),
    'C5': (5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]),
    'bull': (5, [(0, 1), (1, 2), (0, 2), (0, 3), (1, 4)]),
    'bowtie': (5, [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)]),
    'K3+tail2': (5, [(0, 1), (1, 2), (0, 2), (2, 3), (3, 4)]),
    'spider': (7, [(0, 1), (1, 2), (0, 3), (3, 4), (0, 5), (5, 6)]),
    'P6': (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]),
    'C6': (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)]),
    'C5+leaf': (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5)]),
    'C5+2leaf': (7, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (2, 6)]),
    'K3+3leaf': (6, [(0, 1), (1, 2), (0, 2), (0, 3), (1, 4), (2, 5)]),
    'C7': (7, [(i, (i + 1) % 7) for i in range(7)]),
    '2K3+e': (6, [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (2, 3)]),
}


def job(args):
    name, kind, extra = args
    n, E = GRAPHS[name]
    t = tau(n, E)
    m = len(E)
    t0 = time.time()
    if kind == 'total':
        r = solve(n, E, m + t - 2)
    elif kind == 'and':
        r = solve(n, E, m + t - 1 + extra, max_and=t - 1)
    else:
        r = solve(n, E, m + t - 1 + extra, max_or=m - 2)
    return name, kind, m, t, r, time.time() - t0


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--extra', type=int, default=3)
    ap.add_argument('--workers', type=int, default=22)
    ap.add_argument('--only', default='')
    a = ap.parse_args()
    names = [x for x in GRAPHS if not a.only or x in a.only.split(',')]
    for x in names:
        assert c4free(*GRAPHS[x]), x
    tasks = [(x, k, a.extra) for x in names for k in ('total', 'and', 'or')]
    with Pool(a.workers) as p:
        for name, kind, m, t, r, dt in p.imap_unordered(job, tasks):
            print('%-9s %-5s E=%d tau=%d  %s  %.1fs' % (name, kind, m, t,
                  'UNSAT' if r is None else 'SAT %s out=%d' % r, dt), flush=True)
