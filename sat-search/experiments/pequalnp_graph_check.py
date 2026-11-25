"""Compare open-goat/pequalnp-proofs edge-function theorems with our corpus intervals.

Their model: fan-in-2 AND/OR/NOT straight-line circuits, every gate (NOT included) counted.
That is the corpus `not` basis (cube_search counts NOT gates in G); `mono` is AND/OR only.
counted-NOT minimum <= monotone minimum, so their lower bounds also bound `mono` from below.

Rows used (all proved in Lean upstream, statements checked against the clone in external/):
  L154  every graph with an edge: size <= |E| + tau - 1 (monotone circuit; valid in both bases)
  L104  forests: size >= |E| + tau - 1                       (counted NOT)
  L204  girth >= 7, degree>=3 vertices pairwise >= 7 apart: size >= |E| + tau - 1 (counted NOT)
  L102  path P_n: n + floor(n/2) - 2 exactly;  L106 cycle C_n, n >= 5: n + ceil(n/2) - 1 exactly
  L112  C_4 (= K_{2,2}): 3 exactly, so |E| + tau - 1 = 5 is NOT a lower bound once a C_4 appears.
Usage: python -I experiments/pequalnp_graph_check.py   (reads results/, writes nothing)
"""
import ast
import json
import os
from collections import deque
from itertools import combinations

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def intervals():
    out = {}
    for path in ('results/synthesis_ablation.jsonl', 'results/synthesis_endpoints.jsonl',
                 'results/synthesis_signed.jsonl'):
        for line in open(os.path.join(HERE, path), encoding='utf-8'):
            r = json.loads(line)
            b = r.get('basis')
            if b not in ('mono', 'not'):
                continue
            key = (r.get('case'), b)
            lo, hi = out.get(key, (0, 10 ** 9))
            if r.get('kind') == 'interval':
                fin = r['final'] if isinstance(r['final'], dict) else ast.literal_eval(r['final'])
                lo, hi = max(lo, fin['lower']), min(hi, fin['upper'])
            elif r.get('kind') == 'job' and 'budget' in r:
                if r.get('status') == 'UNSAT':
                    lo = max(lo, r['budget'] + 1)
                elif r.get('status') in ('SAT', 'WITNESS') or r.get('witness'):
                    hi = min(hi, r['budget'])
            out[key] = (lo, hi)
    return out


def graph_of(n, truth):
    """Return the edge list if truth is exactly an edge function, else None."""
    f = lambda x: truth >> x & 1
    edges = [(a, b) for a, b in combinations(range(n), 2) if f((1 << a) | (1 << b))]
    if f(0) or any(f(1 << a) for a in range(n)) or not edges:
        return None
    for x in range(1 << n):
        if f(x) != any(x >> a & 1 and x >> b & 1 for a, b in edges):
            return None
    return edges


def min_cover(n, edges):
    for k in range(n + 1):
        for S in combinations(range(n), k):
            s = set(S)
            if all(a in s or b in s for a, b in edges):
                return S


def tau(n, edges):
    return len(min_cover(n, edges))


def star_cover_circuit(n, edges):
    """L154 construction: OR over cover vertices v of x_v AND (OR of v's still-uncovered
    neighbours).  Returns (gate count, truth table), evaluated independently of the formula."""
    full = (1 << (1 << n)) - 1
    xs = [sum(1 << r for r in range(1 << n) if r >> i & 1) for i in range(n)]
    left, gates, terms = set(map(frozenset, edges)), 0, []
    for v in min_cover(n, edges):
        nb = [u for e in left if v in e for u in e if u != v]
        if not nb:
            continue
        acc = xs[nb[0]]
        for u in nb[1:]:
            acc |= xs[u]
            gates += 1
        terms.append(acc & xs[v])
        gates += 1
        left = {e for e in left if v not in e}
    out = terms[0]
    for t in terms[1:]:
        out |= t
        gates += 1
    return gates, out & full


def dist(n, adj, s):
    d = [None] * n
    d[s] = 0
    q = deque([s])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if d[v] is None:
                d[v] = d[u] + 1
                q.append(v)
    return d


def girth(n, adj):
    best = 10 ** 9
    for s in range(n):
        d, par = [None] * n, [None] * n
        d[s] = 0
        q = deque([s])
        while q:
            u = q.popleft()
            for v in adj[u]:
                if d[v] is None:
                    d[v], par[v] = d[u] + 1, u
                    q.append(v)
                elif par[u] != v:
                    best = min(best, d[u] + d[v] + 1)
    return best


def predict(n, edges):
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    E, t, g = len(edges), tau(n, edges), girth(n, adj)
    used = [v for v in range(n) if adj[v]]
    hubs = [v for v in range(n) if len(adj[v]) >= 3]
    far = all((dist(n, adj, u)[v] or 10 ** 9) >= 7 for u, v in combinations(hubs, 2))
    cover = E + t - 1
    lb, why = None, []
    if g >= 10 ** 9:
        lb = cover
        why.append('L104 forest')
    elif g >= 7 and far:
        lb = cover
        why.append('L204')
    degs = sorted(len(adj[v]) for v in used)
    m = len(used)
    connected = all(x is not None for x in (dist(n, adj, used[0])[v] for v in used))
    if connected and degs == [1, 1] + [2] * (m - 2):
        exact = m + m // 2 - 2
        lb = exact
        why.append(f'L102 path={exact}')
    if connected and degs == [2] * m and m >= 5:
        exact = m + (m + 1) // 2 - 1
        lb = exact
        why.append(f'L106 cycle={exact}')
    if m == 4 and E == 4 and degs == [2] * 4:
        lb = 3
        why.append('L112 C4=3')
    return dict(E=E, tau=t, girth=g if g < 10 ** 9 else 'inf', hubs_far=far, upper=cover,
                lower=lb, why=why, support=m)


def main():
    iv = intervals()
    seen = set()
    for path in ('results/synthesis_cases.json', 'results/synthesis_signed_cases.json'):
        for c in json.load(open(os.path.join(HERE, path), encoding='utf-8')):
            n, truth, name = int(c['n']), int(c['truth']), c['name']
            if name in seen or int(c['known']) != (1 << (1 << n)) - 1:
                continue
            seen.add(name)
            edges = graph_of(n, truth)
            if edges is None:
                continue
            p = predict(n, edges)
            g, tt = star_cover_circuit(n, edges)
            assert tt == truth and g == p['upper'], (name, g, p['upper'])
            mono, neg = iv.get((name, 'mono')), iv.get((name, 'not'))
            flags = []
            for basis, I in (('mono', mono), ('not', neg)):
                if I is None:
                    continue
                lo, hi = I
                if hi < 10 ** 9 and p['lower'] is not None and hi < p['lower']:
                    flags.append(f'CONFLICT {basis} upper {hi} < theorem lower {p["lower"]}')
                if basis == 'mono' and hi < 10 ** 9 and hi > p['upper']:
                    flags.append(f'L154 improves {basis} upper {hi}->{p["upper"]}')
                if p['lower'] is not None and lo < p['lower']:
                    flags.append(f'theorem improves {basis} lower {lo}->{p["lower"]}')
            print(f"{name:14s} n={n} E={p['E']:2d} tau={p['tau']} girth={p['girth']} "
                  f"cover={p['upper']:2d} thm_lb={p['lower']} {p['why']} mono={mono} not={neg} {flags}")


if __name__ == '__main__':
    main()
