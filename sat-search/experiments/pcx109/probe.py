"""L-pcx-109 probe: for small graphs, min decision-tree leaves L for the search problem
'find an edge with both ends false, or t vertices true' (t = cover number), and check the 4 claims."""
import itertools, sys
from functools import lru_cache
from math import comb

def cover_number(n, E):
    for k in range(n + 1):
        for T in itertools.combinations(range(n), k):
            s = set(T)
            if all(u in s or v in s for u, v in E):
                return k

def min_leaves(n, E, t):
    @lru_cache(None)
    def f(ones, zeros):             # bitmasks of vertices set true / false
        if bin(ones).count('1') >= t or any(zeros >> u & 1 and zeros >> v & 1 for u, v in E):
            return 1
        best = None
        for y in range(n):
            if not (ones | zeros) >> y & 1:
                c = f(ones, zeros | 1 << y) + f(ones | 1 << y, zeros)
                if best is None or c < best: best = c
        return best
    return f(0, 0)

def eq_low(n, E, t):                # the named equality family for the lower bound
    adj = {v: set() for v in range(n)}
    for u, v in E: adj[u].add(v); adj[v].add(u)
    for w in itertools.permutations(range(n), t):
        if all(len(adj[w[j]] - set(w[:j])) >= t - j for j in range(t)):
            return True
    return False

def eq_high(n, E):
    star = any(all(u == c or v == c for u, v in E) for c in range(n))
    deg = [0] * n
    for u, v in E: deg[u] += 1; deg[v] += 1
    return star or max(deg) <= 1

bad = []
for n in range(2, int(sys.argv[1]) + 1):
    pairs = list(itertools.combinations(range(n), 2))
    seen = set()
    for mask in range(1, 1 << len(pairs)):
        E = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
        # canonical form up to isomorphism (cheap: min over permutations for n<=6)
        key = min(tuple(sorted(tuple(sorted((p[u], p[v]))) for u, v in E)) for p in itertools.permutations(range(n)))
        if key in seen: continue
        seen.add(key)
        t = cover_number(n, E)
        L = min_leaves(n, E, t)
        c1 = (t + 1) * (t + 2) <= 2 * L
        c2 = (2 * L == (t + 1) * (t + 2)) == eq_low(n, E, t)
        c3 = L + 1 <= 2 ** (t + 1)
        c4 = (L + 1 == 2 ** (t + 1)) == eq_high(n, E)
        if not (c1 and c2 and c3 and c4):
            bad.append((n, E, t, L, c1, c2, c3, c4, eq_low(n, E, t), eq_high(n, E)))
    print(f'n={n}: {len(seen)} graphs checked, {len(bad)} failures so far', flush=True)
for b in bad[:15]:
    print(b)
