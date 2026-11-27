"""Random targets (uniform T) on the nl x nr one-left-one-right rows, all inputs essential."""
import os, random, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
from tree_dp import all_essential
N, seed, nl, nr = map(int, sys.argv[1:5]); random.seed(seed); n = nl + nr
rows = [(1 << u) | (1 << (nl + v)) for u in range(nl) for v in range(nr)]
FULL = (1 << len(rows)) - 1
w = [sum(((r >> i) & 1) << j for j, r in enumerate(rows)) for i in range(n)]
seen = set()
while len(seen) < N:
    T = random.randrange(1, FULL)
    if T in seen or not all_essential(n, T, w, FULL): continue
    seen.add(T)
    print(f"T-{T} {n} 0 1 {n+2} " + ",".join(f"{r:x}:{T>>j&1}" for j, r in enumerate(rows)))
