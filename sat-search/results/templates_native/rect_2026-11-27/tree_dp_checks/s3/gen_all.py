"""All targets on the nl x nr one-left-one-right rows whose inputs are all essential."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
from tree_dp import all_essential
nl, nr = int(sys.argv[1]), int(sys.argv[2]); n = nl + nr
rows = [(1 << u) | (1 << (nl + v)) for u in range(nl) for v in range(nr)]
FULL = (1 << len(rows)) - 1
w = [sum(((r >> i) & 1) << j for j, r in enumerate(rows)) for i in range(n)]
for T in range(1, FULL):
    if all_essential(n, T, w, FULL):
        print(f"A-{T} {n} 0 1 14 " + ",".join(f"{r:x}:{T>>j&1}" for j, r in enumerate(rows)))
