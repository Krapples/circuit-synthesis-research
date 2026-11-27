"""Cross-check first_gate_lb.LB against exhaustive AIG search (2026-11-26).

For every recursion state reached from f16102 with at most MAXN inputs, and for random
functions on 3 and 4 inputs, check that no AIG with LB-1 gates exists (LB <= exact).
Usage: python first_gate_lb_crosscheck.py <maxn> <samples> <seed> [shard nshards]
"""
import random
import sys

import first_gate_lb as F
from aig_exact_small import has_aig


def main():
    maxn, samples, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    shard, nshards = (int(sys.argv[4]), int(sys.argv[5])) if len(sys.argv) > 5 else (0, 1)
    seen = {}

    orig = F.LB.__wrapped__

    def rec(n, tt, cascade=2):
        key = (n, tt)
        if key not in seen:
            seen[key] = orig(n, tt, cascade)
        return seen[key]

    F.LB = rec
    rec(*F.canon(6, F.table_16102()))
    jobs = [(n, tt, lb) for (n, tt), lb in sorted(seen.items()) if n <= maxn and lb >= 1]
    rng = random.Random(seed)
    for _ in range(samples):
        n = rng.choice((3, 4))
        n2, tt = F.canon(n, rng.getrandbits(1 << n))
        lb = rec(n2, tt) if n2 >= 1 else 0
        if lb >= 1:
            jobs.append((n2, tt, lb))
    jobs = jobs[shard::nshards]
    bad = 0
    for k, (n, tt, lb) in enumerate(jobs):
        ok = not has_aig(n, tt, lb - 1)
        if not ok:
            bad += 1
            print(f"UNSOUND n={n} tt={tt:x} LB={lb}", flush=True)
        if k % 100 == 0:
            print(f"progress {k}/{len(jobs)}", flush=True)
    print(f"shard {shard}/{nshards}: checked {len(jobs)} cases, unsound {bad}", flush=True)


if __name__ == "__main__":
    main()
