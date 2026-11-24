"""Soundness check for consistent_network.consistent_feasible: build random monotone circuits with the exact
regional structure (groups in order, inputs read once, each non-output terminal read twice by later
regions), and require SAT for their own function with both row sets. Also report how often a mismatched
function (from another random circuit on the same groups) is rejected, to show the test has teeth.
Usage: python consistent_network_test.py [trials]"""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from consistent_network import consistent_feasible, minmax_rows, all_rows


def random_circuit(n, groups, rng):
    k = len(groups)
    N = 1 << n
    xt = [sum(1 << r for r in range(N) if r >> v & 1) for v in range(n)]
    incoming = [[] for _ in range(k)]
    for i in range(k - 1):
        a, b = sorted(rng.randint(i + 1, k - 1) for _ in range(2))
        incoming[a].append(i)
        incoming[b].append(i)
    h = []
    for j in range(k):
        leaves = [xt[v] for v in range(n) if groups[j] >> v & 1] + [h[i] for i in incoming[j]]
        while len(leaves) > 1:
            x = leaves.pop(rng.randrange(len(leaves)))
            y = leaves.pop(rng.randrange(len(leaves)))
            leaves.append(x & y if rng.random() < 0.5 else x | y)
        h.append(leaves[0])
    return h[-1], [len(incoming[j]) for j in range(k)]


def random_groups(n, k, rng):
    perm = list(range(n))
    rng.shuffle(perm)
    cuts = sorted(rng.sample(range(1, n), k - 1))
    parts = [perm[a:b] for a, b in zip([0] + cuts, cuts + [n])]
    return [sum(1 << v for v in p) for p in parts]


if __name__ == '__main__':
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    rng = random.Random(1)
    bad = rejected = tested = 0
    for t in range(trials):
        n = rng.randint(4, 7)
        k = rng.randint(2, min(n, 5))
        groups = random_groups(n, k, rng)
        tab, needs = random_circuit(n, groups, rng)
        f = lambda r, tab=tab: tab >> r & 1
        full = (1 << n) - 1
        for R in (all_rows(full), minmax_rows(n, f, full)):
            if not consistent_feasible(groups, needs, R, f):
                bad += 1
                print('UNSOUND: groups', [bin(g) for g in groups], 'needs', needs, 'rows', len(R), flush=True)
        tab2, _ = random_circuit(n, groups, rng)          # a different circuit on the same groups
        if tab2 != tab:
            f2 = lambda r, tab=tab2: tab >> r & 1
            # require at least the original circuit's wire counts so the two are comparable
            tested += 1
            rejected += not consistent_feasible(groups, needs, all_rows(full), f2)
    print(f'{trials} random circuits: {bad} unsound rejections; mismatched functions rejected {rejected}/{tested}')
