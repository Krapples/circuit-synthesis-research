"""Structural interface widths for independent sets of graph functions."""

from functools import lru_cache
from itertools import combinations


def graph_neighbors(n, masks):
    neighbors = [0] * n
    for edge in masks:
        a, b = (i for i in range(n) if edge >> i & 1)
        neighbors[a] |= 1 << b
        neighbors[b] |= 1 << a
    return tuple(neighbors)


def crossing_edges(neighbors, side):
    return [(a, b) for a, row in enumerate(neighbors) if side >> a & 1
            for b in range(len(neighbors)) if (row & ~side) >> b & 1]


def crossing_matching(neighbors, side):
    """Maximum matching cardinality on the crossing graph, by augmenting paths."""
    owner = {}

    def augment(a, seen):
        targets = neighbors[a] & ~side
        while targets:
            b = targets & -targets
            targets ^= b
            if b not in seen:
                seen.add(b)
                if b not in owner or augment(owner[b], seen):
                    owner[b] = a
                    return True
        return False

    return sum(augment(a, set()) for a in range(len(neighbors)) if side >> a & 1)


@lru_cache(maxsize=64)
def matching_cuts(n, masks):
    """All proper independent cuts with at least two vertices and no crossing C4."""
    neighbors = graph_neighbors(n, masks)
    cuts = []

    def collect(side, available):
        while available:
            bit = available & -available
            available ^= bit
            u = bit.bit_length() - 1
            # Existing members and u are independent. A common neighbor of
            # two members must lie outside the side, even after adding vertices.
            if any((neighbors[v] & neighbors[u]).bit_count() >= 2 for v in range(u) if side >> v & 1):
                continue
            group = side | bit
            if side:
                width = crossing_matching(neighbors, group)
                if width:
                    cuts.append((group, width))
            collect(group, available & ~neighbors[u])

    collect(0, (1 << n) - 1)
    return tuple(sorted(cuts, key=lambda cut: (cut[0].bit_count() - cut[1], -cut[1], cut[0])))


def pinned_interface_excess(n, pinned, cuts):
    """Lower bound on excess fan-out from fixed gates with known structural support."""
    support = {i: 1 << i for i in range(n)}
    known = []
    for offset, (_, left, right) in sorted(pinned.items()):
        if left in support and right in support:
            a, b = support[left], support[right]
            support[n + offset] = a | b
            known.append((a, b))
    best, side = 0, 0
    for group, width in cuts:
        pure_gates = exits = 0
        for a, b in known:
            left_pure = not a & ~group
            right_pure = not b & ~group
            pure_gates += left_pure and right_pure
            exits += left_pure != right_pure
        charge = pure_gates + max(exits, width) - group.bit_count()
        if charge > best:
            best, side = charge, group
    return best, side


def biclique_conflicts(neighbors, side):
    """Two crossing edges conflict if they cannot be in the same biclique."""
    edges = crossing_edges(neighbors, side)
    pairs = [(i, j) for (i, (a, b)), (j, (c, d)) in combinations(enumerate(edges), 2)
             if not (neighbors[a] >> d & 1 and neighbors[c] >> b & 1)]
    return len(edges), pairs
