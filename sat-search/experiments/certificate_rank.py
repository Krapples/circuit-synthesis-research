"""Sharing lower bounds from complete monotone certificate intersections."""

from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from port_certificates import modular_rank


def intersection_matrix(minterms, zero_certificates):
    return tuple(tuple((a & b).bit_count() - 1 for b in zero_certificates) for a in minterms)


def one_share_support(matrix):
    """Check that the ones form at most two disjoint complete bipartite components."""
    if any(value not in (0, 1) for row in matrix for value in row):
        return False
    neighborhoods = {tuple(i for i, value in enumerate(row) if value) for row in matrix} - {()}
    return len(neighborhoods) <= 2 and sum(map(len, neighborhoods)) == len(set().union(*map(set, neighborhoods)))


def coexistence_color_bound(minterms, zero_certificates):
    """Lower-bound the colors needed when both kinds of certificate pair must be separate."""
    def pairs(terms):
        return {pair for term in terms for pair in combinations(
            (i for i in range(term.bit_length()) if term >> i & 1), 2)}

    edges = pairs(minterms) & pairs(zero_certificates)
    if not edges:
        return 1
    neighbors = {}
    for a, b in edges:
        neighbors.setdefault(a, set()).add(b)
        neighbors.setdefault(b, set()).add(a)
    lower = 2
    for adjacent in neighbors.values():
        clique_size = 1
        following = adjacent
        while following:
            chosen = max(following, key=lambda vertex: (len(following & neighbors[vertex]), vertex))
            following = following & neighbors[chosen]
            clique_size += 1
        lower = max(lower, clique_size)
    if lower >= 3:
        return lower

    colors = {}
    for vertex in neighbors:
        if vertex in colors:
            continue
        colors[vertex] = False
        queue = [vertex]
        for a in queue:
            for b in neighbors[a]:
                if b not in colors:
                    colors[b] = not colors[a]
                    queue.append(b)
                elif colors[a] == colors[b]:
                    return 3
    return 2


@dataclass(frozen=True)
class CertificateBound:
    rank: int
    max_entry: int
    excess: int
    gates: int


def analyze(minterms, zero_certificates):
    minterms, zero_certificates = tuple(minterms), tuple(zero_certificates)
    if not minterms or not zero_certificates or 0 in minterms or 0 in zero_certificates:
        raise ValueError('expected certificates of a nonconstant complete monotone function')
    matrix = intersection_matrix(minterms, zero_certificates)
    if any(value < 0 for row in matrix for value in row):
        raise ValueError('each minterm must meet each zero certificate')
    max_entry = max(map(max, matrix))
    rank = max(modular_rank(matrix, prime) for prime in (2, 101))
    excess = max(max_entry, (rank + 3) // 3 if rank else 0)
    if excess == 1 and not one_share_support(matrix):
        excess = 2
    support = 0
    for term in minterms:
        support |= term
    return CertificateBound(rank, max_entry, excess, support.bit_count() - 1 + excess)
