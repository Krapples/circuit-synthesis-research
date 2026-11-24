"""Exact relaxed monotone interfaces with provider-specific ancestor sets."""

from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import cube_search as cs
from monotone_interface import biclique_conflicts, graph_neighbors
from pysat.formula import IDPool
from pysat.solvers import Solver


def biclique_cover_number(n, masks, side):
    """Exact Boolean rank of the crossing adjacency matrix for small cuts."""
    count, conflicts = biclique_conflicts(graph_neighbors(n, masks), side)
    return cs.chromatic(range(count), conflicts)


def _upward(terms, row):
    return any(row & term == term for term in terms)


@dataclass(frozen=True)
class InterfaceSolution:
    hidden: int
    shift: int
    provider_terms: tuple
    decoder_terms: tuple

    def signature(self, row):
        signal_bits = sum(1 << i for i, terms in enumerate(self.provider_terms) if _upward(terms, row))
        # Ignore bits outside the labeled domain so they cannot alias ports.
        return ((row & ((1 << self.shift) - 1)) & ~self.hidden) | (signal_bits << self.shift)

    def evaluate(self, row):
        return _upward(self.decoder_terms, self.signature(row))


def synthesize_interface(hidden, ancestors, positives, negatives, *, solver='g4'):
    """Return arbitrary monotone providers and decoder, or None if the lists conflict."""
    ancestors = tuple(ancestors)
    positives, negatives = tuple(sorted(set(positives))), tuple(sorted(set(negatives)))
    masks = (hidden, *ancestors, *positives, *negatives)
    if min(masks) < 0:
        raise ValueError('expected nonnegative input masks')
    pool = IDPool()
    provider_pairs = [{} for _ in ancestors]
    clauses = []
    for a in positives:
        for b in negatives:
            difference = a & ~b
            if difference & ~hidden:
                continue  # the decoder can already distinguish this pair on raw outside inputs
            eligible = []
            for i, mask in enumerate(ancestors):
                if difference & mask:
                    pair = a & mask, b & mask
                    var = pool.id((i, pair))
                    provider_pairs[i][pair] = var
                    eligible.append(var)
            if not eligible:
                return None
            clauses.append(eligible)

    for pairs in provider_pairs:
        for ((a, b), left), ((c, d), right) in combinations(pairs.items(), 2):
            if not a & ~d or not c & ~b:
                clauses.append([-left, -right])

    with Solver(name=solver, bootstrap_with=clauses) as sat:
        if not sat.solve():
            return None
        model = set(sat.get_model())
    terms = tuple(cs._anti(a for (a, _), var in pairs.items() if var in model) for pairs in provider_pairs)
    solution = InterfaceSolution(hidden, max(masks).bit_length(), terms, ())
    decoder = cs._anti(solution.signature(row) for row in positives)
    return InterfaceSolution(hidden, solution.shift, terms, decoder)
