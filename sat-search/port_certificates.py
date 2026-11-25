"""Incoming-port lower bounds from complete monotone certificates."""

from functools import lru_cache
from itertools import combinations


PORT_CERTIFICATE_LEVELS = ('rank', 'clique', 'exact')


@lru_cache(maxsize=128)
def incompatible_primary_pairs(minterms, zero_certificates):
    """Pairs that occur together on each certificate axis cannot share a region."""
    def pairs(family):
        return {a | b for term in family for a, b in combinations(
            (1 << i for i in range(term.bit_length()) if term >> i & 1), 2)}

    return tuple(sorted(pairs(minterms) & pairs(zero_certificates)))


@lru_cache(maxsize=128)
def minimal_zero_certificates(minterms):
    """Compute the minimal hitting sets of a complete minterm family."""
    hitting_sets = (0,)
    for term in minterms:
        bits = tuple(1 << i for i in range(term.bit_length()) if term >> i & 1)
        candidates = {new for hit in hitting_sets for new in
                      ((hit,) if hit & term else (hit | bit for bit in bits))}
        minimal = []
        for hit in sorted(candidates, key=lambda mask: (mask.bit_count(), mask)):
            if not any(hit & other == other for other in minimal):
                minimal.append(hit)
        hitting_sets = tuple(minimal)
    return tuple(sorted(hitting_sets))


@lru_cache(maxsize=2048)
def residual_matrix(minterms, zero_certificates, primary, *, output=False):
    """Return the residual on rows known to visit a region, or None if impossible."""
    positive, negative = [tuple(sorted({term & primary for term in family
                                        if output or term & primary}))
                          for family in (minterms, zero_certificates)]
    if not positive or not negative:
        return ()
    rows = tuple(tuple(1 - (a & b).bit_count() for b in negative) for a in positive)
    if any(value < 0 for row in rows for value in row):
        return None
    # Deleting all-zero or duplicate rows and columns preserves the partition
    # number: extend a partition by copying each representative's memberships.
    rows = tuple(dict.fromkeys(row for row in rows if any(row)))
    columns = tuple(dict.fromkeys(col for col in zip(*rows) if any(col)))
    return tuple(zip(*columns))


def modular_rank(matrix, prime):
    """Compute rank over the prime field, a lower bound on rational rank."""
    basis = {}
    for row in matrix:
        candidate = [value % prime for value in row]
        for i, value in enumerate(candidate):
            if not value:
                continue
            if i not in basis:
                inverse = pow(value, -1, prime)
                basis[i] = [entry * inverse % prime for entry in candidate[i:]]
                break
            for j, entry in enumerate(basis[i], i):
                candidate[j] = (candidate[j] - value * entry) % prime
    return len(basis)


@lru_cache(maxsize=4096)
def affine_rank(masks):
    """A certified affine incidence rank, using two finite fields."""
    if len(masks) < 2:
        return 0
    columns = sorted({i for mask in masks for i in range(mask.bit_length()) if mask >> i & 1})
    matrix = tuple((1, *(mask >> i & 1 for i in columns)) for mask in masks)
    return max(modular_rank(matrix, prime) for prime in (2, 101)) - 1


def certificate_type_costs(positives, zeros, primary, *, output=False, visits=None):
    """Lower bounds on regional AND and OR gates from known visits."""
    families = []
    for axis, rows in enumerate((zeros, positives)):
        known = () if visits is None else visits[1 - axis]
        projected = {row & primary for row in rows if output or row & primary or row in known}
        families.append(affine_rank(tuple(sorted(projected))))
    return tuple(families)


def rectangle_clique(matrix, *, max_cells=96):
    """Greedily find a clique of ones that cannot share an all-one rectangle."""
    cells = [(i, j) for i, row in enumerate(matrix) for j, value in enumerate(row) if value]
    if len(cells) > max_cells:
        # Sample across the whole matrix so every early row cannot fill the cap.
        cells = [cells[i * len(cells) // max_cells] for i in range(max_cells)]
    conflicts = [0] * len(cells)
    for (a, (i, j)), (b, (r, c)) in combinations(enumerate(cells), 2):
        if not matrix[i][c] or not matrix[r][j]:
            conflicts[a] |= 1 << b
            conflicts[b] |= 1 << a
    order = sorted(range(len(cells)), key=lambda i: (-conflicts[i].bit_count(), i))
    best = 0
    for start in order:
        clique = 1
        candidates = conflicts[start]
        for i in order:
            if clique + candidates.bit_count() <= best:
                break
            if candidates >> i & 1:
                clique += 1
                candidates &= conflicts[i]
        best = max(best, clique)
    return best


def rectangle_partition(matrix, lower=0, *, max_states=20_000):
    """Solve a small edge-disjoint rectangle cover, returning None past the cap."""
    if not matrix:
        return 0
    height, width = len(matrix), len(matrix[0])
    ones = sum(map(sum, matrix))
    if not ones:
        return 0
    upper = min(sum(map(any, matrix)), sum(map(any, zip(*matrix))))
    if upper == lower:
        return upper
    if max(height, width) > 8 or ones > 32:
        return None

    rows = [sum(1 << j for j, value in enumerate(row) if value) for row in matrix]
    full = sum(row << (i * width) for i, row in enumerate(rows))
    containing = [[] for _ in range(height * width)]
    for subset in range(1, 1 << height):
        indices = [i for i in range(height) if subset >> i & 1]
        common = (1 << width) - 1
        for i in indices:
            common &= rows[i]
        columns = common
        while columns:
            rectangle = sum(columns << (i * width) for i in indices)
            remaining = rectangle
            while remaining:
                bit = remaining & -remaining
                containing[bit.bit_length() - 1].append(rectangle)
                remaining ^= bit
            columns = (columns - 1) & common
    for candidates in containing:
        candidates.sort(key=int.bit_count, reverse=True)

    states = 0

    class StateLimit(Exception):
        pass

    @lru_cache(maxsize=None)
    def feasible(remaining, budget):
        nonlocal states
        if not remaining:
            return True
        if budget == 0:
            return False
        states += 1
        if states > max_states:
            raise StateLimit
        cells = [i for i in range(remaining.bit_length()) if remaining >> i & 1]
        pivot = min(cells, key=lambda i: len(containing[i]))
        return any(feasible(remaining ^ rect, budget - 1)
                   for rect in containing[pivot] if rect & remaining == rect)

    try:
        for budget in range(max(1, lower), upper):
            if feasible(full, budget):
                return budget
        return upper
    except StateLimit:
        return None


@lru_cache(maxsize=2048)
def incoming_port_bound(minterms, zero_certificates, primary, level='rank', *, output=False):
    """Return a lower bound on port occurrences, or None for incompatible primaries."""
    if level not in PORT_CERTIFICATE_LEVELS:
        raise ValueError(f'unknown port-certificate level {level!r}')
    matrix = residual_matrix(minterms, zero_certificates, primary, output=output)
    if matrix is None:
        return None
    if not matrix:
        return 0
    rank = max(modular_rank(matrix, prime) for prime in (101, 2))
    upper = min(len(matrix), len(matrix[0]))
    if level == 'rank' or rank == upper:
        return rank
    bound = max(rank, rectangle_clique(matrix))
    if level == 'exact':
        partition = rectangle_partition(matrix, bound)
        if partition is not None:
            bound = partition
    return bound
