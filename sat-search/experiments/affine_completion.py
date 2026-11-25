"""Affine completion of fixed, exact read-once terminal certificates."""

from fractions import Fraction
from functools import lru_cache

from certificate_compatibility import _join, indices, tree_leaves


def binary_basis(vectors):
    """Canonical RREF with the highest bit as pivot."""
    rows = {}
    for value in vectors:
        for pivot in sorted(rows, reverse=True):
            if value >> pivot & 1:
                value ^= rows[pivot]
        if value:
            pivot = value.bit_length() - 1
            for old, row in rows.items():
                if row >> pivot & 1:
                    rows[old] = row ^ value
            rows[pivot] = value
    return tuple(rows[pivot] for pivot in sorted(rows, reverse=True))


def direction(terms):
    anchor, *rest = terms
    return binary_basis(term ^ anchor for term in rest)


def kernel(rows, leaves):
    basis = binary_basis(rows)
    pivots = {row.bit_length() - 1 for row in basis}
    return binary_basis((1 << i) | sum(1 << (row.bit_length() - 1) for row in basis if row >> i & 1)
                        for i in indices(leaves) if i not in pivots)


def restrict_space(rows, support):
    """Intersect with the coordinate subspace supported on support."""
    outside = {}
    local = []
    for original in rows:
        row = original
        while row & ~support:
            pivot = (row & ~support).bit_length() - 1
            if pivot not in outside:
                outside[pivot] = row
                break
            row ^= outside[pivot]
        else:
            local.append(row)
    return binary_basis(local)


def coordinate_components(basis, support):
    groups = [1 << i for i in indices(support)]
    for row in basis:
        active = [group for group in groups if group & row]
        if len(active) > 1:
            groups = [group for group in groups if not group & row] + [sum(active)]
    return groups


def recover(positive, negative, leaves):
    if len(positive) + len(negative) != leaves.bit_count() - 1:
        return None
    if leaves.bit_count() == 1:
        return leaves.bit_length() - 1
    p = coordinate_components(positive, leaves)
    n = coordinate_components(negative, leaves)
    if (len(p) > 1) == (len(n) > 1):
        return None
    op, blocks = (0, p) if len(p) > 1 else (1, n)
    children = [recover(restrict_space(positive, block), restrict_space(negative, block), block) for block in blocks]
    return None if any(child is None for child in children) else _join(op, children)


def is_exact_certificate(tree, mask, high):
    if isinstance(tree, int):
        return mask == 1 << tree
    op, left, right = tree
    left_leaves, right_leaves = tree_leaves(left), tree_leaves(right)
    if bool(op) != high:
        return (is_exact_certificate(left, mask & left_leaves, high)
                and is_exact_certificate(right, mask & right_leaves, high))
    return ((mask & left_leaves == mask and is_exact_certificate(left, mask, high))
            or (mask & right_leaves == mask and is_exact_certificate(right, mask, high)))


@lru_cache(maxsize=6)
def quotient_subspaces(dimension):
    seen = {()}
    frontier = [()]
    for basis in frontier:
        for vector in range(1, 1 << dimension):
            extended = binary_basis((*basis, vector))
            if extended not in seen:
                seen.add(extended)
                frontier.append(extended)
    return tuple(frontier)


def complete_affine(leaves, positives, negatives, *, max_deficit=3):
    """Return (tree, deficit, status) for exact prescribed certificates."""
    positives, negatives = tuple(positives), tuple(negatives)
    if not leaves or not positives or not negatives or any(not x or x & ~leaves for x in (*positives, *negatives)):
        return None, None, 'inapplicable'
    if any((a & b).bit_count() != 1 for a in positives for b in negatives):
        return None, None, 'intersection'
    if not 0 <= max_deficit <= 5:
        raise ValueError('max_deficit must be between zero and five')
    u0, v0 = direction(positives), direction(negatives)
    deficit = leaves.bit_count() - 1 - len(u0) - len(v0)
    if deficit > max_deficit:
        return None, deficit, 'limit'
    if deficit < 0:
        raise AssertionError('cross intersection implies nonnegative deficit')
    extended, quotient = u0, []
    for row in kernel(negatives, leaves):
        bigger = binary_basis((*extended, row))
        if len(bigger) > len(extended):
            extended = bigger
            quotient.append(row)
    if len(quotient) != deficit:
        raise AssertionError('wrong quotient dimension')
    for subspace in quotient_subspaces(deficit):
        lifts = []
        for coefficient in subspace:
            value = 0
            for i in indices(coefficient):
                value ^= quotient[i]
            lifts.append(value)
        u = binary_basis((*u0, *lifts))
        v = kernel((*u, positives[0]), leaves)
        candidate = recover(u, v, leaves)
        if candidate is not None and all(is_exact_certificate(candidate, term, high)
                                         for high, family in ((True, positives), (False, negatives))
                                         for term in family):
            return candidate, deficit, 'completed'
    return None, deficit, 'excluded'


def rational_affine_basis(terms):
    """Select original rows spanning the same rational affine hull."""
    terms = tuple(terms)
    columns = sorted({i for term in terms for i in indices(term)})
    chosen, pivots = [], {}
    for term in terms:
        row = [Fraction(1), *(Fraction(term >> i & 1) for i in columns)]
        for i in range(len(row)):
            if not row[i]:
                continue
            if i not in pivots:
                pivots[i] = [value / row[i] for value in row[i:]]
                chosen.append(term)
                break
            scale = row[i]
            for j, value in enumerate(pivots[i], i):
                row[j] -= scale * value
    return tuple(chosen)
