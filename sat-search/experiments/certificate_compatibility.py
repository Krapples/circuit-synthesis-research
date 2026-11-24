"""Read-once certificate compatibility and witnessed graph obstructions."""

from dataclasses import dataclass
from functools import reduce
from itertools import combinations
from operator import or_


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


@dataclass(frozen=True)
class Obstruction:
    leaves: int
    # Every edge stores its certificate row and the two leaf indices.
    trees: tuple[tuple[tuple[int, int, int], ...], ...]


def _join(op, children):
    result, *rest = children
    for child in rest:
        result = op, result, child
    return result


def compatible_tree(leaves, positive, negative):
    """Return a compatible binary tree or two witnessed spanning trees on a bad subset."""
    if leaves <= 0:
        raise ValueError('expected at least one leaf')
    graphs = []
    for family in (positive, negative):
        adjacency = {i: {} for i in indices(leaves)}
        for row, cert in enumerate(family):
            if cert & ~leaves:
                raise ValueError('certificate uses an unavailable leaf')
            for a, b in combinations(indices(cert), 2):
                if graphs and b in graphs[0][a]:
                    return None, Obstruction((1 << a) | (1 << b), (((graphs[0][a][b], a, b),), ((row, a, b),)))
                if b not in adjacency[a]:
                    adjacency[a][b] = adjacency[b][a] = row
        graphs.append(adjacency)

    def components(subset, adjacency):
        pending = set(indices(subset))
        parts, spanning = [], []
        while pending:
            head = min(pending)
            pending.remove(head)
            queue = [head]
            for a in queue:
                for b, row in adjacency[a].items():
                    if b in pending:
                        pending.remove(b)
                        queue.append(b)
                        spanning.append((row, a, b))
            parts.append(sum(1 << i for i in queue))
        return parts, tuple(spanning)

    def split(subset):
        if subset.bit_count() == 1:
            return subset.bit_length() - 1, None
        trees = []
        for op, prohibited in ((1, graphs[0]), (0, graphs[1])):
            parts, spanning = components(subset, prohibited)
            if len(parts) > 1:
                children = []
                for part in parts:
                    child, obstruction = split(part)
                    if obstruction is not None:
                        return None, obstruction
                    children.append(child)
                return _join(op, children), None
            trees.append(spanning)
        return None, Obstruction(subset, tuple(trees))

    return split(leaves)


def tree_leaves(tree):
    if isinstance(tree, int):
        return 1 << tree
    return tree_leaves(tree[1]) | tree_leaves(tree[2])


def restrict_certificates(tree, positive, negative):
    """Build a formula for nonempty pairwise-cross-intersecting local obligations."""
    def visit(node, ones, zeros):
        if not (ones and zeros):
            union = reduce(or_, ones or zeros, 0)
            if not union:
                leaves = tree_leaves(node)
                union = leaves & -leaves
            return _join(int(bool(ones)), indices(union))
        if isinstance(node, int):
            return node
        op, left, right = node
        confined = ones if op else zeros
        passing = zeros if op else ones
        children = []
        for child in (left, right):
            mask = tree_leaves(child)
            local = tuple(cert for cert in confined if cert & mask)
            if local:
                other = tuple(cert & mask for cert in passing)
                children.append(visit(child, local, other) if op else visit(child, other, local))
        return _join(op, children)

    return visit(tree, tuple(mask for mask in positive if mask), tuple(mask for mask in negative if mask))


def obstruction_clause(obstruction, membership):
    """Independently check the two spanning-tree witnesses and build the blocking clause."""
    leaves = set(indices(obstruction.leaves))
    if len(leaves) < 2 or len(obstruction.trees) != 2 or len(membership) != 2:
        raise ValueError('expected two trees on a nonsingleton subset')
    clause = set()
    for witnesses, axis in zip(obstruction.trees, membership):
        if len(witnesses) != len(leaves) - 1:
            raise ValueError('incorrect spanning-tree edge count')
        parent = {leaf: leaf for leaf in leaves}

        def root(leaf):
            while parent[leaf] != leaf:
                leaf = parent[leaf]
            return leaf

        for row, a, b in witnesses:
            if a not in leaves or b not in leaves or not 0 <= row < len(axis) or root(a) == root(b):
                raise ValueError('invalid spanning-tree edge')
            first, second = axis[row][a], axis[row][b]
            if first is None or second is None:
                raise ValueError('edge membership cannot hold in this region')
            parent[root(a)] = root(b)
            clause.update((-first, -second))
    return tuple(sorted(clause))
