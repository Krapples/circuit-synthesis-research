"""A SAT encoding of read-once AND/OR formulas by their cographs."""

from itertools import combinations, permutations


_PATHS_ON_FOUR = tuple(frozenset(tuple(sorted((left, right))) for left, right in zip(order, order[1:]))
                       for order in permutations(range(4)) if order[0] < order[-1])
_PAIRS_ON_FOUR = tuple(combinations(range(4), 2))


class CographFormula:
    """One formula on fixed leaf positions, possibly with symbolic row values."""

    def __init__(self, width, pool, key, clauses, *, eager=True):
        self.leaves = tuple(range(width))
        self.pool = pool
        self.key = key
        self.clauses = clauses
        self.edges = {(a, b): pool.id((key, 'edge', a, b)) for a, b in combinations(self.leaves, 2)}
        if eager:
            for four in combinations(self.leaves, 4):
                edges = [self.edges[four[a], four[b]] for a, b in _PAIRS_ON_FOUR]
                for path in _PATHS_ON_FOUR:
                    clauses.append([-edge if pair in path else edge for pair, edge in zip(_PAIRS_ON_FOUR, edges)])

    def induced_path_clauses(self, model):
        """Separate every induced P4 in this assignment of the edge variables."""
        for four in combinations(self.leaves, 4):
            edges = [self.edges[four[a], four[b]] for a, b in _PAIRS_ON_FOUR]
            present = frozenset(pair for pair, edge in zip(_PAIRS_ON_FOUR, edges) if edge in model)
            if present in _PATHS_ON_FOUR:
                yield [-edge if edge in model else edge for edge in edges]

    def edge(self, a, b):
        return self.edges[min(a, b), max(a, b)]

    def require(self, row, values, high, *, guard=None, active=None):
        """Require the indicated output on Boolean constants or SAT literals.

        A guard activates the row constraint only if it is true. An optional
        active literal per leaf selects the induced subgraph used by the formula.
        """
        if active is None:
            active = (True,) * len(self.leaves)
        allowed = tuple(value if high else (not value if isinstance(value, bool) else -value) for value in values)
        picks = {i: self.pool.id((self.key, 'pick', row, high, i)) for i in self.leaves
                 if allowed[i] is not False and active[i] is not False}
        for i, pick in picks.items():
            if allowed[i] is not True:
                self.clauses.append([-pick, allowed[i]])
            if active[i] is not True:
                self.clauses.append([-pick, active[i]])
        for a, b in combinations(picks, 2):
            edge = self.edge(a, b)
            self.clauses.append([-picks[a], -picks[b], edge if high else -edge])
        for j, can_choose in enumerate(allowed):
            if can_choose is True or active[j] is False:
                continue
            blockers = [] if guard is None else [-guard]
            if active[j] is not True:
                blockers.append(-active[j])
            if can_choose is not False:
                blockers.append(can_choose)
            for i, pick in picks.items():
                if i != j:
                    edge = self.edge(i, j)
                    block = self.pool.id((self.key, 'block', row, high, i, j))
                    self.clauses.extend(([-block, pick], [-block, -edge if high else edge]))
                    blockers.append(block)
            self.clauses.append(blockers)

    def decode(self, model, leaves=None):
        leaves = self.leaves if leaves is None else tuple(leaves)
        indices = {leaf: i for i, leaf in enumerate(leaves)}
        neighbors = {leaf: set() for leaf in self.leaves}
        for (a, b), edge in self.edges.items():
            if edge in model:
                neighbors[a].add(b)
                neighbors[b].add(a)

        def components(group, complement):
            unseen = set(group)
            groups = []
            while unseen:
                first = min(unseen)
                unseen.remove(first)
                component = [first]
                for a in component:
                    adjacent = unseen - neighbors[a] if complement else unseen & neighbors[a]
                    component.extend(sorted(adjacent))
                    unseen.difference_update(adjacent)
                groups.append(component)
            return groups

        def tree(group):
            if len(group) == 1:
                return indices[group[0]]
            parts = components(group, False)
            op = 1  # disjoint union is OR
            if len(parts) == 1:
                parts = components(group, True)
                op = 0  # complete join is AND
            if len(parts) == 1:
                raise RuntimeError('model contains an induced P4')
            first, *rest = (tree(part) for part in parts)
            for following in rest:
                first = op, first, following
            return first

        return tree(leaves)
