"""Boundary-demand cuts for read-once formulas on concrete leaf occurrences."""

from functools import lru_cache
from regional_search import MAX_KNOWN_LEAVES, pareto
from regional_synthesis import _bits


def _row_signatures(columns, rows):
    signatures = {}
    for row in _bits(rows):
        signature = sum(1 << i for i, col in enumerate(columns) if col & row)
        signatures[signature] = signatures.get(signature, 0) | row
    return signatures


@lru_cache(maxsize=2048)
def forced_by_outside(columns, positive, negative):
    """Find terminal labels forced when outside leaf values cannot distinguish a pair."""
    ones = _row_signatures(columns, positive)
    zeros = _row_signatures(columns, negative)
    forced_positive = forced_negative = 0
    for a, a_rows in ones.items():
        for b, b_rows in zeros.items():
            if not a & ~b:
                forced_positive |= a_rows
                forced_negative |= b_rows
    return forced_positive, forced_negative


def _splits(group):
    low = group & -group
    left = (group - 1) & group
    while left:
        if left & low:
            yield left, group ^ left
        left = (left - 1) & group


class _SubtreeCuts:
    def __init__(self, columns, positive, negative):
        self.full = (1 << len(columns)) - 1
        ones = _row_signatures(columns, positive)
        zeros = _row_signatures(columns, negative)
        self.pairs = tuple((a & ~b, a_rows, b_rows) for a, a_rows in ones.items() for b, b_rows in zeros.items())
        self.grouped = {}
        for difference, a, b in self.pairs:
            p, n = self.grouped.get(difference, (0, 0))
            self.grouped[difference] = p | a, n | b
        self.labels = {self.full: (positive, negative)}
        self.possible = {}

    def requirements(self, group):
        if group not in self.labels:
            positive = negative = 0
            for difference, (a, b) in self.grouped.items():
                if not difference & ~group:
                    positive |= a
                    negative |= b
            self.labels[group] = positive, negative
        return self.labels[group]

    def tree_possible(self, group):
        if group not in self.possible:
            positive, negative = self.requirements(group)
            admissible = not any(a & positive and b & negative and not difference & group
                                 for difference, a, b in self.pairs)
            self.possible[group] = admissible and (group.bit_count() == 1 or any(
                self.tree_possible(left) and self.tree_possible(right) for left, right in _splits(group)))
        return self.possible[group]


@lru_cache(maxsize=256)
def _prepared_cuts(columns, positive, negative):
    return _SubtreeCuts(columns, positive, negative)


def subtree_possible(columns, positive, negative):
    cuts = _prepared_cuts(columns, positive, negative)
    return cuts.tree_possible(cuts.full)


@lru_cache(maxsize=1024)
def constrained_formulas(columns, positive, negative, global_negative):
    """Read-only frontier satisfying local labels and whether structure alone rejects it.

    Dominance still uses all global labels, including rows unforced at this terminal.
    """
    if not 1 <= len(columns) <= MAX_KNOWN_LEAVES:
        raise ValueError('unsupported formula width')
    cuts = _prepared_cuts(columns, positive, negative)
    if not cuts.tree_possible(cuts.full):
        return {}, True

    @lru_cache(maxsize=None)
    def formulas(group):
        if not cuts.tree_possible(group):
            return {}
        p, n = cuts.requirements(group)
        if group.bit_count() == 1:
            leaf = group.bit_length() - 1
            col = columns[leaf]
            return {col: leaf} if col & p == p and not col & n else {}
        tables = {}
        for left, right in _splits(group):
            left_tables, right_tables = formulas(left), formulas(right)
            for a, fa in left_tables.items():
                for b, fb in right_tables.items():
                    for op, table in ((0, a & b), (1, a | b)):
                        if table & p == p and not table & n:
                            tables.setdefault(table, (op, fa, fb))
        return pareto(tables, global_negative)

    return formulas(cuts.full), False
