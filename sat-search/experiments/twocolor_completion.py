"""Read-once formula completion for the Pitt–Valiant single-zero label pattern."""

from functools import lru_cache

from subtree_formulas import _row_signatures
from pysat.solvers import Solver


@lru_cache(maxsize=1024)
def two_coloring(width, zero_sets):
    """Return the two nonempty color classes, or None if a zero set cannot be split."""
    if not zero_sets:
        return (0,), tuple(range(1, width))
    variables = list(range(1, width + 1))
    clauses = []
    for zero in zero_sets:
        edge = [v for v in variables if zero >> (v - 1) & 1]
        if len(edge) < 2:
            return None
        clauses.extend((edge, [-v for v in edge]))
    with Solver(name='g4', bootstrap_with=clauses) as solver:
        if not solver.solve():
            return None
        model = set(solver.get_model())
    return tuple(tuple(i for i, v in enumerate(variables) if (v in model) == color) for color in (False, True))


def complete(columns, positive, negative):
    """Return (status, formula) on the given labeled leaf occurrences.

    Inapplicable and fallback queries require ordinary exact formula completion.
    """
    width = len(columns)
    if width < 2 or positive.bit_count() < width:
        return 'inapplicable', None
    full = (1 << width) - 1
    positives = _row_signatures(columns, positive)
    if any(full ^ (1 << i) not in positives for i in range(width)):
        return 'inapplicable', None
    zeros = tuple(sorted(full ^ row for row in _row_signatures(columns, negative)))
    colors = two_coloring(width, zeros)
    if colors is None:
        return 'unsat', None
    left_mask, right_mask = (sum(1 << i for i in part) for part in colors)
    if any(row & left_mask != left_mask and row & right_mask != right_mask for row in positives):
        return 'fallback', None

    def conjunction(leaves):
        if len(leaves) == 1:
            return leaves[0]
        middle = len(leaves) // 2
        return 0, conjunction(leaves[:middle]), conjunction(leaves[middle:])

    left, right = map(conjunction, colors)
    return 'sat', (1, left, right)
