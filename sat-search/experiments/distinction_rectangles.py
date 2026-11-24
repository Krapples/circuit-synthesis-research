"""Formula synthesis from rectangles on the positive-negative pair grid."""

from functools import lru_cache, reduce
from itertools import product
from operator import or_

from regional_synthesis import _bits
from subtree_formulas import _splits


def _components(scopes):
    components = []
    for scope in scopes:
        disjoint = []
        for part in components:
            if part & scope:
                scope |= part
            else:
                disjoint.append(part)
        components = [*disjoint, scope]
    return components


def _separate(rectangles):
    for axis, op in ((0, 1), (1, 0)):
        components = _components(rect[axis] for rect in rectangles)
        if len(components) > 1:
            return op, tuple(tuple(rect for rect in rectangles if rect[axis] & part) for part in components)
    return None


def _join(op, children):
    tree, *rest = children
    for child in rest:
        tree = op, tree, child
    return tree


def slicing_tree(rectangles):
    """Return (tree, None) or (None, an indivisible tiling of a subgrid)."""
    if len(rectangles) == 1:
        return rectangles[0][2], None
    separation = _separate(rectangles)
    if separation is None:
        return None, rectangles
    op, parts = separation
    children = []
    for part in parts:
        child, obstruction = slicing_tree(part)
        if obstruction is not None:
            return None, obstruction
        children.append(child)
    return _join(op, children), None


def minimum_formula(rectangles):
    """Return (leaf count, formula) for a disjoint tiling, allowing repeated owners."""
    if len(rectangles) == 1:
        return 1, rectangles[0][2]
    separation = _separate(rectangles)
    if separation is not None:
        op, parts = separation
        results = [minimum_formula(part) for part in parts]
        return sum(cost for cost, _ in results), _join(op, [tree for _, tree in results])

    rows = reduce(or_, (r for r, _, _ in rectangles))
    cols = reduce(or_, (c for _, c, _ in rectangles))
    return _minimum_protocol(rectangles, rows, cols)


def _minimum_protocol(rectangles, rows, cols):
    @lru_cache(maxsize=None)
    def best(rows, cols):
        for r, c, leaf in rectangles:
            if rows & r == rows and cols & c == cols:
                return 1, leaf
        cost = rows.bit_count() * cols.bit_count() + 1
        tree = None
        for op, domain in ((1, rows), (0, cols)):
            for left, right in _splits(domain):
                a, first = best(left, cols) if op else best(rows, left)
                b, second = best(right, cols) if op else best(rows, right)
                if a + b < cost:
                    cost, tree = a + b, (op, first, second)
        return cost, tree

    try:
        return best(rows, cols)
    finally:
        best.cache_clear()


def _rectangles(columns, positive, negative):
    return tuple((col & positive, negative & ~col, i) for i, col in enumerate(columns)
                 if col & positive and negative & ~col)


def _matching_endpoints(rectangles):
    # Outside the matching endpoints, no variable can distinguish two cells.
    matched = set()
    for rows, cols, _ in rectangles:
        pending = None
        for row in _bits(rows):
            for col in _bits(cols):
                cell = row, col
                if cell in matched:
                    continue
                if pending is None:
                    pending = cell
                else:
                    matched.update((pending, cell))
                    pending = None
    return tuple(sorted(matched))


def _reduce_grid(rectangles, positive, negative):
    matched = _matching_endpoints(rectangles)
    middle_p = reduce(or_, (row for row, _ in matched), 0)
    middle_n = reduce(or_, (col for _, col in matched), 0)
    cap = len(matched)

    def representatives(domain, core, oriented_pairs, available):
        retained = core
        ends = {}
        for row, col in oriented_pairs:
            ends[col] = ends.get(col, 0) | row
        requests = {}
        for col, rows in ends.items():
            subsets = [0]
            subset = rows
            while subset:
                subsets.append(subset)
                subset = (subset - 1) & rows
            requests[col] = subsets
        kept = {}
        for row in _bits(domain & ~core):
            profile = []
            for col, subsets in requests.items():
                compatible = [rows for rows, cols in available if rows & row and cols & col]
                profile.append((0, *(need for need in subsets[1:] if any(need & ~rows == 0 for rows in compatible))))
            for request in product(*profile):
                if any(request) and kept.get(request, 0) < cap:
                    kept[request] = kept.get(request, 0) + 1
                    retained |= row
        return retained or (domain & -domain)

    p = representatives(positive, middle_p, sorted(matched), tuple((r, c) for r, c, _ in rectangles))
    n = representatives(negative, middle_n, sorted((c, r) for r, c in matched), tuple((c, r) for r, c, _ in rectangles))
    return p, n


def minimum_partial_formula(columns, positive, negative):
    """Return (leaf count, formula) on a mixed partial table, or None if inconsistent."""
    if not positive or not negative:
        raise ValueError('expected both positive and negative rows')
    rectangles = _rectangles(columns, positive, negative)
    cells = {}
    for rows, cols, leaf in rectangles:
        for row in _bits(rows):
            for col in _bits(cols):
                cells.setdefault((row, col), leaf)
    size = positive.bit_count() * negative.bit_count()
    if len(cells) != size:
        return None
    p, n = _reduce_grid(rectangles, positive, negative)
    core_count, tree = _minimum_protocol(rectangles, p, n)
    tree = _extend_grid(tree, p, n, positive, negative, cells)
    return size - p.bit_count() * n.bit_count() + core_count, tree


def _extend_grid(tree, p, n, positive, negative, cells):
    for op, leaves in _grid_extensions(p, n, positive, negative, cells):
        tree = op, tree, _join(1 - op, leaves)
    return tree


def _grid_extensions(p, n, positive, negative, cells):
    core_columns = _bits(n)
    all_rows = _bits(positive)
    for row in _bits(positive & ~p):
        yield 1, tuple(cells[row, col] for col in core_columns)
    for col in _bits(negative & ~n):
        yield 0, tuple(cells[row, col] for row in all_rows)


def singleton_padding_core(rectangles):
    """Return the row/column masks and tiles of a unique grid's exact circuit core."""
    shared = tuple((rows, cols) for rows, cols, _ in rectangles if rows.bit_count() * cols.bit_count() > 1)
    if not shared:
        row, col, _ = rectangles[0]
        return row, col, rectangles[:1]
    p = reduce(or_, (row for row, _ in shared))
    n = reduce(or_, (col for _, col in shared))
    return p, n, tuple(rect for rect in rectangles if rect[0] & p and rect[1] & n)


def unique_distinction_tree(columns, positive, negative):
    """Return the status and a formula or obstruction for a uniquely labeled grid."""
    if not positive or not negative:
        return 'inapplicable', None
    rectangles = _rectangles(columns, positive, negative)
    if len(rectangles) != len(columns):
        return 'inapplicable', None
    for row in _bits(positive):
        covered = 0
        for rows, cols, _ in rectangles:
            if rows & row:
                if covered & cols:
                    return 'inapplicable', None
                covered |= cols
        if covered != negative:
            return 'inapplicable', None
    tree, obstruction = slicing_tree(rectangles)
    return ('unsat', obstruction) if obstruction is not None else ('sat', tree)
