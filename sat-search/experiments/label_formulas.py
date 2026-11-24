"""Top-down read-once formula search on a labeled domain."""

from functools import lru_cache

from regional_synthesis import _bits
from subtree_formulas import _row_signatures, _splits


@lru_cache(maxsize=1024)
def obligation_tree(columns, positive, negative, *, exact):
    """Return a formula, or None. In relaxed mode the tree may omit ambiguous labels."""
    if not columns:
        return None
    ones = _row_signatures(columns, positive)
    zeros = _row_signatures(columns, negative)
    pairs = tuple((a & ~b, a_rows, b_rows) for a, a_rows in ones.items() for b, b_rows in zeros.items())

    @lru_cache(maxsize=None)
    def blocked(group, p, n):
        bad_p = bad_n = 0
        for difference, a_rows, b_rows in pairs:
            if a_rows & p and b_rows & n and not difference & group:
                bad_p |= a_rows & p
                bad_n |= b_rows & n
        return bad_p, bad_n

    @lru_cache(maxsize=None)
    def search(group, p, n):
        if group.bit_count() == 1:
            leaf = group.bit_length() - 1
            return leaf if columns[leaf] & p == p and not columns[leaf] & n else None
        if not p or not n:
            # All-OR is pointwise largest, and all-AND is pointwise smallest.
            op = int(bool(p))
            leaves = [bit.bit_length() - 1 for bit in _bits(group)]
            tree = leaves[0]
            table = columns[tree]
            for leaf in leaves[1:]:
                tree = op, tree, leaf
                table = table | columns[leaf] if op else table & columns[leaf]
            return tree if table & p == p and not table & n else None
        if blocked(group, p, n)[0]:
            return None
        for left, right in _splits(group):
            lp, ln = blocked(left, p, n)
            rp, rn = blocked(right, p, n)
            if not ln & rn:
                tree = join(0, left, right, p, ln, rn, n & ~(ln | rn))
                if tree is not None:
                    return tree
            if not lp & rp:
                tree = join(1, left, right, n, lp, rp, p & ~(lp | rp))
                if tree is not None:
                    return tree
        return None

    def join(op, left, right, common, bad_left, bad_right, ambiguous):
        def child(group, assigned):
            return search(group, assigned, common) if op else search(group, common, assigned)

        if not exact:
            a, b = child(left, bad_right), child(right, bad_left)
            return (op, a, b) if a is not None and b is not None else None
        assigned_left = ambiguous
        while True:
            a = child(left, bad_right | assigned_left)
            if a is not None:
                b = child(right, bad_left | (ambiguous ^ assigned_left))
                if b is not None:
                    return op, a, b
            if not assigned_left:
                return None
            assigned_left = (assigned_left - 1) & ambiguous

    try:
        return search((1 << len(columns)) - 1, positive, negative)
    finally:
        search.cache_clear()
        blocked.cache_clear()
