"""Bounds on gates that read fixed inputs in a complete AO2 circuit."""
from itertools import combinations
from monotone_frontier import monotone_frontier


def support_size(table):
    return sum(
        any(table[row] != table[row | bit] for row in range(len(table)) if not row & bit)
        for bit in (1 << i for i in range(len(table).bit_length() - 1))
    )


def support_lower_bound(table):
    return max(0, support_size(table) - 1)


def read_once_lower_bound(table):
    """A monotone minterm/maxterm intersection can exclude tree size."""
    support = support_size(table)
    if support < 2:
        return 0
    minimal_true, maximal_false = monotone_frontier(table)
    universe = len(table) - 1
    obstruction = any(
        (positive & (universe ^ negative)).bit_count() >= 2
        for positive in minimal_true
        for negative in maximal_false
    )
    return support - 1 + obstruction


def direct_reader_caps(table, gates, width, *, lower_bound=support_lower_bound):
    """Yield (fixed input bits, cap) using the strongest cofactor bound."""
    inputs = range(len(table).bit_length() - 1)

    def masks(positions):
        values = [0]
        for i in positions:
            values += [value | (1 << i) for value in values]
        return values

    for count in range(1, width + 1):
        for fixed in combinations(inputs, count):
            free_rows = masks(i for i in inputs if i not in fixed)
            bound = max(lower_bound([table[row | base] for row in free_rows]) for base in masks(fixed))
            if bound:
                yield fixed, gates - bound


def append_direct_reader_caps(clauses, selectors, caps, top_id, card_encoder):
    """Add existential per-gate touch flags and bounded cardinalities."""
    for fixed, cap in caps:
        if cap < 0:
            clauses.append([])
            return top_id
        touched = [
            [selector for (a, b), selector in pairs.items() if a in fixed or b in fixed]
            for pairs in selectors
        ]
        if cap >= sum(bool(pairs) for pairs in touched):
            continue
        flags = []
        for pairs in touched:
            if pairs:
                top_id += 1
                flags.append(top_id)
                clauses.extend([-selector, top_id] for selector in pairs)
        constraint = card_encoder(lits=flags, bound=cap, top_id=top_id, encoding=1)
        top_id = max(top_id, constraint.nv)
        clauses.extend(constraint.clauses)
    return top_id
