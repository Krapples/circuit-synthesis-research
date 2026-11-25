"""Reduce exact regional obligations by observable provider patterns."""

from two_sharing_core import ANY


def quotient_rows(patterns, obligations, signed, one):
    """Keep actual row indices so slice-specific checks can use their targets."""
    requested = {}
    kept = [ANY] * len(obligations)
    for row, (pattern, target) in enumerate(zip(patterns, obligations)):
        if target == ANY:
            continue
        if pattern in requested:
            if target != kept[requested[pattern]]:
                return None
        else:
            requested[pattern] = row
            kept[row] = target
    if not signed:
        for value in (0, one):
            matching = (p for p, i in requested.items() if kept[i] == value)
            extremal = []
            for pattern in sorted(matching, key=int.bit_count, reverse=value == 0):
                if any((pattern & prior) == (pattern if value == 0 else prior) for prior in extremal):
                    kept[requested[pattern]] = ANY
                else:
                    extremal.append(pattern)
    return tuple(kept)
