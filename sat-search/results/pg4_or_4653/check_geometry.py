"""Enumerate minimal vertex covers of the cyclic PG(2, 4) incidence graph."""

from collections import Counter
from itertools import combinations
import json
from math import gcd

from projective_symmetry import boundary_orbits


ORDER = 21
ALL = (1 << ORDER) - 1
DIFFERENCES = (0, 5, 7, 17, 20)


def neighbors(points_left):
    sign = 1 if points_left else -1
    return [
        sum(1 << ((vertex + sign * delta) % ORDER) for delta in DIFFERENCES)
        for vertex in range(ORDER)
    ]


def maximal_independent_sets(rows):
    """Close each distinct union-of-neighborhoods signature."""
    signatures = {0}
    for row in rows:
        signatures.update(signature | row for signature in tuple(signatures))
    result = set()
    for signature in signatures:
        left = sum(1 << index for index, row in enumerate(rows) if row & ~signature == 0)
        result.add((left, ALL ^ signature))
    return result


def enumerate_small_side(rows, reversed_rows):
    """Independently enumerate from a side of size at most six."""
    result = set()
    for side, swap in ((rows, False), (reversed_rows, True)):
        for count in range(7):
            for vertices in combinations(range(ORDER), count):
                seen = 0
                for v in vertices:
                    seen |= side[v]
                other = ALL ^ seen
                original = sum(1 << v for v, row in enumerate(side) if row & other == 0)
                if original.bit_count() == count:
                    result.add((other, original) if swap else (original, other))
    return result


def cover_orbits(independent):
    """Use cyclic affine incidence symmetries and the explicit point-line duality."""
    multipliers = [(a, b) for a in range(ORDER) if gcd(a, ORDER) == 1 for b in range(ORDER)
                   if {(a * d + b) % ORDER for d in DIFFERENCES} == set(DIFFERENCES)]

    def apply(mask, a, b):
        return sum(1 << ((a * vertex + b) % ORDER) for vertex in range(ORDER) if mask >> vertex & 1)

    remaining = set(independent)
    sizes = Counter()
    while remaining:
        p, l = min(remaining)
        orbit = set()
        for a, b in multipliers:
            for shift in range(ORDER):
                orbit.add((apply(p, a, shift), apply(l, a, shift + b)))
                orbit.add((apply(l, -a, shift), apply(p, -a, shift + b)))
        assert orbit <= remaining
        remaining.difference_update(orbit)
        sizes[len(orbit)] += 1
    return multipliers, dict(sorted(sizes.items()))


def main():
    points, lines = neighbors(True), neighbors(False)
    for rows in (points, lines):
        assert all(row.bit_count() == 5 for row in rows)
        assert all((a & b).bit_count() == 1 for a, b in combinations(rows, 2))
    independent = maximal_independent_sets(points)
    assert independent == {(p, l) for l, p in maximal_independent_sets(lines)}
    assert independent == enumerate_small_side(points, lines)
    shapes = Counter((p.bit_count(), l.bit_count()) for p, l in independent)
    cover_sizes = Counter(2 * ORDER - p.bit_count() - l.bit_count() for p, l in independent)
    frontier = [shape for shape in shapes if not any(other != shape and other[0] >= shape[0]
                                                    and other[1] >= shape[1] for other in shapes)]
    multipliers, orbit_sizes = cover_orbits(independent)
    print(json.dumps({
        "edges": sum(row.bit_count() for row in points),
        "minimal_covers": len(independent),
        "independent_shapes": {f"{p},{l}": count for (p, l), count in sorted(shapes.items())},
        "minimal_cover_sizes": dict(sorted(cover_sizes.items())),
        "largest_minimal_cover_lower_bound": max(cover_sizes) - 1,
        "incidence_free_rectangle_frontier": sorted(frontier),
        "max_incidence_free_rectangle_area": max(p * l for p, l in shapes),
        "affine_multipliers": multipliers,
        "minimal_cover_orbit_sizes": orbit_sizes,
        "projective_symmetry": boundary_orbits(independent, points, DIFFERENCES),
    }, indent=2))


if __name__ == "__main__":
    main()
