"""Generators and boundary orbits in the cyclic order-four incidence graph."""

from collections import Counter, deque
from itertools import permutations, product
from math import gcd


def multiply(a, b):
    """Multiply in GF(64), using x^6 + x + 1."""
    value = 0
    while b:
        if b & 1:
            value ^= a
        a <<= 1
        if a & 64:
            a ^= 0b1000011
        b >>= 1
    return value


def boundary_orbits(independent, rows, differences):
    powers = [1]
    for _ in range(62):
        powers.append(multiply(powers[-1], 2))
    assert len(set(powers)) == 63 and multiply(powers[-1], 2) == 1
    cycle = 21

    def trace(exponent):
        return powers[exponent % 63] ^ powers[(4 * exponent) % 63] ^ powers[(16 * exponent) % 63]

    difference_trace = {d for d in range(cycle) if trace(-d) == 0}
    mult, shift = next((a, b) for a in range(cycle) if gcd(a, cycle) == 1 for b in range(cycle)
                       if {(a * d + b) % cycle for d in differences} == difference_trace)
    assert all(bool(rows[p] >> l & 1) == (trace(mult * (p - l) - shift) == 0)
               for p in range(cycle) for l in range(cycle))
    point = [powers[(mult * p) % cycle] for p in range(cycle)]
    ray = {value: (i * pow(mult, -1, cycle)) % cycle for i, value in enumerate(powers)}
    subfield = [0, 1, powers[21], powers[42]]

    def value(coords):
        a, b, c = coords
        return a ^ multiply(b, 2) ^ multiply(c, 4)

    coordinates = {value(c): c for c in product(subfield, repeat=3)}
    assert len(coordinates) == 64

    def linear_actions():
        for target, source in permutations(range(3), 2):
            yield lambda c, i=target, j=source: tuple(v ^ c[j] if k == i else v for k, v in enumerate(c))
        yield lambda c: (c[1], c[0], c[2])
        yield lambda c: (c[0], c[2], c[1])
        yield lambda c: (multiply(c[0], subfield[2]), c[1], c[2])

    point_actions = [tuple(ray[value(action(coordinates[p]))] for p in point) for action in linear_actions()]
    point_actions.append(tuple(ray[multiply(p, p)] for p in point))
    line_to_points = [sum(1 << p for p, r in enumerate(rows) if r >> l & 1) for l in range(cycle)]
    points_to_line = {mask: l for l, mask in enumerate(line_to_points)}

    def rename(mask, perm):
        result = 0
        while mask:
            low = mask & -mask
            result |= 1 << perm[low.bit_length() - 1]
            mask ^= low
        return result

    actions = []
    for perm in point_actions:
        assert len(set(perm)) == cycle
        lines = tuple(points_to_line[rename(mask, perm)] for mask in line_to_points)
        assert len(set(lines)) == cycle
        actions.append((perm, lines))
    dual = tuple(-v % cycle for v in range(cycle))
    assert all(bool(rows[p] >> l & 1) == bool(rows[dual[l]] >> dual[p] & 1)
               for p in range(cycle) for l in range(cycle))

    remaining = set(independent)
    orbit_counts = Counter()
    orbits_by_shape = Counter()
    while remaining:
        initial = min(remaining)
        queue = deque([initial])
        seen = {initial}
        while queue:
            p, l = queue.popleft()
            images = [(rename(p, a), rename(l, b)) for a, b in actions]
            images.append((rename(l, dual), rename(p, dual)))
            for pair in images:
                if pair not in seen:
                    seen.add(pair)
                    queue.append(pair)
        assert seen <= remaining
        remaining.difference_update(seen)
        orbit_counts[len(seen)] += 1
        orbits_by_shape[tuple(sorted(s.bit_count() for s in initial))] += 1
    return {
        "trace_coordinates": {"multiplier": mult, "line_offset": shift},
        "point_generators": [list(a) for a, _ in actions],
        "cover_orbit_sizes": dict(sorted(orbit_counts.items())),
        "cover_orbits_by_unordered_shape": {f"{p},{l}": count for (p, l), count in sorted(orbits_by_shape.items())},
    }
