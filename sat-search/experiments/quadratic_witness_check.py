"""Exact quadratic address images, with independent finite and grammar checks."""

import argparse
from collections import Counter
import json
from random import Random
from time import perf_counter
from typing import NamedTuple

from sat_encoding_bound_review import encode, parse, satisfiable


class Quadratic(NamedTuple):
    constant: int
    linear: int
    rows: tuple[int, ...]  # Upper triangle, with bit j for monomial x_i*x_j.


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def polynomial(n, linear=(), edges=(), constant=0):
    rows = [0] * n
    singles = 0
    for i in linear:
        singles ^= 1 << i
    for i, j in edges:
        if i == j:
            singles ^= 1 << i
        else:
            lo, hi = sorted((i, j))
            rows[lo] ^= 1 << hi
    return Quadratic(constant, singles, tuple(rows))


def qxor(f, g):
    return Quadratic(f.constant ^ g.constant, f.linear ^ g.linear,
                     tuple(a ^ b for a, b in zip(f.rows, g.rows, strict=True)))


def evaluate(f, x):
    degree_one = (f.linear & x).bit_count()
    degree_two = sum((f.rows[i] & x).bit_count() for i in indices(x))
    return (f.constant + degree_one + degree_two) & 1


def enumerated_image(fs, active=None):
    if active is None:
        active = range(len(fs[0].rows))
    representatives = [0]
    for i in active:
        representatives.extend([x | (1 << i) for x in representatives])
    return Counter(sum(evaluate(f, x) << j for j, f in enumerate(fs))
                   for x in representatives)


def signed_sum(f, cap=None):
    """Return sum_x (-1)^f(x), or None after cap pivots have bounded its magnitude."""
    c, linear, rows = f
    rows = list(rows)
    pairs = 0
    for i in range(len(rows)):
        if not rows[i]:
            continue
        j = next(indices(rows[i]))
        a = rows[i] ^ (1 << j)
        b = rows[j]
        for p in range(i + 1, j):
            if rows[p] >> j & 1:
                b |= 1 << p
                rows[p] ^= 1 << j
        ac, bc = linear >> i & 1, linear >> j & 1
        rows[i] = rows[j] = 0
        linear &= ~((1 << i) | (1 << j))
        # Add the product (ac + a.x)(bc + b.x) over GF(2).
        c ^= ac & bc
        linear ^= (b if ac else 0) ^ (a if bc else 0) ^ (a & b)
        for p in indices(a | b):
            change = (b if a >> p & 1 else 0) ^ (a if b >> p & 1 else 0)
            rows[p] ^= change & (-2 << p)
        pairs += 1
        if pairs == cap:
            return None
    return 0 if linear else (-1 if c else 1) * (1 << (len(rows) - pairs))


def walsh(values):
    values = list(values)
    step = 1
    while step < len(values):
        for start in range(0, len(values), 2 * step):
            for i in range(start, start + step):
                a, b = values[i], values[i + step]
                values[i], values[i + step] = a + b, a - b
        step *= 2
    return values


def character_sums(fs, cap=None):
    # Generate one polynomial at a time, with only k polynomials on the stack.
    def sums(f, j):
        if j < 0:
            yield signed_sum(f, cap)
        else:
            yield from sums(f, j - 1)
            yield from sums(qxor(f, fs[j]), j - 1)

    return list(sums(polynomial(len(fs[0].rows)), len(fs) - 1))


def fourier_histogram(fs):
    spectrum = character_sums(fs)
    scale = len(spectrum)
    inverse = walsh(spectrum)
    assert all(v >= 0 and v % scale == 0 for v in inverse)
    return [v // scale for v in inverse], spectrum


def certified_support(fs, cap):
    """Classify addresses by an exact marginal and a bound on its Fourier tail."""
    assert cap > 0
    spectrum = character_sums(fs, cap)
    basis = {}
    for i, value in enumerate(spectrum):
        if value:
            insert(basis, i)
    span = [0]
    for row in basis.values():
        span.extend([i ^ row for i in span])
    marginal = [0] * len(spectrum)
    tail_terms = spectrum.count(None)
    for i in span:
        value = spectrum[i]
        if value is None:
            value = signed_sum(combination(fs, i))
            tail_terms -= 1
        marginal[i] = value
    tail = tail_terms * (1 << (len(fs[0].rows) - cap)) if tail_terms else 0
    mass = walsh(marginal)
    assert all(value >= 0 and value % len(span) == 0 for value in mass)
    # A nonzero degree-2k fiber indicator has at least 2^(n-2k) ones.
    min_mass = len(spectrum) << max(0, len(fs[0].rows) - 2 * len(fs))
    support = []
    for v in mass:
        if v == 0 or v + tail < min_mass:
            support.append(False)
        elif v > tail:
            support.append(True)
        else:
            support.append(None)
    return support, len(basis)


def insert(basis, row):
    while row:
        i = row.bit_length() - 1
        if i not in basis:
            basis[i] = row
            return
        row ^= basis[i]


def polar_rows(f):
    rows = list(f.rows)
    for i, mask in enumerate(f.rows):
        for j in indices(mask):
            rows[j] ^= 1 << i
    return rows


def neutral_complement(fs):
    """Coordinate units giving one representative per common neutral coset."""
    basis = {}
    n = len(fs[0].rows)
    # Record which output has nonzero polar form. An affine output needs only its
    # original linear row, without evaluation on the radical basis.
    nonlinear = []
    for f in fs:
        if any(f.rows):
            nonlinear.append(f)
            for row in polar_rows(f):
                insert(basis, row)
    pivots = sorted(basis)
    extra = [f.linear for f in fs if not any(f.rows)]
    free = [i for i in range(n) if i not in basis]
    restricted = [0] * len(nonlinear)
    for i in free:
        x = 1 << i
        for pivot in pivots:
            if (basis[pivot] & x).bit_count() & 1:
                x |= 1 << pivot
        for j, f in enumerate(nonlinear):
            if evaluate(f, x) ^ f.constant:
                restricted[j] |= 1 << i
    for row in extra + restricted:
        insert(basis, row)
    return sorted(basis)


def quotient_histogram(fs, cap):
    active = neutral_complement(fs)
    d = len(active)
    if d > cap:
        return None, d
    hist = enumerated_image(fs, active)
    lift = 1 << (len(fs[0].rows) - d)
    return [lift * hist[i] for i in range(1 << len(fs))], d


def image_counts(fs):
    hist = enumerated_image(fs)
    return [hist[i] for i in range(1 << len(fs))]


def rank(f):
    basis = {}
    for row in polar_rows(f):
        insert(basis, row)
    return len(basis)


def combination(fs, selector):
    return fold_xor((fs[j] for j in indices(selector)), len(fs[0].rows))


def fold_xor(fs, n):
    out = polynomial(n)
    for f in fs:
        out = qxor(out, f)
    return out


def random_map(rng, n, k, width=None):
    width = n if width is None else width
    out = []
    for _ in range(k):
        edges = [tuple(rng.sample(range(width), 2)) for _ in range(2 * width)] if width > 1 else []
        linear = list(indices(rng.getrandbits(width)))
        out.append(polynomial(n, linear, edges, rng.randrange(2)))
    return out


def parity_lift(fs, n):
    """Replace each short witness by the XOR of one disjoint block of bits."""
    width = len(fs[0].rows)
    groups = [range(i, n, width) for i in range(width)]
    return [polynomial(n, (x for i in indices(f.linear) for x in groups[i]),
                       ((x, y) for i, row in enumerate(f.rows) for j in indices(row)
                        for x in groups[i] for y in groups[j]), f.constant)
            for f in fs]


def matched_profiles():
    f = polynomial(4, [0], [(0, 1), (1, 3)])
    g = polynomial(4, [1], [(0, 2), (0, 3)])
    h = polynomial(4, [0, 2], [(0, 1), (0, 2), (0, 3), (1, 3), (2, 3)])
    changed = h._replace(linear=(1 << 0) | (1 << 3))
    maps = ([f, g, h], [f, g, changed])
    results = []
    for fs in maps:
        hist, spec = fourier_histogram(fs)
        assert hist == image_counts(fs) == quotient_histogram(fs, 4)[0]
        results.append((hist, spec, [rank(combination(fs, t)) for t in range(8)]))
    a, b = results
    assert a[2] == b[2] and list(map(abs, a[1])) == list(map(abs, b[1]))
    assert all(a[0]) and [i for i, m in enumerate(b[0]) if not m] == [1, 6]
    return results


def connected_example(n, k):
    """Full common dimension and a connected interaction graph, with missing addresses."""
    assert n % 2 == 0 and k >= 3
    pairs = [(i, i + 1) for i in range(2, n, 2)]
    fs = [polynomial(n, edges=[(0, 1)]),
          polynomial(n, [0], [(0, 1)]),
          polynomial(n, edges=pairs + [(0, i) for i, _ in pairs])]
    fs.extend(polynomial(n, [i + 2]) for i in range(k - 3))
    return fs


def rare_fibers(n, k):
    pairs = [(i, i + 1) for i in range(0, n, 2)]
    return ([polynomial(n, edges=[pair]) for pair in pairs[:k - 1]]
            + [polynomial(n, edges=pairs + [(0, i) for i, _ in pairs[1:]])])


def tests():
    rng = Random(575007)
    cases = combinations = quotient_directions = bounded_checks = unresolved = exact_support_checks = 0
    for n in range(1, 10):
        for i in range(24):
            k = rng.randrange(1, 6)
            width = n if i % 2 else rng.randrange(1, n + 1)
            fs = random_map(rng, n, k, width)
            expected = image_counts(fs)
            observed, spec = fourier_histogram(fs)
            quotient, dimension = quotient_histogram(fs, n)
            assert expected == observed == quotient and dimension <= width
            assert spec == walsh(expected)
            support, _ = certified_support(fs, 2 * k + 1)
            assert support == [want > 0 for want in expected]
            exact_support_checks += len(support)
            for cap in range(1, min(n, 4) + 1):
                support, _ = certified_support(fs, cap)
                assert all(got is None or got == (want > 0) for got, want in zip(support, expected))
                bounded_checks += len(support)
                unresolved += support.count(None)
            for t in range(1 << k):
                f = combination(fs, t)
                r = rank(f)
                assert r % 2 == 0
                assert abs(spec[t]) in (0, 1 << (n - r // 2))
                combinations += 1
            # Independently enumerate all common neutral translations for n <= 5.
            if n <= 5:
                words = [tuple(evaluate(f, x) for f in fs) for x in range(1 << n)]
                neutral = [z for z in range(1 << n)
                           if all(words[x] == words[x ^ z] for x in range(1 << n))]
                assert len(neutral) == 1 << (n - dimension)
                quotient_directions += 1 << n
            cases += 1
    # Actual rank truncation at the guaranteed cutoff, not merely exact inversions.
    for k in range(1, 6):
        fs = random_map(rng, 6 * k + 4, k)
        cap = 2 * k + 1
        assert None in character_sums(fs, cap)
        assert certified_support(fs, cap)[0] == [v > 0 for v in fourier_histogram(fs)[0]]
        exact_support_checks += 1 << k
    print(json.dumps({"random_maps": cases, "signed_character_checks": combinations,
                      "neutral_directions_checked": quotient_directions,
                      "support_checks": bounded_checks, "support_unknown": unresolved,
                      "guaranteed_cutoff_checks": exact_support_checks}))
    print(json.dumps({"matched_profiles": matched_profiles()}))


def lookup_system(clauses, n):
    """Quadratic one-bit zero lookups for 3-CNF, with one new witness per clause."""
    size = n + len(clauses)
    equations = []
    for i, ((a, sa), (b, sb), (c, sc)) in enumerate(clauses):
        t = n + i
        # The falsity indicator of a signed literal is x + sign.
        equations.append(polynomial(size, [t] + ([a] if sb else []) + ([b] if sa else []),
                                    [(a, b)], int(sa and sb)))
        equations.append(polynomial(size, [t] if sc else [], [(t, c)]))
    return equations


def literal_id(lit):
    return lit[0] + 1 if lit[1] else -lit[0] - 1


def gate_clauses(a, b, z, op):
    return [[lit if not value else -lit for lit, value in
             zip((a, b, z), (u, v, 1 ^ op(u, v)), strict=True)]
            for u in (0, 1) for v in (0, 1)]


def grammar_checks():
    # Equal clause lengths and one renamed witness distinguish these
    # contexts. The two checks are each satisfiable with witnesses free.
    # Use nonzero equal-width witness IDs (zero based) 4, 5, 6.
    a, b, c, t, u = 5, 6, 7, 9, 10  # Signed-literal representation is ID + 1.
    first = gate_clauses(a, b, t, int.__and__) + [[t]]
    conflicting = gate_clauses(a, -b, u, int.__and__) + [[u]]
    independent = gate_clauses(a, -c, u, int.__and__) + [[u]]
    def as_cnf(clauses):
        return [[(abs(v) - 1, v > 0) for v in clause] for clause in clauses]
    words = [encode(as_cnf(f)) for f in (first, conflicting, independent,
                                        first + conflicting, first + independent)]
    assert list(map(lambda word: satisfiable(parse(word)), words)) == [True, True, True, False, True]
    assert len(words[-1]) == len(words[-2])
    changed = [i for i, (x, y) in enumerate(zip(words[-1], words[-2], strict=True)) if x != y]
    print(json.dumps({"paired_sat_context_length": len(words[-1]), "changed_bits": changed}))

    rng = Random(575008)
    checked = 0
    for n in range(3, 6):
        for _ in range(24):
            clauses = [[(i, bool(rng.randrange(2))) for i in rng.sample(range(n), 3)]
                       for _ in range(rng.randrange(1, 7))]
            equations = lookup_system(clauses, n)
            # Count accepting assignments, including uniqueness of the extra witnesses.
            truth = [int(all(any(bool(x >> i & 1) == s for i, s in cl) for cl in clauses))
                     for x in range(1 << n)]
            for x in range(1 << n):
                extensions = sum(all(not evaluate(f, x | (w << n)) for f in equations)
                                 for w in range(1 << len(clauses)))
                assert extensions == truth[x]
            assert satisfiable(parse(encode(clauses))) == bool(sum(truth))
            checked += 1
    print(json.dumps({"three_cnf_lookup_systems": checked}))


def benchmarks():
    rng = Random(575009)
    for n, k in [(16, 4), (48, 5), (96, 6), (128, 7), (192, 8)]:
        for name, fs in [("random", random_map(rng, n, k)),
                         ("parity_lifted", parity_lift(random_map(rng, 12, k), n)),
                         ("connected_missing", connected_example(n, k)),
                         ("rare_fibers", rare_fibers(n, k))]:
            start = perf_counter()
            hist, _ = fourier_histogram(fs)
            fourier_time = perf_counter() - start
            start = perf_counter()
            qhist, d = quotient_histogram(fs, 14)
            quotient_time = perf_counter() - start
            start = perf_counter()
            support, marginal_dimension = certified_support(fs, k + 2)
            certified_time = perf_counter() - start
            assert sum(hist) == 1 << n
            assert all(got is None or got == (want > 0) for got, want in zip(support, hist))
            assert certified_support(fs, 2 * k + 1)[0] == [v > 0 for v in hist]
            if qhist is not None:
                assert qhist == hist
            if n <= 16:
                assert hist == image_counts(fs)
            if name == "connected_missing":
                assert d == n and any(not x for x in hist)
            if name == "rare_fibers":
                assert d == n and all(hist)
                if k >= 6:
                    assert None in support
            print(json.dumps({"family": name, "witnesses": n, "address_bits": k,
                              "quotient_dimension": d, "image_size": sum(x > 0 for x in hist),
                              "fourier_seconds": round(fourier_time, 6),
                              "quotient_seconds": round(quotient_time, 6),
                              "quotient_finished": qhist is not None,
                              "support_seconds": round(certified_time, 6),
                              "support_unknown": support.count(None),
                              "marginal_dimension": marginal_dimension}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["check", "bench"])
    if parser.parse_args().mode == "check":
        tests()
        grammar_checks()
    else:
        benchmarks()
