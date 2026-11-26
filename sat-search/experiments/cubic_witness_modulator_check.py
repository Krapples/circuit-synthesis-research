"""Exact support replay for cubic maps with a small monomial hitting set."""

import json
from itertools import combinations, product
from pathlib import Path
from random import Random
import sys

from quadratic_witness_check import fourier_histogram, polynomial
from sat_encoding_bound_review import parse as independent_parse

sys.path.append(str(Path(__file__).resolve().parents[1] / 'chatgpt_handoff'))
from permutable_andreev_check import balance, build, encode_clause, params, parse, unit_decide


def canonical(records):
    """Apply Boolean idempotence and XOR duplicated monomial coefficients."""
    terms = {}
    for variables, coefficient in records:
        monomial = tuple(sorted(set(variables)))
        terms[monomial] = terms.get(monomial, 0) ^ coefficient
    return {monomial: value for monomial, value in terms.items() if value}


def cover(triples, budget, chosen=()):
    """Pick a cover by branching on the first uncovered triple."""
    obstruction = next((edge for edge in triples if not any(x in chosen for x in edge)), None)
    if obstruction is None:
        return chosen
    if budget:
        for x in obstruction:
            result = cover(triples, budget - 1, chosen + (x,))
            if result is not None:
                return result
    return None


def restrict(terms, fixed, values):
    positions = {var: bit for bit, var in enumerate(fixed)}
    records = []
    for edge, weight in terms.items():
        if all(values >> positions[x] & 1 for x in edge if x in positions):
            records.append((tuple(x for x in edge if x not in positions), weight))
    return canonical(records)


def quadratic_support(terms, q, k):
    outputs = []
    for i in range(k):
        edges = [edge for edge, value in terms.items() if value >> i & 1]
        assert all(len(edge) <= 2 for edge in edges)
        outputs.append(polynomial(q, [e[0] for e in edges if len(e) == 1],
                                  [e for e in edges if len(e) == 2], int(() in edges)))
    counts, _ = fourier_histogram(outputs)
    return {i for i, count in enumerate(counts) if count}


def raw_support(records, q):
    image = set()
    for row in range(1 << q):
        value = 0
        for variables, coefficient in records:
            if all(row >> x & 1 for x in variables):
                value ^= coefficient
        image.add(value)
    return image


def check(records, q, k, stats):
    terms = canonical(records)
    triples = [edge for edge in terms if len(edge) == 3]
    edges = [frozenset(edge) for edge in triples]
    expected = next(h for h in range(q + 1) if any(all(edge.intersection(s) for edge in edges)
                    for s in combinations(range(q), h)))
    found = cover(triples, expected)
    assert found is not None and len(found) == expected
    if expected:
        assert cover(triples, expected - 1) is None
    output = set()
    for bits in range(1 << len(found)):
        output.update(quadratic_support(restrict(terms, found, bits), q, k))
        stats['quadratic_branches'] += 1
    assert output == raw_support(records, q)
    stats['maps'] += 1
    stats['genuinely_cubic'] += bool(triples)
    stats['max_cover'] = max(stats['max_cover'], expected)


def packed_cubic(k, table, selectors, order, labels):
    """Keep the checked base layout and replace each equality slot by a cubic slot."""
    _m, ell, _j, _r, patterns, guards, auxiliaries, old_pool = params(k)
    slots = len(order)
    pool = 1 << (max(4 * patterns, auxiliaries + 3 * slots + 1) - 1).bit_length()
    base, _, _ = build(k, table, selectors, order)

    def widen(lit):
        index = abs(lit)
        if index > old_pool:
            index += pool - old_pool
        return index if lit > 0 else -index

    clauses = [[widen(lit) for lit in c] for c in parse(base)]

    def witness(label):
        return pool + auxiliaries + 2 * slots + label + 1

    out = []

    def emit(clause):
        out.extend(encode_clause(clause))

    def last_literal(clause):
        first = len(out) + len(encode_clause(clause[:-1])) - 2
        emit(clause)
        return tuple(first + 3 + 2 * bit for bit in range(ell))

    for c in clauses[:patterns]:
        emit(c)
    emit([-witness(0)])

    selector_positions = []
    first_slot = len(out)
    literal_bits = 4 + 2 * pool.bit_length()
    # The 10 clauses have 26 literal occurrences, including 2 short pattern literals.
    slot_width = 24 * literal_bits + 2 * (4 + 2 * (ell + 1)) + 20
    for i, triple in enumerate(labels):
        neg, pos = clauses[patterns + 2 * i:patterns + 2 * i + 2]
        z = pos[0]
        t = pool + auxiliaries + i + 1
        p = pool + auxiliaries + slots + i + 1
        selector_positions.extend(zip(last_literal([-t, neg[1]]), last_literal([t, pos[1]])))
        operands = [witness(u) for u in triple]
        for operand in operands:
            emit([-p, operand])
        emit([p] + [-operand for operand in operands])
        for x, y in product(range(2), repeat=2):
            emit([lit if not bv else -lit for lit, bv in zip((t, p, z), (x, y, 1 ^ x ^ y))])
        assert len(out) == first_slot + (i + 1) * slot_width
    for c in clauses[patterns + 2 * slots:-guards]:
        emit(c)
    table_positions = [p for c in clauses[-guards:] for p in last_literal(c)]
    return out, table_positions, selector_positions, witness


def padding(length):
    for long_count in range(5):
        short_total = length - 14 * long_count
        if short_total >= 0 and short_total % 10 == 0:
            return encode_clause([-1, 1]) * (short_total // 10) + encode_clause([-2, 2]) * long_count
    raise ValueError('expected a representable even padding length')


def check_packed(rng):
    stats = dict(instances=0, pinned_cases=0, balanced_cases=0, padded_cases=0,
                 coordinate_probes=0, genuine_cubic_cases=0)
    for k in range(1, 7):
        m, ell, j, r, _p, _b, _a, _q = params(k)
        slots = k * j
        for case in range(8):
            table = [rng.randrange(2) for _ in range(m)]
            selectors = [rng.randrange(2) for _ in range(k * r)]
            order = rng.sample(range(slots), slots)
            labels = [tuple(rng.randrange(min(slots, 4) + 1) for _ in range(3)) for _ in range(slots)]
            if case == 0:
                labels[0] = (0, 1, 1)
            if case == 1 and slots >= 3:
                labels[0] = (1, 2, 3)
            word, ht, xs, witness = packed_cubic(k, table, selectors, order, labels)
            original = ''.join(map(str, word))
            independent = independent_parse(original)
            assert independent is not None
            assert [[(v + 1) if positive else -(v + 1) for v, positive in c]
                    for c in independent] == parse(word)
            assert len(set(ht + [p for pair in xs for p in pair])) == len(ht) + 2 * len(xs)
            assert [word[p] for p in ht] == table
            assert [[word[p] for p in pair] for pair in xs] == [[b, b] for b in selectors]
            pad_length = 48 + 2 * rng.randrange(10)
            padded = word + padding(pad_length)
            assert len(padded) == len(word) + pad_length
            balanced = balance(padded)
            assert len(balanced) == 3 * len(padded) + 12 and sum(balanced) == 2 * len(padded) + 5
            raw = parse(word)
            padded_cnf = parse(padded)
            balanced_cnf = parse(balanced)
            stats['genuine_cubic_cases'] += any(len(set(t)) == 3 and 0 not in t for t in labels)
            witnesses = sorted({u for t in labels for u in t} - {0})
            for bits in product(range(2), repeat=len(witnesses)):
                values = dict(zip(witnesses, bits))
                values[0] = 0
                address = 0
                for i, (slot, triple) in enumerate(zip(order, labels)):
                    digit = (sum(selectors[i * ell:(i + 1) * ell]) & 1) ^ all(values[u] for u in triple)
                    address ^= digit << (slot // j)
                units = [[witness(u) if bit else -witness(u)] for u, bit in zip(witnesses, bits)]
                for cnf, key in ((raw, 'pinned_cases'), (padded_cnf, 'padded_cases'), (balanced_cnf, 'balanced_cases')):
                    assert unit_decide(cnf + units) == bool(table[address])
                    stats[key] += 1
            # Reprogram metadata once, then compare the exact coordinates of
            # one table bit and one selector bit on this new physical layout.
            trial_order = order[1:] + order[:1]
            trial_labels = [tuple((u + 1) % (slots + 1) for u in t) for t in labels]
            baseline, next_ht, next_xs, _ = packed_cubic(k, table, selectors, trial_order, trial_labels)
            assert len(baseline) == len(word) and ht == next_ht and xs == next_xs
            hi, xi = rng.randrange(m), rng.randrange(len(xs))
            table[hi] ^= 1
            selectors[xi] ^= 1
            changed, _, _, _ = packed_cubic(k, table, selectors, trial_order, trial_labels)
            expected = {ht[hi], *xs[xi]}
            assert changed_coordinates(baseline, changed) == expected
            suffix = padding(pad_length)
            extended = baseline + suffix
            guarded = balance(extended)
            assert changed_coordinates(guarded, balance(changed + suffix)) == (
                expected | {len(extended) + 11 + 2 * p for p in expected})
            stats['coordinate_probes'] += 2
            stats['instances'] += 1
    print(json.dumps(stats))


def changed_coordinates(first, second):
    return {i for i, (a, b) in enumerate(zip(first, second, strict=True)) if a != b}


def main():
    rng = Random(870012)
    stats = dict(maps=0, genuinely_cubic=0, quadratic_branches=0, max_cover=0)
    # This pair checks actual cancellation after fixing a shared variable.
    check([((0, 1, 2), 1), ((0, 2, 1), 1), ((0, 0, 2), 1)], 3, 1, stats)
    check([((0, 1, 2), 1), ((1, 2), 1), ((0, 1, 3), 2)], 4, 2, stats)
    for q in range(3, 10):
        for j in range(30):
            k = rng.randrange(1, 5)
            planted = set(rng.sample(range(q), j % 3 + 1))
            terms = []
            for _ in range(rng.randrange(4, 26)):
                edge = tuple(rng.randrange(q) for _ in range(rng.randrange(4)))
                if j % 2 and len(set(edge)) == 3 and planted.isdisjoint(edge):
                    continue
                terms.append((edge, rng.randrange(1 << k)))
            check(terms, q, k, stats)
    check([(tuple(range(i, i + 3)), 1 << (i // 3)) for i in (0, 3, 6)], 9, 3, stats)
    print(json.dumps(stats))
    check_packed(rng)


if __name__ == '__main__':
    main()
