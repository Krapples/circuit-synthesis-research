"""Signed AIG table queries and exact cubic controls with full marginal dimension."""

import json
from itertools import combinations, product
from random import Random
from sys import argv

from cubic_witness_modulator_check import canonical, cover, packed_cubic, params, parse, unit_decide
from sparse_rank_routing_check import Aig, pack, rank, sorted_join, word


def add(circuit, left, right, carry=0):
    output = []
    for x, y in zip(left, right, strict=True):
        same = circuit.xor(x, y)
        output.append(circuit.xor(same, carry))
        carry = circuit.or_(circuit.and_(x, y), circuit.and_(same, carry))
    return tuple(output)


def multiply(circuit, left, right):
    """Low product bits of two same-width two's-complement integers."""
    bits = len(left)
    value = (0,) * bits
    for shift, bit in enumerate(right):
        value = add(circuit, value, (0,) * shift + circuit.mask(bit, left[:bits - shift]))
    return value


def walsh(circuit, flags, bits):
    values = [(x,) + (0,) * (bits - 1) for x in flags]
    step = 1
    while step < len(values):
        for i in range(0, len(values), 2 * step):
            for j in range(i, i + step):
                x, y = values[j], values[j + step]
                values[j] = add(circuit, x, y)
                values[j + step] = add(circuit, x, tuple(b ^ 1 for b in y), carry=1)
        step *= 2
    return values


def linear(circuit, rows, mask, columns):
    value = (0,) * columns
    for i, row in enumerate(rows):
        if mask >> i & 1:
            value = tuple(circuit.xor(a, b) for a, b in zip(value, row, strict=True))
    return value


def table_query(k, t, branches, batch):
    aig = Aig()
    table = aig.input_word(1 << k)
    data = [(tuple(aig.input_word(k) for _ in range(t)), aig.input_word(1 << t))
            for _ in range(branches)]
    bits = k + 2 * t + 2
    zero = (0,) * bits
    totals = []
    if batch:
        frequencies = [linear(aig, projection, w, k) for projection, _ in data for w in range(1 << t)]
        pulled = sorted_join(aig, walsh(aig, table, bits), frequencies)
        words = iter(pulled[i:i + bits] for i in range(0, len(pulled), bits))
        for _, support in data:
            total = zero
            for coefficient in walsh(aig, support, bits):
                total = add(aig, total, multiply(aig, coefficient, next(words)))
            totals.append(total)
    else:
        for projection, support in data:
            total = zero
            for address, entry in enumerate(table):
                chosen = support
                for row in projection:
                    digit = linear(aig, [(bit,) for bit in row], address, 1)[0]
                    chosen = tuple(aig.select(digit, (y,), (x,))[0] for x, y in zip(chosen[::2], chosen[1::2]))
                hit = aig.and_(entry, chosen[0])
                total = add(aig, total, (0,) * t + (hit,) + (0,) * (bits - t - 1))
            totals.append(total)
    outputs = tuple(b for score in totals for b in score)
    return aig, outputs, bits


def table_cases():
    rng = Random(870015)
    for k, t, branches in ((1, 0, 2), (2, 1, 2), (2, 2, 3), (3, 2, 4), (4, 3, 4)):
        width = (1 << k) + branches * (t * k + (1 << t))
        samples = list(range(1 << width)) if width <= 12 else [rng.getrandbits(width) for _ in range(512)]
        # Constant tables, zero rows, and all-equal rows are explicit controls.
        if width > 12:
            high = ((1 << (t * k + (1 << t))) - 1) << (1 << k)
            samples += [0, (1 << width) - 1, high, high | ((1 << (1 << k)) - 1)]
        expected = []
        for inp in samples:
            scores = []
            offset = 1 << k
            for _ in range(branches):
                projection = [(inp >> (offset + i * k)) & ((1 << k) - 1) for i in range(t)]
                support = inp >> (offset + t * k)
                count = 0
                for a in range(1 << k):
                    key = pack((a & row).bit_count() & 1 for row in projection)
                    count += (inp >> a) & (support >> key) & 1
                scores.append(count << t)
                offset += t * k + (1 << t)
            expected.append(scores)
        counts = {}
        for batch in (False, True):
            aig, outputs, bits = table_query(k, t, branches, batch)
            assert aig.inputs == width
            observed = aig.evaluate(samples, outputs)
            assert [[pack(row[i:i + bits]) for i in range(0, len(outputs), bits)]
                    for row in observed] == expected
            counts['walsh_ands' if batch else 'direct_ands'] = aig.live_count(outputs)
        print(json.dumps(dict(k=k, t=t, branches=branches, inputs=len(samples), **counts)), flush=True)


def pair_value(mix, assignment):
    m = len(mix)
    active = assignment & (assignment >> m)
    control = assignment >> (2 * m)
    return sum((1 if (control & row).bit_count() % 2 else 2) << (2 * i)
               for i, row in enumerate(mix) if active >> i & 1)


def canonical_support(m):
    return {sum(bit << (2 * i) for i, bit in enumerate(row)) for row in product(range(3), repeat=m)}


def pair_polynomial(mix):
    m = len(mix)
    records = []
    for i, row in enumerate(mix):
        records.append(((i, m + i), 1 << (2 * i + 1)))
        for j, bit in enumerate(word(row, m)):
            if bit:
                records.append(((i, m + i, 2 * m + j), 3 << (2 * i)))
    return records


def path_mix(m):
    return tuple((3 << i) if i + 1 < m else (1 << i) for i in range(m))


def dense_mix(m):
    assert m % 2 == 0
    return tuple(((1 << m) - 1) ^ (1 << i) for i in range(m))


def slot_program(k, slots_per_row, records):
    labels_by_slot = [(0, 0, 0)] * (k * slots_per_row)
    used = [0] * k
    for variables, coefficient in records.items():
        if not variables:
            continue
        labels = tuple(v + 1 for v in variables) + (variables[-1] + 1,) * (3 - len(variables))
        for i, enabled in enumerate(word(coefficient, k)):
            if enabled:
                assert used[i] < slots_per_row
                labels_by_slot[i * slots_per_row + used[i]] = labels
                used[i] += 1
    return labels_by_slot


def verify_packed(mix, rng):
    m = len(mix)
    k = 2 * m
    size, _ell, j, r, *_ = params(k)
    expected = canonical_support(m)
    slot_labels = slot_program(k, j, canonical(pair_polynomial(mix)))
    order = rng.sample(range(k * j), k * j)
    labels = [slot_labels[i] for i in order]
    selectors = [0] * (k * r)
    queries = sorted(rng.sample(range(size), min(size, 16)))
    checks = 0
    for address in queries:
        table = [int(i == address) for i in range(size)]
        w, _, _, witness = packed_cubic(k, table, selectors, order, labels)
        clauses = parse(w)
        accepted = False
        for assignment in range(1 << (3 * m)):
            if pair_value(mix, assignment) != address and rng.randrange(127):
                continue
            units = [[witness(i + 1) if assignment >> i & 1 else -witness(i + 1)] for i in range(3 * m)]
            answer = unit_decide(clauses + units)
            assert answer == (pair_value(mix, assignment) == address)
            checks += 1
            if answer:
                accepted = True
                break
        assert accepted == (address in expected)
    return checks


def seven_value(mix, assignment):
    phases = [(row & assignment).bit_count() & 1 for row in mix]
    digits = [pack(phases[i:i + 3]) for i in range(0, len(phases), 3)]
    return sum(0 if digit == 7 else 1 << (7 * i + digit) for i, digit in enumerate(digits))


def seven_polynomial(mix):
    records = []
    for block in range(len(mix) // 3):
        for indicator in range(7):
            terms = {0}
            for i, row in enumerate(mix[3 * block:3 * block + 3]):
                factors = [1 << j for j in range(len(mix)) if row >> j & 1]
                if not indicator >> i & 1:
                    factors.append(0)
                expanded = set()
                for old, new in product(terms, factors):
                    expanded.symmetric_difference_update({old | new})
                terms = expanded
            records.extend((tuple(j for j in range(len(mix)) if p >> j & 1), 1 << (7 * block + indicator))
                           for p in terms)
    return canonical(records)


def isolated_key(key, blocks):
    result = 0
    for block in range(blocks):
        bits = (key >> (6 * block)) & 63
        result |= (bits | ((bits.bit_count() & 1) << 6)) << (7 * block)
    return result


def verify_seven(rng):
    family = [path_mix(3 * m) for m in (1, 2, 3)] + [dense_mix(6)]
    stats = dict(maps=0, witness_assignments=0, image_shifts=0, small_covers=0, code_isolations=0,
                 packed_contexts=0, packed_pins=0)
    for mix in family:
        m = len(mix) // 3
        k = 7 * m
        assert rank(mix) == 3 * m
        terms = seven_polynomial(mix)
        masks = [(sum(1 << j for j in edge), v) for edge, v in terms.items()]
        support = {seven_value(mix, x) for x in range(1 << (3 * m))}
        assert len(support) == 8 ** m
        for x in range(1 << (3 * m)):
            value = 0
            for mask, label in masks:
                if x & mask == mask:
                    value ^= label
            assert value == seven_value(mix, x)
            stats['witness_assignments'] += 1
        triples = [edge for edge in terms if len(edge) == 3]
        for chosen in combinations(range(3 * m), m - 1):
            assert any(set(chosen).isdisjoint(edge) for edge in triples)
            stats['small_covers'] += 1
        for _ in range(240):
            shift = rng.randrange(1, 1 << k)
            assert any((x ^ shift) not in support for x in support)
            stats['image_shifts'] += 1
            b = isolated_key(rng.getrandbits(6 * m), m)
            assert {b ^ x for x in support if all(((b ^ x) >> (7 * i) & 127).bit_count() % 2 == 0
                                                 for i in range(m))} == {b}
            stats['code_isolations'] += 1
        stats['maps'] += 1

    k = 7
    size, _ell, j, r, *_ = params(k)
    mix = path_mix(3)
    terms = seven_polynomial(mix)
    program = slot_program(k, j, terms)
    local = (r - 1) // 6
    order = list(range(k * j))
    for _ in range(32):
        selectors = [0] * (k * r)
        code_data = [rng.randrange(2) for _ in range(64)]
        table = [0] * size
        for i, bit in enumerate(code_data):
            table[isolated_key(i, 1)] = bit
        key = 0
        for i in range(6):
            source = [rng.randrange(2) for _ in range(local)]
            selectors[r * i:r * i + local] = source
            selectors[6 * r + i * local:6 * r + (i + 1) * local] = source
            key |= (sum(source) & 1) << i
        for i in range(k):
            selectors[(i + 1) * r - 1] = terms.get((), 0) >> i & 1
        program_word, _, _, witness = packed_cubic(k, table, selectors, order, program)
        cnf = parse(program_word)
        b = isolated_key(key, 1)
        any_accept = False
        for x in range(8):
            pins = [[witness(i + 1) if x >> i & 1 else -witness(i + 1)] for i in range(3)]
            ok = unit_decide(cnf + pins)
            assert ok == bool(table[b ^ seven_value(mix, x)])
            any_accept |= ok
            stats['packed_pins'] += 1
        assert any_accept == bool(code_data[key])
        stats['packed_contexts'] += 1
    print(json.dumps(stats), flush=True)


def controls():
    rng = Random(870016)
    mixes = [path_mix(m) for m in range(1, 5)] + [dense_mix(m) for m in (2, 4)]
    for m in range(2, 5):
        rows = list(path_mix(m))
        for _ in range(3 * m):
            a, b = rng.sample(range(m), 2)
            rows[a] ^= rows[b]
        mixes.append(tuple(rows))
    counts = dict(maps=0, masks_checked=0, period_shifts_checked=0, coordinate_kernel_checks=0,
                  cover_checks=0, packed_pins=0, affine_restriction_rows=0)
    for mix in mixes:
        m = len(mix)
        assert rank(mix) == m
        support = canonical_support(m)
        truth = [pair_value(mix, x) for x in range(1 << (3 * m))]
        assert set(truth) == support
        coefficients = [(pack(i in edge for i in range(3 * m)), v)
                        for edge, v in canonical(pair_polynomial(mix)).items()]
        for x, y in enumerate(truth):
            value = 0
            for exponents, v in coefficients:
                if x & exponents == exponents:
                    value ^= v
            assert value == y
        counts['masks_checked'] += len(truth)
        fixed = [truth[((1 << m) - 1) | (x << m)] for x in range(1 << (2 * m))]
        assert set(fixed) == support
        counts['affine_restriction_rows'] += len(fixed)
        assert all(any(x ^ d not in support for x in support) for d in range(1, 1 << (2 * m)))
        counts['period_shifts_checked'] += (1 << (2 * m)) - 1
        for keep in range(1 << (3 * m)):
            values = set()
            x = keep
            while True:
                values.add(truth[x])
                if not x:
                    break
                x = (x - 1) & keep
            assert (values == support) == (keep == (1 << (3 * m)) - 1)
            counts['coordinate_kernel_checks'] += 1
        triples = [edge for edge in canonical(pair_polynomial(mix)) if len(edge) == 3]
        assert cover(triples, m - 1) is None and cover(triples, m) is not None
        for h in combinations(range(3 * m), m - 1):
            assert any(set(h).isdisjoint(edge) for edge in triples)
            counts['cover_checks'] += 1
        counts['maps'] += 1
    for mix in (path_mix(3), dense_mix(4)):
        counts['packed_pins'] += verify_packed(mix, rng)
    print(json.dumps(counts), flush=True)
    verify_seven(rng)


if __name__ == '__main__':
    if argv[1] == 'table':
        table_cases()
    elif argv[1] == 'controls':
        controls()
    else:
        raise ValueError('expected table or controls')
