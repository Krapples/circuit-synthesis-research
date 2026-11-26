"""Build and check signed AIGs for sparse rank certificates and sorted joins."""

import json
from dataclasses import dataclass
from itertools import product
from random import Random
from sys import argv

from sat_weight_slice_check import bitonic


def width(size):
    return max(1, (size - 1).bit_length())


def word(value, bits):
    return tuple((value >> bit) & 1 for bit in range(bits))


class Aig:
    def __init__(self):
        self.inputs = 0
        self.gates = []
        self.memo = {}

    def input_word(self, bits):
        assert not self.gates
        result = tuple(2 * i for i in range(self.inputs + 1, self.inputs + bits + 1))
        self.inputs += bits
        return result

    def and_(self, a, b):
        if a == 0 or b == 0 or a == b ^ 1:
            return 0
        if a == 1 or a == b:
            return b
        if b == 1:
            return a
        key = tuple(sorted((a, b)))
        if key not in self.memo:
            self.gates.append(key)
            self.memo[key] = 2 * (self.inputs + len(self.gates))
        return self.memo[key]

    def or_(self, a, b):
        return self.and_(a ^ 1, b ^ 1) ^ 1

    def xor(self, a, b):
        return self.or_(self.and_(a, b ^ 1), self.and_(a ^ 1, b))

    def any(self, bits):
        result = 0
        for bit in bits:
            result = self.or_(result, bit)
        return result

    def eq(self, a, b):
        return self.any(self.xor(x, y) for x, y in zip(a, b)) ^ 1

    def lt(self, a, b):
        result = 0
        for x, y in zip(a, b):
            result = self.or_(self.and_(x ^ 1, y), self.and_(self.xor(x, y) ^ 1, result))
        return result

    def mask(self, enable, bits):
        return tuple(self.and_(enable, bit) for bit in bits)

    def select(self, choose, yes, no):
        return tuple(y if y == n else self.or_(self.and_(choose, y), self.and_(choose ^ 1, n))
                     for y, n in zip(yes, no))

    def sort(self, records, key):
        if not records:
            return []
        count = len(records)
        size = 1 << (count - 1).bit_length()
        array = [r + (0,) for r in records]
        array.extend([(0,) * len(records[0]) + (1,)] * (size - count))
        for high, low in bitonic(size):
            a, b = array[high], array[low]
            move = self.lt(key(a[:-1]) + a[-1:], key(b[:-1]) + b[-1:])
            array[high] = self.select(move, b, a)
            array[low] = self.select(move, a, b)
        return [r[:-1] for r in reversed(array[size - count:])]

    def live_count(self, outputs):
        pending = list(outputs)
        seen = set()
        while pending:
            node = pending.pop() // 2
            if node > self.inputs and node not in seen:
                seen.add(node)
                pending.extend(self.gates[node - self.inputs - 1])
        return len(seen)

    def evaluate(self, assignments, outputs):
        mask = (1 << len(assignments)) - 1
        values = [0] + [sum(((row >> i) & 1) << j for j, row in enumerate(assignments))
                        for i in range(self.inputs)]

        def read(literal):
            return values[literal // 2] ^ (mask if literal & 1 else 0)

        for a, b in self.gates:
            values.append(read(a) & read(b))
        columns = [read(bit) for bit in outputs]
        return [tuple((col >> i) & 1 for col in columns) for i in range(len(assignments))]


@dataclass(frozen=True)
class BasisEntry:
    active: int
    pivot: tuple
    residual: tuple
    original: tuple
    tag: tuple


class Basis:
    """Fixed-capacity insertion-ordered basis, with a retained original tag."""

    def __init__(self, aig, dimension, limit, tag_bits):
        self.aig = aig
        empty = BasisEntry(0, (0,) * dimension, (0,) * dimension,
                           (0,) * dimension, (0,) * tag_bits)
        self.entries = [empty] * limit

    def add(self, vector, tag, enabled=1, reset=0):
        a = self.aig
        remainder = vector
        old = []
        for e in self.entries:
            active = a.and_(e.active, reset ^ 1)
            old.append(active)
            # A one-hot pivot selects a single coordinate, so OR suffices.
            eliminate = a.and_(active, a.any(a.and_(x, p) for x, p in zip(remainder, e.pivot)))
            remainder = tuple(a.xor(x, y) for x, y in zip(remainder, a.mask(eliminate, e.residual)))
        choose = a.and_(enabled, a.any(remainder))
        prefix = 0
        pivot = []
        for bit in remainder:
            pivot.append(a.and_(bit, prefix ^ 1))
            prefix = a.or_(prefix, bit)
        for i, (e, active) in enumerate(zip(self.entries, old)):
            insert = a.and_(choose, active ^ 1)
            choose = a.and_(choose, active)
            self.entries[i] = BasisEntry(
                a.or_(active, insert), a.select(insert, pivot, e.pivot),
                a.select(insert, remainder, e.residual), a.select(insert, vector, e.original),
                a.select(insert, tag, e.tag))


def combine(aig, left, right):
    return tuple(aig.or_(x, y) for x, y in zip(left, right))


def select_columns_and_rows(aig, columns, rows, dimension, limit, tag_bits):
    """Rows on the original selected columns give the square minor."""
    row_basis = Basis(aig, limit, limit, tag_bits)
    for candidate in range(dimension):
        vector = tuple(aig.and_(e.active, e.original[candidate]) for e in columns.entries)
        tag = word(candidate, tag_bits) if rows is None else rows[candidate]
        row_basis.add(vector, tag)
    return row_basis.entries


def rank_level(aig, records, row_bits, column_bits, level, limit, root):
    """One sort, a forward per-column/segment scan and a backward segment scan."""
    if not records:
        return [], (0,) * (limit * (1 + row_bits + column_bits))
    a = aig
    slot_bits = width(limit)
    first_slot = 1 + row_bits + column_bits

    def fields(record):
        return record[0], record[1:1 + row_bits], record[1 + row_bits:first_slot], record[first_slot:]

    def key(record):
        active, row, col, _ = fields(record)
        return col + row[level:] + (active ^ 1,)

    ordered = a.sort(records, key)
    active, rows, cols, slots = (list(x) for x in zip(*(fields(r) for r in ordered)))
    candidates = [(slot + (row[level - 1],)) if level else (0,)
                  for row, slot in zip(rows, slots)]
    dimension = (1 << (slot_bits + 1)) if level else 1
    tag_bits = len(candidates[0])
    same_group = [a.and_(next_active, a.eq(left[level:], right[level:]))
                  for next_active, left, right in zip(active[1:], rows, rows[1:])] + [0]
    same_column = [a.and_(group, a.eq(left, right))
                   for group, left, right in zip(same_group, cols, cols[1:])] + [0]
    col_basis = Basis(a, dimension, limit, column_bits)
    column = (0,) * dimension
    group_rows = [(0,) * row_bits] * dimension
    events = []
    certificates = (0,) * (limit * (1 + row_bits + column_bits))
    for i, live in enumerate(active):
        new_group = same_group[i - 1] ^ 1 if i else 1
        new_column = same_column[i - 1] ^ 1 if i else 1
        end = a.and_(live, same_group[i] ^ 1)
        col_end = a.and_(live, same_column[i] ^ 1)
        hits = [a.and_(live, a.eq(candidates[i], word(j, tag_bits))) for j in range(dimension)]
        column = tuple(a.xor(x, y) for x, y in zip(a.mask(new_column ^ 1, column), hits))
        col_basis.add(column, cols[i], col_end, new_group)
        if root:
            group_rows = [a.select(hit, rows[i], old) for hit, old in zip(hits, group_rows)]
        selected = select_columns_and_rows(a, col_basis, group_rows if root else None,
                                           dimension, limit, row_bits if root else tag_bits)
        if root:
            pair = tuple(bit for row, col in zip(selected, col_basis.entries)
                         for bit in (row.active,) + a.mask(row.active, row.tag + col.tag))
            certificates = combine(a, certificates, a.mask(end, pair))
        else:
            summary = tuple(bit for e in selected for bit in (e.active,) + e.tag)
            events.append((end, summary))
    if root:
        return [], certificates

    summary = (0,) * (limit * (1 + tag_bits))
    updated = []
    for i in reversed(range(len(ordered))):
        end, new_summary = events[i]
        summary = a.select(end, new_summary, summary)
        stride = 1 + tag_bits
        matched = [a.and_(summary[j], a.eq(candidates[i], summary[j + 1:j + stride]))
                   for j in range(0, len(summary), stride)]
        slot = tuple(a.any(flag for j, flag in enumerate(matched) if j >> b & 1)
                     for b in range(slot_bits))
        updated.append((a.and_(active[i], a.any(matched)),) + rows[i] + cols[i] + slot)
    return list(reversed(updated)), certificates


def sparse_certificate(aig, inputs, nr, nc, limit):
    rb, cb = width(nr), width(nc)
    records = tuple((aig.and_(on, bit),) + row + col + (0,) * width(limit)
                    for on, bit, row, col in inputs)
    gates_at_level = []
    final = (nr - 1).bit_length()
    for level in range(final + 1):
        before = len(aig.gates)
        records, result = rank_level(aig, records, rb, cb, level, limit, level == final)
        gates_at_level.append(len(aig.gates) - before)
    return result, gates_at_level


def dense_certificate(aig, inputs, nr, nc, limit):
    """Same input and certificate, with a direct record-to-cell decoder."""
    rbits, cbits = width(nr), width(nc)
    basis = Basis(aig, nr, limit, cbits)
    live = [(aig.and_(on, bit), row, col) for on, bit, row, col in inputs]
    decoded_rows = [[aig.and_(on, aig.eq(row, word(i, rbits))) for i in range(nr)]
                    for on, row, _ in live]
    for j in range(nc):
        hits = [aig.eq(col, word(j, cbits)) for _, _, col in live]
        vector = [0] * nr
        for hit, row in zip(hits, decoded_rows):
            vector = [aig.xor(x, y) for x, y in zip(vector, aig.mask(hit, row))]
        basis.add(tuple(vector), word(j, cbits))
    rows = select_columns_and_rows(aig, basis, None, nr, limit, rbits)
    return tuple(bit for row, col in zip(rows, basis.entries)
                 for bit in (row.active,) + aig.mask(row.active, row.tag + col.tag))


def sorted_join(a, table, queries):
    """Fixed dense table and variable query labels. Out-of-range queries get zero."""
    if not queries:
        return ()
    label_bits, payload_bits, tag_bits = len(queries[0]), len(table[0]), width(len(queries))
    data = [payload + (0,) * tag_bits + (0,) + word(i, label_bits)
            for i, payload in enumerate(table)]
    requests = [(0,) * payload_bits + word(i, tag_bits) + (1,) + label for i, label in enumerate(queries)]
    ordered = a.sort(data + requests, lambda record: record[payload_bits + tag_bits:])
    last_value = (0,) * payload_bits
    last_key = (0,) * label_bits
    valid = 0
    answers = []
    for r in ordered:
        requested = r[payload_bits + tag_bits]
        key = r[-label_bits:]
        valid = a.or_(valid, requested ^ 1)
        last_value = a.select(requested, last_value, r[:payload_bits])
        last_key = a.select(requested, last_key, key)
        hit = a.and_(valid, a.eq(key, last_key))
        answers.append(a.mask(hit, last_value) + r[payload_bits:payload_bits + tag_bits] + (requested ^ 1,))
    restored = a.sort(answers, lambda record: record[payload_bits:])
    return tuple(bit for r in restored[:len(queries)] for bit in r[:payload_bits])


def xor_by_label(a, records, alphabet_size, payload_bits, label_bits):
    """Scatter variable records by XOR, including default-zero table slots."""
    marked = [payload + (0,) + label for label, payload in records]
    marked.extend((0,) * payload_bits + (1,) + word(i, label_bits) for i in range(alphabet_size))
    sorted_records = a.sort(marked, lambda r: r[payload_bits:])
    total = (0,) * payload_bits
    last = (0,) * label_bits
    output = []
    for r in sorted_records:
        label = r[-label_bits:]
        total = a.mask(a.eq(last, label), total)
        total = tuple(a.xor(x, y) for x, y in zip(total, r[:payload_bits]))
        output.append(total + label + (r[payload_bits] ^ 1,))
        last = label
    restored = a.sort(output, lambda r: r[payload_bits:])
    return tuple(r[:payload_bits] for r in restored[:alphabet_size])


def polar_constraints(a, witness_rows, monomials, outputs):
    """Compute every column of the common polar constraint matrix L.

    Monomials are (left endpoint, right endpoint, vector coefficient).
    A repeated endpoint or zero coefficient contributes zero to the polar form.
    """
    queries = [endpoint for u, v, _ in monomials for endpoint in (u, v)]
    pulled = sorted_join(a, witness_rows, queries)
    count = len(witness_rows[0])
    records = []
    for i, (u, v, coefficients) in enumerate(monomials):
        for j, label in enumerate((v, u)):
            local = pulled[(2 * i + j) * count:(2 * i + j + 1) * count]
            records.append((label, tuple(a.and_(bit, c) for bit in local for c in coefficients)))
    return xor_by_label(a, records, len(witness_rows), count * outputs, width(len(witness_rows)))


def rank(matrix):
    rows = list(matrix)
    result = 0
    while rows:
        pivot = max(rows)
        if not pivot:
            break
        rows.remove(pivot)
        high = 1 << (pivot.bit_length() - 1)
        rows = [x ^ pivot if x & high else x for x in rows]
        result += 1
    return result


def pack(bits):
    return sum(bit << i for i, bit in enumerate(bits))


def assignment(records, nr, nc):
    return pack(bit for on, value, i, j in records
                for bit in (on, value) + word(i, width(nr)) + word(j, width(nc)))


def build(nr, nc, cap, limit, sparse):
    a = Aig()
    inputs = [(a.input_word(1)[0], a.input_word(1)[0], a.input_word(width(nr)), a.input_word(width(nc)))
              for _ in range(cap)]
    if sparse:
        output, layers = sparse_certificate(a, inputs, nr, nc, limit)
    else:
        output, layers = dense_certificate(a, inputs, nr, nc, limit), []
    return a, output, layers


def check_outputs(evaluations, instances, nr, nc, limit):
    rb, cb = width(nr), width(nc)
    for state, records in zip(evaluations, instances):
        matrix = [0] * nr
        for on, bit, i, j in records:
            if on and bit:
                matrix[i] ^= 1 << j
        selected = []
        stride = 1 + rb + cb
        for i in range(0, len(state), stride):
            if state[i]:
                assert i == stride * len(selected)
                selected.append((pack(state[i + 1:i + 1 + rb]), pack(state[i + 1 + rb:i + stride])))
            else:
                assert not any(state[i:i + stride])
        ix, jx = zip(*selected) if selected else ((), ())
        assert len(ix) == len(set(ix)) == len(set(jx)) == min(limit, rank(matrix)), (records, state)
        minor = [pack(matrix[i] >> j & 1 for j in jx) for i in ix]
        assert rank(minor) == len(ix), (records, state)


def random_records(rng, nr, nc, cap):
    # Cluster some instances to force repeated columns, duplicate cancellations
    # and empty row intervals even when the sparse capacity is full.
    hot = [(rng.randrange(nr), rng.randrange(nc)) for _ in range(max(1, cap // 4))]
    result = []
    for _ in range(cap):
        i, j = rng.choice(hot) if rng.randrange(2) else (rng.randrange(nr), rng.randrange(nc))
        result.append((rng.randrange(4) != 0, rng.randrange(4) != 0, i, j))
    return result


def verify_rank(nr, nc, cap, limit, instances):
    result = dict(rows=nr, cols=nc, capacity=cap, threshold=limit, assignments=len(instances))
    packed = [assignment(x, nr, nc) for x in instances]
    for sparse in (True, False):
        a, output, layers = build(nr, nc, cap, limit, sparse)
        check_outputs(a.evaluate(packed, output), instances, nr, nc, limit)
        prefix = 'sparse' if sparse else 'dense'
        result[prefix + '_built_ands'] = len(a.gates)
        result[prefix + '_live_ands'] = a.live_count(output)
        if sparse:
            result['sparse_built_by_level'] = layers
    print(json.dumps(result), flush=True)


def verify_joins(rng):
    for q, requests, bits in ((1, 2, 1), (3, 1, 3), (3, 7, 3), (7, 5, 4), (16, 20, 5)):
        a = Aig()
        table = [a.input_word(bits) for _ in range(q)]
        queries = [a.input_word(width(q)) for _ in range(requests)]
        output = sorted_join(a, table, queries)
        assignments = list(range(1 << a.inputs)) if a.inputs <= 12 else [rng.getrandbits(a.inputs) for _ in range(400)]
        offset = q * bits
        for row, answer in zip(assignments, a.evaluate(assignments, output)):
            for j in range(requests):
                index = (row >> (offset + j * width(q))) & ((1 << width(q)) - 1)
                expected = (row >> (bits * index)) & ((1 << bits) - 1) if index < q else 0
                assert pack(answer[j * bits:(j + 1) * bits]) == expected
        print(json.dumps(dict(query_join=q, requests=requests, payload_bits=bits,
                              assignments=len(assignments), live_ands=a.live_count(output))), flush=True)


def verify_polar(rng):
    for q, slots, k, witnesses in ((2, 2, 1, 1), (3, 3, 2, 2), (5, 7, 3, 3), (9, 12, 2, 4)):
        a = Aig()
        rows = [a.input_word(witnesses) for _ in range(q)]
        pairs = [(a.input_word(width(q)), a.input_word(width(q)), a.input_word(k)) for _ in range(slots)]
        routed = polar_constraints(a, rows, pairs, k)
        output = tuple(bit for col in routed for bit in col)
        arguments = []
        if a.inputs <= 12:
            for row_bits in product(range(1 << witnesses), repeat=q):
                options = product(range(q), range(q), range(1 << k))
                arguments.extend((row_bits, terms) for terms in product(list(options), repeat=slots))
        else:
            for _ in range(360):
                row_bits = tuple(rng.randrange(1 << witnesses) for _ in range(q))
                terms = tuple((rng.randrange(q), rng.randrange(q), rng.randrange(1 << k)) for _ in range(slots))
                arguments.append((row_bits, terms))
        assignments = [pack(bit for field, bits in [(w, witnesses) for w in row_bits] +
                            [(field, bits) for u, v, c in terms for field, bits in
                             ((u, width(q)), (v, width(q)), (c, k))] for bit in word(field, bits))
                       for row_bits, terms in arguments]
        for (row_bits, terms), observed in zip(arguments, a.evaluate(assignments, output)):
            expected = [0] * q
            for u, v, c in terms:
                for i in range(witnesses):
                    if row_bits[u] >> i & 1:
                        expected[v] ^= c << (i * k)
                    if row_bits[v] >> i & 1:
                        expected[u] ^= c << (i * k)
            assert observed == tuple(bit for x in expected for bit in word(x, k * witnesses))
        print(json.dumps(dict(polar_variables=q, slots=slots, outputs=k, witnesses=witnesses,
                              assignments=len(arguments), live_ands=a.live_count(output))), flush=True)


def main(mode):
    rng = Random(870011)
    if mode == 'check':
        for nr, nc, cap, limit in ((1, 1, 0, 2), (1, 2, 3, 2), (2, 2, 3, 2), (3, 4, 2, 3)):
            values = list(product(range(2), range(2), range(nr), range(nc)))
            verify_rank(nr, nc, cap, limit, list(product(values, repeat=cap)))
        for nr, nc, cap, limit in ((4, 7, 7, 1), (5, 3, 9, 3), (8, 9, 17, 4), (3, 5, 4, 7)):
            planted = [(1, 1, i % nr, i % nc) for i in range(cap)]
            instances = [planted, [(0, 1, i, j) for _, _, i, j in planted]]
            instances += [random_records(rng, nr, nc, cap) for _ in range(240)]
            verify_rank(nr, nc, cap, limit, instances)
        verify_joins(rng)
        verify_polar(rng)
    elif mode == 'bench':
        for n in (8, 16, 32, 64):
            cap = n + 1
            verify_rank(n, n, cap, 2, [random_records(rng, n, n, cap) for _ in range(80)])
    else:
        raise ValueError('expected check or bench')


if __name__ == '__main__':
    main(argv[1])
