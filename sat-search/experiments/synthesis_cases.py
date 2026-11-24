"""Deterministic small monotone and partial-function benchmark corpus."""

from dataclasses import dataclass
from itertools import combinations
from random import Random


@dataclass(frozen=True)
class Witness:
    gates: tuple
    output: int


@dataclass(frozen=True)
class Case:
    name: str
    family: str
    n: int
    known: int
    truth: int
    witness: Witness

    def labels(self):
        return {x: bool(self.truth >> x & 1) for x in range(1 << self.n) if self.known >> x & 1}


def full_rows(n):
    return (1 << (1 << n)) - 1


def truth_table(n, witness):
    """Independent bit-parallel verifier for the serialized circuit."""
    wires = [sum(1 << row for row in range(1 << n) if row >> bit & 1) for bit in range(n)]
    for op, left, right in witness.gates:
        if not 0 <= left <= right < len(wires) or op not in (0, 1, 2) or (op == 2) != (left == right):
            raise ValueError('invalid circuit gate')
        a, b = wires[left], wires[right]
        wires.append(a & b if op == 0 else a | b if op == 1 else full_rows(n) ^ a)
    if not 0 <= witness.output < len(wires):
        raise ValueError('invalid circuit output')
    return wires[witness.output]


def trim(n, witness):
    mapping = {i: i for i in range(n)}
    gates = []

    def visit(wire):
        if wire not in mapping:
            op, a, b = witness.gates[wire - n]
            left, right = sorted((visit(a), visit(b)))
            mapping[wire] = n + len(gates)
            gates.append((op, left, right))
        return mapping[wire]

    output = visit(witness.output)
    return Witness(tuple(gates), output)


class Builder:
    def __init__(self, n):
        self.n = n
        self.gates = []
        self.memo = {}

    def gate(self, op, a, b):
        if a == b:
            return a
        key = op, min(a, b), max(a, b)
        if key not in self.memo:
            self.memo[key] = self.n + len(self.gates)
            self.gates.append(key)
        return self.memo[key]

    def fold(self, op, wires):
        iterator = iter(wires)
        output = next(iterator)
        for wire in iterator:
            output = self.gate(op, output, wire)
        return output

    def finish(self, output):
        return trim(self.n, Witness(tuple(self.gates), output))


def dnf(n, terms):
    terms = set(terms)
    terms = sorted(t for t in terms if not any(u != t and u & t == u for u in terms))
    b = Builder(n)
    groups = [b.fold(0, (i for i in range(n) if mask >> i & 1)) for mask in terms]
    return b.finish(b.fold(1, groups))


def threshold(n, k):
    b = Builder(n)
    previous = [0]
    for x in range(1, n):
        current = [b.gate(1, previous[0], x)]
        for j in range(1, min(k, x + 1)):
            raised = b.gate(0, previous[j - 1], x)
            current.append(b.gate(1, previous[j], raised) if j < len(previous) else raised)
        previous = current
    return b.finish(previous[k - 1])


def boundary_labels(n, labels):
    """Delete monotone-redundant labels, including on partial domains."""
    pos = [x for x, high in labels.items() if high]
    neg = [x for x, high in labels.items() if not high]
    return {**{x: True for x in pos if not any(y != x and y & x == y for y in pos)},
            **{x: False for x in neg if not any(y != x and x & y == x for y in neg)}}


def essential(n, labels):
    return sum(any(x ^ (1 << i) in labels and labels[x ^ (1 << i)] != high for x, high in labels.items())
               for i in range(n))


def corpus():
    rng = Random(20261124)
    cases, seen = [], set()

    def add(name, family, n, witness, known=None):
        if known is None:
            known = full_rows(n)
        table = truth_table(n, witness) & known
        key = n, known, table
        if key in seen:
            return False
        item = Case(name, family, n, known, table, witness)
        if essential(n, item.labels()) != n:
            return False
        seen.add(key)
        cases.append(item)
        return True

    def sample(family, widths, make):
        for i, n in enumerate(widths, 1):
            for _ in range(2000):
                if add(f'{family}-{i:02d}', family, n, make(n)):
                    break
            else:
                raise RuntimeError(f'could not generate {family} case {i}')

    def fixed(name, family, n, witness):
        if not add(name, family, n, witness):
            raise RuntimeError(f'duplicate or inessential fixed case {name}')

    def hypergraph(n):
        candidates = [sum(1 << v for v in edge) for edge in combinations(range(n), 3)]
        return dnf(n, rng.sample(candidates, rng.randint(2, min(len(candidates), n + 1))))

    sample('hypergraph', (4, 5, 6, 7, 8) * 4 + (5, 6, 7, 8), hypergraph)
    for n in range(4, 9):
        for k in (3 if n == 4 else n // 2 + 1, n):
            fixed(f'threshold-{n}-{k}', 'threshold', n, threshold(n, k))

    def random_terms(n):
        return dnf(n, rng.sample(range(1, 1 << n), rng.randint(3, n + 2)))

    def read_once(n):
        b = Builder(n)
        wires = list(range(n))
        while len(wires) > 1:
            a = wires.pop(rng.randrange(len(wires)))
            c = wires.pop(rng.randrange(len(wires)))
            wires.append(b.gate(rng.randrange(2), a, c))
        return b.finish(wires[0])

    def random_circuit(n):
        b = Builder(n)
        output = b.gate(rng.randrange(2), 0, 1)
        for j in range(2, n + 5):
            a = j if j < n else rng.randrange(n + len(b.gates))
            c = rng.randrange(n + len(b.gates))
            branch = b.gate(rng.randrange(2), a, c)
            output = b.gate(rng.randrange(2), output, branch)
        return b.finish(output)

    def comparator_output(n):
        b = Builder(n)
        lines = list(range(n))
        for _ in range(rng.randint(n, 3 * n)):
            a, c = sorted(rng.sample(range(n), 2))
            lines[a], lines[c] = b.gate(0, lines[a], lines[c]), b.gate(1, lines[a], lines[c])
        return b.finish(rng.choice(lines))

    widths = (4, 5, 6, 7, 8) * 2
    for n in range(4, 8):
        fixed(f'complete-{n}', 'graph', n, threshold(n, 2))
    for p, q in ((2, 2), (2, 3), (3, 3), (4, 4)):
        b = Builder(p + q)
        output = b.gate(0, b.fold(1, range(p)), b.fold(1, range(p, p + q)))
        fixed(f'bipartite-{p}-{q}', 'graph', p + q, b.finish(output))
    sample('graph', (5, 6, 7), lambda n: dnf(n, [a | b for a, b in
           rng.sample(list(combinations((1 << i for i in range(n)), 2)), n + 1)]))
    for n, cycle in ((4, False), (5, True)):
        terms = [(1 << i) | (1 << (i + 1)) for i in range(n - 1)]
        fixed(f'{"cycle" if cycle else "path"}-{n}', 'graph', n, dnf(n, terms + ([1 | (1 << (n - 1))] if cycle else [])))
    edges = [(i, (i + 1) % 5) for i in range(5)] + [(i + 5, (i + 2) % 5 + 5) for i in range(5)] + [(i, i + 5) for i in range(5)]
    fixed('petersen-10', 'graph', 10, dnf(10, ((1 << a) | (1 << b) for a, b in edges)))

    sample('random-monotone', widths, random_terms)
    sample('read-once', widths, read_once)
    sample('generated', widths + (5, 6), random_circuit)
    sample('comparator', widths, comparator_output)

    sources = tuple(cases)
    for i, n in enumerate(widths, 1):
        for _ in range(2000):
            original = rng.choice([c for c in sources if c.n == n])
            rows = set(rng.sample(range(1 << n), rng.randint(1, 1 << (n - 2))))
            for bit in range(n):
                a = rng.choice([x for x in range(1 << n) if not x >> bit & 1 and
                                (original.truth >> x ^ original.truth >> (x | (1 << bit))) & 1])
                rows.update((a, a | (1 << bit)))
            known = sum(1 << x for x in rows)
            if known != full_rows(n) and add(f'partial-{i:02d}', 'partial', n, original.witness, known):
                break
        else:
            raise RuntimeError(f'could not generate partial case {i}')
    return cases
