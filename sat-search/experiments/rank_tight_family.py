"""Explicit certificate minors for the guarded rank-tight circuit family."""

from certificate_rank import intersection_matrix, modular_rank
from synthesis_cases import Builder


def guarded_family(excess):
    """Return the circuit and 3e-1 positive and negative certificate witnesses."""
    if excess < 1:
        raise ValueError('expected positive excess')
    n = 6 * excess + 1
    builder = Builder(n)
    next_input = 1

    def wrap(wire):
        nonlocal next_input
        a, b, c = range(next_input, next_input + 3)
        next_input += 3
        gated = builder.gate(0, a, builder.gate(1, c, wire))
        return builder.gate(1, b, gated), tuple(1 << i for i in (a, b, c))

    terminals = [0] * excess
    inner = [None] * (excess - 1)
    for j in range(excess - 2, -1, -1):
        terminals[j], inner[j] = wrap(terminals[j + 1])
    outer = [wrap(wire) for wire in terminals]
    right, right_atoms = wrap(terminals[0])
    circuit = builder.finish(builder.gate(1, builder.fold(0, (wire for wire, _ in outer)), right))
    if next_input != n:
        raise RuntimeError('inconsistent guarded construction')

    def positive(direct, follow=None, *, right_side=False):
        if right_side:
            support = right_atoms[0]
        else:
            support = sum(atoms[0 if j in direct else 1] for j, (_, atoms) in enumerate(outer))
        demanded = set(direct)
        for j in range(excess):
            if j not in demanded:
                continue
            if j == excess - 1:
                support |= 1
            elif j == follow:
                support |= inner[j][0]
                demanded.add(j + 1)
            else:
                support |= inner[j][1]
        return support

    def zero_path(start, end):
        support = sum(inner[j][1] | inner[j][2] for j in range(start, end))
        return support | (1 if end == excess - 1 else inner[end][0] | inner[end][1])

    def negative(j, direct, chain):
        a, b, c = outer[j][1]
        ar, br, cr = right_atoms
        left = b | c | zero_path(j, j) if direct else a | b
        right = br | cr | zero_path(0, j) if chain else ar | br
        return left | right

    p = [positive({0}), positive({0}, right_side=True)]
    z = [negative(0, True, False), negative(0, False, True)]
    for j in range(1, excess):
        p.extend((positive({j - 1}, j - 1), positive({j}), positive({j - 1, j}, j - 1)))
        z.extend((negative(j, False, True), negative(j, True, False), negative(j, True, True)))
    bypass = positive(set())
    essential_terms = [bypass, right_atoms[1], right_atoms[0] | right_atoms[2]]
    for _, (a, b, c) in outer:
        essential_terms.append((bypass ^ b) | a | c)
    for j, (a, b, c) in enumerate(inner):
        essential_terms.append((positive({j}) ^ b) | a | c)
    return n, circuit, tuple(p), tuple(z), tuple(essential_terms)


def verify_minor(excess):
    n, circuit, positive, zeros, additional = guarded_family(excess)
    full = (1 << n) - 1

    def value(mask):
        wires = [bool(mask >> i & 1) for i in range(n)]
        for op, a, b in circuit.gates:
            wires.append(wires[a] | wires[b] if op else wires[a] & wires[b])
        return wires[circuit.output]

    primal_support = 0
    for high, terms in ((True, (*positive, *additional)), (False, zeros)):
        for term in terms:
            if high:
                primal_support |= term
            row = term if high else full ^ term
            if value(row) != high or any(value(row ^ (1 << i)) == high for i in range(n) if term >> i & 1):
                raise AssertionError((excess, high, term))
    if len(circuit.gates) != 7 * excess:
        raise AssertionError('unexpected size')
    if primal_support != full:
        raise AssertionError('essentiality witnesses do not cover all inputs')
    rank = modular_rank(intersection_matrix(positive, zeros), 2)
    if rank != 3 * excess - 1:
        raise AssertionError((excess, rank))
    return rank
