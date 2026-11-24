"""Choose the primary partition, linked ports, and regional formulas in one SAT call."""

from regional_synthesis import RegionalSolution, _bits
from cograph_formulas import CographFormula
from pysat.card import CardEnc
from pysat.formula import IDPool
from pysat.solvers import Solver


def synthesize_partition(n, ports, labels, *, input_limit=None, solver='g4', on_unsat=None):
    """Solve ordered primary partitions, optionally selecting a subset of the inputs.

    An UNSAT callback receives the variable count, clauses, and solver proof trace.
    """
    ports = tuple(ports)
    if n < 1 or not ports or ports[0] or any(count < 0 for count in ports):
        raise ValueError('expected inputs and nonnegative port counts beginning with zero')
    if any(row < 0 or row >= 1 << n for row in labels):
        raise ValueError('label outside the primary-input domain')
    if input_limit is not None and not 0 <= input_limit <= n:
        raise ValueError('input limit outside the primary-input domain')

    pool = IDPool()
    clauses = []
    rows = tuple(sorted(labels))
    assignment = [tuple(pool.id(('region', i, leaf)) for leaf in range(n)) for i in range(len(ports))]
    cardinality = CardEnc.equals if input_limit is None else CardEnc.atmost
    for choices in zip(*assignment):
        clauses.extend(cardinality(choices, 1, vpool=pool).clauses)
    if input_limit is not None:
        selected = [pick for region in assignment for pick in region]
        clauses.extend(CardEnc.atmost(selected, input_limit, vpool=pool).clauses)
    outputs = [{row: pool.id(('out', i, row)) for row in rows} for i in range(len(ports))]
    readers = [[] for _ in ports[:-1]]
    encodings, wiring = [], []
    cuts = tuple((a, b, a & ~b) for a in rows if labels[a] for b in rows if not labels[b])

    for i, count in enumerate(ports):
        if count < 2:
            clauses.append(list(assignment[i]))
        values, sources = [], []
        for slot in range(count):
            picks = [pool.id(('source', i, slot, src)) for src in range(i)]
            clauses.extend(CardEnc.equals(picks, 1, vpool=pool).clauses)
            port = {row: pool.id(('port', i, slot, row)) for row in rows}
            for src, pick in enumerate(picks):
                readers[src].append(pick)
                for row in rows:
                    wire = outputs[src][row]
                    clauses.extend(([-pick, -port[row], wire], [-pick, port[row], -wire]))
            values.append(port)
            sources.append(picks)

        active = assignment[i] + (True,) * count
        out = outputs[i]
        encoding = CographFormula(n + count, pool, i, clauses)
        for row in rows:
            leaves = tuple(bool(row >> leaf & 1) for leaf in range(n)) + tuple(port[row] for port in values)
            if i == len(ports) - 1:
                encoding.require(row, leaves, bool(labels[row]), active=active)
            else:
                encoding.require(row, leaves, True, guard=out[row], active=active)
                encoding.require(row, leaves, False, guard=-out[row], active=active)
        if i != len(ports) - 1:
            for a, b, difference in cuts:
                outside = [region[bit.bit_length() - 1] for bit in _bits(difference)
                           for j, region in enumerate(assignment) if j != i]
                clauses.extend(([*outside, out[a]], [*outside, -out[b]]))
        encodings.append(encoding)
        wiring.append(sources)

    for used in readers:
        if len(used) < 2:
            if on_unsat is None:
                return None
            clauses.append([])
        else:
            clauses.extend(CardEnc.atleast(used, 2, vpool=pool).clauses)
    with Solver(name=solver, bootstrap_with=clauses, with_proof=on_unsat is not None) as sat:
        if not sat.solve():
            if on_unsat is not None:
                on_unsat(pool.top, clauses, sat.get_proof())
            return None
        model = set(sat.get_model())

    primary = [tuple(i for i, pick in enumerate(region) if pick in model) for region in assignment]
    groups = tuple(sum(1 << leaf for leaf in region) for region in primary)
    formulas = tuple(encoding.decode(model, (*leaves, *range(n, n + count)))
                     for encoding, leaves, count in zip(encodings, primary, ports))
    providers = tuple(tuple(next(src for src, pick in enumerate(slot) if pick in model) for slot in region)
                      for region in wiring)
    return RegionalSolution(groups, formulas, providers)
