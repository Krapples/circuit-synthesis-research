"""Construct a fixed-occurrence witness from a small supported regional formula."""

from collections import Counter
from functools import reduce
from operator import or_

from packed_regional_tables import PackedTables
from two_sharing_core import ANY, assignments


def absorption_witness(m, ports, patterns, targets, signed, solve_core, stats):
    """Use a spare read of a retained port to absorb the unused leaves."""
    multiplicity = Counter(ports)
    if not any(count > 1 for count in multiplicity.values()):
        return None
    known = {pattern: table for pattern, table in zip(patterns, targets) if table != ANY}
    if not known:
        return None
    columns = PackedTables(m)
    support = reduce(or_, map(columns.support, known.values()), 0)
    private = tuple(i for i in range(m) if support >> i & 1)
    live = sum(1 << port for port in multiplicity)
    for port in sorted(multiplicity):
        reduced_mask = live ^ (1 << port)
        reduced = {}
        for pattern, table in known.items():
            if reduced.setdefault(pattern & reduced_mask, table) != table:
                break
        else:
            live, known = reduced_mask, reduced
    retained_ports = tuple(port for port in sorted(multiplicity) if live >> port & 1)
    carrier = next((port for port in retained_ports if multiplicity[port] > 1), None)
    if carrier is None or len(private) + len(retained_ports) > 7:
        return None
    if stats is not None:
        stats['absorption_trials'] += 1
    core_m = len(private)
    active_rows = assignments(private)
    pats, tables = zip(*known.items())
    targets = tuple(sum((table >> a & 1) << i for i, a in enumerate(active_rows)) for table in tables)
    core = solve_core(core_m, retained_ports, pats, targets, signed, stats)
    if core is None:
        return None

    rest = multiplicity - Counter(retained_ports)
    rest[carrier] -= 1
    unused = [('x', i, False) for i in range(m) if not support >> i & 1]
    unused.extend(('x', m + port, False) for port, count in rest.items() for _ in range(count))
    tail = reduce(lambda a, b: ('&', a, b), unused) if unused else None

    def lift(node):
        if node[0] != 'x':
            return node[0], lift(node[1]), lift(node[2])
        _, index, negate = node
        if index < core_m:
            return 'x', private[index], negate
        port = index - core_m
        literal = 'x', m + port, negate
        if port == carrier:
            return '|', literal, ('&', literal, tail) if tail is not None else literal
        return literal

    if stats is not None:
        stats['absorption_witnesses'] += 1
        stats['absorption_leaves_removed'] += m + len(ports) - core_m - len(retained_ports)
    return lift(core)
