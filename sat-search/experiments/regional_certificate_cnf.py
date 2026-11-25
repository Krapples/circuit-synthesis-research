"""Exact CDCL completion of fixed monotone and free-NOT regional leaves."""

from collections import Counter
from itertools import islice
from time import perf_counter

from pysat.formula import IDPool
from pysat.solvers import Solver

from cograph_formulas import CographFormula
from regional_absorption import absorption_witness
from regional_deadline import cdcl_deadline
from regional_root_relaxation import minimal_masks
from two_sharing_core import tree


DEFAULT_SOLVER = 'maplechrono'
ANY = -1


def labeled_rows(m, ports, patterns, targets):
    labels = {}
    for pattern, table in zip(patterns, targets, strict=True):
        if table == ANY:
            continue
        base = sum(1 << (m + i) for i, provider in enumerate(ports) if pattern >> provider & 1)
        for assignment in range(1 << m):
            row = base | assignment
            high = bool(table >> assignment & 1)
            if labels.setdefault(row, high) != high:
                return None
    return tuple(sorted(labels.items()))


def _evaluate(cotree, columns):
    if isinstance(cotree, int):
        return columns[cotree]
    op, left, right = cotree
    a, b = _evaluate(left, columns), _evaluate(right, columns)
    return a | b if op else a & b


def _lift(cotree, leaves, flipped):
    if isinstance(cotree, int):
        return 'x', leaves[cotree], flipped[cotree]
    op, left, right = cotree
    return '|' if op else '&', _lift(left, leaves, flipped), _lift(right, leaves, flipped)


def _boundary(rows, width):
    """Keep minimal recorded ones and maximal recorded zeroes."""
    mask = (1 << width) - 1
    positive = minimal_masks(row for row, high in rows if high)
    negative = minimal_masks(mask ^ row for row, high in rows if not high)
    return tuple(sorted((*((row, True) for row in positive), *((mask ^ row, False) for row in negative))))


def anchored_clauses(graph, phase, m, ports, patterns, targets, signed):
    """Fix private phases and LCA operations from exact restricted read-once slices."""
    required = set()

    def learn(node, coordinates):
        if node[0] == 'x':
            _, var, negate = node
            position = coordinates[var]
            if signed:
                required.add(phase[position] if negate else -phase[position])
            return (position,)
        op, *children = node
        previous = ()
        for child in children:
            current = learn(child, coordinates)
            for a in previous:
                for b in current:
                    edge = graph.edge(a, b)
                    required.add(edge if op == '&' else -edge)
            previous += current
        return previous

    def accept(width, known, coordinates):
        if known in (0, (1 << (1 << width)) - 1):
            return True
        cotree = tree(width, known, signed)
        if cotree is None:
            return False
        learn(cotree, coordinates)
        return True

    coordinates = tuple(range(m))
    mask = sum(1 << provider for provider in set(ports))
    observed = {pattern & mask: target for pattern, target in zip(patterns, targets) if target != ANY}
    for target in set(observed.values()):
        if not accept(m, target, coordinates):
            return None
    # A singly read provider may stay free alongside the private variables.
    counts = Counter(ports)
    for i, provider in enumerate(ports):
        if counts[provider] != 1:
            continue
        bit = 1 << provider
        for pattern, table in observed.items():
            if not pattern & bit and pattern | bit in observed:
                combined = table | (observed[pattern | bit] << (1 << m))
                if not accept(m + 1, combined, (*coordinates, m + i)):
                    return None
    if any(-v in required for v in required):
        return None
    return tuple([v] for v in sorted(required))


def local_cnf(m, ports, patterns, targets, signed, stats=None, module_filter=True, *,
              eager=True, lazy_rows=False, anchored=False, absorb=False, solver_name=DEFAULT_SOLVER):
    """Solve an exact local query. Each occurrence gets its own vertex and phase."""
    start = perf_counter()
    if stats is not None:
        stats['certificate_calls'] += 1
    leaves = (*range(m), *(m + provider for provider in ports))
    if not leaves:
        return None
    rows = labeled_rows(m, ports, patterns, targets)
    if rows is None:
        return None
    if absorb:
        def solve_core(*args):
            return local_cnf(*args, eager=True, anchored=True, solver_name=solver_name)

        witness = absorption_witness(m, ports, patterns, targets, signed, solve_core, stats)
        if witness is not None:
            return witness
    if stats is not None:
        stats['certificate_rows_available'] += len(rows)
    if anchored and not signed:
        rows = _boundary(rows, len(leaves))
    pool, clauses = IDPool(), []
    graph = CographFormula(len(leaves), pool, 'local', clauses, eager=eager)
    phase = tuple(pool.id(('phase', i)) for i in range(len(leaves))) if signed else ()
    if anchored and m <= 8:
        constraints = anchored_clauses(graph, phase, m, ports, patterns, targets, signed)
        if stats is not None:
            stats['certificate_anchors'] += len(constraints) if constraints is not None else 0
        if constraints is None:
            if stats is not None:
                stats['certificate_anchor_rejects'] += 1
                stats['certificate_encode_seconds'] += perf_counter() - start
            return None
        clauses.extend(constraints)
    row_columns = tuple(sum((row >> i & 1) << j for j, (row, _) in enumerate(rows)) for i in range(len(leaves)))
    desired = sum(high << i for i, (_, high) in enumerate(rows))
    all_rows = (1 << len(rows)) - 1
    active = set()

    def add_rows(indices):
        for i in indices:
            row, high = rows[i]
            values = tuple(-v if row >> j & 1 else v for j, v in enumerate(phase)) if signed else (
                tuple(bool(row >> j & 1) for j in range(len(leaves))))
            graph.require(i, values, high)
            active.add(i)

    if lazy_rows:
        # Seed both output labels when they occur. Further rows follow from counterexamples.
        add_rows(next(i for i, (_, label) in enumerate(rows) if label == bit)
                 for bit in {label for _, label in rows})
    else:
        add_rows(range(len(rows)))
    if stats is not None:
        stats['certificate_encode_seconds'] += perf_counter() - start
        stats['certificate_rows_after_boundary'] += len(rows)

    with Solver(name=solver_name, use_timer=True) as cdcl, cdcl_deadline(cdcl) as deadline:
        def push():
            begin = perf_counter()
            if stats is not None:
                stats['certificate_clauses'] += len(clauses)
            cdcl.append_formula(clauses)
            clauses.clear()
            if stats is not None:
                stats['certificate_load_seconds'] += perf_counter() - begin

        push()
        try:
            while True:
                if deadline is not None:
                    deadline.check()
                begin = perf_counter()
                try:
                    sat = cdcl.solve() if deadline is None else cdcl.solve_limited(expect_interrupt=True)
                finally:
                    if stats is not None:
                        stats['certificate_solves'] += 1
                        stats['certificate_solve_seconds'] += perf_counter() - begin
                if sat is None:
                    raise KeyboardInterrupt
                if not sat:
                    return None
                model = set(cdcl.get_model())
                begin = perf_counter()
                if not eager:
                    clauses.extend(graph.induced_path_clauses(model))
                    if clauses:
                        if stats is not None:
                            stats['certificate_paths'] += len(clauses)
                            stats['certificate_separation_seconds'] += perf_counter() - begin
                        push()
                        continue
                cotree = graph.decode(model)
                flipped = tuple(v in model for v in phase) if signed else (False,) * len(leaves)
                columns = tuple(column ^ (all_rows if neg else 0) for column, neg in zip(row_columns, flipped))
                mismatches = _evaluate(cotree, columns) ^ desired
                if not mismatches:
                    if stats is not None:
                        stats['certificate_separation_seconds'] += perf_counter() - begin
                    return _lift(cotree, leaves, flipped)
                missed = tuple(i for i in range(len(rows)) if mismatches >> i & 1)
                if not lazy_rows or any(i in active for i in missed):
                    raise RuntimeError('certificate model violates an encoded row')
                # Bound the clause growth per candidate, independently of the total row count.
                add_rows(islice(missed, 32))
                if stats is not None:
                    stats['certificate_encode_seconds'] += perf_counter() - begin
                push()
        finally:
            if stats is not None:
                stats['certificate_rows_encoded'] += len(active)
                stats['certificate_variables'] += pool.top
                stats['certificate_conflicts'] += cdcl.accum_stats().get('conflicts', 0)
