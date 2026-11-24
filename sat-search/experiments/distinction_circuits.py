"""Exact circuit synthesis via certificate-defined distinction-grid cores."""

from functools import reduce
from itertools import combinations
from operator import or_

import antichain_search as ac
from distinction_rectangles import _grid_extensions, _matching_endpoints, _minimum_protocol, _rectangles
from regional_synthesis import _bits


def _wire_tables(circuit, columns, steps=None):
    tables = list(columns)
    for op, left, right in circuit.gates:
        a, b = tables[left], tables[right]
        value = a | b if op else a & b
        if steps is not None:
            steps.append((op, a, b, value))
        tables.append(value)
    return tables


def certificate_requirements(circuit, columns, positive, negative):
    """Return each input's (positive, negative) obligations in left-first DAG certificates."""
    tables = _wire_tables(circuit, columns)
    if tables[circuit.output] & (positive | negative) != positive:
        raise ValueError('expected a circuit satisfying all labels')
    needed = [0] * len(tables)
    needed[circuit.output] = positive | negative
    for i, (op, left, right) in reversed(tuple(enumerate(circuit.gates, circuit.inputs))):
        both = needed[i] & (negative if op else positive)
        either = needed[i] ^ both
        to_left = either & (tables[left] if op else ~tables[left])
        needed[left] |= both | to_left
        needed[right] |= both | (either ^ to_left)
    return tuple((mask & positive, mask & negative) for mask in needed[:circuit.inputs])


def _fringe_patterns(rectangles, marked, endpoints):
    on_line = {}
    for row, col in endpoints:
        on_line[col] = on_line.get(col, 0) | row

    # With an unmarked row in a multi-cell rectangle, its column is unique.
    available = {}
    for rows, cols, _ in rectangles:
        row = rows & ~marked
        covered = rows & on_line.get(cols, 0)
        if row and covered:
            available.setdefault(row, set()).add((cols, covered))
    return available


def _request_candidates(available, limit):
    candidates = {}
    for row, patterns in sorted(available.items()):
        choices = set()
        for col, mask in patterns:
            subset = mask
            while subset:
                choices.add((col, subset))
                subset = (subset - 1) & mask
        choices = sorted(choices)
        for count in range(1, min(limit, len(choices)) + 1):
            for request in combinations(choices, count):
                rows = candidates.setdefault(request, [])
                if len(rows) < limit:
                    rows.append(row)
    return candidates


def _match_requests(requests, candidates):
    """Return the coordinate mask of an injective realization, if one exists."""
    assigned = {}

    def place(index, visited):
        for row in candidates[requests[index]]:
            if row in visited:
                continue
            visited.add(row)
            if row not in assigned or place(assigned[row], visited):
                assigned[row] = index
                return True
        return False

    if all(place(index, set()) for index in range(len(requests))):
        return sum(assigned)
    return None


def _cover_size(rectangles, endpoints):
    """Find the minimum cover of a feasible grid by tracking just the marked cells."""
    marked = {cell: 1 << i for i, cell in enumerate(endpoints)}
    alternatives = {}
    extra = set()
    for rows, cols, _ in rectangles:
        coverage = 0
        outside = None
        for row in _bits(rows):
            for col in _bits(cols):
                cell = row, col
                if cell in marked:
                    coverage |= marked[cell]
                else:
                    outside = cell  # A variable can cover at most one cell outside X.
        if coverage:
            extra.add(coverage)
        if outside is not None:
            alternatives.setdefault(outside, set()).add(coverage)

    full = (1 << len(endpoints)) - 1
    count = len(alternatives)
    frontier = {0}
    for choices in alternatives.values():
        if full in frontier:
            return count
        frontier = {old | choice for old in frontier for choice in choices}

    seen = set(frontier)
    while full not in frontier:
        frontier = {old | choice for old in frontier for choice in extra} - seen
        if not frontier:
            raise ValueError('expected a feasible distinction grid')
        count += 1
        seen.update(frontier)
    return count


def _representative_cores(rectangles, positive, negative, endpoints, limit):
    """Realize request multisets with bounded total size and deduplicate padded cores."""
    if not endpoints:
        yield positive & -positive, negative & -negative
        return
    p = reduce(or_, (row for row, _ in endpoints))
    n = reduce(or_, (col for _, col in endpoints))
    fringe_p = _fringe_patterns(rectangles, p, endpoints)
    fringe_n = _fringe_patterns(tuple((c, r, i) for r, c, i in rectangles), n,
                                tuple((c, r) for r, c in endpoints))
    if len(fringe_p) + len(fringe_n) <= limit:
        yield p | sum(fringe_p), n | sum(fringe_n)
        return

    candidates = (_request_candidates(fringe_p, limit), _request_candidates(fringe_n, limit))
    kinds = sorted(((axis, request) for axis, choices in enumerate(candidates) for request in choices),
                   key=lambda item: (len(item[1]), item))
    requests = ([], [])
    padding = tuple((0, row) for row in sorted(fringe_p)) + tuple((1, row) for row in sorted(fringe_n))
    seen = set()

    def visit(start, remaining):
        rows = _match_requests(requests[0], candidates[0])
        cols = _match_requests(requests[1], candidates[1])
        if rows is None or cols is None:
            return
        core = [rows, cols]
        # Adding coordinates cannot worsen the lifted optimum.
        left = limit - rows.bit_count() - cols.bit_count()
        for axis, row in padding:
            if not left:
                break
            if not core[axis] & row:
                core[axis] |= row
                left -= 1
        key = (p | core[0], n | core[1])
        if key not in seen:
            seen.add(key)
            yield key
        for index in range(start, len(kinds)):
            axis, request = kinds[index]
            if len(request) > remaining:
                break
            requests[axis].append(request)
            yield from visit(index, remaining - len(request))
            requests[axis].pop()

    yield from visit(0, limit)


def _core_input_sets(core, canonical, endpoints, limit):
    """Add bounded choices that can meet demands on the marked cells."""
    extras = tuple(col for col in core if col not in canonical and
                   any(col & row and not col & neg for row, neg in endpoints))
    for chosen in combinations(extras, min(limit, len(extras))):
        keep = canonical.union(chosen)
        yield tuple(col for col in core if col in keep)


def minimum_partial_circuit(columns, positive, negative, *, stats=None):
    """Return an exact gate-minimum circuit for AND/OR labels, or None if inconsistent.

    For homogeneous labels, the distinction gap is measured after adding the
    automatic opposite label at an extreme input.
    """
    if min(positive, negative) < 0 or positive & negative:
        raise ValueError('expected disjoint row masks')
    columns = tuple(col & (positive | negative) for col in columns)
    if not columns:
        return None
    if not (positive | negative):
        return ac.Circuit(len(columns), (), 0)
    if not positive:
        positive = 1 << negative.bit_length()
        columns = tuple(col | positive for col in columns)
    if not negative:
        negative = 1 << positive.bit_length()
    rectangles = _rectangles(columns, positive, negative)
    cells = {}
    for rows, cols, leaf in rectangles:
        for row in _bits(rows):
            for col in _bits(cols):
                cells.setdefault((row, col), leaf)
    size = positive.bit_count() * negative.bit_count()
    if len(cells) != size:
        return None
    endpoints = _matching_endpoints(rectangles)
    full_cover = _cover_size(rectangles, endpoints)
    gap = size - full_cover
    limit = len(endpoints) * (gap + 1)

    best = None
    for p, n in _representative_cores(rectangles, positive, negative, endpoints, limit):
        deleted = size - p.bit_count() * n.bit_count()
        if stats is not None:
            stats['cores'] += 1
            stats['deleted_cells'] += deleted
        # A useful projected column is determined by its nonempty rectangle.
        original = {columns[i] & (p | n): i for rows, cols, i in rectangles if rows & p and cols & n}
        core = tuple(original)
        core_rectangles = _rectangles(core, p, n)
        required = full_cover if not deleted else _cover_size(core_rectangles, endpoints)
        lower = required - 1
        if best is not None and lower + deleted >= len(best.gates):
            continue

        leaves, formula = _minimum_protocol(core_rectangles, p, n)
        steps = []
        ac._formula_steps(formula, core, steps)
        witness = ac._reconstruct(core, steps, p)
        if leaves > required:
            lower += 1  # The connectivity equality would force a formula on exactly required leaves.
        upper = len(witness.gates) - 1
        if best is not None:
            upper = min(upper, len(best.gates) - deleted - 1)
        witness_columns = core
        canonical = {columns[cells[row, col]] & (p | n) for row in _bits(p) for col in _bits(n)}
        for budget in range(lower, upper + 1):
            # At this budget at most budget - required + 1 repeated reads are possible.
            limit = len(endpoints) * (budget - required + 2)
            for available in _core_input_sets(core, canonical, endpoints, limit):
                smaller = ac.solve_columns(available, p, n, budget, sharing=1)
                if smaller is not None:
                    witness, witness_columns = smaller, available
                    break
            else:
                continue
            break
        if best is not None and len(witness.gates) + deleted >= len(best.gates):
            continue

        steps.clear()
        available = tuple(columns[original[table]] for table in witness_columns)
        tables = _wire_tables(witness, available, steps)
        output = tables[witness.output]
        for op, (first, *rest) in _grid_extensions(p, n, positive, negative, cells):
            side = columns[first]
            for leaf in rest:
                value = side & columns[leaf] if op else side | columns[leaf]
                steps.append((1 - op, side, columns[leaf], value))
                side = value
            value = output | side if op else output & side
            steps.append((op, output, side, value))
            output = value
        best = ac._reconstruct(columns, steps, positive)
    return best
