"""Forward monotone regional synthesis on concrete boundary-row columns."""

from collections import Counter
from functools import lru_cache
from itertools import combinations_with_replacement, product

from regional_synthesis import RegionalSolution, _bits, _layout_domain, synthesize_regions
from joint_regional_synthesis import synthesize_partition


MAX_KNOWN_LEAVES = 9


def dominates(stronger, weaker, negative):
    """Compare two concrete columns using the requested labels on the rows."""
    return (weaker ^ negative) & ~(stronger ^ negative) == 0


def pareto(tables, negative):
    """Keep one representative formula per maximal agreement mask."""
    kept = {}
    agreements = []
    for table in sorted(tables, key=lambda t: (-(t ^ negative).bit_count(), t)):
        good = table ^ negative
        if not any(good & ~other == 0 for other in agreements):
            agreements.append(good)
            kept[table] = tables[table]
    return kept


def useful_gate(op, left, right, positive, negative):
    rows = negative if op == 0 else positive
    return bool(rows & left & ~right) and bool(rows & right & ~left)


@lru_cache(maxsize=512)
def _known_formulas(columns, negative, positive, prune, useful):
    @lru_cache(maxsize=None)
    def formulas(leaves):
        low = leaves & -leaves
        if low == leaves:
            i = low.bit_length() - 1
            return {columns[i]: i}
        tables = {}
        left = (leaves - 1) & leaves
        while left:
            if left & low:
                for a, fa in formulas(left).items():
                    for b, fb in formulas(leaves ^ left).items():
                        if not useful or useful_gate(0, a, b, positive, negative):
                            tables.setdefault(a & b, (0, fa, fb))
                        if not useful or useful_gate(1, a, b, positive, negative):
                            tables.setdefault(a | b, (1, fa, fb))
            left = (left - 1) & leaves
        return pareto(tables, negative) if prune else tables

    return formulas((1 << len(columns)) - 1)


def known_formulas(columns, negative, *, prune=True):
    """Enumerate concrete regional tables using every labeled leaf exactly once."""
    columns = tuple(columns)
    if not 1 <= len(columns) <= MAX_KNOWN_LEAVES:
        raise ValueError(f'concrete formula search requires 1 to {MAX_KNOWN_LEAVES} leaves')
    return dict(_known_formulas(columns, negative, 0, prune, False))


def covers_state(stronger, weaker, negative):
    """Match (table, reads still required, reads still allowed) for all old terminals."""
    if len(stronger) != len(weaker):
        return False
    candidates = [tuple(i for i, (a, minimum, capacity) in enumerate(stronger)
                        if minimum <= need and capacity >= limit and dominates(a, b, negative))
                  for b, need, limit in weaker]
    candidates.sort(key=len)
    owners = {}

    def assign(j, visited):
        for i in candidates[j]:
            if i in visited:
                continue
            visited.add(i)
            if i not in owners or assign(owners[i], visited):
                owners[i] = j
                return True
        return False

    return all(assign(j, set()) for j in range(len(candidates)))


def _forward(groups, ports, labels, reader_limits, prune, useful, state_dominance, stats):
    rows = tuple(sorted(labels))
    positive = sum(1 << i for i, row in enumerate(rows) if labels[row])
    negative = ((1 << len(rows)) - 1) ^ positive
    inputs = {bit: sum(1 << i for i, row in enumerate(rows) if row & bit)
              for group in groups for bit in _bits(group)}
    locals_ = [tuple(inputs[bit] for bit in _bits(group)) for group in groups]
    remaining = [sum(ports[i:]) for i in range(len(groups) + 1)]
    failed = [set() for _ in groups]
    formulas, wiring = [], []

    def visit(region, state):
        stats['states'] += 1
        key = tuple(sorted(state))
        if key in failed[region]:
            stats['equality_hits'] += 1
            return False
        if state_dominance and any(covers_state(old, key, negative) for old in failed[region]):
            stats['dominance_hits'] += 1
            return False
        outgoing = reader_limits[region] if region < len(reader_limits) else (0, 0)
        next_slots = remaining[region + 1]
        for providers in combinations_with_replacement(range(region), ports[region]):
            occurrences = Counter(providers)
            if any(occurrences[i] > limit for i, (_, _, limit) in enumerate(state)):
                continue
            next_readers = tuple((table, max(0, need - occurrences[i]), min(next_slots, limit - occurrences[i]))
                                 for i, (table, need, limit) in enumerate(state))
            need, limit = outgoing
            if (sum(item[1] for item in next_readers) + need > next_slots
                    or any(minimum > maximum for _, minimum, maximum in next_readers)):
                continue
            columns = locals_[region] + tuple(state[i][0] for i in providers)
            tables = _known_formulas(columns, negative, positive if useful else 0, prune, useful)
            stats['candidates'] += len(tables)
            if region == len(groups) - 1:
                if positive in tables:
                    formulas.append(tables[positive])
                    wiring.append(providers)
                    return True
                continue
            capacity = next_slots if limit is None else min(next_slots, limit)
            for table, formula in tables.items():
                formulas.append(formula)
                wiring.append(providers)
                if visit(region + 1, next_readers + ((table, need, capacity),)):
                    return True
                formulas.pop()
                wiring.pop()
        if state_dominance:
            failed[region] = {old for old in failed[region] if not covers_state(key, old, negative)}
        failed[region].add(key)
        return False

    if visit(0, ()):
        return RegionalSolution(groups, tuple(formulas), tuple(wiring))
    return None


def synthesize_forward(groups, ports, labels, *, reader_limits=None, prune=True, state_dominance=False, stats=None):
    """Solve a fixed layout with concrete provider values and optional dominance pruning."""
    groups, ports, limits, widths = _layout_domain(groups, ports, labels, reader_limits)
    if max(widths) > MAX_KNOWN_LEAVES:
        raise NotImplementedError(f'concrete search supports at most {MAX_KNOWN_LEAVES} leaves per region')
    if not min(widths) or ports[0]:
        return None
    return _forward(groups, ports, labels, limits, prune, False, state_dominance,
                    stats if stats is not None else Counter())


def _port_counts(count, total):
    return [(0, *tail) for tail in product(range(total + 1), repeat=count - 1)
            if sum(tail) == total and all(sum(tail[i:]) >= 2 * (count - i - 1) for i in range(count - 1))]


def canonical_layouts(n, gates):
    """Yield all ordered regional layouts for an all-wires-used circuit of this size."""
    for count in range(1, gates - n + 3):
        distributions = _port_counts(count, gates - n + count)
        for assignment in product(range(count), repeat=n):
            groups = [0] * count
            for i, region in enumerate(assignment):
                groups[region] |= 1 << i
            if groups[0]:
                for ports in distributions:
                    if all(group or p >= 2 for group, p in zip(groups, ports)):
                        yield tuple(groups), ports


def find_minimum(n, labels, max_gates, *, useful=False, state_dominance=False, formula_backend='forward', stats=None):
    """Search increasing sizes for a target whose partial labels require all n inputs."""
    if n < 1:
        raise ValueError('expected at least one primary input')
    if formula_backend not in ('forward', 'cograph', 'joint-cograph'):
        raise ValueError('expected forward, cograph, or joint-cograph formula backend')
    full = (1 << n) - 1
    if any(row < 0 or row & ~full for row in labels):
        raise ValueError('expected labels on an n-input domain')
    positive = [r for r in labels if labels[r]]
    negative = [r for r in labels if not labels[r]]
    cuts = {a & ~b for a in positive for b in negative}
    if 0 in cuts or any(bit not in cuts for bit in _bits(full)):
        raise ValueError('partial labels must be monotone-consistent and force every primary input')
    stats = stats if stats is not None else Counter()
    for gates in range(n - 1, max_gates + 1):
        if formula_backend == 'joint-cograph':
            for count in range(1, gates - n + 3):
                for ports in _port_counts(count, gates - n + count):
                    stats['port_patterns'] += 1
                    solution = synthesize_partition(n, ports, labels)
                    if solution is not None:
                        return gates, solution
            continue
        unsupported = False
        for groups, ports in canonical_layouts(n, gates):
            if formula_backend == 'forward' and max(g.bit_count() + p for g, p in zip(groups, ports)) > MAX_KNOWN_LEAVES:
                unsupported = True
                continue
            stats['layouts'] += 1
            limits = ((2, None),) * (len(groups) - 1)
            if formula_backend == 'cograph':
                solution = synthesize_regions(groups, ports, labels, reader_limits=limits, formula_encoding='cograph')
            else:
                # In usefulness mode compare only equal columns and never discard a
                # useful formula in favor of a dominating column with different values.
                solution = _forward(groups, ports, labels, limits, not useful, useful,
                                    state_dominance and not useful, stats)
            if solution is not None:
                return gates, solution
        if unsupported:
            raise NotImplementedError(f'size {gates} includes regions wider than {MAX_KNOWN_LEAVES} leaves')
    return None


def main():
    import argparse
    from time import perf_counter
    from cube_search import boundary_rows

    parser = argparse.ArgumentParser(description='Find a small exact monotone graph-circuit minimum by regional search')
    parser.add_argument('--n', type=int, required=True)
    parser.add_argument('--edges', required=True, help='comma-separated edges, such as 0-1,1-2')
    parser.add_argument('--max-gates', type=int, required=True)
    parser.add_argument('--formula-backend', choices=('forward', 'cograph', 'joint-cograph'), default='forward')
    parser.add_argument('--useful', '--monouseful', action='store_true', help='use gate usefulness in the forward backend')
    matching = parser.add_mutually_exclusive_group()
    matching.add_argument('--state-dominance', action='store_true', help='match failed states under dominance and reader limits')
    matching.add_argument('--equality-memo', dest='state_dominance', action='store_false', help='use equality memoization (default)')
    parser.set_defaults(state_dominance=False)
    args = parser.parse_args()
    if args.n < 1 or args.max_gates < 0:
        parser.error('--n must be positive and --max-gates must be nonnegative')
    try:
        edges = [tuple(map(int, edge.split('-'))) for edge in args.edges.split(',')]
        if any(not (0 <= a < args.n and 0 <= b < args.n and a != b) for a, b in edges):
            raise ValueError('each edge needs two distinct endpoints in range')
    except ValueError as error:
        parser.error(str(error))
    masks = tuple(sorted({(1 << a) | (1 << b) for a, b in edges}))
    positive, negative = boundary_rows(args.n, masks)
    labels = {**dict.fromkeys(positive, True), **dict.fromkeys(negative, False)}
    stats = Counter()
    start = perf_counter()
    try:
        result = find_minimum(args.n, labels, args.max_gates, useful=args.useful,
                              state_dominance=args.state_dominance, formula_backend=args.formula_backend, stats=stats)
    except ValueError as error:
        parser.error(str(error))
    except NotImplementedError as error:
        print(f'INCONCLUSIVE {error}')
        return 2
    if result is None:
        print(f'UNSAT through size {args.max_gates}')
    else:
        gates, solution = result
        if not all(solution.evaluate(row) == any(row & mask == mask for mask in masks)
                   for row in range(1 << args.n)):
            raise RuntimeError('reconstructed circuit failed full truth-table verification')
        print(f'MINIMUM {gates} gates, full truth table verified')
        print(solution)
    print(f'{dict(stats)} in {perf_counter() - start:.3f}s')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
