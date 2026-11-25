"""Exact fixed-region completion by LCA blocks and port multiplicities."""

from collections import Counter
from functools import lru_cache
from itertools import product

from block_order_requirements import block_requirements
from packed_regional_tables import PackedTables
from regional_row_quotient import quotient_rows
from two_sharing_core import ANY, tree


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


class CompletionWorkLimit(Exception):
    """A portfolio stage stopped before it could decide the query."""


def local_blocks(m, ports, pats, targets, signed, stats=None, module_filter=True, *,
                 row_filter=True, endpoint_branches=True, dominance_branches=True,
                 port_first=False, witness_cover=False, block_order=False, row_quotient=False,
                 table_factory=PackedTables, root_relaxation=False, work_limit=None):
    """Return a tree using every private leaf and allocated port occurrence."""
    if stats is not None:
        stats['local'] += 1
    tables = table_factory(m)
    one = tables.one
    last = (one + 1) >> 1
    full, columns = tables.full, tables.columns
    counts = Counter(ports)
    providers = tuple(sorted(counts))
    all_rows = (1 << len(pats)) - 1
    phase = {}
    forced = {'&': [0] * m, '|': [0] * m}
    work = 0

    def charge():
        nonlocal work
        work += 1
        if work > work_limit:
            raise CompletionWorkLimit

    if root_relaxation:
        from regional_root_relaxation import children

    def learn(node):
        if node[0] == 'x':
            _, i, neg = node
            if i in phase and phase[i] != neg:
                return None
            phase[i] = neg
            return 1 << i
        op, *children = node
        opposite = '|' if op == '&' else '&'
        seen = 0
        for child in children:
            used = learn(child)
            if used is None:
                return None
            for i in indices(used):
                if forced[opposite][i] & seen:
                    return None
                forced[op][i] |= seen
            for i in indices(seen):
                forced[op][i] |= used
            seen |= used
        return seen

    for target in set(targets) - {0, one, ANY}:
        recognized = tree(m, target, signed)
        if recognized is None or learn(recognized) is None:
            return None

    @lru_cache(maxsize=1024)
    def components(primary, op):
        """Connected components of the induced opposite-operation graph."""
        remaining, groups = primary, []
        edges = forced['|' if op == '&' else '&']
        while remaining:
            pending = block = remaining & -remaining
            while pending:
                bit = pending & -pending
                pending ^= bit
                adjacent = edges[bit.bit_length() - 1] & remaining & ~block
                block |= adjacent
                pending |= adjacent
            groups.append(block)
            remaining ^= block
        return tuple(groups)

    def partitions(primary, available, op):
        blocks = components(primary, op)
        if blocks:
            groups = ((blocks[0],), *((0, block) for block in blocks[1:]))
            offered = tuple(range(count + 1) for count in available)
        else:
            # Anchor one occurrence of the lowest available provider.
            anchor = next(i for i, count in enumerate(available) if count)
            groups = ()
            offered = tuple(range(int(i == anchor), count + 1) for i, count in enumerate(available))
        for selected in product(*groups, *offered):
            left = sum(selected[:len(groups)])
            taking = selected[len(groups):]
            if left != primary or taking != available:
                yield left, taking

    @lru_cache(maxsize=2048)
    def support_demands(mask, exact, is_and):
        first = {}
        forbidden = 0
        hits = set()
        for row, required in exact:
            pattern = pats[row] & mask
            forbidden |= required ^ first.setdefault(pattern, required)
            if not signed and pattern == (0 if is_and else mask):
                hits.add(required)
        return forbidden, tuple(sorted(hits))

    @lru_cache(maxsize=512)
    def order_demands(blocks, exact, is_and, live):
        return block_requirements(blocks, exact, pats, project, is_and, signed, live)

    @lru_cache(maxsize=1024)
    def forbidden_blocks(blocks, demands, mask):
        return sum(block for block, clauses in zip(blocks, demands) if any(not clause & mask for clause in clauses))

    def port_partitions(primary, available, op, obligations):
        blocks = components(primary, op)
        is_and = op == '&'
        absorbing = 0 if is_and else one
        exact_rows = tuple((row, t) for row, t in enumerate(obligations) if t not in (ANY, absorbing))
        exact = tuple((row, support(t)) for row, t in exact_rows)
        demands = order_demands(blocks, exact_rows, is_and, port_mask(available)) if block_order and blocks else ()
        port_anchor = next((i for i, count in enumerate(available) if count), -1) if not blocks else -1
        offered = tuple(range(int(i == port_anchor), count + 1) for i, count in enumerate(available))
        for taking in product(*offered):
            if work_limit is not None:
                charge()
            if stats is not None:
                stats['port_allocations'] += 1
            remaining = tuple(a - b for a, b in zip(available, taking))
            left_mask, right_mask = port_mask(taking), port_mask(remaining)
            forbid_left, hits_left = support_demands(left_mask, exact, is_and)
            forbid_right, hits_right = support_demands(right_mask, exact, is_and)
            if demands:
                more_left = forbidden_blocks(blocks, demands, left_mask)
                more_right = forbidden_blocks(blocks, demands, right_mask)
                if stats is not None and any((more_left & block and not forbid_left & block)
                                             or (more_right & block and not forbid_right & block) for block in blocks):
                    stats['block_order_forces'] += 1
                forbid_left |= more_left
                forbid_right |= more_right
            # Fix child order using the first primary component, or a port occurrence.
            force_left = forbid_right | (blocks[0] if blocks else 0)
            free = []
            left = right = 0
            for block in blocks:
                if block & force_left:
                    if block & forbid_left:
                        break
                    left |= block
                elif block & forbid_left:
                    right |= block
                else:
                    free.append((0, block))
            else:
                if (all(hit & (primary ^ right) for hit in hits_left)
                        and all(hit & (primary ^ left) for hit in hits_right)):
                    for chosen in product(*free):
                        inside = left | sum(chosen)
                        outside = primary ^ inside
                        if (any(taking) or inside) and (any(remaining) or outside) and (
                                all(hit & inside for hit in hits_left) and all(hit & outside for hit in hits_right)):
                            yield inside, taking
                    continue
            if stats is not None:
                stats['port_allocation_reject'] += 1

    support = lru_cache(maxsize=4096)(tables.support)
    project = lru_cache(maxsize=4096)(tables.project)

    @lru_cache(maxsize=4096)
    def exposed(row, inside):
        return tables.exposed(targets[row], inside, project)

    @lru_cache(maxsize=256)
    def row_order(mask):
        rows = tuple(pattern & mask for pattern in pats)
        zero = tuple(i for i, value in enumerate(rows) if value == 0)
        high = tuple(i for i, value in enumerate(rows) if value == mask)
        order = tuple((i, j) for i, a in enumerate(rows) for j, b in enumerate(rows) if i != j and a & b == a)
        return zero, high, order

    @lru_cache(maxsize=256)
    def ordered_rows(mask, is_and):
        comparable = [0] * len(pats)
        for lo, hi in row_order(mask)[2]:
            if is_and:
                comparable[hi] |= 1 << lo
            else:
                comparable[lo] |= 1 << hi
        return tuple(comparable)

    def prune_constant_branches(options, left_ports, right_ports, is_and):
        related = ordered_rows(left_ports, is_and), ordered_rows(right_ports, is_and)
        opposing = [0, 0]
        absorbing = 0 if is_and else one
        for row, pairs in enumerate(options):
            if len(pairs) == 1:
                for child, target in enumerate(pairs[0]):
                    if target not in (ANY, absorbing):
                        opposing[child] |= 1 << row
        for row, pairs in enumerate(options):
            if len(pairs) > 1:
                # All ambiguous branches require the same absorbing constant.
                # Only fixed, opposing obligations can conflict with this choice.
                options[row] = tuple(pair for pair in pairs if all(
                    target == ANY or not related[child][row] & opposing[child]
                    for child, target in enumerate(pair)))
                if not options[row]:
                    return False
        return True

    def port_mask(available):
        return sum(1 << i for i, count in zip(providers, available) if count)

    @lru_cache(maxsize=4096)
    def endpoints(node):
        """Bitsets of row minima and maxima over the private variables."""
        op, a, b = node
        if op == 'x':
            if a < m:
                return 0, all_rows
            values = sum(((pattern >> (a - m) & 1) ^ b) << row for row, pattern in enumerate(pats))
            return values, values
        lo_a, hi_a = endpoints(a)
        lo_b, hi_b = endpoints(b)
        return (lo_a & lo_b, hi_a & hi_b) if op == '&' else (lo_a | lo_b, hi_a | hi_b)

    def cover(left, taking, right, remaining, options, absorbing):
        fixed = tuple(pairs[0] if len(pairs) == 1 else (ANY, ANY) for pairs in options)
        a_fixed, b_fixed = zip(*fixed)
        ambiguous = sum(1 << row for row, pairs in enumerate(options) if len(pairs) > 1)

        def require(fixed_rows, rows):
            return tuple(absorbing if rows >> row & 1 else value for row, value in enumerate(fixed_rows))

        visited = set()

        def branch(required):
            if required in visited:
                return None
            if len(visited) < 4096:
                visited.add(required)
            if work_limit is not None:
                charge()
            if stats is not None:
                stats['cover_nodes'] += 1
            a = solve(left, taking, require(a_fixed, required))
            if a is None:
                return None
            lo, hi = endpoints(a)
            uncovered = ambiguous & (hi if absorbing == 0 else ~lo)
            b = solve(right, remaining, require(b_fixed, uncovered))
            if b is not None:
                return a, b
            # Any successful extension must take at least one of the right child's failed rows.
            for row in indices(uncovered):
                result = branch(required | (1 << row))
                if result is not None:
                    return result
            return None

        return branch(0)

    @lru_cache(maxsize=8192)
    def complete(primary, available, obligations):
        if work_limit is not None:
            charge()
        if stats is not None:
            stats['rec'] += 1
        size = primary.bit_count() + sum(available)
        if not size or any(t != ANY and support(t) & ~primary for t in obligations):
            return None
        if row_filter and not signed:
            zero, high, order = row_order(port_mask(available))
            # Every live leaf agrees at the all-zero/all-one endpoints.
            # At fixed primary values, a larger port pattern can only increase the output.
            if (any((t := obligations[i]) != ANY and t & 1 for i in zero)
                    or any((t := obligations[i]) != ANY and not t & last for i in high)
                    or any((a := obligations[i]) != ANY and (b := obligations[j]) != ANY and a & ~b
                           for i, j in order)):
                if stats is not None:
                    stats['row_reject'] += 1
                return None
        if module_filter and any(t not in (0, one, ANY) and exposed(j, primary) != t
                                 for j, t in enumerate(obligations)):
            if stats is not None:
                stats['module_reject'] += 1
            return None
        if size == 1:
            if primary:
                i = primary.bit_length() - 1
                values = (columns[i],) * len(pats)
            else:
                provider = next(i for i, count in zip(providers, available) if count)
                i = m + provider
                values = tuple(one if pattern >> provider & 1 else 0 for pattern in pats)
            phases = (phase[i],) if i in phase else range(2 if signed else 1)
            for neg in phases:
                if all(t == ANY or t == v ^ (one if neg else 0) for t, v in zip(obligations, values)):
                    return 'x', i, bool(neg)
            return None

        for op in ('&', '|'):
            is_and = op == '&'
            absorbing = 0 if is_and else one
            neutral = one ^ absorbing
            if root_relaxation and primary.bit_count() <= 2:
                splits = children(m, primary, components(primary, op), providers, available, pats, obligations,
                                  signed, is_and, stats, charge if work_limit is not None else None)
            else:
                splits = port_partitions(primary, available, op, obligations) if port_first else partitions(primary, available, op)
            for left, taking in splits:
                if stats is not None:
                    stats['partition_checks'] += 1
                right = primary ^ left
                remaining = tuple(a - b for a, b in zip(available, taking))
                endpoint_test = row_filter and endpoint_branches and not signed
                if endpoint_test:
                    left_ports, right_ports = port_mask(taking), port_mask(remaining)
                options = []
                for row, target in enumerate(obligations):
                    if target == ANY:
                        pairs = ((ANY, ANY),)
                    elif target == absorbing:
                        pairs = ((absorbing, ANY), (ANY, absorbing))
                    elif target == neutral:
                        pairs = ((neutral, neutral),)
                    else:
                        a, b = project(target, left, is_and), project(target, right, is_and)
                        if (a & b if is_and else a | b) != target:
                            break
                        pairs = ((a, b),)
                    if endpoint_test and target != ANY:
                        pairs = tuple((a, b) for a, b in pairs
                                      if endpoint_allows(a, pats[row], left_ports)
                                      and endpoint_allows(b, pats[row], right_ports))
                        if not pairs:
                            if stats is not None:
                                stats['endpoint_split_reject'] += 1
                            break
                    options.append(pairs)
                else:
                    if (endpoint_test and dominance_branches and any(len(pairs) > 1 for pairs in options)
                            and not prune_constant_branches(options, left_ports, right_ports, is_and)):
                        if stats is not None:
                            stats['dominance_split_reject'] += 1
                        continue
                    if stats is not None:
                        stats['obligation_partitions'] += 1
                    if witness_cover and any(len(pairs) > 1 for pairs in options):
                        result = cover(left, taking, right, remaining, options, absorbing)
                        if result is not None:
                            return op, *result
                        continue
                    for selected in product(*options):
                        a_targets, b_targets = map(tuple, zip(*selected))
                        a = solve(left, taking, a_targets)
                        if a is not None:
                            b = solve(right, remaining, b_targets)
                            if b is not None:
                                return op, a, b
        return None

    def endpoint_allows(target, pattern, mask):
        if target == ANY:
            return True
        pattern &= mask
        return (pattern != 0 or not target & 1) and (pattern != mask or bool(target & last))

    @lru_cache(maxsize=256)
    def observed_patterns(mask):
        return tuple(pattern & mask for pattern in pats)

    @lru_cache(maxsize=4096)
    def canonical(mask, obligations):
        normalized = quotient_rows(observed_patterns(mask), obligations, signed, one)
        if stats is not None:
            if normalized is None:
                stats['quotient_conflicts'] += 1
            else:
                stats['quotient_dropped'] += normalized.count(ANY) - obligations.count(ANY)
        return normalized

    def solve_quotiented(primary, available, obligations):
        normalized = canonical(port_mask(available), obligations)
        return None if normalized is None else complete(primary, available, normalized)

    solve = solve_quotiented if row_quotient else complete
    try:
        return solve(full, tuple(counts[i] for i in providers), tuple(targets))
    finally:
        for cached in (components, support_demands, order_demands, forbidden_blocks, support, project, exposed,
                       row_order, ordered_rows, endpoints, complete, observed_patterns, canonical):
            cached.cache_clear()


if __name__ == '__main__':
    import sys
    from pathlib import Path

    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'experiments'))
    from regional_completion_check import main

    main()
