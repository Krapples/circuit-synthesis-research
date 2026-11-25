"""Exact fixed-region completion by LCA blocks and port multiplicities."""

from collections import Counter
from functools import lru_cache
from itertools import product

from two_sharing_core import ANY, assignments, tree, vars


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def local_blocks(m, ports, pats, targets, signed, stats=None, module_filter=True):
    """Return a tree using every private leaf and allocated port occurrence."""
    if stats is not None:
        stats['local'] += 1
    one = (1 << (1 << m)) - 1
    full = (1 << m) - 1
    columns = vars(m)
    counts = Counter(ports)
    providers = tuple(sorted(counts))
    phase = {}
    forced = {'&': [0] * m, '|': [0] * m}

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

    @lru_cache(maxsize=4096)
    def support(table):
        return sum(1 << i for i, column in enumerate(columns) if (table ^ (table << (1 << i))) & column)

    @lru_cache(maxsize=4096)
    def project(table, inside, is_and):
        for i in indices(full ^ inside):
            column = columns[i]
            low, high = table & ~column, (table & column) >> (1 << i)
            value = low | high if is_and else low & high
            table = value | (value << (1 << i))
        return table

    @lru_cache(maxsize=4096)
    def exposed(row, inside):
        """The unique nonconstant cofactor a subtree may expose in this slice."""
        target = targets[row]
        if target in (ANY, 0, one):
            return None
        owned = assignments(tuple(indices(inside)))
        outside = assignments(tuple(indices(full ^ inside)))
        constant = (1 << len(owned)) - 1
        found = None
        for fixed in outside:
            part = sum((target >> (a | fixed) & 1) << i for i, a in enumerate(owned))
            if part in (0, constant):
                continue
            if found is not None and found != part:
                return None
            found = part
        if found is None:
            return None
        return sum((found >> i & 1) << (a | fixed) for i, a in enumerate(owned) for fixed in outside)

    @lru_cache(maxsize=8192)
    def complete(primary, available, obligations):
        if stats is not None:
            stats['rec'] += 1
        size = primary.bit_count() + sum(available)
        if not size or any(t != ANY and support(t) & ~primary for t in obligations):
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
            for left, taking in partitions(primary, available, op):
                if stats is not None:
                    stats['partition_checks'] += 1
                right = primary ^ left
                remaining = tuple(a - b for a, b in zip(available, taking))
                options = []
                for target in obligations:
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
                    options.append(pairs)
                else:
                    for selected in product(*options):
                        a_targets, b_targets = map(tuple, zip(*selected))
                        a = complete(left, taking, a_targets)
                        if a is not None:
                            b = complete(right, remaining, b_targets)
                            if b is not None:
                                return op, a, b
        return None

    try:
        return complete(full, tuple(counts[i] for i in providers), tuple(targets))
    finally:
        for cached in (components, support, project, exposed, complete):
            cached.cache_clear()


if __name__ == '__main__':
    import sys
    from pathlib import Path

    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'experiments'))
    from regional_completion_check import main

    main()
