"""Necessary split conditions for monotone and free-NOT regional children."""

from itertools import product

from two_sharing_core import ANY, assignments


def minimal_masks(masks):
    minimal = []
    for mask in sorted(set(masks), key=lambda value: (value.bit_count(), value)):
        if not any(mask & earlier == earlier for earlier in minimal):
            minimal.append(mask)
    return tuple(minimal)


def families(positive, negative, groups, signed, is_and):
    """Each family has to be hit by all the available groups of one child."""
    sources, opposites = (negative, positive) if is_and else (positive, negative)
    result = set()
    for row in sources:
        distinctions = ((row ^ other if signed else other & ~row if is_and else row & ~other)
                        for other in opposites)
        masks = tuple(sum(1 << i for i, group in enumerate(groups) if group & difference)
                      for difference in distinctions)
        if masks:
            result.add(minimal_masks(masks))
    return tuple(sorted(result, key=lambda family: (len(family), family), reverse=True))


def allocations(groups, demands, stats=None, charge=None):
    """Exact multiplicity splits satisfying the necessary root conditions."""
    if not groups or any(0 in family for family in demands):
        return
    masks = tuple(map(sum, groups))
    full = sum(masks)
    anchor = full & -full
    domains = [7 if len(group) > 1 else 3 for group in groups]
    domains[next(i for i, mask in enumerate(masks) if mask & anchor)] &= 5
    priority = [sum(4 if mask == 1 << i else 1 for family in demands for mask in family if mask >> i & 1)
                for i in range(len(groups))]

    def propagate(domain):
        while True:
            left = sum(1 << i for i, possible in enumerate(domain) if possible & 5)
            right = sum(1 << i for i, possible in enumerate(domain) if possible & 6)
            changed = False
            for family in demands:
                can_left = all(mask & left for mask in family)
                can_right = all(mask & right for mask in family)
                if not (can_left or can_right):
                    return False
                if can_left and can_right:
                    continue
                eligible, keep = (left, 5) if can_left else (right, 6)
                for mask in family:
                    single = mask & eligible
                    if single.bit_count() == 1:
                        i = single.bit_length() - 1
                        narrowed = domain[i] & keep
                        changed |= narrowed != domain[i]
                        domain[i] = narrowed
            if not changed:
                return True

    def visit(domain):
        if charge is not None:
            charge()
        if stats is not None:
            stats['root_nodes'] += 1
        if not propagate(domain):
            if stats is not None:
                stats['root_reject'] += 1
            return
        undecided = [i for i, possible in enumerate(domain) if possible.bit_count() > 1]
        if undecided:
            i = max(undecided, key=lambda j: (-domain[j].bit_count(), priority[j]))
            for side in (1, 2, 4):
                if domain[i] & side:
                    child = domain.copy()
                    child[i] = side
                    yield from visit(child)
            return
        choices = ((mask,) if side == 1 else (0,) if side == 2 else
                   tuple(sum(group[:i]) for i in range(1, len(group)))
                   for group, mask, side in zip(groups, masks, domain))
        for pieces in product(*choices):
            left = sum(pieces)
            if left != full and left & anchor:
                yield left

    yield from visit(domains)


def children(m, primary, blocks, providers, available, patterns, targets, signed, is_and, stats=None, charge=None):
    """Build the relaxation only on the active rows and leaf occurrences."""
    slots = []
    offset = m
    for count in available:
        slots.append(tuple(1 << i for i in range(offset, offset + count)))
        offset += count
    groups = tuple((block,) for block in blocks) + tuple(group for group in slots if group)
    port_slots = tuple(zip(tuple(map(sum, slots)), providers))
    primary_rows = assignments(tuple(i for i in range(m) if primary >> i & 1))
    positive, negative = set(), set()
    for pattern, target in zip(patterns, targets):
        if target == ANY:
            continue
        ports = sum(group for group, provider in port_slots if pattern >> provider & 1)
        for row in primary_rows:
            (positive if target >> row & 1 else negative).add(ports | row)
    demands = families(positive, negative, tuple(map(sum, groups)), signed, is_and)
    for left in allocations(groups, demands, stats, charge):
        yield left & primary, tuple((left & sum(group)).bit_count() for group in slots)
