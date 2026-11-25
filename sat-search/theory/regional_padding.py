"""Constructive single-graft padding of exact regional leaf allocations."""

from collections import Counter
from functools import lru_cache, reduce
from itertools import combinations_with_replacement, islice
from operator import and_, or_

from packed_regional_tables import PackedTables
from regional_root_relaxation import minimal_masks
from two_sharing_core import ANY, assignments, tree, vars as truth_variables


def columns(m, ports, patterns, targets):
    exact = tuple((p, t) for p, t in zip(patterns, targets, strict=True) if t != ANY)
    width = 1 << m
    one = (1 << (len(exact) * width)) - 1
    values = {i: sum(v << (j * width) for j in range(len(exact))) for i, v in enumerate(truth_variables(m))}
    values.update({m + p: sum(((1 << width) - 1) << (j * width) for j, (row, _) in enumerate(exact)
                             if row >> p & 1) for p in set(ports)})
    return values, sum(t << (j * width) for j, (_, t) in enumerate(exact)), one


def combine(op, leaves):
    return reduce(lambda a, b: (op, a, b), leaves)


def evaluate(tree, values, one):
    if tree[0] == 'x':
        return values[tree[1]] ^ (one if tree[2] else 0)
    a, b = (evaluate(child, values, one) for child in tree[1:])
    return a & b if tree[0] == '&' else a | b


def graft(core, spare, values, one, signed):
    """Find an exact single AND/OR graft at any node of this fixed core."""
    if not spare:
        return core
    raw = tuple(values[i] for i in spare)
    if not signed:
        conjunction, disjunction = reduce(and_, raw), reduce(or_, raw)

    @lru_cache(maxsize=128)
    def subtree_value(node):
        if node[0] == 'x':
            return values[node[1]] ^ (one if node[2] else 0)
        a, b = map(subtree_value, node[1:])
        return a & b if node[0] == '&' else a | b

    def filler(required, op):
        inner = '&' if op == '|' else '|'
        if not signed:
            bad = conjunction if op == '|' else one ^ disjunction
            return None if required & bad else combine(inner, (('x', i, False) for i in spare))
        observed = set()
        while required:
            bit = required & -required
            required ^= bit
            observed.add(sum(bool(col & bit) << i for i, col in enumerate(raw)))
        if len(observed) == 1 << len(raw):
            return None
        absent = next(i for i in range(len(observed) + 1) if i not in observed)
        return combine(inner, (('x', leaf, bool((absent >> i & 1) ^ (op == '|')))
                               for i, leaf in enumerate(spare)))

    def visit(node, sensitivity):
        value = subtree_value(node)
        for op, required in (('|', sensitivity & (one ^ value)), ('&', sensitivity & value)):
            extra = filler(required, op)
            if extra is not None:
                return op, node, extra
        if node[0] != 'x':
            op, left, right = node
            neutral = 0 if op == '&' else one
            a = visit(left, sensitivity & (subtree_value(right) ^ neutral))
            if a is not None:
                return op, a, right
            b = visit(right, sensitivity & (subtree_value(left) ^ neutral))
            if b is not None:
                return op, left, b
        return None

    try:
        return visit(core, one)
    finally:
        subtree_value.cache_clear()


def complete_core(width, providers, projected, signed):
    """Recognize a complete table on distinct independent leaves."""
    bindings = (*range(width), *(width + p for p in providers))
    table = sum(target << ((1 << width) * sum((pattern >> p & 1) << i for i, p in enumerate(providers)))
                for pattern, target in projected.items())
    if PackedTables(len(bindings)).support(table).bit_count() != len(bindings):
        return None
    recognized = tree(len(bindings), table, signed)
    if recognized is None:
        return None

    def bind(node):
        if node[0] == 'x':
            return 'x', bindings[node[1]], node[2]
        return combine(node[0], map(bind, node[1:]))

    return bind(recognized)


def fast_witness(m, ports, patterns, targets, signed, stats=None, *, max_core=6, max_trials=24,
                 max_allocations=512, compact=True):
    """Return a verified construction or None (unknown)."""
    from regional_block_completion import CompletionWorkLimit, local_blocks

    if m > 8 or len(patterns) > 128 or len(patterns) * (1 << m) > 4096:
        return None
    counts = Counter(ports)
    mask = sum(1 << p for p in counts)
    observed = {}
    for p, t in zip(patterns, targets, strict=True):
        if t != ANY and observed.setdefault(p & mask, t) != t:
            return None
    if not observed:
        return None
    private_mask = reduce(or_, map(PackedTables(m).support, observed.values()), 0) if compact else (1 << m) - 1
    private = tuple(i for i in range(m) if private_mask >> i & 1)
    width = len(private)
    if width > max_core or m + len(ports) < 2:
        return None
    rows, tables = zip(*observed.items())
    demands = minimal_masks((a ^ b if signed else a & ~b) for a, t in observed.items()
                            for b, u in observed.items() if (t != u if signed else t & ~u))
    if 0 in demands:
        return None
    required = tuple(i.bit_length() - 1 for i in demands if i.bit_count() == 1)
    limit = min(max_core - width, len(ports), m + len(ports) - width - 1)
    start = max(0, 1 - width, len(required))
    if start > limit:
        return None
    restricted = tuple(sum((t >> a & 1) << i for i, a in enumerate(assignments(private))) for t in tables)
    options = (tuple(sorted((*required, *extra))) for size in range(start, limit + 1)
               for extra in combinations_with_replacement(sorted(counts), size - len(required)))
    trials = 0
    packed = None

    def lift(node):
        if node[0] != 'x':
            return node[0], lift(node[1]), lift(node[2])
        _, i, phase = node
        return 'x', private[i] if i < width else m + i - width, phase

    for kept in islice(options, max_allocations):
        current = Counter(kept)
        used = sum(1 << p for p in current)
        if current - counts or any(not used & d for d in demands):
            continue
        if trials >= max_trials:
            break
        trials += 1
        if stats is not None:
            stats['padding_trials'] += 1
        # Hitting the demands guarantees equal targets on duplicate projected rows.
        projected = dict(zip((row & used for row in rows), restricted))
        try:
            if len(current) == len(kept) and len(projected) == 1 << len(kept):
                core = complete_core(width, kept, projected, signed)
                if stats is not None:
                    stats['padding_complete_cores'] += 1
            else:
                core = local_blocks(width, kept, tuple(projected), tuple(projected.values()), signed, port_first=True,
                                    witness_cover=True, row_quotient=True, work_limit=2048 if signed else 256)
        except CompletionWorkLimit:
            if stats is not None:
                stats['padding_core_limits'] += 1
            continue
        if core is None:
            continue
        if stats is not None:
            stats['padding_cores'] += 1
        if packed is None:
            packed = columns(m, ports, patterns, targets)
        spare = (*(i for i in range(m) if not private_mask >> i & 1),
                 *(m + p for p in (counts - current).elements()))
        result = graft(lift(core), spare, packed[0], packed[2], signed)
        if result is not None:
            present = Counter()
            pending = [result]
            while pending:
                node = pending.pop()
                if node[0] == 'x':
                    present[node[1]] += 1
                else:
                    pending.extend(node[1:])
            if present != Counter((*range(m), *(m + p for p in ports))) or evaluate(result, packed[0], packed[2]) != packed[1]:
                raise RuntimeError('invalid padding witness')
            if stats is not None:
                stats['padding_witnesses'] += 1
            return result
    return None
