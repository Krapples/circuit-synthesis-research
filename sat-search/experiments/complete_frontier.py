"""Constructive complete-function synthesis parameterized by excess plus NOTs."""

from collections import Counter
from functools import lru_cache
from itertools import product

from synthesis_cases import Witness, trim


ANY, NONCONSTANT = -1, -2


class FrontierLimit(Exception):
    """The experiment reached its state cap before an exact verdict."""


def subsets(mask):
    part = mask
    while True:
        yield part
        if not part:
            return
        part = (part - 1) & mask


def reader_shapes(excess):
    yield ()
    for extra in range(1, excess + 1):
        for tail in reader_shapes(excess - extra):
            yield (extra + 1, *tail)


class CompleteFrontier:
    def __init__(self, n, *, signed=False, compress=True, cache=True):
        if n < 1:
            raise ValueError('expected at least one essential primary')
        self.n = n
        self.full = (1 << n) - 1
        self.one = (1 << (1 << n)) - 1
        self.variables = tuple(sum(1 << row for row in range(1 << n) if row >> i & 1) for i in range(n))
        self.signed, self.compress, self.cache = signed, compress, cache
        self.restrict = lru_cache(maxsize=32_768)(self._restrict)
        self.cofactors = lru_cache(maxsize=8192)(self._cofactors)
        self.stats = Counter()
        self.limit = None

    def _restrict(self, table, selected, assignment):
        while selected:
            bit = selected & -selected
            selected ^= bit
            index = bit.bit_length() - 1
            upper = self.variables[index]
            if assignment & bit:
                high = table & upper
                table = high | (high >> bit)
            else:
                low = table & ~upper
                table = low | (low << bit)
        return table

    def _cofactors(self, table, selected):
        return frozenset(self.restrict(table, selected, a) for a in subsets(selected))

    def _count(self, kind):
        self.stats[kind] += 1
        if self.limit is not None and self.stats['states'] + self.stats['local_states'] > self.limit:
            raise FrontierLimit(self.limit)

    def _local(self, primary, ports, patterns, targets, not_budget):
        self.stats['local_calls'] += 1
        leaves = primary | (((1 << len(ports)) - 1) << self.n)
        if not leaves:
            return None

        @lru_cache(maxsize=None)
        def canonical(j, inside):
            table = targets[j]
            if table in (ANY, NONCONSTANT, 0, self.one):
                return None
            cofactors = self.cofactors(table, primary & ~inside) - {0, self.one}
            return next(iter(cofactors)) if len(cofactors) == 1 else None

        def acceptable(j, inside, table):
            if table in (ANY, NONCONSTANT, 0, self.one):
                return True
            standard = canonical(j, inside)
            return standard is not None and (table == standard or self.signed and table == (standard ^ self.one))

        def project(table, remove, op):
            while remove:
                bit = remove & -remove
                remove ^= bit
                a, b = self.restrict(table, bit, 0), self.restrict(table, bit, bit)
                table = a & b if op else a | b
            return table

        @lru_cache(maxsize=None)
        def complete(support, obligations, left):
            self._count('local_states')
            if left:
                complement = tuple(t if t in (ANY, NONCONSTANT) else t ^ self.one for t in obligations)
                child = complete(support, complement, left - 1)
                if child is not None:
                    return 2, child
            if support.bit_count() == 1:
                index = support.bit_length() - 1
                for pattern, target in zip(patterns, obligations):
                    value = (self.variables[index] if index < self.n
                             else self.one if pattern >> ports[index - self.n] & 1 else 0)
                    if target == NONCONSTANT:
                        if value in (0, self.one):
                            return None
                    elif target != ANY and target != value:
                        return None
                return index
            first = support & -support
            for subset in subsets(support ^ first):
                a, b = subset | first, support ^ (subset | first)
                if not b:
                    continue
                a_primary, b_primary = a & self.full, b & self.full
                for op in (0, 1):
                    absorbed = self.one if op else 0
                    neutral = absorbed ^ self.one
                    options = []
                    for j, target in enumerate(obligations):
                        if target == ANY:
                            pairs = ((ANY, ANY),)
                        elif target == absorbed:
                            pairs = ((absorbed, ANY), (ANY, absorbed))
                        elif target == neutral:
                            pairs = ((neutral, neutral),)
                        elif target == NONCONSTANT:
                            pairs = ((NONCONSTANT, NONCONSTANT), (NONCONSTANT, neutral), (neutral, NONCONSTANT))
                        else:
                            x = project(target, b_primary, op)
                            y = project(target, a_primary, op)
                            if ((x | y if op else x & y) != target
                                    or not acceptable(j, a_primary, x) or not acceptable(j, b_primary, y)):
                                break
                            pairs = ((x, y),)
                        options.append(pairs)
                    else:
                        for selected in product(*options):
                            a_targets, b_targets = map(tuple, zip(*selected))
                            for a_budget in range(left + 1):
                                first_tree = complete(a, a_targets, a_budget)
                                if first_tree is not None:
                                    second_tree = complete(b, b_targets, left - a_budget)
                                    if second_tree is not None:
                                        return op, first_tree, second_tree
            return None

        return complete(leaves, targets, not_budget)

    def _normalize(self, obligations, remaining):
        keep = sum(1 << i for i, count in enumerate(remaining) if count or not self.compress)
        result = {}
        for pattern, table in obligations:
            key = pattern & keep
            if key in result:
                if result[key] != table:
                    self.stats['forgotten_conflicts'] += 1
                    return None
                self.stats['merged_patterns'] += 1
            else:
                result[key] = table
        return tuple(sorted(result.items()))

    def synthesize(self, target, overhead, *, max_states=None, check_invariant=False):
        """Return a witness within n-1+overhead gates, or None after exhaustive exclusion."""
        if overhead < 0 or not 0 < target < self.one:
            raise ValueError('expected a nonconstant target and nonnegative overhead')
        if any(len(self.cofactors(target, 1 << i)) != 2 for i in range(self.n)):
            raise ValueError('every declared primary must be essential')
        if not self.signed:
            for i in range(self.n):
                bit = 1 << i
                if self.restrict(target, bit, 0) & ~self.restrict(target, bit, bit):
                    raise ValueError('expected a monotone target')
        self.limit = max_states
        self.stats.clear()
        local = lru_cache(maxsize=4096)(self._local) if self.cache else self._local
        for shape in reader_shapes(overhead):
            spare = overhead - sum(degree - 1 for degree in shape) if self.signed else 0

            @lru_cache(maxsize=None)
            def search(processed, remaining, state, unary):
                self._count('states')
                if check_invariant:
                    assert frozenset(table for _, table in state) == self.cofactors(target, processed)
                patterns = tuple(pattern for pattern, _ in state)
                unused = self.full ^ processed
                index = len(remaining)
                if index == len(shape):
                    ports = tuple(i for i, count in enumerate(remaining) for _ in range(count))
                    tree = local(unused, ports, patterns, tuple(t for _, t in state), unary)
                    return None if tree is None else ((ports, tree),)
                for primary in subsets(unused):
                    next_processed = processed | primary
                    if len(self.cofactors(target, next_processed)) > 1 << (index + 1):
                        continue
                    options = []
                    for _, table in state:
                        cofactors = self.cofactors(table, primary)
                        if len(cofactors) > 2:
                            break
                        if len(cofactors) == 1:
                            pair, = cofactors
                            options.append(((0, pair, ANY), (self.one, ANY, pair), (NONCONSTANT, pair, pair)))
                            continue
                        low, high = (sorted(cofactors) if self.signed else
                                     (self.restrict(table, primary, 0), self.restrict(table, primary, primary)))
                        selector = sum((self.restrict(table, primary, a) == high) << a for a in subsets(primary))
                        # Extend the selector from assignments supported on primary to the full truth table.
                        missing = self.full ^ primary
                        while missing:
                            bit = missing & -missing
                            missing ^= bit
                            selector |= selector << bit
                        choices = ((selector, low, high),)
                        if self.signed:
                            choices += ((selector ^ self.one, high, low),)
                        options.append(choices)
                    else:
                        for take in product(*(range(count + 1) for count in remaining)):
                            ports = tuple(i for i, count in enumerate(take) for _ in range(count))
                            if not (primary or ports):
                                continue
                            next_remaining = tuple(count - used for count, used in zip(remaining, take)) + (shape[index],)
                            for choice in product(*options):
                                targets = tuple(row[0] for row in choice)
                                if not primary and NONCONSTANT in targets:
                                    continue
                                next_state = self._normalize(((p | (high << index), row[high + 1])
                                                              for p, row in zip(patterns, choice)
                                                              for high in (0, 1) if row[high + 1] != ANY), next_remaining)
                                if next_state is None:
                                    continue
                                for spent in range(unary + 1):
                                    tree = local(primary, ports, patterns, targets, spent)
                                    if tree is None:
                                        continue
                                    suffix = search(next_processed, next_remaining, next_state, unary - spent)
                                    if suffix is not None:
                                        return ((ports, tree), *suffix)
                return None

            plan = search(0, (), ((0, target),), spare)
            if plan is not None:
                if self.cache:
                    self.stats['local_hits'] = local.cache_info().hits
                return self._flatten(plan)
        if self.cache:
            self.stats['local_hits'] = local.cache_info().hits
        return None

    def _flatten(self, regions):
        gates, signals, known = [], [], {}

        def wire(tree, ports):
            if isinstance(tree, int):
                return tree if tree < self.n else signals[ports[tree - self.n]]
            op = tree[0]
            first = wire(tree[1], ports)
            if op == 2:
                recipe = op, first, first
            else:
                second = wire(tree[2], ports)
                if first == second:
                    return first
                recipe = op, min(first, second), max(first, second)
            if recipe not in known:
                known[recipe] = self.n + len(gates)
                gates.append(recipe)
            return known[recipe]

        for ports, tree in regions:
            signals.append(wire(tree, ports))
        return trim(self.n, Witness(tuple(gates), signals[-1]))
