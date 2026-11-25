"""Provider-first layout search on reduced monotone and free-NOT cores."""

from collections import Counter
from functools import lru_cache
from itertools import combinations, product

from conditional_provider import compositions, options
from module_contraction import essential, raw_monotone, simplify
from ordered_quotient_core import fixed, make_completion
from restriction_excess import first_gate_candidates, lower
from signed_region_bounds import Bound
from two_sharing_core import assignments, slices


class Projection:
    def __init__(self, n, target, repeated, signed):
        self.target, self.signed, self.repeated = target, signed, tuple(repeated)
        self.inputs = tuple(range(n))
        self.bound = Bound(n, target)
        self.cut = lru_cache(maxsize=2048)(self._cut)
        self.step = lru_cache(maxsize=4096)(self._step)

    def _cut(self, processed, readable, internals):
        """At fixed readable primary values at most 2^internals cofactors survive."""
        future = tuple(i for i in self.inputs if i not in processed)
        mask = sum(1 << i for i in readable)
        buckets = {}
        for assignment, table in zip(assignments(processed), slices(self.target, processed, future)):
            bucket = buckets.setdefault(assignment & mask, set())
            bucket.add(table)
            if len(bucket) > 1 << internals:
                return False
        return True

    def _step(self, processed, primary, readable, internals, output):
        """Count distinct observable selector slices at each readable pattern."""
        if not self.bound.compatible(sum(1 << i for i in primary), output):
            return False
        future = tuple(i for i in self.inputs if i not in processed and i not in primary)
        mask = sum(1 << i for i in readable)
        buckets = {}
        for assignment in assignments(processed):
            cofactors = slices(self.target, primary, future, assignment)
            if output:
                selector = cofactors
            else:
                if len(set(cofactors)) == 1:
                    continue
                choices = options(cofactors, len(primary), self.signed)
                if not choices:
                    return False
                selector = min(row[0] for row in choices)
            bucket = buckets.setdefault(assignment & mask, set())
            bucket.add(selector)
            if len(bucket) > 1 << internals:
                return False
        return True

    def support_cut(self, processed, supports):
        """Fix a support union and count the capacity of the remaining live wires."""
        for size in range(1, len(supports) + 1):
            for frozen in combinations(supports, size):
                union = 0
                for mask in frozen:
                    union |= mask
                fixed = tuple(i for i in processed if union >> i & 1)
                if not self.cut(processed, fixed, len(supports) - size):
                    return False
        return True


def port_patterns(repeated, internals, excess):
    """Enumerate recipient multiplicities for each provider in topological order."""
    if repeated + internals == 0:
        if excess == 0:
            yield ((),)
        return
    for extras in compositions(excess - repeated - internals, repeated + internals):
        choices = []
        for i, extra in enumerate(extras):
            start = max(0, i - repeated + 1)
            choices.append(tuple((0,) * start + row for row in compositions(extra + 2, internals + 1 - start)))
        for rows in product(*choices):
            ports = tuple(tuple(i for i, row in enumerate(rows) for _ in range(row[j]))
                          for j in range(internals + 1))
            if all(ports):
                yield ports


def group_candidates(inputs):
    for size in range(len(inputs) + 1):
        yield from combinations(inputs, size)


def search_exact(n, target, excess, signed=False, stats=None, *, projection=True, restrictions=True,
                 support_filter=False, internal_first=False, completion=None):
    """Try one allocated excess. An empty result is provisional at higher excess."""
    if (n < 2 or not essential(n, target) or not signed and not raw_monotone(n, target)
            or simplify(n, target, signed)[0] != n):
        raise ValueError('expected a fully reduced nonconstant essential core')
    if excess < 1:
        raise ValueError('the provider-first stage expects positive allocated excess')
    stats = stats if stats is not None else Counter()
    if completion is None:
        completion = make_completion()
    vertices = tuple(range(n))
    first = first_gate_candidates(n, target, excess, signed) if restrictions else None
    if first is not None and not first:
        stats['analytical_first_gate'] += 1
        return None

    @lru_cache(maxsize=None)
    def restriction_bound(fixed_inputs):
        rest = tuple(i for i in vertices if i not in fixed_inputs)
        return max(lower(len(rest), table, signed) for table in slices(target, fixed_inputs, rest))

    classes = [(r, k) for k in range(excess) for r in range(1, min(n, excess - k) + 1)]
    if internal_first:
        classes.sort(key=lambda shape: -shape[1])
    for repeated_count, interne in classes:
        candidates = []
        for repeated in combinations(vertices, repeated_count):
            if first is not None and not any(set(row[-1]) <= set(repeated) for row in first):
                stats['first_gate_reject'] += 1
                continue
            if restrictions and repeated_count + restriction_bound(repeated) > excess:
                stats['restriction_class_reject'] += 1
                continue
            candidates.append(repeated)
        if not candidates:
            continue
        patterns = tuple(port_patterns(repeated_count, interne, excess))
        for repeated in candidates:
            cut = Projection(n, target, repeated, signed)
            for ports in patterns:
                stats['patterns'] += 1
                if restrictions:
                    degrees = Counter(i for row in ports for i in row)
                    if (sum(degrees[i] - 1 for i in range(repeated_count)) + restriction_bound(repeated) > excess
                            or any(degrees[i] - 1 + restriction_bound((wire,)) > excess
                                   for i, wire in enumerate(repeated))):
                        stats['restriction_reject'] += 1
                        continue
                live = [set(i for suffix in ports[j:] for i in suffix if i < repeated_count + j)
                        for j in range(interne + 1)]

                def signals(pool):
                    return (tuple(repeated[i] for i in sorted(pool) if i < repeated_count),
                            sum(i >= repeated_count for i in pool))

                cut_signals = [signals(row) for row in live]
                incoming = [signals(set(row)) for row in ports]

                def place(region, processed, remaining, groups, supports):
                    stats['nodes'] += 1
                    if projection and not cut.cut(processed, *cut_signals[region]):
                        stats['cut_reject'] += 1
                        return None
                    if support_filter and not cut.support_cut(processed, tuple(supports[i] for i in sorted(live[region]))):
                        stats['support_reject'] += 1
                        return None
                    output = region == interne
                    for primary in ((remaining,) if output else group_candidates(remaining)):
                        if len(primary) + len(ports[region]) < 2:
                            continue
                        if projection and not cut.step(processed, primary, *incoming[region], output):
                            stats['step_reject'] += 1
                            continue
                        extended = (*groups, primary)
                        if output:
                            stats['fixed_calls'] += 1
                            trees = fixed(n, target, repeated, extended, ports, signed, stats, completion=completion)
                            if trees is not None:
                                return repeated, extended, ports, trees
                            continue
                        support = sum(1 << i for i in primary)
                        for i in ports[region]:
                            support |= supports[i]
                        result = place(region + 1, tuple(sorted((*processed, *primary))),
                                       tuple(i for i in remaining if i not in primary), extended, (*supports, support))
                        if result is not None:
                            return result
                    return None

                result = place(0, repeated, tuple(i for i in vertices if i not in repeated), (),
                               tuple(1 << i for i in repeated))
                if result is not None:
                    return result
    return None
