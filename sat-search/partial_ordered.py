"""Ordered terminal-group bounds for partial monotone Boolean functions."""

from functools import lru_cache


@lru_cache(maxsize=16)
def feature_columns(width):
    """For each feature, a bitset of pattern indices on which it is one."""
    patterns = 1 << width
    universe = (1 << patterns) - 1
    # Feature i alternates blocks of 2**i zeroes and ones across the pattern indices.
    return tuple(universe // ((1 << (1 << i)) + 1) << (1 << i) for i in range(width))


def monotone_closure(width, positives, negatives):
    """Return bitsets of forced positive and negative patterns, including unattainable patterns."""
    ones = sum(1 << x for x in set(positives))
    zeros = sum(1 << x for x in set(negatives))
    for i, column in enumerate(feature_columns(width)):
        ones |= (ones & ~column) << (1 << i)
        zeros |= (zeros & column) >> (1 << i)
    return ones, zeros


def pair_conflicts(width, ones, zeros):
    """Pairs with both an AND and an OR restriction cannot share a read-once region."""
    columns = feature_columns(width)
    conflicts = [0] * width
    for i, left in enumerate(columns):
        for j in range(i + 1, width):
            both_zero = ~(left | columns[j])
            and_context = (ones >> ((1 << i) + (1 << j))) & (zeros >> (1 << i)) & (zeros >> (1 << j))
            or_context = zeros & (ones >> (1 << i)) & (ones >> (1 << j))
            if and_context & both_zero and or_context & both_zero:
                conflicts[i] |= 1 << j
                conflicts[j] |= 1 << i
    return conflicts


def forced_terminal_indices(group, cuts):
    """Indices of positive and negative rows forced at a group's terminal."""
    positives, negatives = set(), set()
    for i, row in enumerate(cuts):
        for j, cut in enumerate(row):
            if cut & ~group == 0:
                positives.add(i)
                negatives.add(j)
    return positives, negatives


def terminal_demands(group, cuts):
    """Return sets of earlier features that must be hit to realize this terminal."""
    positives, negatives = forced_terminal_indices(group, cuts)
    return frozenset(cuts[i][j] for i in positives for j in negatives if not cuts[i][j] & group)


def ordered_group_counter(width, positives, negatives):
    """Return a memoized K(earlier), or None if no monotone completion exists."""
    ones, zeros = monotone_closure(width, positives, negatives)
    if ones & zeros:
        return None
    full = (1 << width) - 1
    conflicts = pair_conflicts(width, ones, zeros)
    if not any(conflicts):
        # The remaining features form one eligible group whenever any remain.
        return lambda earlier: int(earlier != full)
    cuts = tuple(tuple(a & ~b for b in negatives) for a in positives)
    group_sizes = [0] + [-1] * full
    max_group = 1
    for group in range(1, full + 1):
        low = group & -group
        rest = group ^ low
        if group_sizes[rest] >= 0 and not conflicts[low.bit_length() - 1] & rest:
            group_sizes[group] = group_sizes[rest] + 1
            max_group = max(max_group, group_sizes[group])

    @lru_cache(maxsize=None)
    def demands(group):
        return terminal_demands(group, cuts)

    @lru_cache(maxsize=None)
    def remaining(earlier):
        if earlier == full:
            return 0
        rest = full ^ earlier
        if group_sizes[rest] >= 0:
            return 1  # all nonlocal distinctions can come from earlier features
        unassigned = rest.bit_count()
        best = unassigned       # singleton groups never impose earlier demands
        lower = (best + max_group - 1) // max_group
        group = (rest - 1) & rest
        while group and best > lower:
            size = group_sizes[group]
            outside = unassigned - size
            if (size > 0 and 1 + (outside + max_group - 1) // max_group < best
                    and all(earlier & cut for cut in demands(group))):
                best = min(best, 1 + remaining(earlier | group))
            group = (group - 1) & rest
        return best

    return remaining


def minimum_ordered_groups(width, positives, negatives):
    """Lower bound on nonempty terminal groups, or None if no monotone completion exists."""
    counter = ordered_group_counter(width, positives, negatives)
    return counter(0) if counter is not None else None


class SuffixProjection:
    """Partial suffix function and ordered DP shared by candidate pinned gates."""

    def __init__(self, used, bits, positives, negatives, count_groups):
        self.used = used
        self.bits = bits
        self.count_groups = count_groups
        self.and_blockers = [0] * len(bits)
        self.or_blockers = [0] * len(bits)
        self.singleton_pairs = [[] for _ in bits]
        full = (1 << len(bits)) - 1
        for a in positives:
            for b in negatives:
                cut = a & ~b
                if cut.bit_count() == 1:
                    i = cut.bit_length() - 1
                    self.and_blockers[i] |= full ^ a
                    self.or_blockers[i] |= b
                    self.singleton_pairs[i].append((a, b))

    def forced_repeats(self, gate):
        """Return mandatory repeats in the projection's dense coordinate system."""
        op, left, right = gate
        left, right = self.bits.index(1 << left), self.bits.index(1 << right)
        blockers = self.and_blockers if op == 0 else self.or_blockers
        return sum(1 << x for x, y in ((left, right), (right, left)) if blockers[x] >> y & 1)

    def binary_bound(self, repeated=0):
        # Each repeated wire accounts for one excess read and one extra region.
        # Forced repeated inputs are dependency-free singleton regions, placed first.
        width = len(self.bits)
        groups = repeated.bit_count() + self.count_groups(repeated)
        return max(0, width - 1, width + groups - 2)

    def pinned_readers(self, width, gates, after=None):
        """Return dense pinned gates and reader lower bounds, optionally using the exact after set."""
        inputs = len(self.bits)
        dense = {bit.bit_length() - 1: i for i, bit in enumerate(self.bits)}
        dense.update((width + i, inputs + i) for i in range(len(gates)))
        gates = [(op, dense[left], dense[right]) for op, left, right in gates]
        readers = [0] * (inputs + len(gates))
        for _, left, right in gates:
            readers[left] += 1
            readers[right] += 1

        if after is not None:
            for wire, i in dense.items():
                readers[i] += (after >> wire) & 1
        else:
            for i, pairs in enumerate(self.singleton_pairs):
                if readers[i] and any(not _preserves_distinction(a, b, inputs, gates) for a, b in pairs):
                    readers[i] += 1
        for i in range(inputs):
            readers[i] = max(1, readers[i])
        return gates, readers

    def multiplicity_bound(self, width, gates, after=None, empty=False):
        dense, readers = self.pinned_readers(width, gates, after)
        inputs = len(self.bits)
        repeated = sum(1 << i for i in range(inputs) if readers[i] >= 2)
        extra = sum(max(0, count - 2) for count in readers)
        empty_regions = forced_empty_regions(inputs, dense, readers) if empty else 0
        return max(len(gates), self.binary_bound(repeated) + extra + empty_regions)


def _preserves_distinction(a, b, inputs, gates):
    for j, (op, left, right) in enumerate(gates, inputs):
        al, ar = (a >> left) & 1, (a >> right) & 1
        bl, br = (b >> left) & 1, (b >> right) & 1
        av, bv = (al & ar, bl & br) if op == 0 else (al | ar, bl | br)
        if av > bv:
            return True
        a |= av << j
        b |= bv << j
    return False


def forced_empty_regions(inputs, gates, readers):
    """Count repeated internal terminals whose private cone has no original suffix input."""
    private = [1 << i for i in range(inputs)]
    empty = 0
    for j, (_, left, right) in enumerate(gates, inputs):
        support = (private[left] if readers[left] < 2 else 0) | (private[right] if readers[right] < 2 else 0)
        private.append(support)
        empty += readers[j] >= 2 and support == 0
    return empty


def suffix_projections(width, mandatory, positives, negatives):
    """Yield viable suffix-input sets with their reusable analyses."""
    cuts = {a & ~b for a in positives for b in negatives}
    for cut in cuts:
        if cut.bit_count() == 1:
            mandatory |= cut
    optional = ((1 << width) - 1) ^ mandatory
    subset = 0
    while True:
        used = mandatory | subset
        if all(used & cut for cut in cuts):
            bits = tuple(1 << i for i in range(width) if used >> i & 1)

            def project(rows):
                return tuple(sorted({sum(1 << i for i, bit in enumerate(bits) if row & bit) for row in rows}))

            pos, neg = project(positives), project(negatives)
            counter = ordered_group_counter(len(bits), pos, neg)
            if counter is not None:
                yield SuffixProjection(used, bits, pos, neg, counter)
        if subset == optional:
            break
        subset = (subset - optional) & optional


def projected_suffix_bounds(width, mandatory, positives, negatives):
    """Yield each viable suffix-input set and its binary-gate lower bound."""
    for projection in suffix_projections(width, mandatory, positives, negatives):
        yield projection.used, projection.binary_bound()
