"""Global capacity bounds for ordered monotone regions and their providers."""

from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations

from provider_certificates import (allocate_rectangles, incompatibility_cliques, indices,
                                   provider_residual, rectangle_masks)


CAPACITY_LEVELS = ('singletons', 'subsets', 'exact')
ALLOCATION_LEVELS = ('deficit', 'packing', 'exact')


@dataclass(frozen=True)
class CapacityObstruction:
    kind: str
    region: int | None = None
    subset: int = 0
    capacity: int = 0
    cliques: tuple = ()

    @property
    def required(self):
        return sum(map(len, self.cliques))


@dataclass(frozen=True)
class CapacityRegion:
    positives: tuple
    zeros: tuple
    eligibility: tuple


@dataclass(frozen=True)
class CapacityLayout:
    capacities: tuple
    cross: tuple
    mandatory: tuple
    regions: tuple


@lru_cache(maxsize=1024)
def _cross_rows(positives, zeros, support):
    return tuple(sum(1 << j for j, b in enumerate(zeros) if a & b & support) for a in positives)


def prepare_capacity_layout(positives, zeros, groups, capacities, *, supports=None, output=True):
    """Build an ordered layout, or a fixed prefix of non-output regions."""
    positives, zeros, groups, capacities = map(tuple, (positives, zeros, groups, capacities))
    positives = tuple(dict.fromkeys(positives))
    zeros = tuple(dict.fromkeys(zeros))
    if not groups or len(groups) != len(capacities) + int(output) or any(cap < 0 for cap in capacities):
        raise ValueError('expected one outgoing capacity per non-output region')
    prefix = 0
    prefix_supports = []
    for primary in groups:
        if primary < 0 or prefix & primary:
            raise ValueError('expected disjoint nonnegative primary sets')
        prefix |= primary
        prefix_supports.append(prefix)
    if output and any(term & ~prefix for term in (*positives, *zeros)):
        raise ValueError('primary groups must cover the full certificates')
    # Any ancestor of a non-output terminal belongs to its own group or an
    # earlier group. Optional caller-supplied supports must be sound supersets.
    supports = tuple(prefix_supports[:len(capacities)]) if supports is None else tuple(supports)
    if (len(supports) != len(capacities)
            or any(group & ~mask or mask & ~upper
                   for group, mask, upper in zip(groups, supports, prefix_supports))):
        raise ValueError('expected ancestral overestimates between group and prefix support')

    cross, mandatory, available = [], [], []
    for provider, (primary, support) in enumerate(zip(groups, supports)):
        rows = _cross_rows(positives, zeros, support)
        required_p = sum(1 << i for i, a in enumerate(positives) if a & primary)
        required_z = sum(1 << i for i, b in enumerate(zeros) if b & primary)
        compatible_z = (1 << len(zeros)) - 1
        for i in indices(required_p):
            compatible_z &= rows[i]
        if required_z & ~compatible_z:
            return None, CapacityObstruction('mandatory', region=provider)
        cross.append(rows)
        mandatory.append((required_p, required_z))
        available.append(tuple(row & compatible_z if not required_z & ~row else 0 for row in rows))

    positive_ids = {term: i for i, term in enumerate(positives)}
    zero_ids = {term: i for i, term in enumerate(zeros)}
    regions = []
    for region, primary in enumerate(groups):
        residual = provider_residual(positives, zeros, primary, output=output and region == len(groups) - 1)
        if residual is None:
            return None, CapacityObstruction('primary', region=region)
        row_ids = tuple(positive_ids[a] for a in residual.positives)
        col_ids = tuple(zero_ids[b] for b in residual.zeros)
        eligible = []
        for i, row in zip(row_ids, residual.rows):
            options = [0] * len(col_ids)
            for col in indices(row):
                j = col_ids[col]
                options[col] = sum(1 << source for source in range(region)
                                   if capacities[source] and available[source][i] >> j & 1)
                if not options[col]:
                    return None, CapacityObstruction('eligibility', region=region)
            eligible.append(tuple(options))
        regions.append(CapacityRegion(row_ids, col_ids, tuple(eligible)))
    return CapacityLayout(capacities, tuple(cross), tuple(mandatory), tuple(regions)), None


def capacity_subsets(count, level):
    """Try singletons first, then all small subsets or a bounded larger family."""
    yield from (1 << i for i in range(count))
    if level == 'singletons' or count < 2:
        return
    if count <= 5:
        for size in range(2, count + 1):
            yield from (sum(1 << i for i in part) for part in combinations(range(count), size))
    else:
        yield (1 << count) - 1
        if count <= 8:
            yield from ((1 << i) | (1 << j) for i, j in combinations(range(count), 2))


def global_rectangle_allocation(layout, *, regions=None, max_states=12_000):
    """Decide the small joint rectangle relaxation under shared outgoing capacities."""
    regions = layout.regions if regions is None else tuple(regions)
    if (len(layout.capacities) > 8
            or sum(bool(mask) for region in regions for row in region.eligibility for mask in row) > 24):
        return None
    full, choices = 0, []
    for region in regions:
        active_rows = [i for i, row in enumerate(region.eligibility) if any(row)]
        if not active_rows:
            continue
        active_columns = [j for j in range(len(region.zeros))
                          if any(region.eligibility[i][j] for i in active_rows)]
        height, width = len(active_rows), len(active_columns)
        if max(height, width) > 7:
            return None
        p = tuple(region.positives[i] for i in active_rows)
        z = tuple(region.zeros[j] for j in active_columns)
        eligibility = tuple(tuple(region.eligibility[i][j] for j in active_columns) for i in active_rows)
        offset = len(choices)
        choices.extend([] for _ in range(height * width))
        full |= sum(1 << (offset + i * width + j)
                    for i, row in enumerate(eligibility) for j, options in enumerate(row) if options)
        for source in range(len(layout.capacities)):
            rows = tuple(sum(1 << j for j, options in enumerate(row) if options >> source & 1) for row in eligibility)
            if not any(rows):
                continue
            for row_mask, col_mask, cells in rectangle_masks(rows, width):
                positive = sum(1 << p[i] for i in indices(row_mask))
                negative = sum(1 << z[j] for j in indices(col_mask))
                cells <<= offset
                for cell in indices(cells):
                    choices[cell].append((cells, source, positive, negative))
    obligations = tuple((cap, p, z) for cap, (p, z) in zip(layout.capacities, layout.mandatory))
    return allocate_rectangles(full, choices, obligations, layout.cross, max_states)


def capacity_obstruction(layout, level='subsets'):
    """Return a global exclusion backed by regional cliques or bounded exact allocation."""
    if level not in CAPACITY_LEVELS:
        raise ValueError(f'unknown provider-capacity level {level!r}')
    lists = tuple(tuple(options for row in region.eligibility for options in row if options)
                  for region in layout.regions)
    for subset in capacity_subsets(len(layout.capacities), level):
        cap = sum(layout.capacities[i] for i in indices(subset))
        # Even one separate occurrence per cell cannot overload this subset.
        if sum(not options & ~subset for region in lists for options in region) <= cap:
            continue
        cliques = []
        for region in layout.regions:
            clique = max(incompatibility_cliques(region.eligibility, subset), default=(), key=len)
            cliques.append(clique)
        if sum(map(len, cliques)) > cap:
            return CapacityObstruction('capacity', subset=subset, capacity=cap, cliques=tuple(cliques))
    if level == 'exact' and global_rectangle_allocation(layout) is False:
        return CapacityObstruction('allocation')
    return None


def compulsory_demands(layout):
    """Certified F(T) for every subset of a small ordered provider set."""
    count = len(layout.capacities)
    if count > 6:
        raise ValueError('full subset demand is limited to six providers')
    demands = [0] * (1 << count)
    for subset in range(1, len(demands)):
        demands[subset] = sum(max(map(len, incompatibility_cliques(region.eligibility, subset)), default=0)
                              for region in layout.regions)
    return tuple(demands)


def allocation_excess(demands, budget, level='deficit'):
    """Conditional excess bound from F(T), capped at an exact budget exclusion."""
    if level not in ALLOCATION_LEVELS or not demands or len(demands) & (len(demands) - 1):
        raise ValueError('expected a power-of-two subset table and a valid allocation level')
    count = len(demands).bit_length() - 1
    deficits = tuple(max(0, demand - 2 * subset.bit_count()) for subset, demand in enumerate(demands))
    lower = max(deficits)
    if level == 'deficit' or count + lower > budget:
        return count + lower
    packing = [0] * len(demands)
    for subset in range(1, len(demands)):
        low_bit = subset & -subset
        best = packing[subset ^ low_bit]
        block = subset
        while block:
            if block & low_bit and deficits[block]:
                best = max(best, deficits[block] + packing[subset ^ block])
            block = (block - 1) & subset
        packing[subset] = best
    lower = packing[-1]
    if level == 'packing' or count + lower > budget or count == 0:
        return count + lower

    constraints = tuple((tuple(indices(subset)), demand) for subset, demand in enumerate(deficits) if demand)
    required = tuple(deficits[1 << i] for i in range(count))

    def feasible(assignment, remaining):
        n = len(assignment)
        if any(sum(assignment[i] for i in selected if i < n)
               + (remaining if selected[-1] >= n else 0) < demand for selected, demand in constraints):
            return False
        if n == count:
            return True
        return any(feasible((*assignment, extra), remaining - extra)
                   for extra in range(required[n], remaining - sum(required[n + 1:]) + 1))

    for extra in range(lower, budget - count + 1):
        if feasible((), extra):
            return count + extra
    return budget + 1


def ordered_allocation_excess(positives, zeros, costs, output_costs, support, lower, upper, level,
                              *, max_layouts=6_000, stats=None):
    """Raise a whole-target bound only after ruling out every layout at a budget."""
    if support.bit_count() > 6:
        return lower
    examined = 0

    class LayoutLimit(Exception):
        pass

    def permits(groups, left, readers, budget, port_sum):
        nonlocal examined
        if len(groups) == readers:
            if (left and left not in costs) or port_sum + (output_costs.get(left, costs.get(left, 2))
                                                            if left else 2) > budget + readers:
                return False
            if examined >= max_layouts:
                raise LayoutLimit
            examined += 1
            if stats is not None:
                stats['layouts'] += 1
            layout, failure = prepare_capacity_layout(positives, zeros, (*groups, left), (2,) * readers)
            if failure is not None:
                if stats is not None:
                    stats['structural_exclusions'] += 1
                return False
            if level is None:
                return True
            demands = compulsory_demands(layout)
            excluded = allocation_excess(demands, budget, level) > budget
            if stats is not None:
                stats['allocation_exclusions'] += excluded
            return not excluded
        part = left
        while True:
            cost = costs.get(part) if part else 2
            if cost is not None and (part or groups) and port_sum + cost <= budget + readers:
                if permits((*groups, part), left ^ part, readers, budget, port_sum + cost):
                    return True
            if not part:
                return False
            part = (part - 1) & left

    for budget in range(max(0, lower), min(upper, 5) + 1):
        try:
            if any(permits((), support, readers, budget, 0) for readers in range(budget + 1)):
                return budget
        except LayoutLimit:
            if stats is not None:
                stats['capped'] += 1
            return budget
        lower = budget + 1
    return lower
