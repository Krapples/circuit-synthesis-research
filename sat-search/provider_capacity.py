"""Global capacity bounds for ordered monotone regions and their providers."""

from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations

from provider_certificates import (allocate_rectangles, incompatibility_cliques, indices,
                                   provider_residual, rectangle_masks)


CAPACITY_LEVELS = ('singletons', 'subsets', 'exact')


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


def prepare_capacity_layout(positives, zeros, groups, capacities, *, supports=None):
    """Build a full-certificate layout in provider-to-output topological order."""
    positives, zeros, groups, capacities = map(tuple, (positives, zeros, groups, capacities))
    positives = tuple(dict.fromkeys(positives))
    zeros = tuple(dict.fromkeys(zeros))
    if not groups or len(groups) != len(capacities) + 1 or any(cap < 0 for cap in capacities):
        raise ValueError('expected one outgoing capacity per non-output region')
    prefix = 0
    prefix_supports = []
    for primary in groups:
        if primary < 0 or prefix & primary:
            raise ValueError('expected disjoint nonnegative primary sets')
        prefix |= primary
        prefix_supports.append(prefix)
    if any(term & ~prefix for term in (*positives, *zeros)):
        raise ValueError('primary groups must cover the full certificates')
    # Any ancestor of a non-output terminal belongs to its own group or an
    # earlier group. Optional caller-supplied supports must be sound supersets.
    supports = tuple(prefix_supports[:-1]) if supports is None else tuple(supports)
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
        residual = provider_residual(positives, zeros, primary, output=region == len(groups) - 1)
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
