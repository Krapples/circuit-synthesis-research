"""Provider-aware residual tests for complete monotone circuit certificates."""

from dataclasses import dataclass
from functools import lru_cache


PROVIDER_LEVELS = ('eligibility', 'matching', 'exact')


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


@dataclass(frozen=True)
class ProviderResidual:
    common: tuple
    rows: tuple
    positives: tuple = ()
    zeros: tuple = ()


@lru_cache(maxsize=2048)
def provider_residual(positives, zeros, primary, *, output=False):
    """Keep separate rows for full certificates with the same regional projection."""
    positive_rows = tuple(a for a in positives if output or a & primary)
    negative_rows = tuple(b for b in zeros if output or b & primary)
    common = tuple(tuple(a & b for b in negative_rows) for a in positive_rows)
    rows = []
    for row in common:
        local = tuple(value & primary for value in row)
        if any(value.bit_count() > 1 for value in local):
            return None
        rows.append(sum(1 << j for j, value in enumerate(local) if not value))
    return ProviderResidual(common, tuple(rows), positive_rows, negative_rows)


@lru_cache(maxsize=2048)
def required_distinctions(positives, zeros, primary):
    """Minimal common-primary masks that an earlier provider must hit."""
    query = provider_residual(positives, zeros, primary)
    if query is None:
        return None
    masks = {row[j] for row, residual in zip(query.common, query.rows) for j in indices(residual)}
    minimal = []
    for mask in sorted(masks, key=lambda value: (value.bit_count(), value)):
        if not any(mask & smaller == smaller for smaller in minimal):
            minimal.append(mask)
    return tuple(minimal)


def has_capacity(lists, capacities):
    """Check Hall feasibility by matching each cell to a distinct provider slot."""
    slots = tuple(j for j, cap in enumerate(capacities) for _ in range(min(cap, len(lists))))
    choices = [tuple(i for i, j in enumerate(slots) if mask >> j & 1) for mask in lists]
    assigned = [-1] * len(slots)

    def augment(cell, seen):
        for slot in choices[cell]:
            if slot in seen:
                continue
            seen.add(slot)
            if assigned[slot] < 0 or augment(assigned[slot], seen):
                assigned[slot] = cell
                return True
        return False

    return all(augment(cell, set()) for cell in sorted(range(len(choices)), key=lambda i: len(choices[i])))


def _eligibility(query, supports):
    return tuple(tuple(sum(1 << i for i, support in enumerate(supports) if common & support)
                       if residual >> j & 1 else 0 for j, common in enumerate(row))
                 for residual, row in zip(query.rows, query.common))


def _forced_consistent(query, eligibility, supports):
    columns = [0] * len(supports)
    rows = [0] * len(supports)
    for i, row in enumerate(eligibility):
        for j, options in enumerate(row):
            if options and options & (options - 1) == 0:
                provider = options.bit_length() - 1
                rows[provider] |= 1 << i
                columns[provider] |= 1 << j
    return all(query.common[i][j] & support for provider, support in enumerate(supports)
               for i in indices(rows[provider]) for j in indices(columns[provider]))


def incompatibility_cliques(eligibility, subset=None, *, max_cells=80, max_cliques=16):
    """Yield certified cliques of cells whose lists are contained in subset."""
    cells = [(i, j) for i, row in enumerate(eligibility) for j, options in enumerate(row)
             if options and (subset is None or not options & ~subset)]
    if not cells:
        return
    if len(cells) > max_cells:
        cells.sort(key=lambda pos: (eligibility[pos[0]][pos[1]].bit_count(), pos))
        half = max_cells // 2
        tail = cells[half:]
        cells = cells[:half] + [tail[i * len(tail) // (max_cells - half)]
                                for i in range(max_cells - half)]
    options = [eligibility[i][j] for i, j in cells]
    conflicts = [0] * len(cells)
    for u, (i, j) in enumerate(cells):
        for v, (r, c) in enumerate(cells[:u]):
            # Sharing a rectangle needs the same provider at all four corners.
            if not options[u] & options[v] & eligibility[i][c] & eligibility[r][j]:
                conflicts[u] |= 1 << v
                conflicts[v] |= 1 << u
    by_list = sorted(range(len(cells)), key=lambda i: (options[i].bit_count(), -conflicts[i].bit_count()))
    by_degree = sorted(range(len(cells)), key=lambda i: (-conflicts[i].bit_count(), options[i].bit_count()))
    checked = set()
    for order in (by_list, by_degree):
        for start in order[:max_cliques // 2]:
            clique = 1 << start
            candidates = conflicts[start]
            for cell in order:
                if candidates >> cell & 1:
                    clique |= 1 << cell
                    candidates &= conflicts[cell]
            if clique not in checked:
                checked.add(clique)
                yield tuple(cells[i] for i in indices(clique))


def clique_capacity(eligibility, capacities):
    """Test a bounded sample of incompatible cliques against their slot lists."""
    if len(capacities) == 1 and capacities[0] >= sum(sum(map(bool, row)) for row in eligibility):
        return True
    return all(has_capacity(tuple(eligibility[i][j] for i, j in clique), capacities)
               for clique in incompatibility_cliques(eligibility) if len(clique) > 1)


def rectangle_masks(rows, width):
    """Enumerate nonempty all-one rectangles of a bitmask matrix."""
    for row_mask in range(1, 1 << len(rows)):
        selected = tuple(indices(row_mask))
        columns = (1 << width) - 1
        for i in selected:
            columns &= rows[i]
        column_mask = columns
        while column_mask:
            cells = sum(column_mask << (i * width) for i in selected)
            yield row_mask, column_mask, cells
            column_mask = (column_mask - 1) & columns


def allocate_rectangles(full, choices, obligations, cross_masks, max_states):
    """Cover disjoint cells while accumulating each provider's full obligations."""
    for rectangles in choices:
        rectangles.sort(key=lambda item: -item[0].bit_count())
    pivots = sorted(indices(full), key=lambda i: len(choices[i]))
    states = 0

    class StateLimit(Exception):
        pass

    @lru_cache(maxsize=None)
    def search(remaining, assigned):
        nonlocal states
        if not remaining:
            return True
        states += 1
        if states > max_states:
            raise StateLimit
        pivot = next(i for i in pivots if remaining >> i & 1)
        for cells, provider, row_mask, column_mask in choices[pivot]:
            capacity, prior_rows, prior_columns = assigned[provider]
            if not capacity or cells & remaining != cells:
                continue
            combined_rows = prior_rows | row_mask
            combined_columns = prior_columns | column_mask
            if any(combined_columns & ~cross_masks[provider][i] for i in indices(combined_rows)):
                continue
            updated = (capacity - 1, combined_rows, combined_columns)
            if search(remaining ^ cells, (*assigned[:provider], updated, *assigned[provider + 1:])):
                return True
        return False

    try:
        return search(full, obligations)
    except StateLimit:
        return None


def compatible_partition(query, providers, *, max_states=12_000):
    """Decide a small capacitated rectangle partition, or return None at a cap."""
    active_rows = tuple(i for i, row in enumerate(query.rows) if row)
    active_columns = 0
    for row in query.rows:
        active_columns |= row
    active_columns = tuple(indices(active_columns))
    height, width = len(active_rows), len(active_columns)
    if not height:
        return True
    if max(height, width) > 7 or sum(row.bit_count() for row in query.rows) > 24 or len(providers) > 8:
        return None
    common = tuple(tuple(query.common[i][j] for j in active_columns) for i in active_rows)
    rows = tuple(sum(1 << j for j, original in enumerate(active_columns) if query.rows[i] >> original & 1)
                 for i in active_rows)
    full = sum(row << (i * width) for i, row in enumerate(rows))
    choices = [[] for _ in range(height * width)]
    cross_masks = []
    for provider, (support, capacity) in enumerate(providers):
        allowed = tuple(sum(1 << j for j, value in enumerate(row) if value & support) for row in common)
        cross_masks.append(allowed)
        if not capacity:
            continue
        for row_mask, column_mask, cells in rectangle_masks(tuple(a & b for a, b in zip(rows, allowed)), width):
            for cell in indices(cells):
                choices[cell].append((cells, provider, row_mask, column_mask))
    return allocate_rectangles(full, choices, tuple((capacity, 0, 0) for _, capacity in providers),
                               cross_masks, max_states)


def provider_obstruction(query, providers, level='eligibility'):
    """Return a certified obstruction, with None meaning no exclusion was found."""
    if level not in PROVIDER_LEVELS:
        raise ValueError(f'unknown provider level {level!r}')
    if query is None:
        return 'primary'
    providers = tuple((support, capacity) for support, capacity in providers if capacity > 0)
    union = 0
    for support, _ in providers:
        union |= support
    if any(not query.common[i][j] & union for i, row in enumerate(query.rows) for j in indices(row)):
        return 'eligibility'
    if level == 'eligibility' or not any(query.rows):
        return None
    supports = tuple(support for support, _ in providers)
    eligibility = _eligibility(query, supports)
    if not clique_capacity(eligibility, tuple(cap for _, cap in providers)):
        return 'matching'
    if not _forced_consistent(query, eligibility, supports):
        return 'forced_consistency'
    if level == 'exact' and compatible_partition(query, providers) is False:
        return 'partition'
    return None
