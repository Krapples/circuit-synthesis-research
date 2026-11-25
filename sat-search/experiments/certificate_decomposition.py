"""A SAT relaxation of repeated-wire certificate intersections."""

from collections import Counter
from functools import lru_cache
from itertools import combinations, product
from typing import NamedTuple

from affine_completion import complete_affine
from certificate_compatibility import (compatible_tree, indices, obstruction_clause, restrict_certificates,
                                       tree_leaves)
from certificate_rank import coexistence_color_bound, intersection_matrix, modular_rank, one_share_support
from cograph_formulas import CographFormula
from regional_synthesis import CardEnc, IDPool, RegionalSolution, Solver, _bits
from port_certificates import (PORT_CERTIFICATE_LEVELS, incompatible_primary_pairs, incoming_port_bound,
                               minimal_zero_certificates)
from provider_certificates import PROVIDER_LEVELS, provider_obstruction, provider_residual
from provider_capacity import CAPACITY_LEVELS, capacity_obstruction, prepare_capacity_layout


def _reader_counts(excess):
    if excess == 0:
        yield ()
    for first in range(1, excess + 1):
        for tail in _reader_counts(excess - first):
            yield (first + 1, *tail)


def _compress(matrix):
    rows = tuple(dict.fromkeys(row for row in map(tuple, matrix) if any(row)))
    columns = tuple(dict.fromkeys(col for col in zip(*rows) if any(col)))
    return tuple(zip(*columns))


def _terminal_domains(row_wires, col_wires, readers, certificates, pool, clauses):
    owners = [tuple(pool.id() for _ in range(i + 1)) for i, degree in enumerate(readers) for _ in range(degree)]
    groups = (row_wires, col_wires)
    selections = [[tuple(edge for _, edges in wire for edge in edges) for wire in group] for group in groups]
    atoms = ()
    if certificates is not None:
        support = 0
        for term in certificates[0]:
            support |= term
        atoms = _bits(support)
        start = len(owners)
        owners.extend(tuple(pool.id() for _ in range(len(readers) + 1)) for _ in atoms)
        selections = [[(*selected, *(bool(term & atom) for atom in atoms))
                       for selected, term in zip(axis, terms)] for axis, terms in zip(selections, certificates)]
        minterms = set(certificates[0])
        for j, bit in enumerate(atoms):
            for i in range(j):
                swap = bit | atoms[i]
                if all(term & swap in (0, swap) or term ^ swap in minterms for term in minterms):
                    # A primary transposition preserving all minterms preserves the target.
                    for r, first in enumerate(owners[start + i]):
                        clauses.extend([-first, -second] for second in owners[start + j][:r])

    for choices in owners:
        clauses.extend(CardEnc.equals(choices, 1, vpool=pool).clauses)
    return owners, atoms, selections


def _add_visit_implications(owners, selections, groups, clauses):
    for axis, group in zip(selections, groups):
        for chosen, wire in zip(axis, group):
            for selection, choices in zip(chosen, owners):
                if selection is not False:
                    guard = [] if selection is True else [-selection]
                    clauses.extend([*guard, -pick, wire[i][0]] for i, pick in enumerate(choices[1:]))


def _add_topology(row_wires, col_wires, readers, certificates, pool, clauses):
    owners, atoms, selections = _terminal_domains(row_wires, col_wires, readers, certificates, pool, clauses)
    cotree = CographFormula(len(owners), pool, 'terminals', clauses)
    groups = (row_wires, col_wires)
    _add_visit_implications(owners, selections, groups, clauses)
    positive, negative = selections
    for t, choices in enumerate(owners):
        for s in range(t):
            sign = cotree.edge(s, t)
            for first, second in zip(owners[s], choices):
                for axis, relation in ((positive, sign), (negative, -sign)):
                    for selected in axis:
                        a, b = selected[s], selected[t]
                        if a is not False and b is not False:
                            clauses.append([-first, -second, relation, *(-v for v in (a, b) if v is not True)])

    if certificates is not None:
        for r in range(len(readers) + 1):
            active = tuple(choices[r] if r < len(choices) else False for choices in owners)
            clauses.append([pick for pick in active if pick is not False])
            for high, axis, group in ((True, positive, row_wires), (False, negative, col_wires)):
                for row, (chosen, wire) in enumerate(zip(axis, group)):
                    values = chosen if high else tuple(not v if isinstance(v, bool) else -v for v in chosen)
                    cotree.require((r, row), values, high, guard=wire[r - 1][0] if r else None, active=active)
        return cotree, owners, atoms
    return None


class LazyTopology(NamedTuple):
    owners: tuple
    atoms: tuple
    memberships: tuple
    visits: tuple


def _port_sources(readers):
    return tuple(i + 1 for i, degree in enumerate(readers) for _ in range(degree))


def _capacity_owner_cut(topology, readers, certificates, assignments, level, stats, stage):
    groups = [0] * (len(readers) + 1)
    for atom, region in zip(topology.atoms, assignments):
        groups[region] |= atom
    layout, obstruction = prepare_capacity_layout(*certificates, tuple(reversed(groups)), tuple(reversed(readers)))
    if obstruction is None:
        obstruction = capacity_obstruction(layout, level)
    stats[f'capacity_{stage}_layouts'] += 1
    if obstruction is None or obstruction.kind == 'primary':
        return None  # The existing formula compatibility check handles primary conflicts.
    stats[f'capacity_{stage}_{obstruction.kind}'] += 1
    owners = topology.owners[len(topology.owners) - len(topology.atoms):]
    return tuple(-choices[region] for choices, region in zip(owners, assignments))


def _capacity_prefix_clauses(topology, readers, certificates, level, stats, *, limit=96):
    """Budgeted prescreen for fixed prefixes, before the membership SAT solve."""
    owners = topology.owners[len(topology.owners) - len(topology.atoms):]
    capacities = tuple(reversed(readers))
    conflicts = incompatible_primary_pairs(*certificates)
    clauses = []
    pending = limit

    def visit(groups, remaining):
        nonlocal pending
        output = len(groups) == len(readers)
        bits = _bits(remaining)
        candidates = ((remaining,) if output else
                      (sum(group) for size in range(int(not groups), len(bits) + 1)
                       for group in combinations(bits, size)))
        for primary in candidates:
            if not pending:
                break
            pending -= 1
            if any(primary & pair == pair for pair in conflicts):
                continue
            fixed = (*groups, primary)
            caps = capacities if output else capacities[:len(fixed)]
            layout, obstruction = prepare_capacity_layout(*certificates, fixed, caps, output=output)
            if obstruction is None:
                obstruction = capacity_obstruction(layout, 'subsets' if level == 'exact' and not output else level)
            stats['capacity_prefix_layouts'] += 1
            if obstruction is None:
                if not output:
                    visit(fixed, remaining ^ primary)
                continue
            if obstruction.kind == 'primary':
                continue
            stats[f'capacity_prefix_{obstruction.kind}'] += 1
            fixed_regions = tuple(range(len(readers), len(readers) - len(fixed), -1))
            guard = []
            for atom, choices in zip(topology.atoms, owners):
                owned = next((r for r, group in zip(fixed_regions, fixed) if atom & group), None)
                if owned is None:
                    guard.extend(choices[r] for r in fixed_regions)
                else:
                    guard.append(-choices[owned])
            clauses.append(tuple(guard))

    visit((), sum(topology.atoms))
    return clauses


def _add_lazy_topology(row_wires, col_wires, readers, certificates, pool, clauses):
    owners, atoms, selections = _terminal_domains(row_wires, col_wires, readers, certificates, pool, clauses)
    groups = (row_wires, col_wires)
    _add_visit_implications(owners, selections, groups, clauses)
    memberships = []
    for r in range(len(readers) + 1):
        active = tuple(choices[r] if r < len(choices) else None for choices in owners)
        clauses.append([pick for pick in active if pick is not None])
        axes = []
        for chosen_rows, wires in zip(selections, groups):
            rows = []
            for chosen, wire in zip(chosen_rows, wires):
                local = []
                for pick, selection in zip(active, chosen):
                    if pick is None or selection is False:
                        local.append(None)
                    elif selection is True:
                        local.append(pick)
                    else:
                        member = pool.id()
                        clauses.extend(([-member, pick], [-member, selection], [member, -pick, -selection]))
                        local.append(member)
                guard = [-wire[r - 1][0]] if r else []
                clauses.append(guard + [member for member in local if member is not None])
                rows.append(tuple(local))
            axes.append(tuple(rows))
        memberships.append(tuple(axes))
    visits = tuple(tuple(tuple(vertex for vertex, _ in row) for row in wires) for wires in groups)
    return LazyTopology(tuple(owners), atoms, tuple(memberships), visits)


def _lazy_port_cuts(topology, model, certificates, level, include_output=False):
    owners, atoms, memberships, _ = topology
    first_primary = len(owners) - len(atoms)
    port_owners, primary_owners = owners[:first_primary], owners[first_primary:]
    cuts = []
    for region in range(len(memberships)):
        choices = tuple(picks[region] for picks in primary_owners)
        primary = sum(atom for atom, pick in zip(atoms, choices) if pick in model)
        output = include_output and region == 0
        if not primary and not output:
            continue
        eligible = [picks[region] for picks in port_owners if region < len(picks)]
        absent = [pick for pick in eligible if pick not in model]
        bound = incoming_port_bound(*certificates, primary, level, output=output)
        if bound is not None and len(eligible) - len(absent) >= bound:
            continue
        guard = [-pick if pick in model else pick for pick in choices]
        if bound is not None and bound <= len(eligible):
            # If these ports stay absent, at most bound - 1 ports can be owned
            # here. The ownership guard fixes exactly the primary subset.
            guard.extend(absent[:len(eligible) - bound + 1])
        cuts.append(tuple(guard))
    return cuts


@lru_cache(maxsize=64)
def _positive_port_costs(certificates, atoms, level, output):
    conflicts = incompatible_primary_pairs(*certificates)
    support = sum(atoms)
    costs = {}
    primary = support
    while primary:
        if all(primary & pair != pair for pair in conflicts):
            lower = incoming_port_bound(*certificates, primary, level, output=output)
            if lower:
                costs[primary] = lower
        primary = (primary - 1) & support
    return costs


def _add_static_port_bounds(topology, certificates, level, include_output, pool, clauses):
    owners, atoms, memberships, _ = topology
    first_primary = len(owners) - len(atoms)
    port_owners, primary_owners = owners[:first_primary], owners[first_primary:]
    conflicts = incompatible_primary_pairs(*certificates)
    for region in range(len(memberships)):
        choices = tuple(picks[region] for picks in primary_owners)
        for pair in conflicts:
            clauses.append([-pick for atom, pick in zip(atoms, choices) if atom & pair])
        if len(atoms) > 8:
            continue  # Keep the static subset enumeration bounded.
        ports = [picks[region] for picks in port_owners if region < len(picks)]
        requirements = _positive_port_costs(certificates, atoms, level, include_output and region == 0)
        thresholds = {}
        for primary, lower in requirements.items():
            guard = [-pick if primary & atom else pick for atom, pick in zip(atoms, choices)]
            if lower == 1:
                clauses.append([*guard, *ports])
            elif lower > len(ports):
                clauses.append(guard)
            else:
                if lower not in thresholds:
                    enabled = thresholds[lower] = pool.id()
                    cardinality = CardEnc.atleast(ports, lower, vpool=pool)
                    clauses.extend([-enabled, *clause] for clause in cardinality.clauses)
                clauses.append([*guard, thresholds[lower]])


def _add_provider_ancestry(topology, readers, certificates, pool, clauses):
    """Propagate the implied reachability of atoms distinguishing provider visits."""
    sources = _port_sources(readers)
    port_owners, primary_owners = topology.owners[:len(sources)], topology.owners[len(sources):]
    reachable = {}
    for region in range(len(readers), 0, -1):
        upstream = [(source, picks[region]) for source, picks in zip(sources, port_owners) if region < len(picks)]
        for atom, picks in zip(topology.atoms, primary_owners):
            if not upstream:
                reachable[region, atom] = picks[region]
                continue
            reach = reachable[region, atom] = pool.id()
            paths = [picks[region]]
            for source, owner in upstream:
                path = pool.id()
                paths.append(path)
                clauses.extend(([-path, owner], [-path, reachable[source, atom]]))
            clauses.append([-reach, *paths])
    for a, positive in zip(certificates[0], topology.visits[0]):
        for b, negative in zip(certificates[1], topology.visits[1]):
            shared = _bits(a & b)
            for region, (high, low) in enumerate(zip(positive, negative), 1):
                clauses.append([-high, -low, *(reachable[region, bit] for bit in shared)])


def _provider_model_cuts(topology, readers, model, certificates, level):
    sources = _port_sources(readers)
    chosen = tuple(next(r for r, pick in enumerate(picks) if pick in model) for picks in topology.owners)
    groups = [0] * (len(readers) + 1)
    providers = [Counter() for _ in groups]
    for atom, region in zip(topology.atoms, chosen[len(sources):]):
        groups[region] |= atom
    for source, region in zip(sources, chosen):
        providers[region][source] += 1
    supports = groups.copy()
    cones = [1 << r for r in range(len(groups))]
    for region in range(len(groups) - 1, -1, -1):
        for source in providers[region]:
            supports[region] |= supports[source]
            cones[region] |= cones[source]

    # These are the union of obligations from every reader of the source.
    positive, negative = topology.visits
    for region in range(1, len(groups)):
        high = [(a, row[region - 1]) for a, row in zip(certificates[0], positive) if row[region - 1] in model]
        low = [(b, row[region - 1]) for b, row in zip(certificates[1], negative) if row[region - 1] in model]
        for a, visit_high in high:
            for b, visit_low in low:
                if a & b & supports[region]:
                    continue
                cone = cones[region]
                # The cone can gain a distinguishing atom only through a new
                # primary owner inside it, or an incoming port from outside.
                escape = [pick for atom, picks in zip(topology.atoms, topology.owners[len(sources):])
                          if atom & a & b for r, pick in enumerate(picks) if cone >> r & 1]
                escape.extend(pick for source, picks in zip(sources, topology.owners) if not cone >> source & 1
                              for r, pick in enumerate(picks) if cone >> r & 1)
                return 'consistency', [(-visit_high, -visit_low, *escape)]
    for region, (primary, local) in enumerate(zip(groups, providers)):
        if not primary and region:
            continue
        query = provider_residual(*certificates, primary, output=region == 0)
        if query is None:
            # The existing formula-compatibility check supplies the primary
            # obstruction. Keep this layer specific to provider feasibility.
            continue
        obstruction = provider_obstruction(query, ((supports[src], cap) for src, cap in local.items()), level)
        if obstruction is not None:
            return obstruction, [tuple(-picks[r] for picks, r in zip(topology.owners, chosen))]
    return None, ()


def _lazy_formulas(topology, model, affine_completion=None, stats=None):
    owners, _, memberships, _ = topology
    leaves = [0] * len(memberships)
    for i, choices in enumerate(owners):
        owner = next(r for r, pick in enumerate(choices) if pick in model)
        leaves[owner] |= 1 << i
    formulas, cuts = [], set()
    for support, membership in zip(leaves, memberships):
        positive, negative = (tuple(sum(1 << i for i, lit in enumerate(row) if lit in model) for row in axis)
                              for axis in membership)
        if affine_completion is not None:
            tree, deficit, status = complete_affine(support, (p for p in positive if p),
                                                    (z for z in negative if z), max_deficit=affine_completion)
            stats[f'affine_{status}'] += 1
            if tree is not None:
                stats['affine_zero_deficit'] += deficit == 0
                formulas.append((tree, positive, negative, True))
                continue
        tree, obstruction = compatible_tree(support, positive, negative)
        if obstruction is not None:
            cut = obstruction_clause(obstruction, membership)
            if not all(-lit in model for lit in cut):
                raise RuntimeError('obstruction clause does not exclude the candidate')
            cuts.add(cut)
        formulas.append((tree, positive, negative, False))
    if cuts:
        return None, sorted(cuts)
    # Either local constraints enforce intersection, or the matrix equality counts
    # one common terminal per common region and compatibility allows at most one.
    if any(not p & n for _, positive, negative, _ in formulas for p in positive if p for n in negative if n):
        raise RuntimeError('compatible model violated cross-intersection')
    return [tree if exact else restrict_certificates(tree, positive, negative)
            for tree, positive, negative, exact in formulas], ()


def _decode_lazy(formulas, atoms, readers):
    targets = _port_sources(readers)
    used = [tuple(indices(tree_leaves(tree))) for tree in formulas]
    reachable = {0}
    for r, leaves in enumerate(used):
        if r in reachable:
            reachable.update(targets[i] for i in leaves if i < len(targets))
    order = sorted(reachable, reverse=True)
    positions = {r: i for i, r in enumerate(order)}
    groups, packed, providers = [], [], []
    for r in order:
        primary = tuple(i for i in used[r] if i >= len(targets))
        ports = tuple(i for i in used[r] if i < len(targets))
        remap = {leaf: i for i, leaf in enumerate(primary + ports)}

        def rename(tree):
            if isinstance(tree, int):
                return remap[tree]
            op, left, right = tree
            return op, rename(left), rename(right)

        groups.append(sum(atoms[i - len(targets)] for i in primary))
        packed.append(rename(formulas[r]))
        providers.append(tuple(positions[targets[i]] for i in ports))
    return RegionalSolution(tuple(groups), tuple(packed), tuple(providers))


def _decode_topology(topology, readers, model):
    cotree, candidates, atoms = topology
    owners = tuple(next(r for r, pick in enumerate(choices) if pick in model) for choices in candidates)
    targets = tuple(len(readers) - i - 1 for i, degree in enumerate(readers) for _ in range(degree))
    groups, formulas, providers = [], [], []
    for r in range(len(readers), -1, -1):
        primary = tuple(i for i in range(len(atoms)) if owners[len(targets) + i] == r)
        ports = tuple(i for i in range(len(targets)) if owners[i] == r)
        groups.append(sum(atoms[i] for i in primary))
        leaves = tuple(len(targets) + i for i in primary) + ports
        formulas.append(cotree.decode(model, leaves))
        providers.append(tuple(targets[i] for i in ports))
    return RegionalSolution(tuple(groups), tuple(formulas), tuple(providers))


def encode_decomposition(matrix, readers, *, prefix=True, regions=False, certificates=None, lazy=False,
                         local_intersection=False, portcertrank=None, portcertoutput=False, provider_level=None,
                         stats=None):
    """Encode one ordered reader-count pattern, without constructing circuit gates."""
    pool = IDPool()
    clauses = []
    height, width = len(matrix), len(matrix[0])

    def memberships(size):
        groups = []
        for _ in range(size):
            wire = []
            for degree in readers:
                vertex = pool.id()
                edges = tuple(pool.id() for _ in range(degree))
                clauses.append([-vertex, *edges])
                clauses.extend([-edge, vertex] for edge in edges)
                wire.append((vertex, edges))
            groups.append(wire)
        return groups

    def common(a, b):
        both = pool.id()
        clauses.extend(([-both, a], [-both, b], [both, -a, -b]))
        return both

    row_wires, col_wires = memberships(height), memberships(width)
    for _, edges in row_wires[0]:
        # Reader slots are interchangeable. Sort the first row's membership bits.
        clauses.extend([left, -right] for left, right in zip(edges, edges[1:]))
    topology = None
    if lazy:
        topology = _add_lazy_topology(row_wires, col_wires, readers, certificates, pool, clauses)
        if provider_level is not None and local_intersection:
            before = len(clauses)
            _add_provider_ancestry(topology, readers, certificates, pool, clauses)
            if stats is not None:
                stats['provider_static_clauses'] += len(clauses) - before
        if portcertrank is not None and local_intersection:
            before = len(clauses)
            _add_static_port_bounds(topology, certificates, portcertrank, portcertoutput, pool, clauses)
            if stats is not None:
                stats['port_static_clauses'] += len(clauses) - before
    elif regions or certificates is not None:
        topology = _add_topology(row_wires, col_wires, readers, certificates, pool, clauses)
    for i, row in enumerate(matrix):
        for j, target in enumerate(row):
            if target > len(readers):
                clauses.append([])
                continue
            if local_intersection:
                owners, atoms = topology.owners, topology.atoms
                local = [[] for _ in range(len(readers) + 1)]
                ports = [common(x, y) for (_, a), (_, b) in zip(row_wires[i], col_wires[j]) for x, y in zip(a, b)]
                for edge, choices in zip(ports, owners):
                    for r, pick in enumerate(choices):
                        local[r].append(edge if len(choices) == 1 else common(edge, pick))
                shared_atoms = certificates[0][i] & certificates[1][j]
                for atom, choices in zip(atoms, owners[len(ports):]):
                    if atom & shared_atoms:
                        for r, pick in enumerate(choices):
                            local[r].append(pick)
                for r, terminals in enumerate(local):
                    guard = [-row_wires[i][r - 1][0], -col_wires[j][r - 1][0]] if r else []
                    clauses.append(guard + terminals)
                    if len(terminals) > 1:
                        clauses.extend(CardEnc.atmost(terminals, 1, vpool=pool).clauses)
                continue
            if not readers:
                continue
            reached, incoming = [], []
            for (a, a_edges), (b, b_edges) in zip(row_wires[i], col_wires[j]):
                incoming.extend(common(x, y) for x, y in zip(a_edges, b_edges))
                if prefix:
                    # Incoming common edges use distinct paths already present at this cut.
                    lits = incoming + [-vertex for vertex in reached]
                    clauses.extend(CardEnc.atmost(lits, len(reached) + 1, vpool=pool).clauses)
                reached.append(common(a, b))
            lits = reached + [-edge for edge in incoming]
            clauses.extend(CardEnc.equals(lits, target + len(incoming), vpool=pool).clauses)
    return pool.top, clauses, topology


def decomposition_status(matrix, excess, *, prefix=True, regions=False, max_cells=400, conflicts=2000,
                         verify_unsat=None, certificates=None, on_sat=None, backend='complete-terminal', stats=None,
                         local_intersection=False, portcertrank=None, portcertoutput=False, provider_level=None,
                         provider_capacity=None, affine_completion=None):
    """Return SAT, UNSAT, or UNKNOWN for the relaxation at an at-most excess budget."""
    matrix = tuple(map(tuple, matrix))
    if excess < 0 or any(value < 0 for row in matrix for value in row):
        raise ValueError('expected nonnegative intersections and excess')
    lazy = backend == 'lazy-certificates'
    if backend not in ('complete-terminal', 'lazy-certificates') or lazy and certificates is None:
        raise ValueError('expected a complete certificate set for the lazy backend')
    if local_intersection and not lazy:
        raise ValueError('local intersection is available with the lazy backend')
    if portcertoutput and portcertrank is None:
        raise ValueError('output certificate costs require a port certificate level')
    if portcertrank is not None:
        if not lazy or portcertrank not in PORT_CERTIFICATE_LEVELS:
            raise ValueError('certificate port bounds require a valid level and the lazy backend')
    if provider_level is not None and (not lazy or provider_level not in PROVIDER_LEVELS):
        raise ValueError('provider bounds require a valid level and the lazy backend')
    if provider_capacity is not None and (not lazy or provider_capacity not in CAPACITY_LEVELS):
        raise ValueError('provider capacity requires a valid level and the lazy backend')
    if affine_completion is not None and (not lazy or not 0 <= affine_completion <= 5):
        raise ValueError('affine completion requires a deficit cap from zero to five and the lazy backend')
    if portcertrank is not None or provider_level is not None or provider_capacity is not None:
        minterms, zero_certificates = certificates = tuple(map(tuple, certificates))
        if (not minterms or not zero_certificates or any(term <= 0 for term in minterms + zero_certificates)
                or any(a != b and a & b == a for a in minterms for b in minterms)
                or set(zero_certificates) != set(minimal_zero_certificates(tuple(sorted(set(minterms)))))
                or matrix != intersection_matrix(*certificates)):
            raise ValueError('certificate port bounds require matching complete monotone certificates')
    stats = stats if stats is not None else Counter()
    if certificates is None:
        matrix = _compress(matrix)
    if not matrix:
        return 'SAT'
    height, width = len(matrix), len(matrix[0])
    max_entry = max(map(max, matrix))
    rank = max(modular_rank(matrix, prime) for prime in (2, 101))
    if max_entry > excess or rank > 3 * excess - int(prefix and excess > 0):
        return 'UNSAT'
    one_share = one_share_support(matrix)
    if excess >= 1 and one_share and certificates is None:
        return 'SAT'
    if excess == 1 and not one_share:
        return 'UNSAT'
    colors = coexistence_color_bound(*certificates) if certificates is not None else 1
    if colors > excess + 1:
        return 'UNSAT'
    if max_cells is not None and height * width > max_cells:
        return 'UNKNOWN'

    unknown = False
    first = 0 if not max_entry else 1 if one_share else 2
    for used in range(max(first, max_entry, colors - 1), excess + 1):
        for readers in _reader_counts(used):
            first_saves_rank = prefix and bool(readers) and readers[0] == 2
            available_rank = sum(degree + 1 for degree in readers) - int(first_saves_rank)
            if len(readers) < max(max_entry, colors - 1) or available_rank < rank:
                continue
            variables, clauses, topology = encode_decomposition(matrix, readers, prefix=prefix, regions=regions,
                                                                certificates=certificates, lazy=lazy,
                                                                local_intersection=local_intersection,
                                                                portcertrank=portcertrank, portcertoutput=portcertoutput,
                                                                provider_level=provider_level,
                                                                stats=stats)
            capacity_owners = ()
            checked_layouts = set()
            if provider_capacity is not None and readers:
                count = len(topology.atoms)
                if (len(readers) + 1) ** count <= 128 and provider_capacity != 'exact':
                    # Check small primary layouts without constructing any port
                    # ownership or certificate membership for them.
                    for assignments in product(range(len(readers) + 1), repeat=count):
                        cut = _capacity_owner_cut(topology, readers, certificates, assignments,
                                                  provider_capacity, stats, 'static')
                        if cut is not None:
                            clauses.append(cut)
                elif local_intersection:
                    # Local intersections imply capacity on complete models.
                    # Look for useful prefix clauses before asking SAT for one.
                    clauses.extend(_capacity_prefix_clauses(topology, readers, certificates, provider_capacity, stats))
                else:
                    capacity_owners = topology.owners[len(topology.owners) - count:]
            stats['patterns'] += 1
            stats['initial_variables'] += variables
            stats['initial_clauses'] += len(clauses)
            with Solver(name='g4', bootstrap_with=clauses) as solver:
                while True:
                    if conflicts is None:
                        answer = solver.solve()
                    else:
                        remaining = conflicts - solver.accum_stats()['conflicts']
                        if remaining <= 0:
                            answer = None
                            break
                        solver.conf_budget(remaining)
                        answer = solver.solve_limited()
                    if answer is not True:
                        break
                    stats['models'] += 1
                    if not lazy:
                        if on_sat is not None and topology is not None:
                            on_sat(used, _decode_topology(topology, readers, set(solver.get_model())))
                        break
                    model = set(solver.get_model())
                    cuts = ()
                    if capacity_owners:
                        assignments = tuple(next(r for r, pick in enumerate(choices) if pick in model)
                                            for choices in capacity_owners)
                        if assignments not in checked_layouts:
                            checked_layouts.add(assignments)
                            cut = _capacity_owner_cut(topology, readers, certificates, assignments,
                                                      provider_capacity, stats, 'lazy')
                            if cut is not None:
                                cuts = (cut,)
                    if not cuts and portcertrank and not local_intersection:
                        cuts = _lazy_port_cuts(topology, model, certificates, portcertrank, portcertoutput)
                        if cuts:
                            stats['port_cuts'] += len(cuts)
                            stats['port_cut_literals'] += sum(map(len, cuts))
                    if not cuts and provider_level is not None and not local_intersection:
                        reason, cuts = _provider_model_cuts(topology, readers, model, certificates, provider_level)
                        if cuts:
                            stats[f'provider_{reason}_cuts'] += len(cuts)
                    if not cuts:
                        formulas, cuts = _lazy_formulas(topology, model, affine_completion, stats)
                    if not cuts:
                        if on_sat is not None:
                            on_sat(used, _decode_lazy(formulas, topology.atoms, readers))
                        break
                    stats['cuts'] += len(cuts)
                    stats['cut_literals'] += sum(map(len, cuts))
                    for cut in cuts:
                        solver.add_clause(cut)
                    clauses.extend(cuts)
                stats['conflicts'] += solver.accum_stats()['conflicts']
            if answer is False and verify_unsat is not None:
                # Check the final clause set in a fresh proof-producing solver.
                with Solver(name='g4', bootstrap_with=clauses, with_proof=True) as proof_solver:
                    if proof_solver.solve() is not False:
                        raise RuntimeError('UNSAT clause set did not reproduce in proof replay')
                    verify_unsat(readers, variables, clauses, proof_solver.get_proof())
            if answer is True:
                return 'SAT'
            unknown |= answer is None
    return 'UNKNOWN' if unknown else 'UNSAT'


def complete_status(minterms, zero_certificates, excess, **options):
    """Decide the gate budget for a nonconstant complete monotone certificate pair."""
    certificates = tuple(minterms), tuple(zero_certificates)
    if any(not terms or 0 in terms for terms in certificates):
        raise ValueError('expected certificates of a nonconstant complete monotone function')
    return decomposition_status(intersection_matrix(*certificates), excess, certificates=certificates, **options)
