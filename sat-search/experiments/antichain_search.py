"""At-most monotone synthesis over concrete boundary-row signal antichains."""

from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations, product

from joint_regional_synthesis import synthesize_partition
from label_formulas import obligation_tree
from regional_search import MAX_KNOWN_LEAVES, _known_formulas, _port_counts, canonical_layouts, dominates, synthesize_forward
from regional_synthesis import _bits
from subtree_formulas import constrained_formulas, forced_by_outside, subtree_possible
from twocolor_completion import complete as complete_twocolor


def minimal_demands(demands):
    """Remove duplicate demands and supersets of another demand."""
    minimal = []
    for demand in sorted(set(demands), key=lambda d: (d.bit_count(), d)):
        if not any(other & demand == other for other in minimal):
            minimal.append(demand)
    return tuple(minimal)


@lru_cache(maxsize=65536)
def hitting_number(demands):
    """Exact hitting number of a tuple normalized by minimal_demands."""
    if not demands:
        return 0
    if demands[0] == 0:
        return float('inf')
    return 1 + min(hitting_number(tuple(d for d in demands if not d & bit)) for bit in _bits(demands[0]))


def frontier_demands(columns, positive, negative):
    def row_columns(row):
        return sum(1 << i for i, table in enumerate(columns) if table & row)

    ones = {row_columns(row) for row in _bits(positive)}
    zeros = {row_columns(row) for row in _bits(negative)}
    return minimal_demands(a & ~b for a in ones for b in zeros)


def _hitting_sets(columns, demands, size):
    for indices in combinations(range(len(columns)), size):
        used = sum(1 << i for i in indices)
        if all(d & used for d in demands):
            yield tuple(columns[i] for i in indices)


def state_dominates(stronger, weaker, negative):
    """Unrestricted fan-out allows several weaker columns to share a substitute."""
    return all(any(dominates(h, g, negative) for h in stronger) for g in weaker)


def useful_signal(table, positive, negative):
    return bool(table & positive and negative & ~table)


def preserving_gates(columns, demands, required, candidates, row_pairs):
    """Tables of gates that lower the hitting number by one."""
    if required < 2 or not candidates:
        return set()
    total = (1 << len(row_pairs)) - 1

    def coverage(table):
        return sum(1 << i for i, (a, b) in enumerate(row_pairs) if table & a and not table & b)

    covers = {table: coverage(table) for table in columns}
    residuals = {}
    for used in _hitting_sets(columns, demands, required):
        for a, b in combinations(used, 2):
            covered = 0
            for wire in used:
                if wire != a and wire != b:
                    covered |= covers[wire]
            residuals.setdefault((a, b), set()).add(total ^ covered)
    result = set()
    for table, (_, a, b, _) in candidates.items():
        if (a, b) in residuals:
            covered = coverage(table)
            if any(demand & ~covered == 0 for demand in residuals[a, b]):
                result.add(table)
    return result


def _formula_steps(formula, leaves, steps):
    if isinstance(formula, int):
        return leaves[formula]
    op, left, right = formula
    a = _formula_steps(left, leaves, steps)
    b = _formula_steps(right, leaves, steps)
    table = a & b if op == 0 else a | b
    steps.append((op, a, b, table))
    return table


def _regional_steps(solution, columns):
    steps, signals = [], []
    for group, formula, providers in zip(solution.groups, solution.formulas, solution.providers):
        leaves = [columns[bit.bit_length() - 1] for bit in _bits(group)] + [signals[i] for i in providers]
        signals.append(_formula_steps(formula, leaves, steps))
    return tuple(steps)


def _splits(columns, include_empty=False):
    """Ordered splits, with the whole set available to the first side."""
    for subset in range(0 if include_empty else 1, 1 << len(columns)):
        yield (tuple(col for i, col in enumerate(columns) if subset >> i & 1),
               tuple(col for i, col in enumerate(columns) if not subset >> i & 1))


def _direct_completion(used, excess, positive, negative, stats, *, subtreecuts=True, twocolorcompletion=False,
                       typedsubtreecuts=False, labelcompletion=False, seen=None):
    """Enumerate private formulas for up to two units of excess fan-out."""
    complete = True
    if seen is None:
        seen = set()

    def demand(outside):
        return forced_by_outside(tuple(sorted(outside)), positive, negative) if subtreecuts else (0, 0)

    def options(leaves, required):
        nonlocal complete
        leaves = tuple(sorted(leaves))  # port occurrences remain distinct even when columns agree
        if len(leaves) > MAX_KNOWN_LEAVES:
            complete = False
            return leaves, {}
        stats['formula_tests'] += 1
        p, n = required if subtreecuts else (0, 0)
        query = leaves, p, n
        if p or n:
            tables, rejected = constrained_formulas(leaves, p, n, negative)
        else:
            tables, rejected = _known_formulas(leaves, negative, 0, True, False), False
        if rejected:
            stats['structural_rejections'] += 1
        if query not in seen:
            seen.add(query)
            stats['distinct_formula_tests'] += 1
            stats['distinct_structural_rejections' if rejected else 'distinct_formula_enumerations'] += 1
        return leaves, tables

    def final(leaves, prefix=()):
        formula = None
        if twocolorcompletion:
            status, formula = complete_twocolor(leaves, positive, negative)
            stats[f'twocolor_{status}'] += 1
            if status == 'unsat':
                return None
        if formula is None and (typedsubtreecuts or labelcompletion):
            leaves = tuple(sorted(leaves))
            within_width = len(leaves) <= MAX_KNOWN_LEAVES
            if subtreecuts and within_width and not subtree_possible(leaves, positive, negative):
                stats['output_subtree_rejections'] += 1
                return None
            if typedsubtreecuts and (within_width or labelcompletion):
                stats['typed_subtree_tests'] += 1
                if obligation_tree(leaves, positive, negative, exact=False) is None:
                    stats['typed_subtree_rejections'] += 1
                    return None
            if labelcompletion:
                stats['label_completion_tests'] += 1
                formula = obligation_tree(leaves, positive, negative, exact=True)
                if formula is None:
                    return None
        if formula is None:
            leaves, tables = options(leaves, (positive, negative))
            formula = tables.get(positive)
            if formula is None:
                return None
        steps = []
        for private_formula, inputs in prefix:
            _formula_steps(private_formula, inputs, steps)
        _formula_steps(formula, leaves, steps)
        return tuple(steps)

    plan = final(used)
    if plan is not None or excess == 0:
        return plan, complete
    stats['one_sharing_sets'] += 1
    for a, rest in _splits(used):
        if not rest:
            continue  # repeating a formula on all inputs just gives that same formula
        inputs, tables = options(a, demand(rest))
        for h1, f1 in tables.items():
            plan = final((*rest, h1, h1), ((f1, inputs),))
            if plan is not None:
                return plan, True
    if excess == 1:
        return None, complete
    stats['two_sharing_sets'] += 1
    for a, rest in _splits(used):
        if not rest:
            continue
        inputs, tables = options(a, demand(rest))
        for h1, f1 in tables.items():
            first = (f1, inputs)
            plan = final((*rest, h1, h1, h1), (first,))
            if plan is not None:
                return plan, True
            for b, c in _splits(rest, include_empty=True):
                for q in range(3):
                    if not b and q < 2:
                        continue  # an empty private region needs a binary gate
                    outside = c + (h1,) * (2 - q)
                    middle, middle_tables = options(b + (h1,) * q, demand(outside))
                    for h2, f2 in middle_tables.items():
                        plan = final(outside + (h2, h2), (first, (f2, middle)))
                        if plan is not None:
                            return plan, True
    return None, complete


def _complete(columns, demands, required, budget, positive, negative, stats, *, subtreecuts, twocolorcompletion,
              typedsubtreecuts, labelcompletion, seen):
    """Try all viable suffix input sets. An unsupported layout defers to gate search."""
    complete = True
    for size in range(max(1, required), min(len(columns), budget + 1) + 1):
        for used in _hitting_sets(columns, demands, size):
            excess = budget - size + 1
            plan, covered = _direct_completion(used, min(2, excess), positive, negative, stats,
                                               subtreecuts=subtreecuts, twocolorcompletion=twocolorcompletion,
                                               typedsubtreecuts=typedsubtreecuts, labelcompletion=labelcompletion,
                                               seen=seen)
            if plan is not None:
                return plan, True
            complete &= covered
            if excess <= 2:
                continue
            labels = {sum(1 << i for i, col in enumerate(used) if col & row): bool(row & positive)
                      for row in _bits(positive | negative)}
            for gates in range(size + 2, budget + 1):
                for groups, ports in canonical_layouts(size, gates):
                    stats['regional_tests'] += 1
                    limits = ((2, None),) * (len(groups) - 1)
                    try:
                        solution = synthesize_forward(groups, ports, labels, reader_limits=limits,
                                                      state_dominance=False)
                    except NotImplementedError:
                        complete = False
                        continue
                    if solution is not None:
                        return _regional_steps(solution, used), True
    return None, complete


def _joint_completion(columns, required, budget, positive, negative, stats, *, on_unsat=None):
    labels = {sum(1 << i for i, col in enumerate(columns) if col & row): bool(row & positive)
              for row in _bits(positive | negative)}
    for count in range(1, budget - required + 3):
        for total in range(2 * (count - 1), budget + count - required + 1):
            input_limit = min(len(columns), budget + count - total)
            for ports in _port_counts(count, total):
                stats['joint_completion_patterns'] += 1
                solution = synthesize_partition(len(columns), ports, labels, input_limit=input_limit, on_unsat=on_unsat)
                if solution is not None:
                    return _regional_steps(solution, columns)
    return None


@dataclass(frozen=True)
class Circuit:
    inputs: int
    gates: tuple
    output: int

    def evaluate(self, row):
        wires = [bool(row >> i & 1) for i in range(self.inputs)]
        for op, left, right in self.gates:
            a, b = wires[left], wires[right]
            wires.append(a & b if op == 0 else a | b)
        return wires[self.output]


def _reconstruct(columns, plan, target):
    wires = {table: i for i, table in enumerate(columns)}
    gates = []
    for op, a, b, table in plan:
        if table not in wires:
            wires[table] = len(columns) + len(gates)
            gates.append((op, *sorted((wires[a], wires[b]))))
    return Circuit(len(columns), tuple(gates), wires[target])


def solve_columns(columns, positive, negative, budget, *, antichain=True, hitting=True, tight=True,
                  sharing=None, nondegenerate=True, sharing_order=False, subtreecuts=True,
                  twocolorcompletion=False, typedsubtreecuts=False, labelcompletion=False,
                  jointcompletion=False, dominance_memo=False, stats=None):
    """Return a witness of at most budget gates, or None after exhaustive rejection."""
    columns = tuple(columns)
    if not columns or not isinstance(budget, int) or budget < 0 or min(positive, negative, min(columns)) < 0 or positive & negative:
        raise ValueError('expected nonnegative columns and disjoint labels, inputs, and gate budget')
    if any(table & ~(positive | negative) for table in columns):
        raise ValueError('columns must contain only labeled rows')
    if sharing is not None and (not isinstance(sharing, int) or sharing < 0 or not hitting):
        raise ValueError('sharing completion requires hitting-set pruning and a nonnegative integer allowance')
    if sharing_order and not hitting:
        raise ValueError('sharing order requires hitting-set pruning')
    nondegenerate = bool(nondegenerate and positive and negative)
    row_pairs = tuple(product(_bits(positive), _bits(negative))) if sharing_order else ()
    stats = stats if stats is not None else Counter()
    seen_queries = set()
    failed = {}
    state = tuple(sorted(set(columns)))
    if nondegenerate:
        state = tuple(g for g in state if useful_signal(g, positive, negative))
    if antichain:
        state = tuple(g for g in state if not any(h != g and dominates(h, g, negative) for h in state))

    def visit(state, remaining):
        if positive in state:
            return ()
        if failed.get(state, -1) >= remaining:
            stats['memo_hits'] += 1
            return None
        if dominance_memo and any(b >= remaining and state_dominates(old, state, negative)
                                  for old, b in failed.items()):
            stats['dominance_hits'] += 1
            return None
        stats['states'] += 1
        plan = search(state, remaining)
        if plan is None:
            failed[state] = max(remaining, failed.get(state, -1))
        return plan

    def search(state, remaining):
        if not remaining:
            return None
        if hitting:
            demands = frontier_demands(state, positive, negative)
            required = hitting_number(demands)
            allowance = remaining + 1 - required
            if allowance < 0:
                stats['frontier_rejections'] += 1
                return None
            if (tight and allowance == 0) or (sharing is not None and allowance <= sharing):
                stats['completion_states'] += 1
                if jointcompletion:
                    return _joint_completion(state, required, remaining, positive, negative, stats)
                suffix, complete = _complete(state, demands, required, remaining, positive, negative, stats,
                                             subtreecuts=subtreecuts, twocolorcompletion=twocolorcompletion,
                                             typedsubtreecuts=typedsubtreecuts, labelcompletion=labelcompletion,
                                             seen=seen_queries)
                if complete:
                    return suffix
        candidates = {}
        for a, b in combinations(state, 2):
            for op, table in ((0, a & b), (1, a | b)):
                if table == positive:
                    return ((op, a, b, table),)
                if (table not in state and table not in candidates
                        and (not nondegenerate or useful_signal(table, positive, negative))
                        and (not antichain or not any(dominates(h, table, negative) for h in state))):
                    candidates[table] = (op, a, b, table)
        if remaining == 1:
            return None
        order = set()
        if sharing_order:
            order = preserving_gates(state, demands, required, candidates, row_pairs)
            stats['preserving_gates'] += len(order)
            stats['spending_gates'] += len(candidates) - len(order)
            if allowance == 0:
                candidates = {table: candidates[table] for table in order}
        for table in sorted(candidates, key=lambda t: (t not in order, -(t ^ negative).bit_count(), t)):
            kept = (g for g in state if not antichain or not dominates(table, g, negative))
            following = tuple(sorted((*kept, table)))
            suffix = visit(following, remaining - 1)
            if suffix is not None:
                return (candidates[table], *suffix)
        return None

    plan = visit(state, budget)
    return None if plan is None else _reconstruct(columns, plan, positive)


def solve_partial(n, labels, budget, **options):
    """Synthesize a monotone circuit for a partial {input pattern: target bit} table."""
    if n < 1 or any(row < 0 or row >= 1 << n for row in labels):
        raise ValueError('expected labels on a positive-width input domain')
    rows = tuple(sorted(labels))
    positive = sum(1 << i for i, row in enumerate(rows) if labels[row])
    negative = ((1 << len(rows)) - 1) ^ positive
    columns = tuple(sum(1 << j for j, row in enumerate(rows) if row >> i & 1) for i in range(n))
    return solve_columns(columns, positive, negative, budget, **options)


def main():
    import argparse
    from time import perf_counter
    from cube_search import boundary_rows

    parser = argparse.ArgumentParser(description='Exact at-most monotone gate search on boundary rows')
    parser.add_argument('--n', type=int, required=True)
    parser.add_argument('--edges', required=True, help='comma-separated edges such as 0-1,1-2')
    parser.add_argument('--budget', type=int, required=True)
    parser.add_argument('--no-antichain', action='store_true')
    parser.add_argument('--no-hitting', action='store_true')
    parser.add_argument('--tightfrontier', action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument('--subtreecuts', action=argparse.BooleanOptionalAction, default=True,
                        help='rule out impossible subtree structures before enumerating formulas')
    parser.add_argument('--twocolorcompletion', action='store_true', help='try SAT two-coloring on single-zero formula queries')
    parser.add_argument('--typedsubtreecuts', action='store_true', help='propagate forced labels through output operations')
    parser.add_argument('--labelcompletion', action='store_true', help='search output formulas by assigning label obligations')
    parser.add_argument('--jointcompletion', action='store_true', help='use joint regional SAT at completion states')
    parser.add_argument('--sharing', type=int, help='try completion at this sharing allowance or lower')
    parser.add_argument('--nondegenerate', action=argparse.BooleanOptionalAction, default=True,
                        help='prune columns that distinguish no positive-negative pair')
    parser.add_argument('--sharing-order', action='store_true', help='try gates that preserve sharing allowance first')
    parser.add_argument('--state-dominance', action='store_true', help='compare failed states by noninjective coverage')
    parser.add_argument('--certrank', action='store_true', help='try certificate-intersection rank at the graph root')
    parser.add_argument('--certdecomp', action='store_true', help='also try the certificate decomposition through excess three')
    args = parser.parse_args()
    try:
        edges = [tuple(map(int, edge.split('-'))) for edge in args.edges.split(',')]
        if any(not (0 <= a < args.n and 0 <= b < args.n and a != b) for a, b in edges):
            raise ValueError('each edge needs two distinct endpoints in range')
        masks = tuple(sorted({(1 << a) | (1 << b) for a, b in edges}))
        positive, negative = boundary_rows(args.n, masks)
        labels = {**dict.fromkeys(positive, True), **dict.fromkeys(negative, False)}
        stats = Counter()
        start = perf_counter()
        if args.budget < 0:
            raise ValueError('expected a nonnegative gate budget')
        excluded = False
        if args.certrank or args.certdecomp:
            from certificate_rank import analyze, coexistence_color_bound, intersection_matrix

            full = (1 << args.n) - 1
            zeros = tuple(full ^ row for row in negative)
            bound = analyze(positive, zeros)
            stats.update(cert_rank=bound.rank, cert_bound=bound.gates)
            excluded = args.budget < bound.gates
            support_bound = bound.gates - bound.excess
            excess = args.budget - support_bound
            if args.certdecomp and not excluded:
                colors = coexistence_color_bound(positive, zeros)
                stats['cert_colors'] = colors
                excluded = excess + 1 < colors
            if args.certdecomp and not excluded and excess <= 3:
                from certificate_decomposition import decomposition_status

                status = decomposition_status(intersection_matrix(positive, zeros), excess, regions=True, conflicts=500)
                stats[f'cert_decomp_{status.lower()}'] += 1
                excluded = status == 'UNSAT'
        if excluded:
            circuit = None
            stats['cert_rejections'] += 1
        else:
            circuit = solve_partial(args.n, labels, args.budget, antichain=not args.no_antichain,
                                    hitting=not args.no_hitting, tight=args.tightfrontier, sharing=args.sharing,
                                    nondegenerate=args.nondegenerate, sharing_order=args.sharing_order,
                                    subtreecuts=args.subtreecuts,
                                    twocolorcompletion=args.twocolorcompletion,
                                    typedsubtreecuts=args.typedsubtreecuts, labelcompletion=args.labelcompletion,
                                    jointcompletion=args.jointcompletion,
                                    dominance_memo=args.state_dominance, stats=stats)
    except ValueError as error:
        parser.error(str(error))
    if circuit is None:
        print(f'UNSAT through size {args.budget}')
    else:
        if not all(circuit.evaluate(row) == any(row & mask == mask for mask in masks) for row in range(1 << args.n)):
            raise RuntimeError('reconstructed circuit failed full truth-table verification')
        print(f'WITNESS {len(circuit.gates)} gates, full truth table verified')
        print(circuit)
    print(f'{dict(stats)} in {perf_counter() - start:.3f}s')


if __name__ == '__main__':
    main()
