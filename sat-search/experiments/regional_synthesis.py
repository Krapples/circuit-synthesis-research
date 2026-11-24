"""Exact small monotone read-once regions with increasingly constrained port signals."""

from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import cube_search  # loads the repository's vendored PySAT
from partial_ordered import feature_columns, forced_terminal_indices
from pysat.card import CardEnc
from pysat.formula import IDPool
from pysat.solvers import Solver

from cograph_formulas import CographFormula


MAX_LEAVES = 6


def _bits(mask):
    return tuple(1 << i for i in range(mask.bit_length()) if mask >> i & 1)


def _pack(row, bits):
    return sum(1 << i for i, bit in enumerate(bits) if row & bit)


@lru_cache(maxsize=None)
def _formulas(width, leaves):
    """Truth table to representative formula on exactly these labeled leaves."""
    low = leaves & -leaves
    if low == leaves:
        index = low.bit_length() - 1
        return {feature_columns(width)[index]: index}
    tables = {}
    left = (leaves - 1) & leaves
    while left:
        if left & low:
            for a, fa in _formulas(width, left).items():
                for b, fb in _formulas(width, leaves ^ left).items():
                    tables.setdefault(a & b, (0, fa, fb))
                    tables.setdefault(a | b, (1, fa, fb))
        left = (left - 1) & leaves
    return tables


def one_port_feasible(group, earlier, positives, negatives):
    """Exact feasibility with at most one monotone port occurrence on forced rows."""
    bits = _bits(group)
    width = len(bits)
    if not 1 <= width < MAX_LEAVES:
        raise ValueError(f'one-port test requires 1 to {MAX_LEAVES - 1} primary inputs')
    rows = [(_pack(row, bits), row & earlier, target)
            for target, points in ((1, positives), (0, negatives)) for row in points]
    leaves = (1 << width) - 1
    if any(all((table >> local) & 1 == value for local, _, value in rows)
           for table in _formulas(width, leaves)):
        return True
    port = 1 << width
    for table in _formulas(width + 1, leaves | port):
        required = (set(), set())
        for local, context, value in rows:
            zero, one = (table >> local) & 1, (table >> (local | port)) & 1
            if value < zero or value > one:
                break
            if zero != one:
                required[value].add(context)
        else:
            if all(a & ~b for a in required[1] for b in required[0]):
                return True
    return False


@dataclass(frozen=True)
class RegionalSolution:
    groups: tuple
    formulas: tuple
    providers: tuple | None  # None for relaxed modes

    def evaluate(self, row):
        if self.providers is None:
            raise ValueError('only linked formulas form a circuit')

        def value(formula, leaves):
            if isinstance(formula, int):
                return leaves[formula]
            op, left, right = formula
            a, b = value(left, leaves), value(right, leaves)
            return a & b if op == 0 else a | b

        signals = []
        for group, formula, providers in zip(self.groups, self.formulas, self.providers):
            leaves = [bool(row & bit) for bit in _bits(group)] + [signals[i] for i in providers]
            signals.append(value(formula, leaves))
        return signals[-1]


def _layout_domain(groups, ports, labels, reader_limits):
    groups, ports = tuple(groups), tuple(ports)
    if not groups or len(groups) != len(ports) or any(group < 0 or count < 0 for group, count in zip(groups, ports)):
        raise ValueError('expected a nonempty sequence of groups and corresponding nonnegative port counts')
    limits = tuple(reader_limits) if reader_limits is not None else ((1, None),) * (len(groups) - 1)
    if len(limits) != len(groups) - 1 or any(lo < 0 or hi is not None and hi < lo for lo, hi in limits):
        raise ValueError('expected a valid reader range per non-output terminal')
    support = 0
    for group in groups:
        if support & group:
            raise ValueError('groups must be disjoint')
        support |= group
    if any(row < 0 or row & ~support for row in labels):
        raise ValueError('row outside the regional primary-input domain')
    widths = tuple(group.bit_count() + count for group, count in zip(groups, ports))
    return groups, ports, limits, widths


def synthesize_signed_formula(columns, positive, negative, *, solver='g4'):
    """Return (read-once formula, leaf negation mask) with free NOT gates, or None."""
    if not columns or positive & negative:
        raise ValueError('expected leaves and disjoint labels')
    pool = IDPool()
    signs = tuple(pool.id(('negate', i)) for i in range(len(columns)))
    clauses = []
    encoding = CographFormula(len(columns), pool, 'signed', clauses)
    for row in _bits(positive | negative):
        values = tuple(-sign if row & col else sign for sign, col in zip(signs, columns))
        encoding.require(row, values, bool(row & positive))
    with Solver(name=solver, bootstrap_with=clauses) as sat:
        if not sat.solve():
            return None
        model = set(sat.get_model())
    return encoding.decode(model), sum(1 << i for i, sign in enumerate(signs) if sign in model)


def synthesize_regions(groups, ports, labels, *, mode='linked', reader_limits=None, solver='g4',
                       formula_encoding='tables'):
    """Solve fixed ordered groups and port occurrences on a partial {row: bool} table.

    Free port values can vary by row. Consistent ports are monotone functions of
    earlier inputs. Linked ports use actual earlier terminals and per-terminal
    (min, max) reader limits, where max=None is unbounded. Default minimum is one.
    The cograph encoding constructs formulas without enumerating regional tables.
    Return a solution or None for UNSAT. Every regional leaf must occur once.
    """
    if mode not in ('free', 'consistent', 'linked'):
        raise ValueError('expected free, consistent, or linked mode')
    if reader_limits is not None and mode != 'linked':
        raise ValueError('reader limits require linked ports')
    if formula_encoding not in ('tables', 'cograph'):
        raise ValueError('expected table or cograph formula encoding')
    groups, ports, limits, widths = _layout_domain(groups, ports, labels, reader_limits)
    if formula_encoding == 'tables' and max(widths) > MAX_LEAVES:
        raise ValueError(f'regional synthesis supports at most {MAX_LEAVES} leaves per region')
    if not min(widths) or ports[0]:
        return None

    rows = tuple(sorted(labels))
    positives = tuple(row for row in rows if labels[row])
    negatives = tuple(row for row in rows if not labels[row])
    cuts = tuple(tuple(a & ~b for b in negatives) for a in positives)
    pool = IDPool()
    clauses = []
    outputs = [{row: pool.id(('out', i, row)) for row in rows} for i in range(len(groups))]
    readers = [[] for _ in limits]
    choices, wiring = [], []
    earlier = 0
    for i, (group, count, width) in enumerate(zip(groups, ports, widths)):
        out = outputs[i]
        if i == len(groups) - 1:
            fixed = labels
            clauses.extend([out[row] if labels[row] else -out[row]] for row in rows)
        else:
            pos, neg = forced_terminal_indices(group, cuts)
            fixed = {**dict.fromkeys((positives[j] for j in pos), True),
                     **dict.fromkeys((negatives[j] for j in neg), False)}
            clauses.extend([out[positives[j]]] for j in pos)
            clauses.extend([-out[negatives[j]]] for j in neg)

        port_values = []
        sources = []
        for slot in range(count):
            if mode == 'consistent':
                contexts = {row & earlier: pool.id(('port', i, slot, row & earlier)) for row in rows}
                clauses.extend([-va, vb] for a, va in contexts.items() for b, vb in contexts.items()
                               if a != b and a & ~b == 0)
                port_values.append({row: contexts[row & earlier] for row in rows})
            else:
                values = {row: pool.id(('port', i, slot, row)) for row in rows}
                port_values.append(values)
                if mode == 'linked':
                    candidates = [pool.id(('source', i, slot, src)) for src in range(i)]
                    sources.append(candidates)
                    clauses.extend(CardEnc.equals(candidates, 1, vpool=pool).clauses)
                    for src, pick in enumerate(candidates):
                        readers[src].append(pick)
                        for row, value in values.items():
                            provider = outputs[src][row]
                            clauses.extend(([-pick, -value, provider], [-pick, value, -provider]))
        wiring.append(sources)

        bits = _bits(group)
        if formula_encoding == 'cograph':
            encoding = CographFormula(width, pool, i, clauses)
            for row in rows:
                values = tuple(bool(row & bit) for bit in bits) + tuple(port[row] for port in port_values)
                if row in fixed:
                    encoding.require(row, values, fixed[row])
                else:
                    encoding.require(row, values, True, guard=out[row])
                    encoding.require(row, values, False, guard=-out[row])
            choices.append(encoding)
        else:
            local_rows = {row: _pack(row, bits) for row in rows}
            selected = []
            for table, formula in _formulas(width, (1 << width) - 1).items():
                pick = pool.id(('formula', i, table))
                selected.append((pick, formula))
                for row, local in local_rows.items():
                    for values in range(1 << count):
                        mismatch = [-port[row] if values >> j & 1 else port[row] for j, port in enumerate(port_values)]
                        high = (table >> (local | (values << len(bits)))) & 1
                        clauses.append([-pick, *mismatch, out[row] if high else -out[row]])
            clauses.append([pick for pick, _ in selected])
            choices.append(selected)
        earlier |= group

    if mode == 'linked':
        for used, (minimum, maximum) in zip(readers, limits):
            if minimum > len(used):
                return None
            if minimum:
                clauses.extend(CardEnc.atleast(used, minimum, vpool=pool).clauses)
            if maximum is not None and maximum < len(used):
                clauses.extend(CardEnc.atmost(used, maximum, vpool=pool).clauses)
    with Solver(name=solver, bootstrap_with=clauses) as sat:
        if not sat.solve():
            return None
        model = set(sat.get_model())
    if formula_encoding == 'cograph':
        formulas = tuple(encoding.decode(model) for encoding in choices)
    else:
        formulas = tuple(next(formula for pick, formula in selected if pick in model) for selected in choices)
    providers = None
    if mode == 'linked':
        providers = tuple(tuple(next(src for src, pick in enumerate(slot) if pick in model) for slot in region)
                          for region in wiring)
    return RegionalSolution(groups, formulas, providers)
