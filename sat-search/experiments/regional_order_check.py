"""Differential checks and bounded ablations for packed regional completion."""

import argparse
from collections import Counter
import cProfile
import json
from pathlib import Path
import pstats
from random import Random
import sys
import unittest

from regional_completion_check import make_completion
from block_order_requirements import block_requirements
from module_contraction import vars as truth_variables
from packed_regional_tables import PackedTables
from port_certificates_check import bounded
from regional_block_completion import indices
from regional_cover_stress import corpus_work, layout_job, regional_job
from regional_row_quotient import quotient_rows
from two_sharing_core import ANY, assignments


METHODS = ('legacy', 'packed', 'ordered')


def indexes(mask):
    return tuple(i for i in range(mask.bit_length()) if mask >> i & 1)


class LegacyTables(PackedTables):
    """The pre-integration block solver's operations, for matched timing."""

    def support(self, table):
        return sum(1 << i for i, column in enumerate(self.columns) if (table ^ (table << (1 << i))) & column)

    def project(self, table, inside, exists):
        for i in indices(self.full ^ inside):
            column = self.columns[i]
            low, high = table & ~column, (table & column) >> (1 << i)
            value = low | high if exists else low & high
            table = value | (value << (1 << i))
        return table

    def exposed(self, table, inside, project=None):
        if table in (ANY, 0, self.one):
            return None
        owned = assignments(tuple(indices(inside)))
        outside = assignments(tuple(indices(self.full ^ inside)))
        constant = (1 << len(owned)) - 1
        found = None
        for fixed in outside:
            part = sum((table >> (a | fixed) & 1) << i for i, a in enumerate(owned))
            if part in (0, constant):
                continue
            if found is not None and found != part:
                return None
            found = part
        if found is None:
            return None
        return sum((found >> i & 1) << (a | fixed) for i, a in enumerate(owned) for fixed in outside)


def ref_project(table, inside, outside, exists):
    quantifier = any if exists else all
    return sum(1 << (a | b) for a in inside if quantifier(table >> (a | c) & 1 for c in outside) for b in outside)


class RegionalOrderChecks(unittest.TestCase):
    def test_packed_operations_against_assignments(self):
        rng = Random(11242026)
        compared = 0
        for m in range(11):
            packed, legacy = PackedTables(m), LegacyTables(m)
            universe = range(1 << m)
            if m < 4:
                cases = ((table, mask) for table in range(1 << (1 << m)) for mask in universe)
            else:
                cases = ((rng.getrandbits(1 << m), rng.randrange(1 << m)) for _ in range(200))
            for index, (table, mask) in enumerate(cases):
                inside = assignments(indexes(mask))
                outside = assignments(indexes(packed.full ^ mask))
                if m >= 4 and index % 2 == 0:
                    pattern = rng.getrandbits(len(inside))
                    table = 0
                    for b in outside:
                        values = rng.choice((0, pattern, (1 << len(inside)) - 1))
                        table |= sum((values >> j & 1) << (a | b) for j, a in enumerate(inside))
                support = sum(1 << i for i in range(m) if any((table >> a ^ table >> (a ^ (1 << i))) & 1
                                                             for a in universe))
                self.assertEqual(packed.support(table), support)
                for existential in (False, True):
                    self.assertEqual(packed.project(table, mask, existential),
                                     ref_project(table, inside, outside, existential))
                self.assertEqual(packed.exposed(table, mask), legacy.exposed(table, mask))
                compared += 1
        self.assertEqual(compared, 3522)

    def test_order_requirement_uses_the_direction_of_provider_change(self):
        tables = PackedTables(2)
        x, y = tables.columns
        rows = ((0, y), (1, x & y))
        self.assertEqual(block_requirements((1,), rows, (1, 2), tables.project, True, False, 3), ((1,),))
        self.assertEqual(block_requirements((1,), rows, (1, 2), tables.project, True, True, 3), ((3,),))
        self.assertEqual(block_requirements((1,), rows, (1, 2), tables.project, True, False, 2), ((0,),))

    def test_ordered_completion_keeps_the_original_comparator_witness(self):
        from layout_projection import search_exact
        from ordered_quotient_core import reconstruct

        n, target, excess = 5, 0xe8a0a080, 5  # comparator-02
        layout = search_exact(n, target, excess, completion=make_completion('ordered-block'))
        self.assertIsNotNone(layout)
        gates, _ = reconstruct(n, target, *layout, excess)
        self.assertEqual(len(gates), 9)

    def test_row_quotient_keeps_extremal_monotone_obligations(self):
        self.assertEqual(quotient_rows((0, 1, 2, 3, 3), (0, 0, 15, 15, 15), False, 15),
                         (ANY, 0, 15, ANY, ANY))
        self.assertEqual(quotient_rows((0, 1, 2, 3, 3), (0, 0, 15, 15, 15), True, 15),
                         (0, 0, 15, 15, ANY))
        self.assertIsNone(quotient_rows((3, 3), (10, 12), True, 15))


def profile_call(function, args, enabled):
    if not enabled:
        return function(*args)
    profiler = cProfile.Profile()
    result = profiler.runcall(function, *args)
    groups = Counter()
    for (file, _, name), (_, calls, own, cumulative, _) in pstats.Stats(profiler).stats.items():
        if name in ('support', 'project', 'exposed') and (
                file.endswith('packed_regional_tables.py') or file.endswith('regional_order_check.py')):
            group = name
        elif name in ('block_requirements', 'quotient_rows'):
            group = name
        elif file.endswith('regional_block_completion.py') and name in ('port_partitions', 'complete', 'branch'):
            group = name
        elif file.endswith('regional_obligation_cache.py') and name == '_normalize':
            group = 'normalize'
        else:
            continue
        groups[group, 'calls'] += calls
        groups[group, 'own_seconds'] += own
        groups[group, 'cumulative_seconds'] += cumulative
    result['profile'] = {name: {metric: groups[name, metric] for metric in ('calls', 'own_seconds', 'cumulative_seconds')}
                         for name in sorted({name for name, _ in groups})}
    return result


def wide_queries():
    """Generated exact slices with six through ten private coordinates."""
    rng = Random(73911)
    for m in (6, 8, 10):
        one = (1 << (1 << m)) - 1
        for signed in (False, True):
            for trial in range(4):
                ports = (1, 3, 5) if trial % 2 == 0 else (1, 1, 3, 5)
                pats = tuple(sum((a >> i & 1) << port for i, port in enumerate((1, 3, 5))) for a in range(8))
                nodes = [(column,) * len(pats) for column in truth_variables(m)]
                nodes.extend(tuple(one if p >> port & 1 else 0 for p in pats) for port in ports)
                nodes = [tuple(one ^ v for v in row) if signed and rng.randrange(2) else row for row in nodes]
                while len(nodes) > 1:
                    left, right = (nodes.pop(rng.randrange(len(nodes))) for _ in range(2))
                    nodes.append(tuple(a & b for a, b in zip(left, right)) if rng.randrange(2)
                                 else tuple(a | b for a, b in zip(left, right)))
                yield dict(case=f'wide-{m}-{int(signed)}-{trial}', m=m, signed=signed, expected='SAT'), (
                    m, ports, pats, nodes[0], signed)


def selected_layouts(all_layouts):
    for work in corpus_work():
        if work[0] == 'comparator-09':
            # Its independently certified 12-gate exclusion leaves 13 open.
            yield (*work[:3], 7, *work[4:])
        elif work[0] == 'comparator-04' or all_layouts:
            yield work


def run(args, emit):
    expected = {}
    if args.dataset in ('capture', 'layout'):
        worklist = ((dict(case=work[0], n=work[1], truth=hex(work[2]), excess=work[3]), work)
                    for work in selected_layouts(args.dataset == 'layout'))
    elif args.dataset == 'wide':
        worklist = wide_queries()
    else:
        records = [json.loads(line) for path in args.source for line in path.read_text(encoding='utf-8').splitlines()]
        worklist = ((dict(case=row['case'], sequence=call['sequence'], capture_excess=row['excess'],
                          m=call['query'][0], signed=call['query'][-1], expected=call.get('status')), call['query'])
                    for row in records for call in row['calls'])

    for context, work in worklist:
        key = tuple(context.items())
        methods = ('packed',) if args.dataset == 'capture' else args.methods
        for method in methods:
            mode = {'ordered': 'ordered-block', 'quotient': 'row-quotient'}.get(method, 'port-first-witness')
            tables = LegacyTables if method == 'legacy' else None
            if args.dataset in ('capture', 'layout'):
                function = layout_job
                work_args = (work, mode, args.seconds, args.dataset == 'capture', True, tables)
            else:
                function, work_args = regional_job, (work, mode, args.seconds, tables)
            record = bounded(profile_call, (function, work_args, args.profile), args.seconds + 1)
            if record['status'] != 'TIMEOUT':
                wanted = expected.setdefault(key, context.get('expected') or record['status'])
                assert record['status'] == wanted, (context, method, record['status'], wanted)
            emit({**record, **context, 'method': method})


def main():
    if '--bench' not in sys.argv:
        unittest.main()
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bench', action='store_true')
    parser.add_argument('--dataset', required=True, choices=('capture', 'captured', 'wide', 'layout'))
    parser.add_argument('--source', type=Path, action='append', default=[])
    parser.add_argument('--methods', choices=(*METHODS, 'quotient'), nargs='+', default=METHODS)
    parser.add_argument('--profile', action='store_true')
    parser.add_argument('--seconds', type=float, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.seconds <= 0 or args.dataset == 'captured' and not args.source:
        parser.error('need a positive deadline and a --source for captured replay')
    with args.output.open('x', encoding='utf-8') as stream:
        def emit(record):
            line = json.dumps(dict(dataset=args.dataset, cap=args.seconds, profile_enabled=args.profile, **record),
                              sort_keys=True)
            stream.write(line + '\n')
            stream.flush()
            print(line, flush=True)

        run(args, emit)


if __name__ == '__main__':
    main()
