"""Verify slack-two witnesses and replay actual Percy boundaries."""

import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
import sys
from time import perf_counter
from types import SimpleNamespace

from slack_one_native_check import _native, captured_boundaries

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'baselines'))
from benchmark_memory import limit_commit_mib


def independent_columns(n):
    return tuple(sum(1 << row for row in range(1 << n) if row >> i & 1) for i in range(n))


def types(primaries):
    return [column for b, y in enumerate(primaries) for x in primaries[:b]
            for column in (x & ~y, ~x & y, x & y, x | y)]


def verify(columns, h, target, care, regions):
    anchor = care & -care

    def normalize(col):
        return (col & care) ^ (care if col & anchor else 0)

    wires = {i: (normalize(col), i >= h) for i, col in enumerate(columns)}
    reads = Counter()
    gates = 0
    assert 1 <= len(regions) <= 3
    for out, col, inputs, (tree, phase) in regions:
        assert out == len(wires)
        assert len(inputs) >= 2
        occurrences = Counter()

        def evaluate(node):
            nonlocal gates
            if node[0] == 'x':
                occurrence = node[1]
                assert 0 <= occurrence < len(inputs)
                wire, value, raw = inputs[occurrence]
                assert wires[wire] == (value, raw)
                occurrences[occurrence] += 1
                reads[wire] += 1
                return value
            op, pa, pb, po, a, b = node
            assert op == '&'
            if a[0] == b[0] == 'x':
                left, right = inputs[a[1]], inputs[b[1]]
                assert left[0] != right[0] and not (left[2] and right[2])
            gates += 1
            return ((evaluate(a) ^ (care if pa else 0)) &
                    (evaluate(b) ^ (care if pb else 0))) ^ (care if po else 0)

        assert evaluate(tree) ^ (care if phase else 0) == col & care
        assert occurrences == dict.fromkeys(range(len(inputs)), 1)
        wires[out] = col, False
    assert (col ^ target) & care == 0
    assert set(reads) == set(wires) - {out}
    assert all(reads[wire] >= 2 for wire in range(len(columns), out))
    assert sum(count - 1 for count in reads.values()) == 2
    assert gates == len(columns) + 1


def direct_tables(columns, h, care):
    """Enumerate exact trimmed distinct-fanin DAGs directly for small boundaries."""
    k = len(columns)
    tables = set()
    wires = list(columns)

    def visit(used, left):
        if not left:
            if used == (1 << (len(wires) - 1)) - 1:
                tables.update((wires[-1], wires[-1] ^ care))
            return
        for a, b in combinations(range(len(wires)), 2):
            if h <= a < b < k:
                continue
            mask = used | (1 << a) | (1 << b)
            if len(wires) - mask.bit_count() > left:
                continue
            x, y = wires[a], wires[b]
            for value in (x & ~y, ~x & y, x & y, x | y):
                wires.append(value & care)
                visit(mask, left - 1)
                wires.pop()

    visit(0, k + 1)
    return tables


def check():
    checks = 0
    for k in (2, 3):
        full = (1 << (1 << k)) - 1
        for care in (full, full ^ 1, full ^ 17 if k == 3 else full ^ 2):
            for h in range(1, k + 1):
                columns = [col & care for col in independent_columns(k)]
                expected = direct_tables(columns, h, care)
                for value in range(full + 1):
                    if value & ~care:
                        continue
                    for mode in (0, 2, 3, 4, 5):
                        metrics, regions = _native.slack_two_boundary(
                            columns, h, [], 0, [], value, care, 2_000_000, 0, mode)
                        assert metrics['status'] == (value in expected), (columns, h, care, value, mode)
                        assert bool(regions) == (metrics['status'] == 1)
                        if regions:
                            verify(columns, h, value, care, regions)
                        checks += 1

    a, b, c, d, e = primaries = independent_columns(5)
    columns = [a & b, c]
    args = columns, 1, primaries, 4, types(primaries), a & b & c & d & e, 0xffffffff
    for mode in (2, 3, 4, 5):
        metrics, regions = _native.slack_two_boundary(*args, deadline_seconds=0, mode=mode)
        assert not regions and metrics['status'] == 0 and metrics['extension_unknown'] == 0, metrics
        assert metrics['extension_feasible'] == 2, metrics
        assert metrics['mixed_extensions'] == 24 and metrics['gate_extensions'] == 1 << 38, metrics
        for limits in ((0, 0), (100_000, 1e-12)):
            metrics, regions = _native.slack_two_boundary(*args, *limits, mode)
            assert not regions and metrics['status'] == 2 and not metrics['extension_excluded'], metrics

    # Identical columns still describe distinct first-layer wires.
    columns = [0x88, 0x88, 0xf0]
    care = 0xff
    expected = direct_tables(columns, 2, care)
    for mode in (2, 3, 4, 5):
        for target in (0, 0x80, 0xf0, 0x7f):
            metrics, regions = _native.slack_two_boundary(columns, 2, [], 0, [], target, care, mode=mode)
            assert metrics['status'] == (target in expected)
            if regions:
                verify(columns, 2, target, care, regions)

    x, y, z = columns = independent_columns(3)
    for mode in (4, 5):
        # This cap interrupts the first phase check before any exact tree call.
        metrics, regions = _native.slack_two_boundary(columns, 3, [], 0, [], 0x96, care, 24, 0, mode)
        assert not regions and metrics['status'] == 2 and metrics['phase_checks'] == 1
        assert not (metrics['phase_rejects'] or metrics['tree_calls'] or metrics['extension_excluded'])

        # (x & z) XOR y can be binate in x and z even when each feeds only
        # the shared provider. Screening the whole DAG as one tree would be unsound.
        target = (x & z) ^ y
        metrics, regions = _native.slack_two_boundary(columns, 3, [], 0, [], target, care, mode=mode)
        assert metrics['status'] == 1
        verify(columns, 3, target, care, regions)
    print(json.dumps({'oracle_comparisons': checks, 'duplicated_wire_checks': 16,
                      'extension_and_limit_checks': 14, 'shared_provider_checks': 2}))


def replay(path, output, work_limit, deadline, limit, modes, repetitions):
    reference = SimpleNamespace(independent_columns=independent_columns)
    with output.open('x', encoding='utf-8') as out:
        for name, record, first, mixed_ids, primaries, _, target, care in captured_boundaries(
                reference, path, limit, event='slack_two'):
            columns = [*first, *(primaries[i] for i in mixed_ids)]
            assert record['k'] == 2 * len(first) + len(mixed_ids) + 1
            gate_columns = types(primaries)
            decided = set()
            for repetition in range(repetitions):
                offset = repetition % len(modes)
                for mode in (*modes[offset:], *modes[:offset]):
                    start = perf_counter()
                    metrics, regions = _native.slack_two_boundary(
                        columns, len(first), primaries, record['mixed'], gate_columns, target, care,
                        work_limit, deadline, mode)
                    elapsed = perf_counter() - start
                    if metrics['status'] != 2:
                        decided.add(metrics['status'])
                    if metrics['status'] == 1:
                        verify(columns, len(first), target, care, regions)
                    out.write(json.dumps(dict(record, **metrics, name=name, mode=mode, repetition=repetition,
                                              wall_seconds=elapsed, deadline_seconds=deadline,
                                              work_limit=work_limit)) + '\n')
            assert len(decided) <= 1, (name, record, decided)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--capture', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--work-limit', type=int, default=100_000)
    parser.add_argument('--deadline', type=float, default=0.025)
    parser.add_argument('--limit', type=int, default=128)
    parser.add_argument('--memory-mib', type=int, default=512)
    parser.add_argument('--modes', type=int, nargs='+', choices=range(6), default=list(range(4)))
    parser.add_argument('--repetitions', type=int, default=1)
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error('--repetitions must be positive')
    limit_commit_mib(args.memory_mib)
    if args.capture:
        if not args.output:
            parser.error('--capture requires --output')
        replay(args.capture, args.output, args.work_limit, args.deadline, args.limit, args.modes, args.repetitions)
    else:
        check()
