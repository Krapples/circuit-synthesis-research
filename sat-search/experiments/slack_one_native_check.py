"""Replay the attached independent slack-one reference and captured Percy queries."""

import argparse
from collections import Counter
import importlib.util
from itertools import combinations
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'theory'))
from regional_native import _native


def check_generated(reference):
    counts = Counter()
    reference_solver = reference.Solver

    class CheckedSolver(reference_solver):
        def solve(self, slack):
            witness = super().solve(slack)
            if slack == 1:
                rows = range(self.rows)
                # Include a care hole between every pair of rows.
                def spread(value):
                    return sum(((value >> row) & 1) << (2 * row + 1) for row in rows)

                status, _, _, kind, *_ = _native.slack_one_extensions(
                    [spread(col) for col in self.cols], self.h, [], 0,
                    spread(self.target), spread(self.mask), work_limit=2_000_000)
                assert status == int(witness is not None), (self.cols, self.h, self.target, status)
                counts['oracle slack-one'] += 1
                counts[('infeasible', 'boundary', 'provider')[kind]] += 1
            return witness

    reference.Solver = CheckedSolver
    reference.check()
    reference.Solver = reference_solver

    extension_cut = reference.extension_cut

    def check_extension(first, mixed, primaries, rows, target):
        expected = extension_cut(first, mixed, primaries, rows, target)
        boundary = [*first, *(primaries[i] for i in mixed)]
        mask = sum(1 << i for i in mixed)
        args = boundary, len(first), primaries, mask, target, (1 << rows) - 1
        status, feasible, unknown, *_ = _native.slack_one_extensions(
            *args, work_limit=2_000_000, tight_work_limit=2_000_000)
        assert status == (expected is None) and not unknown, (args, expected, status, feasible, unknown)
        if expected is not None:
            assert feasible == sum(1 << i for i in expected)
            low = _native.slack_one_extensions(*args, work_limit=2_000_000, tight_work_limit=0)
            assert low[:3] == (0, 0, ((1 << len(primaries)) - 1) ^ mask), (args, low)
        counts['generated extensions'] += 1
        return expected

    reference.extension_cut = check_extension
    reference.extension_screen()
    reference.extension_cut = extension_cut

    # abcd has the tight extension d from H=(ab), M=(c). Adding e cannot
    # make up for the missing d. A bounded-out extension must be retained.
    a, b, c, d, e = reference.independent_columns(5)
    primaries = a, b, c, d, e
    args = [a & b, c], 1, primaries, 1 << 2, a & b & c & d, (1 << 32) - 1
    assert extension_cut([a & b], [2], primaries, 32, a & b & c & d) == (3,)
    assert _native.slack_one_extensions(*args)[:3] == (0, 1 << 3, 0)
    assert _native.slack_one_extensions(*args, tight_work_limit=0)[:3] == (0, 0, 0b11011)

    # A signal cannot feed both operands, even with complementary phases.
    # Two distinct wires of equal value are allowed.
    assert _native.slack_one_extensions([0xaa], 1, [], 0, 0xaa, 0xff)[0] == 0
    assert _native.slack_one_extensions([0xaa, 0xaa], 2, [], 0, 0, 0xff)[0] == 1
    assert _native.slack_one_extensions([0xaa], 1, [], 0, 0xaa, 0xff, work_limit=0)[0] == 2
    assert _native.slack_one_extensions([0xaa], 1, [], 0, 0xaa, 0xff, deadline_seconds=1e-12)[0] == 2
    columns = reference.independent_columns(6)
    assert _native.slack_one_extensions(columns, 1, [], 0, columns[0], (1 << 64) - 1,
                                        work_limit=0)[0] == 2
    assert _native.slack_one_extensions([0] * 7, 1, [], 0, 0, 1)[0] == 2
    assert _native.slack_one_extensions([0] * 6, 1, [0], 0, 1, 3)[:3] == (0, 0, 1)
    print(json.dumps(dict(kind='generated', **counts)), flush=True)


def captured_boundaries(reference, path, limit):
    with path.open(encoding='utf-8') as source:
        jobs = [json.loads(line) for line in source]
    seen = set()
    for job in jobs:
        n, target = job['n'], int(job['tt'], 16)
        primaries = reference.independent_columns(n)
        rows = 1 << n
        care = (1 << rows) - 1
        pairs = [(a, b) for b in range(n) for a in range(b)]
        for record in job['records']:
            if record.get('event') != 'slack_one':
                continue
            types, mixed = record['types'], record['mixed']
            key = n, target, tuple(sorted(types)), mixed
            if key in seen:
                continue
            seen.add(key)
            first = []
            for index in types:
                a, b = (primaries[i] for i in pairs[index // 4])
                first.append((a & ~b, ~a & b, a & b, a | b)[index % 4])
            mixed_ids = [i for i in range(n) if mixed >> i & 1]
            yield job['name'], record, first, mixed_ids, primaries, rows, target, care
            if len(seen) == limit:
                return


def check_captured(reference, path, limit):
    counts = Counter()
    for name, record, first, mixed_ids, primaries, rows, target, care in captured_boundaries(reference, path, limit):
        status = record['exact']
        boundary = [*first, *(primaries[i] for i in mixed_ids)]
        replay, feasible, unknown, *_ = _native.slack_one_extensions(
            boundary, len(first), primaries, record['mixed'], target, care,
            work_limit=2_000_000, tight_work_limit=2_000_000)
        if status == 2:
            counts[f'offline from unknown to {replay}'] += 1
        else:
            assert replay == status, (name, record, replay)
        if len(boundary) <= 5:
            expected = reference.extension_cut(first, mixed_ids, primaries, rows, target)
            counts['Python reference'] += 1
            assert replay == (expected is None), (name, record, expected, replay)
            if expected is not None:
                possible = sum(1 << i for i in expected)
                assert possible & ~unknown == feasible
                if status == 0:
                    possible &= ~record['unknown_extensions']
                    assert possible == record['feasible_extensions'], (name, record, expected)
        counts['case ' + str(status)] += 1
        counts['conditional'] += status == 0 and bool(record['feasible_extensions'] | record['unknown_extensions'])
        counts['checked'] += 1
    print(json.dumps(dict(kind='captured', **counts)), flush=True)
    assert counts['checked']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('reference', type=Path)
    parser.add_argument('--captured', type=Path)
    parser.add_argument('--limit', type=int, default=64)
    args = parser.parse_args()
    module = importlib.util.spec_from_file_location('slack_one_reference', args.reference)
    reference = importlib.util.module_from_spec(module)
    module.loader.exec_module(reference)
    if args.captured:
        check_captured(reference, args.captured, args.limit)
    else:
        check_generated(reference)


if __name__ == '__main__':
    main()
