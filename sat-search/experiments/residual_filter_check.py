"""Replay the attached filter oracle and ablate filters on frozen Percy boundaries."""

import argparse
from collections import Counter
import json
from pathlib import Path
import sys
from time import perf_counter

from slack_one_native_check import _native, captured_boundaries

MODES = ('off', 'root', 'parity', 'direct')


def check(reference):
    counts = Counter()
    filtered = reference.Filtered

    class Checked(filtered):
        def solve(self, slack):
            witness = super().solve(slack)
            # Use a non-contiguous care mask that can include row 63.
            def spread(column):
                return sum(((column >> row) & 1) << (4 * row + 3) for row in range(self.rows))

            columns = [spread(c) for c in self.cols]
            target, care = spread(self.target), spread(self.mask)
            for mode in range(len(MODES)):
                if slack:
                    status = _native.slack_one_extensions(
                        columns, self.h, [], 0, target, care, work_limit=2_000_000, filter_mode=mode)[0]
                else:
                    status = _native.tight_residual(columns, self.h, target, care, 2_000_000, mode)
                assert status == int(witness is not None), (slack, mode, columns, target, status)
            counts[slack] += 1
            return witness

    reference.Filtered = Checked
    reference.checks()
    a, b, c, d, e = reference.independent_columns(5)
    args = [a & b, c], 1, (a, b, c, d, e), 1 << 2, a & b & c & d, (1 << 32) - 1
    for mode in range(len(MODES)):
        assert _native.slack_one_extensions(*args, filter_mode=mode)[:3] == (0, 1 << 3, 0)
        assert _native.slack_one_extensions(*args, filter_mode=mode, work_limit=0)[:3] == (2, 0, 0)
        assert _native.slack_one_extensions(*args, filter_mode=mode, deadline_seconds=1e-12)[:3] == (2, 0, 0)
        assert _native.slack_one_extensions(
            *args, filter_mode=mode, tight_work_limit=0)[:3] == (0, 0, 0b11011)
    print(json.dumps(dict(kind='oracle', slack_zero=counts[0], slack_one=counts[1],
                          comparisons=sum(counts.values()) * len(MODES))), flush=True)


def replay(reference, capture, output):
    boundaries = list(captured_boundaries(reference, capture, 64))
    assert boundaries
    with output.open('x', encoding='utf-8') as log:
        for name, record, first, mixed, primaries, rows, target, care in boundaries:
            columns = [*first, *(primaries[i] for i in mixed)]
            independent = reference.Filtered(columns, len(first), rows, target)
            witness = independent.solve(1)
            if witness is not None:
                independent.verify(witness, 1)
            expected = int(witness is not None)
            required, excluded = 0, 0
            for cap in (100_000, 2_000_000):
                for mode, label in enumerate(MODES):
                    started = perf_counter()
                    status, feasible, unknown, kind, work, candidates, filtered, decoders, counters = (
                        _native.slack_one_extensions(
                            columns, len(first), primaries, record['mixed'], target, care,
                            work_limit=cap, tight_work_limit=4096, filter_mode=mode, include_metrics=True))
                    elapsed = perf_counter() - started
                    if status == 0:
                        possible_extensions = ((1 << len(primaries)) - 1) ^ record['mixed']
                        required |= feasible
                        excluded |= possible_extensions & ~(feasible | unknown)
                        assert not (required & excluded), (name, record, mode, cap)
                    if status != 2:
                        assert status == expected, (name, record, mode, cap, status, expected)
                    row = dict(name=name, types=record['types'], mixed=record['mixed'], k=record['k'],
                               width=len(columns), captured_status=record['exact'], mode=label, work_limit=cap,
                               status=status, expected=expected, feasible_extensions=feasible, unknown_extensions=unknown,
                               seconds=elapsed, case=kind, work=work, providers=candidates,
                               filtered=filtered, decoders=decoders, **counters)
                    log.write(json.dumps(row) + '\n')
    print(f'Replayed {len(boundaries)} unique Percy boundaries across {len(MODES)} modes and two caps.', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('reference_dir', type=Path)
    parser.add_argument('--capture', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    sys.path.insert(0, str(args.reference_dir.resolve()))
    import residual_parity_filter
    if args.capture and args.output:
        replay(residual_parity_filter, args.capture, args.output)
    elif not args.capture and not args.output:
        check(residual_parity_filter)
    else:
        parser.error('--capture and --output must be supplied together')


if __name__ == '__main__':
    main()
