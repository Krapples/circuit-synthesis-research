"""Verify reconstructed native residuals and replay fixed Percy boundaries."""

import argparse
from collections import Counter
import json
from pathlib import Path
from statistics import median
import sys
from time import perf_counter

from slack_one_native_check import _native, captured_boundaries

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'baselines'))
from benchmark_memory import limit_commit_mib

MODES = ('columns', 'directed', 'dominance')


def verify(witness, columns, h, target, care, slack):
    case, repeated, subset, provider_column, provider, decoder = witness
    boundary = [(i, col, i >= h) for i, col in enumerate(columns)]
    anchor = care & -care
    gates = 0

    def eval_tree(w, leaves):
        tree, phase = w
        used = set()

        def visit(t):
            nonlocal gates
            if t[0] == 'x':
                i = t[1]
                assert 0 <= i < len(leaves) and i not in used
                used.add(i)
                value = leaves[i][1] & care
                return value ^ (care if value & anchor else 0)
            op, pa, pb, po, a, b = t
            assert op == '&'
            if a[0] == b[0] == 'x':
                left, right = leaves[a[1]], leaves[b[1]]
                assert left[0] != right[0] and not (left[2] and right[2])
            x, y = visit(a), visit(b)
            gates += 1
            return ((x ^ (care if pa else 0)) & (y ^ (care if pb else 0))) ^ (care if po else 0)

        value = visit(tree)
        assert used == set(range(len(leaves)))
        return value ^ (care if phase else 0)

    assert bool(case) == bool(slack)
    if case == 1:
        assert provider is None and subset == 0
        boundary.append(boundary[repeated])
    if case == 2:
        inside = [leaf for i, leaf in enumerate(boundary) if subset >> i & 1]
        assert 2 <= len(inside) < len(boundary)
        assert eval_tree(provider, inside) == provider_column
        boundary = [leaf for i, leaf in enumerate(boundary) if not (subset >> i & 1)]
        boundary += [(len(columns), provider_column, False)] * 2
    assert eval_tree(decoder, boundary) == target & care
    assert gates == len(columns) - 1 + slack


def check(reference):
    counts = Counter()

    class Checked(reference.Directed):
        def solve(self, slack):
            reference_witness = super().solve(slack)
            expected = reference_witness is not None

            def scatter(col):
                return sum((col >> r & 1) << (4 * r + 3) for r in range(self.rows))

            columns = [scatter(col) for col in self.cols]
            target, care = scatter(self.target), scatter(self.mask)
            for dominance in (False, True):
                status, witness = _native.directed_completion(columns, self.h, target, care, slack,
                                                               2_000_000, dominance)
                assert status == int(expected), (columns, self.h, target, slack, status)
                if witness:
                    verify(witness, columns, self.h, target, care, slack)
                    counts[f'witness_{witness[0]}'] += 1
            counts[f'slack_{slack}'] += 1
            # The reference independently verifies its own witness.
            return reference_witness

    reference.Directed = Checked
    reference.check()
    a, b, c, d, e = reference.independent_columns(5)
    args = [a & b, c], 1, (a, b, c, d, e), 1 << 2, a & b & c & d, (1 << 32) - 1
    for backend in (1, 2):
        assert _native.slack_one_extensions(*args, backend=backend)[:3] == (0, 1 << 3, 0)
        assert _native.slack_one_extensions(*args, backend=backend, work_limit=0)[:3] == (2, 0, 0)
        assert _native.slack_one_extensions(*args, backend=backend, deadline_seconds=1e-12)[:3] == (2, 0, 0)
        assert _native.slack_one_extensions(*args, backend=backend, tight_work_limit=0)[:3] == (0, 0, 27)
    status, witness = _native.directed_completion([0xaa, 0xcc], 1, 0, 0, 0)
    assert status == 1
    verify(witness, [0xaa, 0xcc], 1, 0, 0, 0)
    print(json.dumps(dict(kind='oracle', **counts)), flush=True)


def replay(reference, capture, output, memory_mib):
    boundaries = list(captured_boundaries(reference, capture, 64))
    assert len(boundaries) == 34
    with output.open('x', encoding='utf-8') as log:
        for index, (name, record, first, mixed, primaries, _, target, care) in enumerate(boundaries):
            columns = [*first, *(primaries[i] for i in mixed)]
            for cap in (100_000, 2_000_000):
                timings = [[] for _ in MODES]
                samples = [[] for _ in MODES]
                feasible, excluded = 0, 0
                for pass_index in range(5):
                    for offset in range(len(MODES)):
                        backend = (index + pass_index + offset) % len(MODES)
                        started = perf_counter()
                        result = _native.slack_one_extensions(
                            columns, len(first), primaries, record['mixed'], target, care,
                            work_limit=cap, tight_work_limit=4096, deadline_seconds=0.025,
                            filter_mode=3, include_metrics=True, backend=backend)
                        timings[backend].append(perf_counter() - started)
                        samples[backend].append(result)
                        status, allowed, unknown = result[:3]
                        assert status != 1, (name, record, result)  # verified Python exclusions from prior replay
                        if status == 0:
                            feasible |= allowed
                            excluded |= ((1 << len(primaries)) - 1) & ~(record['mixed'] | allowed | unknown)
                            assert not (feasible & excluded), (name, record, result)
                for backend, label in enumerate(MODES):
                    runs = samples[backend]
                    status, allowed, unknown, _, work, _, _, _, counters = runs[0]
                    log.write(json.dumps(dict(
                        name=name, types=record['types'], mixed=record['mixed'], k=record['k'],
                        width=len(columns), mode=label, work_limit=cap, memory_mib=memory_mib,
                        deadline_seconds=0.025, median_seconds=median(timings[backend]),
                        samples_seconds=timings[backend], samples_status=[r[0] for r in runs],
                        status=status, feasible_extensions=allowed, unknown_extensions=unknown,
                        work=work, **counters)) + '\n')
    print('Replayed 34 captured boundaries, five samples per mode and cap.', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('reference_dir', type=Path)
    parser.add_argument('--capture', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--memory-mib', type=int, default=512)
    args = parser.parse_args()
    limit_commit_mib(args.memory_mib)
    sys.path.insert(0, str(args.reference_dir.resolve()))
    import residual_target_recursion
    if args.capture and args.output:
        replay(residual_target_recursion, args.capture, args.output, args.memory_mib)
    elif not args.capture and not args.output:
        check(residual_target_recursion)
    else:
        parser.error('--capture and --output must be supplied together')


if __name__ == '__main__':
    main()
