"""Bounded, instrumented split of the size-19 L1343 shard-2 x0 OR x2 cube."""

import argparse
import json
import math
from multiprocessing import Pool, TimeoutError
from pathlib import Path
import random
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import cube_search as cs
import l1343_full as shard
from partial_ordered import (monotone_closure, ordered_group_counter, pair_conflicts,
                             projected_suffix_bounds, terminal_demands)

PARENT = (1, 0, 2)
BUDGET = 19
BASE = next(args for case, _, gate, args in shard.tasks_for(BUDGET)
            if case == 'a' and gate == PARENT)
PREFIX = (BASE[4], *(tuple(gate[1:]) for gate in BASE[7]['fixgates']))
MASKS = tuple(shard.MASKS)


def continuations():
    width = shard.n + len(PREFIX)
    for right in range(width):
        for left in range(right):
            if (right, left) >= (PARENT[2], PARENT[1]):
                for op in (0, 1):
                    yield op, left, right


def screen(gate):
    start = time.perf_counter()
    bound = cs.ordered_prefix_bound(shard.n, MASKS, (*PREFIX, gate))
    return dict(event='screen', gate=gate, bound=bound if math.isfinite(bound) else 'infeasible',
                status='EXCLUDED' if bound > BUDGET else 'OPEN', seconds=time.perf_counter() - start)


def two_groups(conflicts, cuts):
    """Test every ordered bipartition of the pair-conflict graph."""
    uncolored = (1 << len(conflicts)) - 1
    first_groups = [0]
    while uncolored:
        a, b = uncolored & -uncolored, 0
        queue = a
        uncolored ^= a
        while queue:
            bit = queue & -queue
            queue ^= bit
            neighbors = conflicts[bit.bit_length() - 1]
            if neighbors & (a if a & bit else b):
                return False
            fresh = uncolored & neighbors
            if a & bit:
                b |= fresh
            else:
                a |= fresh
            uncolored ^= fresh
            queue |= fresh
        first_groups = [group | color for group in first_groups for color in (a, b)]
    # The second group can obtain every nonlocal distinction from the first.
    return any(not terminal_demands(group, cuts) for group in first_groups)


def within_ordered_budget(width, mandatory, positives, negatives, budget):
    cuts = {a & ~b for a in positives for b in negatives}
    if 0 in cuts:
        return False
    for cut in cuts:
        if cut.bit_count() == 1:
            mandatory |= cut
    optional = ((1 << width) - 1) ^ mandatory
    subset = 0
    while True:
        used = mandatory | subset
        size = used.bit_count()
        max_groups = budget + 2 - size
        if size <= budget + 1 and all(used & cut for cut in cuts):
            bits = tuple(1 << i for i in range(width) if used >> i & 1)

            def project(rows):
                return tuple(sorted({sum(1 << i for i, bit in enumerate(bits) if row & bit) for row in rows}))

            pos, neg = project(positives), project(negatives)
            ones, zeros = monotone_closure(size, pos, neg)
            if not ones & zeros:
                conflicts = pair_conflicts(size, ones, zeros)
                if not any(conflicts):
                    return True
                if max_groups == 2:
                    if two_groups(conflicts, tuple(tuple(a & ~b for b in neg) for a in pos)):
                        return True
                elif max_groups > 2 and ordered_group_counter(size, pos, neg)(0) <= max_groups:
                    return True
        if subset == optional:
            return False
        subset = (subset - optional) & optional


def screen_threshold(gate):
    start = time.perf_counter()
    prefix = (*PREFIX, gate)
    rows = cs.prefix_boundary(shard.n, MASKS, prefix)
    survives = within_ordered_budget(shard.n + len(prefix), *rows, BUDGET - len(prefix))
    return dict(event='screen', gate=gate, status='OPEN' if survives else 'EXCLUDED',
                seconds=time.perf_counter() - start)


def check_threshold():
    rng = random.Random(1343)
    checks = 0
    for width in range(2, 8):
        for trial in range(80):
            count = 1 << width
            rows = rng.sample(range(count), rng.randint(2, min(20, count)))
            if trial % 4:
                terms = rng.sample(range(1, count), rng.randint(1, min(6, count - 1)))
                pos = [row for row in rows if any(row & term == term for term in terms)]
                neg = [row for row in rows if row not in pos]
                if not pos or not neg:
                    continue
            else:
                pos, neg = rows[:len(rows) // 2], rows[len(rows) // 2:]
            mandatory = rng.randrange(count)
            minimum = min((bound for _, bound in projected_suffix_bounds(width, mandatory, pos, neg)),
                          default=math.inf)
            for budget in range(2 * width):
                actual = within_ordered_budget(width, mandatory, pos, neg, budget)
                assert actual == (minimum <= budget), (width, mandatory, pos, neg, budget, minimum)
                checks += 1
    print(f'{checks} threshold comparisons passed')


def solve(job):
    gate, solver_name, conflicts, telemetry = job
    start = time.perf_counter()
    flags = {**BASE[7], 'cert': True, 'frontier': True, 'reuse': False}
    if gate is not None:
        flags['fixgates'] = [*flags['fixgates'], (len(PREFIX), *gate)]
    solver_factory = cs.Solver

    def make_solver(*args, **kwargs):
        solver = solver_factory(*args, **kwargs)
        original = solver.solve_limited

        def measured(*args, **kwargs):
            solver.conf_budget(conflicts)
            with telemetry.open('a', encoding='utf-8') as trace:
                trace.write(json.dumps(dict(seconds=time.perf_counter() - start,
                                            vars=solver.nof_vars(), clauses=solver.nof_clauses())) + '\n')
            return original(*args, **kwargs)

        solver.solve_limited = measured
        return solver

    cs.Solver = make_solver
    try:
        args = (*BASE[:3], solver_name, *BASE[4:7], flags)
        _, status, circuit, seconds, stats = cs.run_cube(args)
    finally:
        cs.Solver = solver_factory
    if status == 'WITNESS':
        fixed = PREFIX if gate is None else (*PREFIX, gate)
        assert len(circuit) == BUDGET and tuple(circuit[:len(fixed)]) == fixed
        assert all(cs.evaluate(shard.n, circuit, row) == any(row & mask == mask for mask in MASKS)
                   for row in range(1 << shard.n))
    return dict(event='solve', gate=gate, status='UNKNOWN' if status == 'STOPPED' else status,
                circuit=circuit, seconds=seconds, stats=stats)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', nargs='?', type=Path)
    parser.add_argument('--check', action='store_true', help='compare threshold decisions with the exact bound')
    source_mode = parser.add_mutually_exclusive_group()
    source_mode.add_argument('--screen', type=Path, help='replay open branches from this screen into SAT')
    source_mode.add_argument('--recheck', type=Path, help='recheck every open branch with the full ordered bound')
    parser.add_argument('--threshold', action='store_true', help='screen with the budget decision test')
    parser.add_argument('--workers', type=int, default=8)
    parser.add_argument('--seconds', type=float, default=120)
    parser.add_argument('--solver', choices=('cadical195', 'glucose42'), default='cadical195')
    parser.add_argument('--conflicts', type=int, default=20_000)
    args = parser.parse_args()
    if args.check:
        check_threshold()
        return
    if args.output is None:
        parser.error('output is required for a screen or SAT run')
    full = list(continuations())
    assert len(full) == 208
    source = args.screen or args.recheck
    if source:
        rows = [json.loads(line) for line in source.read_text(encoding='utf-8').splitlines()]
        screened = {tuple(row['gate']): row['status'] for row in rows if row['event'] == 'screen'}
        assert set(screened) <= set(full)
        gates = [gate for gate in full if screened.get(gate) == 'OPEN']
    if args.screen:
        # Each job has an independent file so a deadline can stop a worker
        # even if it is inside the solver or has yet to reach it.
        traces = args.output.parent / (args.output.stem + '_timing')
        traces.mkdir()
        jobs = [(gate, args.solver, args.conflicts, traces / f'{i}.jsonl')
                for i, gate in enumerate([None, *gates])]
        work = solve
    elif args.recheck:
        jobs, work = gates, screen
    else:
        jobs = full
        work = screen_threshold if args.threshold else screen

    start = time.perf_counter()
    deadline = start + args.seconds
    with args.output.open('x', encoding='utf-8') as output:
        def record(**row):
            output.write(json.dumps(dict(row, elapsed=time.perf_counter() - start)) + '\n')
            output.flush()

        record(event='start', prefix=PREFIX, budget=BUDGET, jobs=len(jobs), workers=args.workers,
               seconds_limit=args.seconds, solver=args.solver if args.screen else None,
               conflicts_per_call=args.conflicts if args.screen else None, threshold=args.threshold)
        finished = 0
        with Pool(args.workers) as pool:
            results = pool.imap_unordered(work, jobs)
            while finished < len(jobs):
                try:
                    row = results.next(timeout=max(0, deadline - time.perf_counter()))
                except TimeoutError:
                    break
                if args.recheck:
                    assert row['status'] == 'OPEN', row
                record(**row)
                finished += 1
                if row['status'] == 'WITNESS':
                    break
        if args.screen:
            for (gate, _, _, trace) in jobs:
                if trace.exists():
                    rows = [json.loads(line) for line in trace.read_text(encoding='utf-8').splitlines()
                            if line.endswith('}')]
                    if rows:
                        record(event='first_solver_call', gate=gate, **rows[0])
        record(event='end', finished=finished, remaining=len(jobs) - finished)
        print(f'{finished}/{len(jobs)} jobs returned in {time.perf_counter() - start:.2f}s', flush=True)


if __name__ == '__main__':
    main()
