"""ARCHIVED evidence driver: the L-meta-1343 shard-2 size-19 ordered-only replay (2026-11-24).

Original location: .scratch-sat/l1343_size19_partialordered.py (untracked scratch folder), sha256
8fae432c35a8a2873521d0439e5384a3c8cabda27b9693a3dd523ab5ca4cfd61. It produced sat-search/logs/l1343_size19_partialordered.log (sha256 93910d6d0a07df9611be8f67ad9d67da7ccdaac2dcc2924c4ecdec24ee43e99f): 315 of 338
cubes excluded analytically, 23 survivors (results/l1343_size19_survivors.json).
Archived unchanged except for this docstring, ROOT (one directory deeper), and the log path argument,
so a replay writes a new log instead of failing on the existing one (the original opened it with mode x).
Evidence class: analytical (partial ordered bound, then forced repeats); SAT is disabled by replacing
cube_search.build and cube_search.Solver. Rule-dependent: correctness rests on the bound proofs
(NOTES_L1343.md) and their differential coverage (verify/AUDIT.md), not on checked SAT proofs.
Usage: python sat-search/experiments/archive/l1343_size19_partialordered.py [log_path]
"""
import os
import sys
import time
from collections import Counter
from multiprocessing import Pool
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'sat-search'))
import cube_search as cs
import l1343_full as shard

class ReachedSATEncoding(Exception):
    pass

def stop_at_encoding(*args, **kwargs):
    raise ReachedSATEncoding()

def forbid_solver(*args, **kwargs):
    raise AssertionError('unexpected SAT solver call')

def setup_worker():
    cs.build = stop_at_encoding
    cs.Solver = forbid_solver

def analytical_result(args, repeat):
    flags = {**args[7], 'partialordered': True, 'partialrepeat': repeat}
    try:
        _, status, _, _, reason = cs.run_cube((*args[:7], flags))
    except ReachedSATEncoding:
        return None
    if status != 'UNSAT' or not reason.startswith('analytical:'):
        raise AssertionError((status, reason))
    return reason

def screen(task):
    case, _, piece, args = task
    ordered = analytical_result(args, repeat=False)
    combined = ordered if ordered is not None else analytical_result(args, repeat=True)
    return case, piece, args[2], ordered, combined

def main():
    start = time.monotonic()
    log = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / 'sat-search' / 'logs' / 'l1343_size19_partialordered.log'
    tasks = shard.tasks_for(19)
    workers = min(16, max(1, (os.cpu_count() or 2) - 2))
    counts = Counter()
    survivors = []
    ordered_survivors = []

    with log.open('x', encoding='utf-8') as out:
        def say(message):
            line = f'{time.monotonic()-start:7.2f}s {message}'
            print(line, flush=True)
            out.write(line + '\n')
            out.flush()

        say(f'L-meta-1343 shard 2 | size 19 | {len(tasks)} cubes | {workers} workers | SAT disabled')
        say('First pass uses --partialordered as at size 17; second pass adds --partialrepeat on the survivors.')
        with Pool(workers, initializer=setup_worker) as pool:
            for done, (case, piece, budget, ordered, combined) in enumerate(
                pool.imap_unordered(screen, tasks, chunksize=1), start=1
            ):
                counts[case, 'checked'] += 1
                if ordered is None:
                    ordered_survivors.append((case, piece, budget))
                elif ordered.startswith('analytical: partial ordered'):
                    counts[case, 'ordered'] += 1
                else:
                    counts[case, 'other'] += 1
                if ordered is None and combined is not None:
                    counts[case, 'additional'] += 1
                if combined is None:
                    survivors.append((case, piece, budget))
                if done % 25 == 0:
                    say(f'progress | {done}/{len(tasks)} checked | {len(survivors)} surviving both so far')
        for case in ('a', 'b'):
            n = counts[case, 'checked']
            ordered = counts[case, 'ordered']
            other = counts[case, 'other']
            additional = counts[case, 'additional']
            say(f'case {case} | {n} checked | {ordered} partial ordered UNSAT | {other} other baseline analytical UNSAT | '
                f'{additional} additional UNSAT with forced repeats | {n-ordered-other-additional} left')
        say(f'ORDERED ONLY SURVIVORS | {len(ordered_survivors)} | '
            + '; '.join(f'{case}:{op}-{left}-{right}' for case, (op, left, right), _ in sorted(ordered_survivors)))
        say(f'COMBINED SURVIVORS | {len(survivors)} | '
            + '; '.join(f'{case}:{op}-{left}-{right}' for case, (op, left, right), _ in sorted(survivors)))
        say(f'RESULT | {len(tasks)-len(ordered_survivors)}/{len(tasks)} excluded on first pass | '
            f'{len(tasks)-len(survivors)}/{len(tasks)} excluded with both | {len(survivors)} open | 0 SAT solver calls')
        if sum(counts[case, 'checked'] for case in ('a', 'b')) != len(tasks):
            raise AssertionError('missing cubes')

if __name__ == '__main__':
    main()
