"""Run matched benchmark tiers: one single-worker first_layer_check screen per (mode, target).

Each job is its own process with a commit cap, so the jobs are independent and the limit that
ended each budget (wall deadline, conflicts, memory) is recorded per budget by percy_run.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
TARGETS = ('npn4-016a', 'npn4-1699', 'npn4-0116', 'npn4-6996', 'npn4-0196', 'npn4-16a9', 'npn4-1668',
           'npn4-1686', 'npn4-1669', 'npn4-166b')
MODES = ('base', 'slack-two-phase-set', 'slack-three-phase-set', 'slack-three-phase-set-lift1')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='combined jsonl (must not exist)')
    parser.add_argument('--logs', type=Path, required=True, help='new directory for per-job records')
    parser.add_argument('--tier', choices=('rapid', 'long', 'extended'))
    parser.add_argument('--seconds', type=float)
    parser.add_argument('--conflicts', type=int)
    parser.add_argument('--conflict-scope', choices=('call', 'budget'), default='call')
    parser.add_argument('--targets', nargs='+', default=TARGETS)
    parser.add_argument('--modes', nargs='+', default=MODES)
    parser.add_argument('--workers', type=int, default=11)
    parser.add_argument('--memory-mib', type=int, default=1024)
    args = parser.parse_args()
    if not args.tier and (args.seconds is None or args.conflicts is None):
        parser.error('give --tier or both --seconds and --conflicts')
    args.logs.mkdir(parents=True)
    limits = ['--tier', args.tier] if args.tier else []
    if args.seconds is not None:
        limits += ['--seconds', str(args.seconds)]
    if args.conflicts is not None:
        limits += ['--conflicts', str(args.conflicts)]
    jobs = [(mode, target) for target in args.targets for mode in args.modes]

    def execute(job):
        mode, target = job
        path = args.logs / f'{mode}__{target}.jsonl'
        command = [sys.executable, str(HERE / 'first_layer_check.py'), 'screen', str(path), '--workers', '1',
                   '--memory-mib', str(args.memory_mib), '--limit', '1', '--targets', target, '--modes', mode,
                   '--conflict-scope', args.conflict_scope, *limits]
        # --tier is applied after --seconds/--conflicts inside the harness, so explicit limits must
        # not be combined with a tier.
        assert not (args.tier and (args.seconds is not None or args.conflicts is not None))
        with (args.logs / f'{mode}__{target}.out').open('w') as log:
            subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, check=True)
        row = json.loads(path.read_text(encoding='utf-8'))
        print(f"{target} {mode} {row['status']} {row['reason']} open={row['open_budget']} "
              f"{row['wall_seconds']:.1f}s", flush=True)
        return row

    with args.output.open('x', encoding='utf-8') as output, ThreadPoolExecutor(args.workers) as pool:
        for row in pool.map(execute, jobs):
            output.write(json.dumps(row) + '\n')
            output.flush()


if __name__ == '__main__':
    main()
