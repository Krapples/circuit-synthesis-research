"""Independently check the Percy first-layer options and run a bounded ablation."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from itertools import combinations
import json
from pathlib import Path
import subprocess
from time import perf_counter

from run_baselines import PERCY, hexstr, parse_percy_chain, peak_of, verify
from benchmark_memory import limit_commit_mib


MODES = {
    'base': (),
    'edges': ('--first-layer', 'edges'),
    'all': ('--first-layer', 'all'),
    'budget': ('--first-layer-budget',),
    'all+budget': ('--first-layer', 'all', '--first-layer-budget'),
}
RESIDUAL_MODES = {
    'residual': ('--tight-residual',),
    'all+budget+residual': (*MODES['all+budget'], '--tight-residual'),
    'all+set-cuts': (*MODES['all'], '--tight-residual', '--tight-residual-set-cuts'),
    'all+budget+set-cuts': (*MODES['all+budget'], '--tight-residual', '--tight-residual-set-cuts'),
}
RESIDUAL_MODES['slack-one'] = (*RESIDUAL_MODES['all+budget+set-cuts'], '--slack-one-residual')
RESIDUAL_MODES['slack-one-trace'] = (*RESIDUAL_MODES['slack-one'], '--trace-slack-one')
for residual_filter in ('root', 'parity', 'direct'):
    RESIDUAL_MODES[f'slack-one-{residual_filter}'] = (
        *RESIDUAL_MODES['slack-one'], '--residual-filter', residual_filter)
for residual_backend in ('directed', 'dominance'):
    RESIDUAL_MODES[f'slack-one-{residual_backend}'] = (
        *RESIDUAL_MODES['slack-one-direct'], '--residual-backend', residual_backend)
RESIDUAL_MODES['slack-two-trace'] = (*RESIDUAL_MODES['slack-one-directed'], '--trace-slack-two')
for slack_two_filter in ('memo', 'unate', 'phase', 'phase-cache'):
    RESIDUAL_MODES[f'slack-two-{slack_two_filter}'] = (
        *RESIDUAL_MODES['slack-one-directed'], '--slack-two-residual', slack_two_filter)
for slack_two_filter in ('unate', 'phase'):
    RESIDUAL_MODES[f'slack-two-{slack_two_filter}-set'] = (
        *RESIDUAL_MODES[f'slack-two-{slack_two_filter}'], '--slack-two-set-cuts')
# Wider slack-two recognizer allowance (10x work, 4x deadline), to test whether its limits bind.
RESIDUAL_MODES['slack-two-phase-set-wide'] = (
    *RESIDUAL_MODES['slack-two-phase-set'], '--slack-two-work', '1000000', '--slack-two-ms', '100')
RESIDUAL_MODES['slack-three-trace'] = (*RESIDUAL_MODES['slack-two-phase-set'], '--trace-slack-three')
for slack_three_filter in ('memo', 'unate', 'phase', 'phase-cache'):
    RESIDUAL_MODES[f'slack-three-{slack_three_filter}'] = (
        *RESIDUAL_MODES['slack-two-phase-set'], '--slack-three-residual', slack_three_filter)
    RESIDUAL_MODES[f'slack-three-{slack_three_filter}-sym'] = (
        *RESIDUAL_MODES[f'slack-three-{slack_three_filter}'], '--slack-three-symmetric')
for slack_three_filter in ('phase', 'phase-sym'):
    RESIDUAL_MODES[f'slack-three-{slack_three_filter}-set'] = (
        *RESIDUAL_MODES[f'slack-three-{slack_three_filter}'], '--slack-three-set-cuts')
    RESIDUAL_MODES[f'slack-three-{slack_three_filter}-set-100ms'] = (
        *RESIDUAL_MODES[f'slack-three-{slack_three_filter}-set'], '--slack-three-ms', '100')
    # Lazy weighted cuts: NOT A OR (W >= w + d) OR R with fewer or no extension checks.
    for policy in ('exact', 'lift1', 'adaptive'):
        RESIDUAL_MODES[f'slack-three-{slack_three_filter}-set-{policy}'] = (
            *RESIDUAL_MODES[f'slack-three-{slack_three_filter}-set'], '--slack-three-policy', policy)
        RESIDUAL_MODES[f'slack-three-{slack_three_filter}-set-{policy}-100ms'] = (
            *RESIDUAL_MODES[f'slack-three-{slack_three_filter}-set-{policy}'], '--slack-three-ms', '100')
# Last-provider decoder phase screen inside the slack-two and slack-three Engines.
for name in ('slack-two-phase-set', 'slack-three-phase-set', 'slack-three-phase-set-exact',
             'slack-three-phase-set-lift1'):
    for decoder in ('1', '2'):
        RESIDUAL_MODES[f'{name}-dec{decoder}'] = (*RESIDUAL_MODES[name], '--decoder-phase', decoder)
# Restriction (gate-elimination) certificates learned on CEGAR models (restriction_certificate.hpp).
RESIDUAL_MODES['base-restrict'] = ('--restriction-cuts', 'cut')
RESIDUAL_MODES['base-restrict-rows'] = ('--restriction-cuts', 'rows')
RESIDUAL_MODES['slack-three-phase-set-lift1-restrict'] = (
    *RESIDUAL_MODES['slack-three-phase-set-lift1'], '--restriction-cuts', 'cut')
# Eager constant-only restriction counters and input-complement normalization (std and CEGAR).
COUNTER_MODES = {'base-renorm': ('--complement-inputs', 'auto')}
for counters in ('zero', 'const', 'anchor'):
    COUNTER_MODES[f'base-count-{counters}'] = ('--restriction-counters', counters)
    COUNTER_MODES[f'base-renorm-count-{counters}'] = (*COUNTER_MODES['base-renorm'], '--restriction-counters', counters)
RESIDUAL_MODES['slack-three-phase-set-lift1-renorm'] = (
    *RESIDUAL_MODES['slack-three-phase-set-lift1'], '--complement-inputs', 'auto')
for counters in ('zero', 'const', 'anchor'):
    RESIDUAL_MODES[f'slack-three-phase-set-lift1-count-{counters}'] = (
        *RESIDUAL_MODES['slack-three-phase-set-lift1'], '--restriction-counters', counters)
    RESIDUAL_MODES[f'slack-three-phase-set-lift1-renorm-count-{counters}'] = (
        *RESIDUAL_MODES['slack-three-phase-set-lift1-renorm'], '--restriction-counters', counters)
# Restricted-output cone caps and essential-input reachability on top of the constant counters.
CONE_VARIANTS = {'ess': ('--restriction-essential',), 'live2': ('--restriction-live', '2'),
                 'live4': ('--restriction-live', '4'), 'liveall': ('--restriction-live', 'all'),
                 'liveall-ess': ('--restriction-live', 'all', '--restriction-essential'),
                 'live2-ess': ('--restriction-live', '2', '--restriction-essential')}
for suffix, flags in CONE_VARIANTS.items():
    COUNTER_MODES[f'base-count-const-{suffix}'] = (*COUNTER_MODES['base-count-const'], *flags)
    RESIDUAL_MODES[f'slack-three-phase-set-lift1-count-const-{suffix}'] = (
        *RESIDUAL_MODES['slack-three-phase-set-lift1-count-const'], *flags)
# Hybrid (--hybrid-witness W): cone-free witness pass with W conflicts per budget, then cone proofs of the
# skipped budgets below the verified upper bound. W = 100k is fixed a priori (5% of the extended per-call
# limit), not tuned on the targets. 'hyb-slice' runs the proof pass with guarded cone-on / cone-off slices.
HYBRID_VARIANTS = {'hyb': ('--hybrid-witness', '100000'),
                   'hyb-slice': ('--hybrid-witness', '100000', '--restriction-cone-slice', '20000')}
for suffix, flags in HYBRID_VARIANTS.items():
    RESIDUAL_MODES[f'slack-three-phase-set-lift1-count-const-liveall-ess-{suffix}'] = (
        *RESIDUAL_MODES['slack-three-phase-set-lift1-count-const-liveall-ess'], *flags)


def exact_tables(n, steps):
    """Enumerate trimmed circuits directly with arbitrary AIG input phases."""
    full = (1 << (1 << n)) - 1
    vals = [sum(1 << a for a in range(1 << n) if a >> i & 1) for i in range(n)]
    tables = set()

    def visit(read):
        if len(vals) == n + steps:
            if read >> n == (1 << (steps - 1)) - 1:
                tables.update((vals[-1], vals[-1] ^ full))
            return
        for a, b in combinations(range(len(vals)), 2):
            x, y = vals[a], vals[b]
            for left in (x, x ^ full):
                for right in (y, y ^ full):
                    vals.append(left & right)
                    visit(read | (1 << a) | (1 << b))
                    vals.pop()

    visit(0)
    return tables


# Benchmark tiers: (wall seconds, SAT conflicts). Rapid is the development screen; the longer
# tiers evaluate the strongest configurations. Unknown is never a verdict at any tier.
TIERS = {'rapid': (8, 20_000), 'long': (60, 200_000), 'extended': (300, 2_000_000)}
KILL_GRACE = 10  # the harness kill is only a backstop behind the driver's own --seconds deadline
MEMORY_EXIT = 3  # percy_run's exit code after std::bad_alloc
USAGE_EXIT = 2  # percy_run's exit code for invalid arguments


def incomplete_record(rows):
    """The budget record that ended the run without a verdict, if any."""
    return next((row for row in reversed(rows) if row.get('status') == 'TIMEOUT'), None)


def run(exe, mode, name, n, tt, care, method, seconds, conflicts, budget=None, start=None,
        conflict_scope='call', driver_deadline=True, memory_capped=False):
    full = (1 << (1 << n)) - 1
    cmd = [exe, '--n', str(n), '--tt', hexstr(n, tt), '--method', method, '--solver', 'satoko',
           '--conflicts', str(conflicts), '--conflict-scope', conflict_scope, *(MODES | RESIDUAL_MODES | COUNTER_MODES)[mode]]
    if driver_deadline:
        cmd += ['--seconds', str(seconds)]
    if care != full:
        cmd += ['--dc', hexstr(n, full ^ care)]
    cmd += ['--budget', str(budget)] if budget is not None else ['--start', str(start), '--max', '12']
    started = perf_counter()
    with subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True) as child:
        timed_out = False
        try:
            stdout, stderr = child.communicate(timeout=seconds + KILL_GRACE if driver_deadline else seconds)
        except subprocess.TimeoutExpired:
            timed_out = True
            child.kill()
            stdout, stderr = child.communicate()
        elapsed, peak = perf_counter() - started, peak_of(child)
        crashed = not timed_out and child.returncode not in (0, MEMORY_EXIT)
        # Exit 2 is percy_run's usage error: never an allocation failure.
        if crashed and (not memory_capped or child.returncode == USAGE_EXIT):
            raise RuntimeError((cmd, child.returncode, stderr, stdout))
    rows = [json.loads(line) for line in stdout.splitlines() if line.startswith('{') and line.endswith('}')]
    final = next((row for row in rows if 'final' in row), {})
    budgets = [row['k'] for row in rows if 'k' in row]
    if timed_out:
        # Killed mid-budget: the open budget is the one after the last reported record.
        status, reason = 'TIMEOUT', 'harness_kill'
        open_budget = (budgets[-1] + 1) if budgets else (budget if budget is not None else start)
    elif child.returncode == MEMORY_EXIT or crashed:
        # A crash under a commit cap is almost always an allocation failure outside C++ new.
        status, reason = 'MEMORY', 'memory' if child.returncode == MEMORY_EXIT else f'crash_{child.returncode}'
        open_budget = final.get('last_k', (budgets[-1] + 1) if budgets else None)
    else:
        status, reason = final['final'], final.get('reason', '')
        # A hybrid SAT run has capped witness-pass records below the minimum; they were proved later.
        pending = incomplete_record(rows) if status != 'SAT' else None
        open_budget = pending['k'] if pending else None
    upper_bound = None
    if status == 'SAT' or final.get('upper_bound', -1) >= 0:
        # A hybrid TIMEOUT also carries the witness of its verified upper bound.
        gates, output = parse_percy_chain(n, final)
        steps = final['steps'] if status == 'SAT' else final['upper_bound']
        assert final['aig'] and len(gates) == steps and verify(n, tt, care, gates, output), (cmd, final)
        upper_bound = steps
    return dict(name=name, n=n, tt=hexstr(n, tt), care=hexstr(n, care), mode=mode, budget=budget, start=start,
                method=method, status=status, reason=reason, open_budget=open_budget, upper_bound=upper_bound,
                wall_seconds=elapsed,
                peak_bytes=peak, conflicts_limit=conflicts, conflict_scope=conflict_scope, wall_limit=seconds,
                driver_deadline=driver_deadline, records=rows)


def check_jobs(exe, modes):
    n = 3
    # Complete AND, multiplexer, majority, parity, and their output phases.
    complete_targets = [0x80, 0x7f, 0xca, 0xe8, 0x96, 0x69]
    if any(mode in RESIDUAL_MODES for mode in modes):
        complete_targets.extend((0x1b, 0x1e))  # exercise set cuts on both feasible and infeasible budgets
    for budget in (2, 3):
        known = exact_tables(n, budget)
        for tt, care in [(tt, 0xff) for tt in complete_targets] + [(0x96, 0x17)]:
            expected = 'SAT' if any((tt ^ f) & care == 0 for f in known) else 'UNSAT'
            for method in ('std', 'cegar') if care == 0xff else ('std',):
                for mode in modes:
                    if mode in RESIDUAL_MODES and method != 'cegar':
                        continue
                    args = (exe, mode, f'check-{tt:02x}', n, tt, care, method, 5, 0, budget)
                    yield args, expected
    if any(mode in RESIDUAL_MODES for mode in modes):
        # ab(c|d) needs a different boundary from H=(ab), M=(c,d).
        known = exact_tables(4, 3)
        for tt in (0x8880, 0x8000, 0x6996):
            for mode in modes:
                yield (exe, mode, f'check-{tt:04x}', 4, tt, 0xffff, 'cegar', 5, 0, 3), (
                    'SAT' if tt in known else 'UNSAT')
    if any(mode.startswith(('slack-two-', 'slack-three-')) for mode in modes):
        known = exact_tables(4, 4)
        for tt in (0x0116, 0x17e8, 0x6996, 0x7fff, 0x8000, 0x8880):
            for mode in modes:
                yield (exe, mode, f'check-{tt:04x}', 4, tt, 0xffff, 'cegar', 5, 0, 4), (
                    'SAT' if tt in known else 'UNSAT')
        known = exact_tables(3, 5)
        for tt in (0x1e, 0x36, 0x96):
            for mode in modes:
                yield (exe, mode, f'check-{tt:02x}', 3, tt, 0xff, 'cegar', 5, 0, 5), (
                    'SAT' if tt in known else 'UNSAT')
        # The plain full-row encoding independently excludes these hard budgets.
        # The CEGAR jobs reach the slack-two clause path at this size.
        for tt in (0x0116, 0x0168, 0x016a):
            yield (exe, 'base', f'check-{tt:04x}', 4, tt, 0xffff, 'std', 8, 250_000, 7), 'UNSAT'
            for mode in modes:
                yield (exe, mode, f'check-{tt:04x}', 4, tt, 0xffff, 'cegar', 8, 250_000, 7), 'UNSAT'
    if any(mode.startswith('slack-three-') for mode in modes):
        # Verified four-input optima (caps_hard_npn4.jsonl): 0116 needs nine gates, 016a needs eight.
        # These size-eight jobs reach the slack-three clause path.
        for tt, expected in ((0x0116, 'UNSAT'), (0x016a, 'SAT')):
            for mode in ('slack-two-phase-set', *modes):
                yield (exe, mode, f'check-{tt:04x}', 4, tt, 0xffff, 'cegar', 60, 0, 8), expected
    if any('-count-' in mode or '-renorm' in mode for mode in modes):
        # Same verified optima: the counters cap deletions on every size-eight and size-nine budget and
        # complement normalization flips an input of 1699, so the mapped-back witness is checked too.
        for tt, budget, expected in ((0x0116, 8, 'UNSAT'), (0x016a, 8, 'SAT'), (0x6996, 8, 'UNSAT'),
                                     (0x1668, 8, 'UNSAT'), (0x0116, 9, 'SAT'), (0x1699, 8, 'SAT')):
            for mode in modes:
                yield (exe, mode, f'check-{tt:04x}', 4, tt, 0xffff, 'cegar', 60, 0, budget), expected
    if any('-restrict' in mode for mode in modes):
        # Verified four-input optima (tier records): restriction cores fire on almost every size-eight
        # and size-nine model, so these budgets exercise the learned clauses on both verdicts.
        for tt, budget, expected in ((0x0116, 8, 'UNSAT'), (0x016a, 8, 'SAT'), (0x6996, 8, 'UNSAT'),
                                     (0x1668, 8, 'UNSAT'), (0x0116, 9, 'SAT'), (0x1699, 8, 'SAT')):
            for mode in modes:
                yield (exe, mode, f'check-{tt:04x}', 4, tt, 0xffff, 'cegar', 60, 0, budget), expected


def screen_jobs(exe, workload, limit, seconds, conflicts, modes, names=None, extra=None):
    with workload.open(encoding='utf-8') as source:
        targets = [json.loads(line) for line in source if line.strip()]
    eligible = [target for target in targets if 2 <= target['n'] <= 5]
    if names:
        chosen = [target for target in eligible if target['name'] in names or target['tt'] in names]
        assert len(chosen) == len(names), (names, [target['name'] for target in chosen])
        eligible = chosen
    for target in eligible[:limit]:
        n, tt = target['n'], int(target['tt'], 16)
        care = (1 << (1 << n)) - 1
        for mode in modes:
            yield (exe, mode, target['name'], n, tt, care, 'cegar', seconds, conflicts, None, n - 1,
                   *(extra or ())), None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('kind', choices=('check', 'screen'))
    parser.add_argument('output', type=Path)
    parser.add_argument('--exe', default=PERCY)
    parser.add_argument('--workers', type=int, choices=range(1, 9), default=1)
    parser.add_argument('--workload', type=Path, default=Path(__file__).resolve().parents[1] /
                        'results' / 'baselines' / 'hard_npn4.jsonl')
    parser.add_argument('--limit', type=int, default=8)
    parser.add_argument('--seconds', type=float, default=6)
    parser.add_argument('--conflicts', type=int, default=20_000)
    parser.add_argument('--tier', choices=tuple(TIERS), help='set --seconds and --conflicts from a benchmark tier')
    parser.add_argument('--conflict-scope', choices=('call', 'budget'), default='call',
                        help='call: --conflicts limits each CEGAR SAT call (Percy); budget: the whole budget')
    parser.add_argument('--no-driver-deadline', action='store_true',
                        help='legacy: only the harness kill enforces --seconds (no per-budget record on timeout)')
    parser.add_argument('--targets', nargs='+', help='screen only these workload names or truth tables')
    parser.add_argument('--modes', nargs='+', choices=tuple(MODES | RESIDUAL_MODES | COUNTER_MODES), default=tuple(MODES))
    parser.add_argument('--memory-mib', type=int, help='commit cap for the single-worker process family')
    args = parser.parse_args()
    if args.memory_mib is not None:
        if args.workers != 1:
            parser.error('--memory-mib needs a single worker')
        limit_commit_mib(args.memory_mib)
    if args.tier:
        args.seconds, args.conflicts = TIERS[args.tier]
    extra = (args.conflict_scope, not args.no_driver_deadline, args.memory_mib is not None)
    jobs = check_jobs(args.exe, args.modes) if args.kind == 'check' else screen_jobs(
        args.exe, args.workload, args.limit, args.seconds, args.conflicts, args.modes, args.targets, extra)

    def execute(job):
        command, expected = job
        row = run(*command)
        if args.memory_mib is not None:
            row['memory_limit_mib'] = args.memory_mib
        if expected:
            assert row['status'] == expected, (command, expected, row)
            row['expected'] = expected
        return row

    verdicts, minima = {}, {}
    with args.output.open('x', encoding='utf-8') as output, ThreadPoolExecutor(args.workers) as pool:
        for row in pool.map(execute, jobs):
            output.write(json.dumps(row) + '\n')
            output.flush()
            key = row['name'], row['care'], row['method']
            for record in row['records']:
                if 'status' in record and record['status'] != 'TIMEOUT':
                    verdict = verdicts.setdefault((*key, record['k']), record['status'])
                    assert verdict == record['status'], (row, verdict)
                if record.get('final') == 'SAT' and args.kind == 'screen':
                    minimum = minima.setdefault(key, record['steps'])
                    assert minimum == record['steps'], (row, minimum)
            print(f"{row['name']} {row['method']} {row['mode']} {row['budget']} {row['status']} {row['reason']}"
                  f" open={row['open_budget']} {row['wall_seconds']:.1f}s", flush=True)


if __name__ == '__main__':
    main()
