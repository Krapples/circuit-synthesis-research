"""Independently check the Percy first-layer options and run a bounded ablation."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from itertools import combinations
import json
from pathlib import Path
import subprocess
from time import perf_counter

from run_baselines import PERCY, hexstr, parse_percy_chain, peak_of, verify


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


def run(exe, mode, name, n, tt, care, method, seconds, conflicts, budget=None, start=None):
    full = (1 << (1 << n)) - 1
    cmd = [exe, '--n', str(n), '--tt', hexstr(n, tt), '--method', method, '--solver', 'satoko',
           '--conflicts', str(conflicts), *(MODES | RESIDUAL_MODES)[mode]]
    if care != full:
        cmd += ['--dc', hexstr(n, full ^ care)]
    cmd += ['--budget', str(budget)] if budget is not None else ['--start', str(start), '--max', '12']
    started = perf_counter()
    with subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True) as child:
        timed_out = False
        try:
            stdout, stderr = child.communicate(timeout=seconds)
        except subprocess.TimeoutExpired:
            timed_out = True
            child.kill()
            stdout, stderr = child.communicate()
        elapsed, peak = perf_counter() - started, peak_of(child)
        if not timed_out and child.returncode:
            raise RuntimeError((cmd, child.returncode, stderr, stdout))
    rows = [json.loads(line) for line in stdout.splitlines() if line.startswith('{') and line.endswith('}')]
    final = next((row for row in rows if 'final' in row), {})
    status = 'TIMEOUT' if timed_out else final['final']
    if status == 'SAT':
        gates, output = parse_percy_chain(n, final)
        assert final['aig'] and len(gates) == final['steps'] and verify(n, tt, care, gates, output), (cmd, final)
    return dict(name=name, n=n, tt=hexstr(n, tt), care=hexstr(n, care), mode=mode, budget=budget, start=start,
                method=method, status=status, wall_seconds=elapsed, peak_bytes=peak, conflicts_limit=conflicts,
                wall_limit=seconds, records=rows)


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


def screen_jobs(exe, workload, limit, seconds, conflicts, modes):
    with workload.open(encoding='utf-8') as source:
        targets = [json.loads(line) for line in source if line.strip()]
    eligible = [target for target in targets if 2 <= target['n'] <= 5]
    for target in eligible[:limit]:
        n, tt = target['n'], int(target['tt'], 16)
        care = (1 << (1 << n)) - 1
        for mode in modes:
            yield (exe, mode, target['name'], n, tt, care, 'cegar', seconds, conflicts, None, n - 1), None


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
    parser.add_argument('--modes', nargs='+', choices=tuple(MODES | RESIDUAL_MODES), default=tuple(MODES))
    args = parser.parse_args()
    jobs = check_jobs(args.exe, args.modes) if args.kind == 'check' else screen_jobs(
        args.exe, args.workload, args.limit, args.seconds, args.conflicts, args.modes)

    def execute(job):
        command, expected = job
        row = run(*command)
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
            print(f"{row['name']} {row['method']} {row['mode']} {row['budget']} {row['status']}", flush=True)


if __name__ == '__main__':
    main()
