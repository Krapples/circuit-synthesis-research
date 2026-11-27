"""Native (percy_run --mixed-rank-cuts) checks and matched benchmark.

  differential: percy_run's printed mixed_floors equal mixed_rank_cuts.select_cuts (Python reference) on every
                4-input table (random sample of 5-input tables), at one tiny budget so the solve is trivial.
  bench:        same binary, control (no flag) vs --mixed-rank-cuts 1 and 2, per (target, budget), each job one
                process under a wall cap (a timeout is UNKNOWN, never UNSAT). Verdicts must agree when both finish.

Usage: python -B experiments/mixed_rank_cuts_native.py differential [--exe PATH]
       python -B experiments/mixed_rank_cuts_native.py bench --targets 0116,1668 --budgets 8,9 --output PATH
"""
import argparse, json, os, random, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
from mixed_rank_cuts import select_cuts  # noqa: E402

EXE = os.path.join(os.path.dirname(ROOT), 'external', 'percy-build-mixed', 'percy_run.exe')


def run(exe, args, cap):
    t0 = time.perf_counter()
    try:
        p = subprocess.run([exe, *args], capture_output=True, text=True, timeout=cap)
    except subprocess.TimeoutExpired:
        return dict(status='TIMEOUT', seconds=cap), []
    recs = []
    for line in p.stdout.splitlines():
        line = line.strip()
        if line.startswith('{'):
            try:
                recs.append(json.loads(line))
            except json.JSONDecodeError:
                pass
    return dict(status='DONE', seconds=time.perf_counter() - t0, rc=p.returncode, err=p.stderr[-400:]), recs


def floors_of(recs):
    for r in recs:
        if 'mixed_floors' in r:
            return [tuple(c) for c in r['mixed_floors']]
    return None


def differential(a):
    tables = [(4, t) for t in range(1 << 16)] if a.all4 else [(4, random.Random(1).getrandbits(16)) for _ in range(400)]
    rng = random.Random(2)
    tables += [(5, rng.getrandbits(32)) for _ in range(a.n5)]
    bad, checked, with_cuts = [], 0, 0

    def one(nt):
        n, t = nt
        hexw = (1 << n) // 4
        _, recs = run(a.exe, ['--n', str(n), '--tt', f'{t:0{hexw}x}', '--method', 'cegar', '--budget', '1',
                              '--mixed-rank-cuts', '1'], 60)
        return nt, floors_of(recs)

    with ThreadPoolExecutor(a.workers) as pool:
        for (n, t), got in pool.map(one, tables):
            want = [tuple(c) for c in select_cuts(n, t, 8, 1)]
            checked += 1
            with_cuts += bool(want)
            if got is None and not want:
                continue  # binary may skip the record when there is nothing to report
            if got != want:
                bad.append(dict(n=n, tt=t, want=want, got=got))
    print(json.dumps(dict(checked=checked, with_cuts=with_cuts, mismatches=len(bad), first=bad[:5])))
    return 1 if bad else 0


def bench(a):
    arms = {'control': [], 'cuts1': ['--mixed-rank-cuts', '1'], 'cuts2': ['--mixed-rank-cuts', '2']}
    jobs = [(t, k, arm) for t in a.targets.split(',') for k in map(int, a.budgets.split(',')) for arm in arms]
    os.makedirs(os.path.dirname(os.path.abspath(a.output)), exist_ok=True)

    def one(job):
        t, k, arm = job
        args = ['--n', str(a.n), '--tt', t, '--method', a.method, '--budget', str(k), *arms[arm]]
        res, recs = run(a.exe, args, a.seconds)
        last = recs[-1] if recs else {}
        return job, dict(res, record=last, cuts=floors_of(recs))

    results = {}
    with open(a.output, 'w') as out:
        out.write(json.dumps(dict(kind='meta', exe=os.path.relpath(a.exe, ROOT), n=a.n, method=a.method,
                                  seconds=a.seconds, workers=a.workers, arms=arms,
                                  started=time.strftime('%Y-%m-%d %H:%M:%S'))) + '\n')
        with ThreadPoolExecutor(a.workers) as pool:
            for job, res in pool.map(one, jobs):
                results[job] = res
                out.write(json.dumps(dict(kind='job', target=job[0], budget=job[1], arm=job[2], **res)) + '\n')
                out.flush()
                rec = res['record']
                print(job, res['status'], f"{res['seconds']:.2f}s", rec.get('final'),
                      rec.get('conflicts', ''), flush=True)
    bad = []
    for (t, k, arm), res in results.items():
        ref = results[(t, k, 'control')]
        v = lambda r: r['record'].get('final') if r['status'] == 'DONE' else None
        if v(ref) and v(res) and v(ref) != v(res):
            bad.append((t, k, arm, v(ref), v(res)))
    print('verdict disagreements:', bad)
    return 1 if bad else 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['differential', 'bench'])
    ap.add_argument('--exe', default=EXE)
    ap.add_argument('--workers', type=int, default=10)
    ap.add_argument('--all4', action='store_true')
    ap.add_argument('--n5', type=int, default=100)
    ap.add_argument('--n', type=int, default=4)
    ap.add_argument('--method', default='cegar')
    ap.add_argument('--targets', default='')
    ap.add_argument('--budgets', default='8,9')
    ap.add_argument('--seconds', type=float, default=300)
    ap.add_argument('--output', default='')
    a = ap.parse_args()
    sys.exit(differential(a) if a.mode == 'differential' else bench(a))


if __name__ == '__main__':
    main()
