"""Matched benchmark: direct SAT synthesis with and without mixed-rank cuts (opt-in).

Arms per (case, basis, budget): 'base' (synthesis_bench.direct_sat unchanged), 'cuts2' (cuts with
floor >= 2, at most 8), 'cuts1' (floor >= 1, at most 8). Complete corpus cases only; the monotone
basis uses the reduced boundary labels (a monotone circuit agreeing on them computes the complete
monotone function, so the complete-function floors still apply). Every job runs in its own spawned
process under a wall cap and is terminated on timeout; a timeout is UNKNOWN, never UNSAT.
Verdicts of the arms must agree whenever both finish; a disagreement aborts the run.

Usage: python -B experiments/mixed_rank_cuts_bench.py --output results/mixed_rank_cuts/bench.jsonl
       [--max-n 6] [--seconds 20] [--workers 8] [--deltas 1,2 | low]
"""
import argparse, json, os, sys, time
from concurrent.futures import ThreadPoolExecutor
from multiprocessing import get_context
from time import perf_counter, process_time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE)); sys.path.insert(1, HERE)

ARMS = {'base': None, 'cuts2': 2, 'cuts1': 1}


def run_job(pipe, name, basis, budget, arm):
    import synthesis_bench as sb
    from synthesis_cases import corpus, boundary_labels
    from mixed_rank_cuts import select_cuts
    case = next(c for c in corpus() if c.name == name)
    labels = boundary_labels(case.n, case.labels()) if basis == 'mono' else case.labels()
    t0, c0 = perf_counter(), process_time()
    cuts = () if ARMS[arm] is None else tuple(select_cuts(case.n, case.truth, 8, ARMS[arm]))
    prep = perf_counter() - t0
    stats = {}
    w = sb.direct_sat(case.n, labels, budget, basis == 'not', mixed_cuts=cuts, stats=stats)
    pipe.send(dict(status='SAT' if w is not None else 'UNSAT', seconds=perf_counter() - t0,
                   prep_seconds=prep, cpu_seconds=process_time() - c0, peak_bytes=sb.peak_bytes(),
                   cuts=[list(c) for c in cuts], solver=stats))
    pipe.close()


def isolated(job, seconds):
    ctx = get_context('spawn'); parent, child = ctx.Pipe()
    p = ctx.Process(target=run_job, args=(child, *job)); p.start(); child.close()
    try:
        if parent.poll(seconds + 15):
            res = parent.recv()
        else:
            res = dict(status='TIMEOUT', seconds=seconds)
    except EOFError:
        res = dict(status='ERROR')
    finally:
        if p.is_alive():
            p.terminate()
        p.join(); p.close()
    if res.get('status') in ('SAT', 'UNSAT') and res['seconds'] > seconds:
        res['status'] = 'TIMEOUT'  # finished past the cap: counted as unknown for the matched comparison
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', required=True)
    ap.add_argument('--max-n', type=int, default=6)
    ap.add_argument('--seconds', type=float, default=20)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--deltas', default='1,2')
    ap.add_argument('--bases', default='mono,not')
    ap.add_argument('--case', action='append', default=[])
    a = ap.parse_args()
    from synthesis_cases import corpus, full_rows
    from mixed_rank_cuts import select_cuts
    jobs = []
    for case in corpus():
        if case.known != full_rows(case.n) or case.n > a.max_n or (a.case and case.name not in a.case):
            continue
        if not select_cuts(case.n, case.truth, 8, 2):
            continue
        w = len(case.witness.gates)
        if a.deltas == 'low':  # budgets from the support bound n - 1 upward (at most 6 of them)
            budgets = range(case.n - 1, min(w, case.n + 5))
        else:
            budgets = [w - d for d in map(int, a.deltas.split(',')) if w - d >= 1]
        for basis in a.bases.split(','):
            for b in budgets:
                jobs.extend((case.name, basis, b, arm) for arm in ARMS)
    os.makedirs(os.path.dirname(os.path.abspath(a.output)), exist_ok=True)
    meta = dict(kind='meta', seconds=a.seconds, workers=a.workers, max_n=a.max_n, deltas=a.deltas,
                arms={k: v for k, v in ARMS.items()}, jobs=len(jobs), solver='maplechrono',
                started=time.strftime('%Y-%m-%d %H:%M:%S'))
    results = {}
    with open(a.output, 'w') as out:
        out.write(json.dumps(meta) + '\n'); out.flush()
        with ThreadPoolExecutor(a.workers) as pool:
            futs = {job: pool.submit(isolated, job, a.seconds) for job in jobs}
            for job, fut in futs.items():
                res = fut.result()
                rec = dict(kind='job', case=job[0], basis=job[1], budget=job[2], arm=job[3], **res)
                out.write(json.dumps(rec) + '\n'); out.flush()
                results[job] = res
                print(job, res['status'], f"{res.get('seconds', 0):.2f}s",
                      res.get('solver', {}).get('conflicts', ''), flush=True)
    bad = []
    for (name, basis, budget, arm), res in results.items():
        ref = results.get((name, basis, budget, 'base'))
        if ref and {ref['status'], res['status']} == {'SAT', 'UNSAT'}:
            bad.append((name, basis, budget, arm, ref['status'], res['status']))
    print('verdict disagreements:', bad)
    if bad:
        sys.exit(1)


if __name__ == '__main__':
    main()
