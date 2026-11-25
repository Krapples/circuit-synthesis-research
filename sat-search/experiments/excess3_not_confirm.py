"""SAT confirmation of counted-NOT lower bounds implied by excess3_ladder.py free-NOT exclusions.
If the free-NOT binary minimum is >= B and every circuit needs >= N NOTs (signed not_lower), then every counted-NOT
circuit has >= B + N gates. Each implied bound L is checked independently: the existing direct counted-NOT encoding
(phase_budget_compare.baseline_cnf, at most L-1 total gates) must be UNSAT. maplechrono, one process per job.
Writes results/excess3_not_confirm.jsonl. Usage: python experiments/excess3_not_confirm.py [seconds]"""
import json, os, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))
from phase_budget_compare import baseline_cnf, solve


def job(a):
    name, n, f, G, secs = a
    P, N = f, ((1 << (1 << n)) - 1) & ~f
    cl, nv = baseline_cnf(n, P, N, G)
    r, dt, conf, model, _ = solve(cl, 'maplechrono', secs)
    return dict(case=name, n=n, G=G, status='open' if r is None else 'SAT' if r else 'UNSAT', seconds=round(dt, 2), conflicts=conf)


if __name__ == '__main__':
    secs = float(sys.argv[1]) if len(sys.argv) > 1 else 300
    from signed_bound_compare import cases, restrict_essential
    sb = {json.loads(l)['case']: json.loads(l) for l in open(os.path.join(HERE, 'results', 'signed_bound_compare.jsonl'))}
    q = {}
    for l in open(os.path.join(HERE, 'results', 'excess3_ladder.jsonl')):
        r = json.loads(l)
        if r['key'].endswith('|free') and r.get('kind', '').startswith('q-') and 'status' not in r and r['result'] is None:
            q[r['key'].split('|')[0]] = r
    jobs = []
    for name, fam, n0, f0 in cases():
        if name not in q:
            continue
        n, f, _ = restrict_essential(n0, f0); s = sb.get(name, {})
        L = q[name]['core_n'] + 3 + q[name]['trace'] + (s.get('not_lower') or 0)
        prior = max(x for x in (s.get('support'), s.get('existing'), s.get('sat_lower'), s.get('signed'), 0) if isinstance(x, int))
        if L > prior:
            jobs.append((name, n, f, L - 1, secs)); print(f'{name}: implied counted-NOT >= {L} (prior {prior}, upper {s.get("upper")})', flush=True)
    out = open(os.path.join(HERE, 'results', 'excess3_not_confirm.jsonl'), 'w', encoding='utf-8')
    with Pool(min(len(jobs), 12), maxtasksperchild=1) as p:
        for r in p.imap_unordered(job, jobs):
            out.write(json.dumps(r) + '\n'); out.flush(); print(r, flush=True)
