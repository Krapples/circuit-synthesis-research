"""Fixed-budget sweep of --restriction-burst on hard size-eight and size-nine budgets (60 s, 200k per call).
Usage: restriction_burst_sweep.py percy_run.exe > records.jsonl"""
import json, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
exe = sys.argv[1]
cases = [('6996', 9), ('1668', 9), ('16a9', 9), ('1686', 9), ('1668', 8), ('0196', 8), ('16a9', 8), ('1686', 8)]
configs = {'plain': [], 'cut': ['--restriction-cuts', 'cut']}
for m in (1, 4, 16, 64):
    configs[f'burst{m}'] = ['--restriction-cuts', 'cut', '--restriction-burst', str(m)]
jobs = [(c, t, k) for t, k in cases for c in configs]


def run(job):
    c, t, k = job
    out = subprocess.run([exe, '--n', '4', '--tt', t, '--method', 'cegar', '--solver', 'satoko', '--budget', str(k),
                          '--conflicts', '200000', '--seconds', '60', *configs[c]], capture_output=True, text=True)
    assert out.returncode == 0, (job, out.returncode, out.stderr)
    r = next(json.loads(l) for l in out.stdout.splitlines() if l.startswith('{"k"'))
    return dict(config=c, target=t, k=k, status=r['status'], reason=r['reason'], seconds=r['seconds'],
                rows=r['cegar_rows'], conflicts=r['conflicts'], cuts=r.get('restriction_cuts', 0))


with ThreadPoolExecutor(11) as pool:
    for row in pool.map(run, jobs):
        print(json.dumps(row), flush=True)
