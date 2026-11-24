"""Cross-check hybrid_search.py (GPU) against sat_reference.py (CaDiCaL) on small graphs.

For each graph: the smallest size where the SAT reference finds a circuit is the minimum m.
The GPU search must find a verified circuit at m and report NONE at m - 1.
Run with the .venv python (numba-cuda); the SAT reference runs with the main python (pysat).
"""
import re, subprocess, sys, time

SAT_PY = r"C:\Users\Carson\.pyenv\pyenv-win\versions\3.15.2\python.exe"
GPU_PY = sys.executable
GRAPHS = {
    'P4 path': (4, '0-1,1-2,2-3'),
    'K3 triangle': (3, '0-1,1-2,0-2'),
    'star K1,4': (5, '0-1,0-2,0-3,0-4'),
    'P5 path': (5, '0-1,1-2,2-3,3-4'),
    'C5 cycle': (5, '0-1,1-2,2-3,3-4,0-4'),
    'K4': (4, '0-1,0-2,0-3,1-2,1-3,2-3'),
    'triangle+leaf': (4, '0-1,1-2,0-2,0-3'),
    'C6 cycle': (6, '0-1,1-2,2-3,3-4,4-5,0-5'),
    'P6 path': (6, '0-1,1-2,2-3,3-4,4-5'),
}


def run(py, script, n, e, s, extra=()):
    t = time.time()
    out = subprocess.run([py, script, '--n', str(n), '--edges', e, '--size', str(s), *extra],
                         capture_output=True, text=True).stdout
    return out, time.time() - t


ok_all = True
for name, (n, e) in GRAPHS.items():
    m, sat_t = None, 0.0
    for s in range(n - 1, 20):
        out, dt = run(SAT_PY, 'sat_reference.py', n, e, s)
        sat_t += dt
        if 'WITNESS' in out:
            m = s
            break
    hi, t_hi = run(GPU_PY, 'hybrid_search.py', n, e, m)
    lo, t_lo = run(GPU_PY, 'hybrid_search.py', n, e, m - 1)
    good = re.search(r'WITNESS with (\d+) gates, verified=True', hi)
    ok = bool(good) and int(good.group(1)) == m and 'NONE' in lo
    ok_all &= ok
    print(f'{name:14s} min={m:2d}  GPU@m: {"witness" if good else "MISSING"}  '
          f'GPU@m-1: {"none" if "NONE" in lo else "FOUND?!"}  '
          f'{"OK " if ok else "BAD"}  (SAT total {sat_t:.1f}s, GPU {t_hi + t_lo:.1f}s)', flush=True)
print('ALL AGREE' if ok_all else 'DISAGREEMENT FOUND')
