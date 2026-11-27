"""Matched solver comparison on identical template CNFs: native CaDiCaL 2.2 (template_synth.exe --solve-cnf)
vs pysat maplechrono / cadical195 (solve() wall time only; the solvers are C/C++ inside pysat).
usage: python solver_cmp.py CNF_DIR OUT.jsonl CAP_S"""
import glob, json, os, subprocess, sys, time
from multiprocessing import Pool

EXE = r'C:\Users\Carson\Documents\ChatGPT\P=NP\sat-search\native\template_synth.exe'


def job(a):
    cnf, solver, cap = a
    if solver == 'cadical22-native':
        p = subprocess.run([EXE, '--seconds', str(cap), '--solve-cnf', cnf.replace(chr(92), '/')], capture_output=True, text=True)
        r = json.loads(p.stdout)
        st = {10: 'SAT', 20: 'UNSAT'}.get(r['status'], 'TIMEOUT')
        return dict(cnf=os.path.basename(cnf), solver=solver, status=st, seconds=r['seconds'])
    from pysat.formula import CNF
    from pysat.solvers import Solver
    import threading
    f = CNF(from_file=cnf)
    with Solver(name=solver, bootstrap_with=f.clauses, use_timer=True) as s:
        t = threading.Timer(cap, s.interrupt)
        t.start()
        t0 = time.perf_counter()
        res = s.solve_limited(expect_interrupt=True)
        dt = time.perf_counter() - t0
        t.cancel()
    st = {True: 'SAT', False: 'UNSAT', None: 'TIMEOUT'}[res]
    return dict(cnf=os.path.basename(cnf), solver=solver, status=st, seconds=round(dt, 3))


if __name__ == '__main__':
    d, out, cap = sys.argv[1], sys.argv[2], float(sys.argv[3])
    jobs = [(c, s, cap) for c in sorted(glob.glob(os.path.join(d, '*.cnf')))
            for s in ('cadical22-native', 'maplechrono', 'cadical195')]
    with Pool(min(22, len(jobs))) as p, open(out, 'w') as f:
        for r in p.imap_unordered(job, jobs):
            f.write(json.dumps(r) + '\n'); f.flush()
            print(r, flush=True)
