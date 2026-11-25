"""Module preprocessing in front of the complete-function FPT solver, on the frozen corpus.

For complete corpus targets with at most MAXN essential inputs (original) or MAXCORE core inputs: exact
counted-NOT minimum (total gates) by
  fpt_original  theory/fast_readonce_fpt.FullPortFastSolver on the original function (when n <= MAXN);
  fpt_core      the same solver on the raw module core, plus the trace length;
  ref_core      verify/reference.py on the core, plus the trace length (independent check).
The minimum is n - 1 + s for the least s the FPT solver accepts. Records time, states and local completion
calls; writes results/module_fpt_bench.jsonl. Usage: python experiments/module_fpt_bench.py [maxn] [maxcore]"""
import json, os, sys, time
from collections import Counter
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'verify', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))
import reference as ref
from module_contraction import simplify
from fast_readonce_fpt import FullPortFastSolver
from signed_bound_compare import cases, restrict_essential


def fpt_minimum(n, f, smax=8):
    sol = FullPortFastSolver(n)
    t0 = time.time()
    for s in range(smax + 1):
        if sol.solve(f, s):
            return n - 1 + s, time.time() - t0, sol.stats
    return None, time.time() - t0, sol.stats


if __name__ == '__main__':
    maxn = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    maxcore = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    out = open(os.path.join(HERE, 'results', 'module_fpt_bench.jsonl'), 'w', encoding='utf-8')
    tot = Counter()
    for name, fam, n0, f0 in cases():
        n, f, _ = restrict_essential(n0, f0)
        if n < 2:
            continue
        m, core, trace = simplify(n, f, signed=False)
        if m > maxcore:
            continue
        rec = dict(case=name, n=n, core_n=m, trace_len=len(trace))
        if m >= 2:
            M, dt, st = fpt_minimum(m, core)
            rec.update(fpt_core=None if M is None else M + len(trace), fpt_core_seconds=round(dt, 3),
                       fpt_core_states=st['states'], fpt_core_local=st['local'] + st['fast_local'])
            t0 = time.time()
            R = ref.minimum(m, core, 'general', seconds=120)[0]
            rec.update(ref_core=None if R in (None, 'undecided') else R + len(trace),
                       ref_core_seconds=round(time.time() - t0, 3))
        else:
            rec.update(fpt_core=len(trace) + (0 if core == 2 else 1), ref_core=len(trace) + (0 if core == 2 else 1))
        if n <= maxn and n >= 2:
            M, dt, st = fpt_minimum(n, f)
            rec.update(fpt_original=M, fpt_original_seconds=round(dt, 3), fpt_original_states=st['states'],
                       fpt_original_local=st['local'] + st['fast_local'])
        agree = len({v for k, v in rec.items() if k in ('fpt_core', 'ref_core', 'fpt_original') and v is not None}) <= 1
        rec['agree'] = agree
        out.write(json.dumps(rec) + '\n'); out.flush()
        tot['cases'] += 1; tot['disagree'] += not agree
        print(json.dumps(rec), flush=True)
    print('SUMMARY', dict(tot))
