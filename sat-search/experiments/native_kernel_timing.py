"""In-process solver timing on the captured queries, without per-query deadline threads: Python reference vs native,
for local_blocks (row-quotient flags, signed) and the phase-first adaptive completion.  Only queries that the Python
reference decided under 2 s in results/native_differential_captured.jsonl are timed (so no cap is needed); each
solver is run on all of them in one process, sequentially, best of `reps` passes.
Usage: python experiments/native_kernel_timing.py [reps]"""
import json, os, sys, time
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))
from regional_block_completion import local_blocks
from regional_native import completion_native
from regional_phase_first import adaptive_completion

FLAGS = dict(port_first=True, witness_cover=True, row_quotient=True)
reps = int(sys.argv[1]) if len(sys.argv) > 1 else 3
decided = {}
for line in open(os.path.join(HERE, 'results', 'native_differential_captured.jsonl')):
    r = json.loads(line)
    decided[r['source'], r['idx']] = (r['blocks_signed']['py'] != 'timeout', r['phase_first']['py'] != 'timeout')
work = {'blocks': [], 'phase': []}
for fn, tag in (('phase_first_captured_heldout.jsonl', 'heldout'), ('phase_first_captured.jsonl', 'dev')):
    for line in open(os.path.join(HERE, 'results', fn)):
        r = json.loads(line)
        for i, q in enumerate(r['queries']):
            ok_blocks, ok_phase = decided[tag, f"{r['case']}:{r['kind']}:{i}"]
            args = (q[0], tuple(q[1]), tuple(q[2]), tuple(q[3]), True)
            if ok_blocks:
                work['blocks'].append(args)
            if ok_phase:
                work['phase'].append(args)
solvers = {
    'blocks': (lambda a: local_blocks(*a, **FLAGS), lambda a: completion_native(*a, adaptive=False)),
    'phase': (lambda a: adaptive_completion(*a), lambda a: completion_native(*a, adaptive=True)),
}
for name, (py, nat) in solvers.items():
    best = {}
    for label, fn in (('python', py), ('native', nat)):
        times = []
        for _ in range(reps):
            t = time.perf_counter()
            for a in work[name]:
                fn(a)
            times.append(time.perf_counter() - t)
        best[label] = min(times)
    print(f"{name}: {len(work[name])} queries  python {best['python']:.2f}s  native {best['native']:.3f}s  "
          f"speed-up {best['python'] / best['native']:.1f}x", flush=True)
