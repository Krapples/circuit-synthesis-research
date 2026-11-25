"""End-to-end check of the opt-in 'phase-first' completion mode: free-NOT solve3 (excess <= 3) on every free-NOT core
of results/excess3_ladder.jsonl, completion 'row-quotient' (baseline, full cap) versus 'phase-first' (capped at
max(10 s, 1.5 x baseline); hitting that cap is 'stopped-worse'). Decisions must agree; witnesses are rebuilt by
materialize3 and checked. Writes results/phase_first_layout.jsonl.
Usage: python experiments/phase_first_layout.py [workers] [seconds] [excess] [base_mode] [challenger_mode]   (excess 3: solve3; >3: layout_projection.search_exact)"""
import json, os, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))


def one(name, mode, seconds, excess=3):
    from collections import Counter
    from module_contraction import simplify
    from signed_bound_compare import cases, restrict_essential
    from ordered_quotient_core import make_completion, solve3, materialize3
    from regional_deadline import timed
    fr = {nm: (n, f) for nm, _, n, f in cases()}
    n, f, _ = restrict_essential(*fr[name]); m, core, _ = simplify(n, f, True)
    comp = make_completion(mode); st = Counter()

    def job():
        if excess == 3:
            a = solve3(m, core, True, st, completion=comp)
            if a is not None:
                materialize3(m, core, a, True)
            return {'status': 'done', 'result': None if a is None else a[0]}
        from layout_projection import search_exact
        from ordered_quotient_core import reconstruct
        a = search_exact(m, core, excess, True, st, completion=comp)
        if a is not None:
            reconstruct(m, core, *a, excess)              # asserts truth table and gate count
        return {'status': 'done', 'result': None if a is None else 'witness'}
    t0 = time.perf_counter(); r = timed(seconds, job, lambda: {})
    return dict(status=r['status'], result=r.get('result'), seconds=round(time.perf_counter() - t0, 3),
                phase_calls=comp.metrics().get('phase_first_calls', 0), core_n=m)


def one_job(a):
    return a[0], a[1], one(*a)


if __name__ == '__main__':
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    seconds = float(sys.argv[2]) if len(sys.argv) > 2 else 120
    excess = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    base_mode = sys.argv[4] if len(sys.argv) > 4 else 'row-quotient'
    challenger = sys.argv[5] if len(sys.argv) > 5 else 'phase-first'
    tag = '' if (base_mode, challenger) == ('row-quotient', 'phase-first') else f'_{challenger}'
    names = sorted({json.loads(l)['key'].split('|')[0] for l in open(os.path.join(HERE, 'results', 'excess3_ladder.jsonl'))
                    if json.loads(l)['key'].endswith('|free')})
    if len(sys.argv) > 6:                       # optional comma-separated subset of cases
        names = [nm for nm in names if nm in set(sys.argv[6].split(','))]
        tag += '_subset'
    out = open(os.path.join(HERE, 'results', ('phase_first_layout' if excess == 3 else f'phase_first_layout_e{excess}') + tag + '.jsonl'), 'w', encoding='utf-8')
    # every solve in a fresh process (no warm module caches); baselines first, then phase-first with early stopping
    with Pool(workers, maxtasksperchild=1) as p:
        base = {nm: r for nm, _, r in p.imap_unordered(one_job, [(nm, base_mode, seconds, excess) for nm in names])}
        caps = {nm: seconds if base[nm]['status'] == 'TIMEOUT' else min(seconds, max(10.0, 1.5 * base[nm]['seconds']))
                for nm in names}
        phase = {nm: r for nm, _, r in p.imap_unordered(one_job, [(nm, challenger, caps[nm], excess) for nm in names])}
    tb = tp = 0.0; agree = 0
    for nm in names:
        b, ph = base[nm], phase[nm]
        if ph['status'] == 'TIMEOUT' and caps[nm] < seconds:
            ph['status'] = 'stopped-worse'
        if b['status'] == ph['status'] == 'done':
            assert (b['result'] is None) == (ph['result'] is None), (nm, b, ph)
            agree += 1; tb += b['seconds']; tp += ph['seconds']
        out.write(json.dumps(dict(case=nm, base=b, phase=ph, cap=round(caps[nm], 1))) + '\n')
        print(f"{nm:20} m={b['core_n']} base {b['status']} {b['result']} {b['seconds']}s | "
              f"phase {ph['status']} {ph['result']} {ph['seconds']}s calls={ph['phase_calls']}", flush=True)
    print(f'DONE {agree} both decided; total base {tb:.2f}s phase {tp:.2f}s', flush=True)
