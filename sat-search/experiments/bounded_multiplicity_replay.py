"""Replay captured signed regional queries: integrated 'phase-first' completion (regional_phase_first.adaptive_completion)
versus the 'bounded-multiplicity' backend (regional_bounded_multiplicity.completion). Per-query cap via
regional_deadline.timed; witnesses checked; decisions must agree.
Workloads: results/phase_first_captured_heldout.jsonl (547) and results/phase_first_captured.jsonl (896).
Writes results/bounded_multiplicity_replay.jsonl. Usage: python experiments/bounded_multiplicity_replay.py [workers] [cap]"""
import json, os, sys, time
from collections import Counter
from multiprocessing import Pool
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))


def job(a):
    src, idx, q, cap = a
    from regional_phase_first import adaptive_completion
    from regional_bounded_multiplicity import completion
    from regional_production_adapter import check_tree
    from regional_deadline import timed
    m, ports, pats, targets = q[0], tuple(q[1]), tuple(q[2]), tuple(q[3])
    out = dict(source=src, idx=idx, m=m, ports=len(ports), repeats=len(ports) - len(set(ports)), rows=len(pats))
    for name, fn in (('phase-first', adaptive_completion), ('bounded', completion)):
        st = Counter(); t0 = time.perf_counter()
        r = timed(cap, lambda: {'status': 'done', 'w': fn(m, ports, pats, targets, True, st)}, lambda: {})
        dt = round(time.perf_counter() - t0, 4)
        if r['status'] == 'TIMEOUT':
            out[name] = ('timeout', dt, {})
        else:
            if r['w'] is not None:
                check_tree(r['w'], m, ports, pats, targets, True)
            keep = {k: st[k] for k in ('optional_lift', 'optional_unsat', 'phase_prescreen', 'fallback') if st.get(k)}
            out[name] = ('sat' if r['w'] is not None else 'unsat', dt, keep)
    d = {out[k][0] for k in ('phase-first', 'bounded') if out[k][0] != 'timeout'}
    assert len(d) <= 1, out
    return out


if __name__ == '__main__':
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    cap = float(sys.argv[2]) if len(sys.argv) > 2 else 0.5
    W = []
    for fn, tag in (('phase_first_captured_heldout.jsonl', 'heldout'), ('phase_first_captured.jsonl', 'dev')):
        for l in open(os.path.join(HERE, 'results', fn)):
            r = json.loads(l)
            W += [(tag, f"{r['case']}:{r['kind']}:{i}", q, cap) for i, q in enumerate(r['queries'])]
    print(f'{len(W)} queries, cap {cap}s', flush=True)
    out = open(os.path.join(HERE, 'results', 'bounded_multiplicity_replay.jsonl'), 'w', encoding='utf-8'); agg = Counter()
    with Pool(workers) as p:
        for r in p.imap_unordered(job, W, chunksize=2):
            out.write(json.dumps(r) + '\n')
            for k in ('phase-first', 'bounded'):
                agg[r['source'], k, 'decided'] += r[k][0] != 'timeout'; agg[r['source'], k, 's'] += r[k][1]
                if r[k][0] == 'timeout' and r['phase-first' if k == 'bounded' else 'bounded'][0] != 'timeout':
                    agg[r['source'], k, 'lost'] += 1
            agg[r['source'], 'n'] += 1
    for src in ('heldout', 'dev'):
        print(src, 'n', agg[src, 'n'], ' '.join(f"{k}: {agg[src, k, 'decided']} decided {agg[src, k, 's']:.2f}s lost {agg[src, k, 'lost']}"
                                                for k in ('phase-first', 'bounded')), flush=True)
