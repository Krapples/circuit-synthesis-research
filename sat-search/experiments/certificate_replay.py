"""Replay captured signed regional queries: integrated 'phase-first' (regional_phase_first.adaptive_completion) versus
'phase-certificate' (regional_certificate_propagation.certificate_completion: same routing + certificate prescreen).
Per-query cap via regional_deadline.timed; witnesses checked; decisions must agree. Reports SAT and UNSAT separately.
Workloads: results/phase_first_captured_heldout.jsonl (547), results/phase_first_captured.jsonl (896).
Writes results/certificate_replay.jsonl. Usage: python experiments/certificate_replay.py [workers] [cap]"""
import json, os, sys, time
from collections import Counter
from multiprocessing import Pool
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))
MODES = ('phase-first', 'phase-certificate')


def job(a):
    src, idx, q, cap = a
    from regional_phase_first import adaptive_completion
    from regional_certificate_propagation import certificate_completion
    from regional_production_adapter import check_tree
    from regional_deadline import timed
    m, ports, pats, targets = q[0], tuple(q[1]), tuple(q[2]), tuple(q[3])
    out = dict(source=src, idx=idx, m=m, ports=len(ports), repeats=len(ports) - len(set(ports)), rows=len(pats))
    for name, fn in zip(MODES, (adaptive_completion, certificate_completion)):
        st = Counter(); t0 = time.perf_counter()
        r = timed(cap, lambda: {'status': 'done', 'w': fn(m, ports, pats, targets, True, st)}, lambda: {})
        dt = round(time.perf_counter() - t0, 4)
        keep = {k: st[k] for k in ('local', 'certificate_queries', 'certificate_rejections', 'monotone_calls') if st.get(k)}
        if r['status'] == 'TIMEOUT':
            out[name] = ('timeout', dt, keep)
        else:
            if r['w'] is not None:
                check_tree(r['w'], m, ports, pats, targets, True)
            out[name] = ('sat' if r['w'] is not None else 'unsat', dt, keep)
    d = {out[k][0] for k in MODES if out[k][0] != 'timeout'}
    assert len(d) <= 1, out
    out['truth'] = d.pop() if d else 'unknown'
    return out


if __name__ == '__main__':
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    cap = float(sys.argv[2]) if len(sys.argv) > 2 else 0.5
    W = []
    for fn, tag in (('phase_first_captured_heldout.jsonl', 'heldout'), ('phase_first_captured.jsonl', 'dev')):
        for l in open(os.path.join(HERE, 'results', fn)):
            r = json.loads(l)
            W += [(tag, f"{r['case']}:{r['kind']}:{i}", q, cap) for i, q in enumerate(r['queries'])]
    out = open(os.path.join(HERE, 'results', 'certificate_replay.jsonl'), 'w', encoding='utf-8'); agg = Counter()
    with Pool(workers) as p:
        for r in p.imap_unordered(job, W, chunksize=2):
            out.write(json.dumps(r) + '\n')
            for k in MODES:
                key = (r['source'], r['truth'], k)
                agg[key + ('n',)] += 1; agg[key + ('decided',)] += r[k][0] != 'timeout'; agg[key + ('s',)] += r[k][1]
                agg[key + ('local',)] += r[k][2].get('local', 0)
    for src in ('heldout', 'dev'):
        for truth in ('sat', 'unsat', 'unknown'):
            row = [f"{k}: {agg[(src, truth, k, 'decided')]}/{agg[(src, truth, k, 'n')]} {agg[(src, truth, k, 's')]:.2f}s local={agg[(src, truth, k, 'local')]}" for k in MODES]
            if agg[(src, truth, MODES[0], 'n')]:
                print(src, truth, ' | '.join(row), flush=True)
