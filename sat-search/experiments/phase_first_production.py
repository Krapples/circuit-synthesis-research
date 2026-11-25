"""Production evaluation of phase-first signed regional completion (theory/regional_phase_first.py).

Baseline = production regional completion: regional_block_completion.local_blocks(signed, port_first,
witness_cover, row_quotient) (the 'row-quotient' mode). Phase-first enumerates feasible literal-polarity classes
and calls the same production solver on monotone recoded queries (regional_production_adapter).

  capture   run free-NOT layout searches with the production completion wrapped in a recorder:
            solve3 (excess <= 3) and layout_projection.search_exact at excess 4, on corpus free-NOT cores;
            writes results/phase_first_captured.jsonl (distinct signed queries, all with m + ports >= 4).
  replay    every query x mode under a per-query cap (regional_deadline.timed, cooperative on Windows):
            base, phase, lift-phase (singleton-port promotion then phase), portfolio (phase for 25% of the
            cap, then base for the rest), adaptive (phase only when the feature rule fires, else base).
            Workloads: captured queries, regional_cover_stress signed generated queries (small and large),
            regional_phase_extra_bench signed cases. Witnesses checked; decisions must agree.
            writes results/phase_first_replay.jsonl.
Usage: python experiments/phase_first_production.py capture [workers] [seconds]
       python experiments/phase_first_production.py replay [workers] [cap]"""
import json, os, sys, time
from collections import Counter
from multiprocessing import Pool
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))

FREE_CORES = ('hypergraph-12', 'graph-01', 'comparator-07', 'hypergraph-08', 'hypergraph-03', 'hypergraph-19',
              'random-monotone-10', 'graph-03', 'comparator-02', 'hypergraph-21', 'mux-4-to-1', 'cycle-5',
              'graph-02', 'hypergraph-23', 'hypergraph-14', 'random-monotone-04')


def features(q):
    m, ports, pats, targets, signed = q
    labelled = sum(1 for t in targets if t != -1) << m
    rep = sum(c - 1 for c in Counter(ports).values())
    return dict(m=m, ports=len(ports), providers=len(set(ports)), repeats=rep, rows=len(pats), labels=labelled)


def adaptive_rule(f):
    """Phase-first when the query is port-heavy (repeated providers) and the label table is small enough that the
    quadratic distinction-clause build stays cheap."""
    return f['repeats'] >= 1 and f['labels'] <= 512


# ---------------------------------------------------------------- capture
def capture_job(a):
    name, kind, seconds = a
    from module_contraction import simplify
    from signed_bound_compare import cases, restrict_essential
    from ordered_quotient_core import make_completion, solve3
    from layout_projection import search_exact
    from regional_deadline import timed
    fr = {nm: (n, f) for nm, _, n, f in cases()}
    n, f, _ = restrict_essential(*fr[name]); m, core, _ = simplify(n, f, True)
    base = make_completion('row-quotient'); seen = {}

    def rec(mm, ports, pats, targets, signed, *rest, **kw):
        if signed and mm + len(ports) >= 4:
            key = (mm, tuple(ports), tuple(pats), tuple(targets))
            seen.setdefault(key, 0); seen[key] += 1
        return base(mm, ports, pats, targets, signed, *rest, **kw)

    def job():
        if kind == 'e3':
            solve3(m, core, True, completion=rec)
        else:
            search_exact(m, core, 4, True, completion=rec)
        return {'status': 'done'}
    r = timed(seconds, job, lambda: {})
    return name, kind, m, r['status'], [list(k) + [True] for k in seen]


# ---------------------------------------------------------------- replay
def run_mode(mode, q, cap):
    from regional_production_adapter import local_cover, check_tree
    from regional_phase_first import phase_first
    from regional_axis_lift import lift_axes
    from regional_deadline import timed
    m, ports, pats, targets, signed = q
    st = Counter()

    def base():
        return local_cover(m, ports, pats, targets, True, st)

    def phase():
        return phase_first(m, ports, pats, targets, st)

    def lift_phase():
        return lift_axes(m, ports, pats, targets, True, st, lambda mm, p, ps, t, s: phase_first(mm, p, ps, t, st))

    def go(fn, seconds):
        t0 = time.perf_counter()
        r = timed(seconds, lambda: {'status': 'done', 'w': fn()}, lambda: {})
        dt = time.perf_counter() - t0
        if r['status'] == 'TIMEOUT':
            return 'timeout', None, dt
        return ('sat' if r['w'] is not None else 'unsat'), r['w'], dt

    t0 = time.perf_counter()
    if mode == 'base':
        s, w, _ = go(base, cap)
    elif mode == 'phase':
        s, w, _ = go(phase, cap)
    elif mode == 'lift-phase':
        s, w, _ = go(lift_phase, cap)
    elif mode == 'portfolio':
        s, w, dt = go(phase, 0.25 * cap)
        if s == 'timeout':
            s, w, _ = go(base, cap - dt)
    elif mode == 'adaptive':
        s, w, _ = go(phase if adaptive_rule(features(q)) else base, cap)
    if w is not None:
        check_tree(w, m, ports, pats, targets, True)
    return s, round(time.perf_counter() - t0, 4), st.get('rec', 0)


MODES = ('base', 'phase', 'lift-phase', 'portfolio', 'adaptive')


def replay_job(a):
    src, idx, q, cap = a
    q = (q[0], tuple(q[1]), tuple(q[2]), tuple(q[3]), True)
    out = dict(source=src, idx=idx, **features(q), rule=adaptive_rule(features(q)))
    for mode in MODES:
        out[mode] = run_mode(mode, q, cap)
    dec = {v[0] for v in (out[k] for k in MODES) if v[0] != 'timeout'}
    assert len(dec) <= 1, out
    return out


def workloads():
    W = []
    for l in open(os.path.join(HERE, 'results', 'phase_first_captured.jsonl')):
        r = json.loads(l)
        for i, q in enumerate(r['queries']):
            W.append((f"captured:{r['case']}:{r['kind']}", i, q))
    from regional_cover_stress import instances
    for large in (False, True):
        for j, q, _ in instances(large):
            if q[-1]:
                W.append((f"stress-{'large' if large else 'small'}", j, list(q)))
    import regional_phase_extra_bench as X
    for j, (m, p, ps, ts, _) in enumerate(X.cases()):
        W.append(('phase-extra', j, [m, p, ps, ts, True]))
    return W


if __name__ == '__main__':
    what = sys.argv[1]
    workers = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    if what == 'capture':
        seconds = float(sys.argv[3]) if len(sys.argv) > 3 else 60
        jobs = [(nm, k, seconds) for nm in FREE_CORES for k in ('e3', 'e4')]
        out = open(os.path.join(HERE, 'results', 'phase_first_captured.jsonl'), 'w', encoding='utf-8')
        with Pool(workers, maxtasksperchild=1) as p:
            for name, kind, m, status, qs in p.imap_unordered(capture_job, jobs):
                # keep at most 60 distinct queries per run, preferring port-heavy ones
                qs.sort(key=lambda q: (-(len(q[1]) - len(set(q[1]))), -len(q[1]), -q[0]))
                qs = qs[:60]
                out.write(json.dumps(dict(case=name, kind=kind, core_n=m, status=status, queries=qs)) + '\n'); out.flush()
                print(f'{name:20} {kind} m={m} {status} captured {len(qs)}', flush=True)
    else:
        cap = float(sys.argv[3]) if len(sys.argv) > 3 else 0.5
        W = workloads(); print(f'{len(W)} queries x {len(MODES)} modes, cap {cap}s, {workers} workers', flush=True)
        out = open(os.path.join(HERE, 'results', 'phase_first_replay.jsonl'), 'w', encoding='utf-8')
        agg = Counter(); k = 0
        with Pool(workers) as p:
            for r in p.imap_unordered(replay_job, [(s, i, q, cap) for s, i, q in W], chunksize=2):
                out.write(json.dumps(r) + '\n'); out.flush(); k += 1
                grp = r['source'].split(':')[0]
                for mode in MODES:
                    agg[grp, mode, 'decided'] += r[mode][0] != 'timeout'; agg[grp, mode, 'seconds'] += r[mode][1]
                agg[grp, 'n'] += 1
                if k % 25 == 0 or k == len(W):
                    print(f'[{k}/{len(W)}]', flush=True)
        for grp in sorted({g for g, *_ in agg}):
            print(grp, 'n', agg[grp, 'n'], ' '.join(f"{m}={agg[grp, m, 'decided']}/{round(agg[grp, m, 'seconds'], 2)}s" for m in MODES), flush=True)
