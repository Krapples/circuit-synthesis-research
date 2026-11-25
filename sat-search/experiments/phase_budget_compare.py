"""Matched comparison: normalized signed-skeleton counted-NOT encoding (theory/phase_budget_cnf.py) versus the
existing direct counted-NOT SAT encoding (experiments/synthesis_bench.direct_sat construction: cube_search.build,
explicit NOT slots, output on any wire, at most G gates).

Both encodings are at-most-G total gates (the new one with activation variables and a joint total budget);
neither is used for exact-size pinned-prefix claims. Same solver per measurement: maplechrono for time and
conflicts, glucose4 with DRUP for proof size (UNSAT only). Witnesses are decoded and checked on every labeled
row. Budgets: M - 1 and M for cases with a known NOT-enabled minimum M (complete targets of the corpus and the
nonmonotone cases). Time limit per solve: interrupt -> 'open'.
Writes results/phase_budget_compare.jsonl. Usage: python experiments/phase_budget_compare.py [workers] [seconds]"""
import json, os, sys, threading, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))
import cube_search as cs
from pysat.solvers import Solver
from pysat.card import CardEnc
from phase_budget_cnf import encode, decode, evaluate
from signed_bound_compare import cases, restrict_essential


def baseline_cnf(n, P, N, G):
    output, pool, clauses, ops, select = cs.build(n, G, colex_from=G, require_used=False)
    outputs = [pool.id(('output', i)) for i in range(output + 1)]
    clauses.extend(CardEnc.equals(outputs, 1, vpool=pool).clauses)
    for row in range(1 << n):
        if not (P | N) >> row & 1:
            continue
        value = P >> row & 1
        vals = [pool.id(('val', row, j)) for j in range(output + 1)]
        clauses.extend([vals[i] if row >> i & 1 else -vals[i]] for i in range(n))
        clauses.extend(cs.truth_gate_clauses(row, vals, pool, ops, select))
        clauses.extend([-sel, vals[i] if value else -vals[i]] for i, sel in enumerate(outputs))
    return clauses, pool.top


def solve(clauses, solver, seconds, proof=False):
    with Solver(name=solver, bootstrap_with=clauses, with_proof=proof) as s:
        timer = threading.Timer(seconds, s.interrupt); timer.start()
        t0 = time.time()
        r = s.solve_limited(expect_interrupt=True)
        dt = time.time() - t0
        timer.cancel()
        st = s.accum_stats() or {}
        model = s.get_model() if r else None
        prf = len(s.get_proof()) if (proof and r is False) else None
    return r, dt, st.get('conflicts'), model, prf


def job(args):
    name, n, P, N, G, enc, seconds = args
    if enc == 'baseline':
        clauses, nv = baseline_cnf(n, P, N, G)
        meta = None
    else:
        c, meta = encode(n, G, G, P, N, atmost=True, total=G)
        clauses, nv = c.clauses, c.n
    r, dt, conf, model, _ = solve(clauses, 'maplechrono', seconds)
    status = 'open' if r is None else 'SAT' if r else 'UNSAT'
    ok = None
    if status == 'SAT' and meta is not None:
        g, v = decode(n, meta, set(l for l in model if l > 0))
        f = evaluate(n, g, v)
        ok = f & P == P and not f & N and len(g) <= G
    prf = None
    if status == 'UNSAT':
        _, _, _, _, prf = solve(clauses, 'glucose4', seconds, proof=True)
    return dict(case=name, n=n, G=G, encoding=enc, status=status, verified=ok, vars=nv, clauses=len(clauses),
                conflicts=conf, seconds=round(dt, 3), proof_lines=prf)


if __name__ == '__main__':
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    seconds = float(sys.argv[2]) if len(sys.argv) > 2 else 300
    known = {}
    for line in open(os.path.join(HERE, 'results', 'signed_bound_compare.jsonl'), encoding='utf-8'):
        r = json.loads(line)
        lo, hi = r.get('sat_lower'), r.get('upper')
        best_lo = max(r['support'], r.get('existing') or 0, lo or 0, r['signed'])
        if hi not in (None, 10 ** 9) and best_lo >= hi:
            known[r['case']] = hi
    jobs = []
    for name, fam, n0, f0 in cases():
        if name not in known:
            continue
        n, f, _ = restrict_essential(n0, f0)
        if n < 2 or n > 6:
            continue
        P, N = f, ((1 << (1 << n)) - 1) & ~f
        M = known[name]
        for G in (M - 1, M):
            if G >= 1:
                for enc in ('baseline', 'phase'):
                    jobs.append((name, n, P, N, G, enc, seconds))
    print(f'{len(jobs)} solves on {len(jobs) // 4} cases', flush=True)
    out = open(os.path.join(HERE, 'results', 'phase_budget_compare.jsonl'), 'w', encoding='utf-8')
    with Pool(workers) as p:
        for r in p.imap_unordered(job, jobs):
            out.write(json.dumps(r) + '\n'); out.flush()
            print(json.dumps(r), flush=True)
    rows = [json.loads(l) for l in open(os.path.join(HERE, 'results', 'phase_budget_compare.jsonl'))]
    for enc in ('baseline', 'phase'):
        rs = [r for r in rows if r['encoding'] == enc]
        print(enc, 'solves', len(rs), 'open', sum(r['status'] == 'open' for r in rs),
              'vars', sum(r['vars'] for r in rs), 'clauses', sum(r['clauses'] for r in rs),
              'conflicts', sum(r['conflicts'] or 0 for r in rs), 'seconds', round(sum(r['seconds'] for r in rs), 1),
              'proof lines', sum(r['proof_lines'] or 0 for r in rs), flush=True)
    pair = {}
    for r in rows:
        pair.setdefault((r['case'], r['G']), {})[r['encoding']] = r
    disagree = [k for k, v in pair.items() if len(v) == 2 and 'open' not in (v['baseline']['status'], v['phase']['status'])
                and v['baseline']['status'] != v['phase']['status']]
    print('verdict disagreements:', disagree, 'bad witnesses:', sum(1 for r in rows if r['verified'] is False))
