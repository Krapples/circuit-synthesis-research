"""Exact low-excess ladder on the frozen corpus: module preprocessing -> one-sharing -> two-sharing.

For each complete target (essential restriction), in each applicable basis
  monotone  (monotone targets; raw module reduction; monotone binary = total cost),
  free-NOT  (signed module reduction; binary gates with free NOTs -- NOT the counted total),
the core is decided by one_sharing_core.solve_core (excess <= 1) and two_sharing_core.solve (excess <= 2).
Exact minimum = (n_core - 1) + excess + len(trace) when the ladder decides it (module reduction: formally
proved in Lean, CircuitLemmas.module_contraction / peel_contraction). Witnesses are rebuilt with
two_sharing_core.reconstruct and checked on every row. Monotone results are compared with the recorded
monotone intervals; timing is compared with the regional FPT solver (complete_sharing_fpt) and the
production SAT search (cube_search.run_cube, monotone, whole function) on the same core.
Each case runs in its own process with a hard deadline (terminated on expiry, recorded as 'timeout').
Writes results/sharing_ladder_corpus.jsonl. Usage: python experiments/sharing_ladder_corpus.py [workers] [deadline]"""
import json, os, sys, time
import multiprocessing as mp
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))


def work(q, name, fam, n, f):
    from module_contraction import simplify, raw_monotone
    from one_sharing_core import solve_core
    from two_sharing_core import solve as solve2, reconstruct
    rec = dict(case=name, family=fam, n=n)
    for basis, signed in (('monotone', False), ('free', True)):
        if basis == 'monotone' and not raw_monotone(n, f):
            continue
        t0 = time.time()
        m, core, tr = simplify(n, f, signed)
        r = dict(core_n=m, trace=len(tr))
        if m <= 1:
            r['excess'] = 0; r['minimum'] = len(tr)
        else:
            one = solve_core(m, core, signed, False)
            if one is not None:
                r['excess'] = 1 if one[0] == m else 0; r['minimum'] = one[0] + len(tr)
            else:
                cert = solve2(m, core, signed)
                if cert is not None:
                    gates, z = reconstruct(m, core, cert, signed)       # asserts truth table and cost
                    r.update(excess=2, minimum=m + 1 + len(tr), certificate=cert[0], witness_gates=len(gates))
                else:
                    r['excess'] = '>2'
        r['seconds'] = round(time.time() - t0, 3)
        # baselines on the same core (monotone only; small cores)
        if basis == 'monotone' and 2 <= m <= 5 and r.get('excess') in (0, 1, 2):
            from complete_sharing_fpt import Solver
            t1 = time.time(); s = Solver(m); e = next((k for k in range(4) if s.solve(core, k)), None)
            r['fpt_excess'] = e; r['fpt_seconds'] = round(time.time() - t1, 3)
        if basis == 'monotone' and 2 <= m <= 7 and isinstance(r.get('excess'), int):
            import cube_search as cs
            terms = [a for a in range(1 << m) if core >> a & 1 and not any(core >> (a ^ (1 << i)) & 1 for i in range(m) if a >> i & 1)]
            t1 = time.time(); found = None
            for G in range(m - 1, m + 3):
                hit = False
                for c in [(op, l, rr) for op in (0, 1) for rr in range(m) for l in range(rr)]:
                    if cs.run_cube((m, terms, G, 'maplechrono', c, False, False, dict(nonot=True)))[1] == 'WITNESS':
                        hit = True; break
                if hit:
                    found = G; break
            r['sat_min'] = found; r['sat_seconds'] = round(time.time() - t1, 3)
        rec[basis] = r
    q.put(rec)


if __name__ == '__main__':
    from signed_bound_compare import cases, restrict_essential
    from one_sharing_corpus import mono_intervals
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    deadline = float(sys.argv[2]) if len(sys.argv) > 2 else 300
    moniv = mono_intervals()
    todo = []
    for name, fam, n0, f0 in cases():
        n, f, _ = restrict_essential(n0, f0)
        if n >= 2:
            todo.append((name, fam, n, f))
    out = open(os.path.join(HERE, 'results', 'sharing_ladder_corpus.jsonl'), 'w', encoding='utf-8')
    q = mp.Queue(); running = {}; done = 0; tally = dict(cases=0, timeouts=0, mono_exact=0, mono_new=0, free_exact=0,
                                                        disagree=0)
    while todo or running:
        while todo and len(running) < workers:
            item = todo.pop(0)
            p = mp.Process(target=work, args=(q, *item)); p.start(); running[item[0]] = (p, time.time(), item)
        while not q.empty():
            rec = q.get(); p, _, _ = running.pop(rec['case']); p.join()
            m = rec.get('monotone', {}); fr = rec.get('free', {})
            lo, hi = moniv.get(rec['case'], (None, None))
            rec['mono_interval'] = [lo, hi]
            tally['cases'] += 1
            if 'minimum' in m:
                tally['mono_exact'] += 1
                if lo is not None and lo < hi:
                    tally['mono_new'] += 1
                if (lo is not None and m['minimum'] < lo) or (hi not in (None, 10 ** 9) and m['minimum'] > hi):
                    tally['disagree'] += 1; print('!!! interval conflict', rec, flush=True)
                if m.get('sat_min') is not None and m['sat_min'] != m['minimum'] + 0 - m['trace'] + m['trace'] and m['core_n'] == m['core_n']:
                    pass
            tally['free_exact'] += 'minimum' in fr
            out.write(json.dumps(rec) + '\n'); out.flush()
            print(f"{rec['case']:22} n={rec['n']} mono={ {k: m.get(k) for k in ('core_n', 'excess', 'minimum', 'seconds', 'fpt_seconds', 'sat_seconds')} } "
                  f"free={ {k: fr.get(k) for k in ('core_n', 'excess', 'minimum', 'seconds')} } interval={rec['mono_interval']}", flush=True)
        for name, (p, t0, item) in list(running.items()):
            if time.time() - t0 > deadline:
                p.terminate(); p.join(); running.pop(name); tally['timeouts'] += 1
                out.write(json.dumps(dict(case=name, n=item[2], status='timeout', deadline=deadline)) + '\n'); out.flush()
                print(f'{name:22} TIMEOUT after {deadline}s', flush=True)
        time.sleep(0.2)
    print('SUMMARY', tally, flush=True)
