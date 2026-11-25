"""Excess-three stage of the exact low-sharing ladder (modules -> one-sharing -> two-sharing -> ordered quotient).

Takes every corpus core that sharing_ladder_corpus.py left undecided (excess > 2) and decides excess <= 3 with
theory/ordered_quotient_core.solve3 (complete, fully reduced monotone / free-NOT cores; NOT counted-NOT).
Jobs, each in its own process with a hard deadline (terminated -> 'timeout'):
  q-default   solve3(internal_first=False)   (one shared internal wire tried before two)
  q-internal  solve3(internal_first=True)
  fpt         complete_sharing_fpt.Solver, excess 3 (monotone, core_n <= 6)
  sat         production cube_search.run_cube, monotone, whole core, G = m+1 (exclusion) and m+2
Status semantics:
  found excess 3: witness rebuilt by materialize3 and checked -> exact minimum (m-1)+3+trace (upper bound
    verified; lower bound = two_sharing exactness + module theorem).
  None: excess >= 4 *if* solve3's exhaustiveness claim at excess 3 holds (prototype claim, checked only on
    small oracles) -> provisional lower bound m+3+trace.
Free-NOT minima count binary gates with free NOTs; they are not counted-NOT totals.
Writes results/excess3_ladder.jsonl. Usage: python experiments/excess3_ladder.py [workers] [deadline]"""
import json, os, sys, time
import multiprocessing as mp
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))


def work(q, key, kind, n, f, signed):
    from collections import Counter
    from module_contraction import simplify
    m, core, tr = simplify(n, f, signed)
    rec = dict(key=key, kind=kind, core_n=m, trace=len(tr))
    t0 = time.time()
    if kind.startswith('q-'):
        from ordered_quotient_core import solve3, materialize3
        st = Counter()
        a = solve3(m, core, signed, st, internal_first=(kind == 'q-internal'))
        rec['seconds'] = round(time.time() - t0, 3)
        if a is not None:
            G, _ = materialize3(m, core, a, signed)
            rec.update(result=a[0], witness_gates=len(G))
        else:
            rec['result'] = None
        rec['stats'] = dict(st)
    elif kind == 'fpt':
        from complete_sharing_fpt import Solver
        s = Solver(m); rec['result'] = bool(s.solve(core, 3)); rec['seconds'] = round(time.time() - t0, 3)
    else:
        import cube_search as cs
        terms = [a for a in range(1 << m) if core >> a & 1 and not any(core >> (a ^ (1 << i)) & 1 for i in range(m) if a >> i & 1)]
        res = {}
        for G in (m + 1, m + 2):
            hit = False
            for c in [(op, l, rr) for op in (0, 1) for rr in range(m) for l in range(rr)]:
                if cs.run_cube((m, terms, G, 'maplechrono', c, False, False, dict(nonot=True)))[1] == 'WITNESS':
                    hit = True; break
            res[G] = hit
            rec[f'G{G}_seconds'] = round(time.time() - t0, 3)
            if hit:
                break
        rec['result'] = {str(k): v for k, v in res.items()}; rec['seconds'] = round(time.time() - t0, 3)
    q.put(rec)


if __name__ == '__main__':
    from signed_bound_compare import cases, restrict_essential
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    deadline = float(sys.argv[2]) if len(sys.argv) > 2 else 300
    ladder = {json.loads(l)['case']: json.loads(l) for l in open(os.path.join(HERE, 'results', 'sharing_ladder_corpus.jsonl'))}
    todo = []
    for name, fam, n0, f0 in cases():
        r = ladder.get(name, {})
        n, f, _ = restrict_essential(n0, f0)
        for basis, signed in (('monotone', False), ('free', True)):
            b = r.get(basis)
            if not b or b.get('excess') != '>2':
                continue
            key = f'{name}|{basis}'
            todo += [(key, 'q-default', n, f, signed), (key, 'q-internal', n, f, signed)]
            if basis == 'monotone' and b['core_n'] <= 6:
                todo.append((key, 'fpt', n, f, signed))
            if basis == 'monotone' and b['core_n'] <= 7:
                todo.append((key, 'sat', n, f, signed))
    # cheap-looking jobs first: smaller cores first
    todo.sort(key=lambda t: (ladder[t[0].split('|')[0]][t[0].split('|')[1]]['core_n'], t[1]))
    print(f'{len(todo)} jobs, {workers} workers, {deadline}s deadline', flush=True)
    out = open(os.path.join(HERE, 'results', 'excess3_ladder.jsonl'), 'w', encoding='utf-8')
    q = mp.Queue(); running = {}; k = 0; total = len(todo)
    while todo or running:
        while todo and len(running) < workers:
            item = todo.pop(0); p = mp.Process(target=work, args=(q, *item)); p.start()
            running[(item[0], item[1])] = (p, time.time(), item)
        while not q.empty():
            rec = q.get(); p, _, _ = running.pop((rec['key'], rec['kind'])); p.join(); k += 1
            out.write(json.dumps(rec) + '\n'); out.flush()
            print(f"[{k}/{total}] {rec['key']:34} {rec['kind']:10} m={rec['core_n']} tr={rec['trace']} "
                  f"result={rec.get('result')} {rec.get('seconds')}s", flush=True)
        for key, (p, t0, item) in list(running.items()):
            if time.time() - t0 > deadline:
                p.terminate(); p.join(); running.pop(key); k += 1
                out.write(json.dumps(dict(key=key[0], kind=key[1], status='timeout', deadline=deadline)) + '\n'); out.flush()
                print(f'[{k}/{total}] {key[0]:34} {key[1]:10} TIMEOUT {deadline}s', flush=True)
        time.sleep(0.2)
    print('DONE', flush=True)
