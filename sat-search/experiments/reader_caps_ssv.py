"""Primary-reader caps (theory/primary_reader_caps.py) inside the SSV AIG encoder (theory/ssv_aig.py).

Configurations (same solver, same CEGAR, same start = proved lower bound ssv_aig.sound_lower):
  base       alonce, colex, oplex, consecutive AND/OR noreapply
  noreapply  base + full no-reapplication (minimum-preserving)
  caps       noreapply + primary-reader caps for budget k (minimum-preserving; conditional caps need noreapply)
Minimum-preserving constraints are only used inside the increasing search from a proved lower bound; their UNSAT
answers are "no minimum circuit of size k", never exact-size or pinned-prefix claims.

  check  correctness: every essential 3-input function and a sample of 4-input NPN classes, all three configs must
         agree with each other and with the reference (brute-force free-NOT oracle for n = 3, Percy sizes for n = 4).
  bench  4-input NPN classes at excess 4 and 5 (sizes from results/baselines/screen_npn4_clean.jsonl), one process
         per (target, config) with a hard deadline; per-budget conflicts, vars, clauses, CEGAR rows, seconds.
Writes results/reader_caps_ssv.jsonl. Usage: python experiments/reader_caps_ssv.py check|bench [workers] [seconds]"""
import json, os, sys, time
import multiprocessing as mp
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))
BASE = ('alonce', 'colex', 'oplex', 'noreapply')
CONFIGS = {'base': dict(sym=BASE), 'noreapply': dict(sym=BASE + ('noreapply_full',)),
           'caps': dict(sym=BASE + ('noreapply_full',), caps=True)}


def run(n, tt, config, solver='cadical195'):
    from ssv_aig import minimum, sound_lower, simulate
    lb = sound_lower(n, tt)
    r = minimum(n, tt, start=lb, solver=solver, **CONFIGS[config])
    if r['steps'] is not None:
        assert simulate(n, r['gates'], r['out']) == tt
    return lb, r


def check():
    from module_contraction import brute, essential
    ref = brute(3, 5, 'free'); C = {}          # exhaustive up to 5 gates; every 3-input function needs <= 6
    for f in range(1, 255):
        if not essential(3, f):
            continue
        sizes = {c: run(3, f, c)[1]['steps'] for c in CONFIGS}
        want = ref.get(f, ref.get(255 ^ f, 6))
        assert len(set(sizes.values())) == 1 and sizes['base'] == want, (hex(f), sizes, want)
        C[f] = want
    print('n=3: all configs agree with the oracle on', len(C), 'essential functions', flush=True)
    rows = [json.loads(l) for l in open(os.path.join(HERE, 'results', 'baselines', 'screen_npn4_clean.jsonl'))]
    percy = {r['name']: r['size'] for r in rows if r.get('tool') == 'percy-cegar-satoko' and r.get('status') == 'OPTIMAL'
             and r['n'] == 4}
    k = 0
    for name, size in sorted(percy.items(), key=lambda kv: kv[1])[:60:3]:
        tt = int(name.split('-')[1], 16)
        sizes = {c: run(4, tt, c)[1]['steps'] for c in CONFIGS}
        assert len(set(sizes.values())) == 1 and sizes['base'] == size, (name, sizes, size)
        k += 1
    print('n=4:', k, 'classes agree with Percy in all configs', flush=True)


def job(q, name, n, tt, config):
    t0 = time.perf_counter()
    lb, r = run(n, tt, config)
    q.put(dict(name=name, n=n, config=config, start=lb, size=r['steps'], seconds=round(time.perf_counter() - t0, 3),
               budgets=r['budgets']))


def bench(workers, seconds):
    rows = [json.loads(l) for l in open(os.path.join(HERE, 'results', 'baselines', 'screen_npn4_clean.jsonl'))]
    targets = []
    for r in rows:
        if r.get('tool') == 'percy-cegar-satoko' and r.get('status') == 'OPTIMAL' and r['n'] == 4:
            exc = r['size'] - 3
            if exc in (4, 5):
                targets.append((exc, r['name'], int(r['name'].split('-')[1], 16)))
    targets.sort()
    pick = [t for t in targets if t[0] == 4][:10] + [t for t in targets if t[0] == 5][:10]
    todo = [(name, 4, tt, c) for _, name, tt in pick for c in CONFIGS]
    print(len(pick), 'targets x', len(CONFIGS), 'configs, cap', seconds, 's,', workers, 'workers', flush=True)
    out = open(os.path.join(HERE, 'results', 'reader_caps_ssv.jsonl'), 'w', encoding='utf-8')
    q = mp.Queue(); running = {}
    while todo or running:
        while todo and len(running) < workers:
            it = todo.pop(0); p = mp.Process(target=job, args=(q, *it)); p.start(); running[(it[0], it[3])] = (p, time.time())
        while not q.empty():
            r = q.get(); p, _ = running.pop((r['name'], r['config'])); p.join()
            out.write(json.dumps(r) + '\n'); out.flush()
            conf = sum(b.get('conflicts', 0) for b in r['budgets'])
            print(f"{r['name']} {r['config']:10} size={r['size']} {r['seconds']}s conflicts={conf}", flush=True)
        for key, (p, t0) in list(running.items()):
            if time.time() - t0 > seconds:
                p.terminate(); p.join(); running.pop(key)
                out.write(json.dumps(dict(name=key[0], config=key[1], status='timeout', cap=seconds)) + '\n'); out.flush()
                print(f'{key[0]} {key[1]:10} TIMEOUT', flush=True)
        time.sleep(0.1)


if __name__ == '__main__':
    if sys.argv[1] == 'check':
        check()
    else:
        bench(int(sys.argv[2]) if len(sys.argv) > 2 else 12, float(sys.argv[3]) if len(sys.argv) > 3 else 120)
