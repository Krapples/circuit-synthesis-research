"""Deterministic (cProfile) time breakdown of the regional completion modes, to choose what to port to native code.

Workloads:
  captured <mode> [cap] [workers]          547 held-out + 896 dev captured signed queries (results/phase_first_captured*.jsonl),
                                           each through a fresh make_completion(mode), per-query cap via regional_deadline.timed
  layout <mode> <excess> [seconds] [workers] [subset]   free-NOT search_exact / solve3 on the 48 corpus cores
                                           (as experiments/phase_first_layout.py), each core in a fresh process
Each worker writes a pstats file; the parent merges them and prints inclusive (outermost) time of the main components
and the top self-time functions.  cProfile inflates small-function cost (~2x); use the shares, not the absolute times.
Writes logs/native_profile_<workload>_<mode>[_e<excess>].txt."""
import cProfile, io, json, os, pstats, sys, tempfile, time
from collections import Counter
from multiprocessing import Pool
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))

# (file suffix, function) -> label for inclusive time (cProfile cumtime counts the outermost call of recursive functions)
COMPONENTS = [
    ('regional_obligation_cache.py', '__call__', 'ObligationCache.__call__ (all completion work)'),
    ('regional_obligation_cache.py', '_normalize', 'ObligationCache._normalize (cache-key normalization)'),
    ('regional_obligation_cache.py', '_solve', 'ObligationCache._solve (solver on cache miss)'),
    ('regional_phase_first.py', 'adaptive_completion', 'phase-first adaptive_completion'),
    ('regional_phase_first.py', 'phase_first', 'phase_first (incl. monotone local_blocks)'),
    ('regional_phase_first.py', 'phase_problem', 'phase_first.phase_problem (clause build)'),
    ('regional_phase_first.py', 'rec', 'phase_first.phase_domains (sign-class enumeration)'),
    ('regional_production_adapter.py', 'check_tree', 'check_tree (lifted witness check)'),
    ('regional_block_completion.py', 'local_blocks', 'local_blocks (regional kernel, all)'),
    ('regional_block_completion.py', 'complete', 'local_blocks.complete (outermost)'),
    ('regional_block_completion.py', 'cover', 'local_blocks.cover'),
    ('regional_block_completion.py', 'port_partitions', 'local_blocks.port_partitions'),
    ('regional_block_completion.py', 'learn', 'local_blocks.learn (read-once constraints)'),
    ('one_sharing_core.py', 'tree', 'one_sharing_core.tree (read-once recognition)'),
    ('regional_block_completion.py', 'solve_quotiented', 'local_blocks.solve_quotiented'),
    ('ordered_quotient_core.py', 'fixed', 'ordered_quotient_core.fixed (layout DP)'),
    ('layout_projection.py', 'search_exact', 'layout_projection.search_exact'),
]


def load_captured():
    work = []
    for fn, tag in (('phase_first_captured_heldout.jsonl', 'heldout'), ('phase_first_captured.jsonl', 'dev')):
        for line in open(os.path.join(HERE, 'results', fn)):
            r = json.loads(line)
            work += [(tag, f"{r['case']}:{r['kind']}:{i}", q) for i, q in enumerate(r['queries'])]
    return work


def captured_chunk(args):
    mode, cap, chunk, out = args
    from ordered_quotient_core import make_completion
    from regional_deadline import timed
    prof = cProfile.Profile(); res = Counter()
    for tag, name, q in chunk:
        m, ports, pats, targets = q[0], tuple(q[1]), tuple(q[2]), tuple(q[3])
        comp = make_completion(mode)
        t0 = time.perf_counter()
        prof.enable()
        r = timed(cap, lambda: {'status': 'done', 'w': comp(m, ports, pats, targets, True)}, lambda: {})
        prof.disable()
        res['seconds'] += time.perf_counter() - t0
        res['timeout' if r['status'] == 'TIMEOUT' else 'sat' if r['w'] is not None else 'unsat'] += 1
    prof.dump_stats(out)
    return res


def layout_job(args):
    name, mode, seconds, excess, out = args
    from phase_first_layout import one
    prof = cProfile.Profile()
    r = prof.runcall(one, name, mode, seconds, excess)
    prof.dump_stats(out)
    return name, r


def report(files, header, wall):
    st = pstats.Stats(files[0])
    for f in files[1:]:
        st.add(f)
    # Exclude the deadline timer thread (cProfile on 3.12+ also samples other threads) from the total.
    idle = lambda fn, nm: fn.endswith('threading.py') or nm in ("<method 'join' of '_thread._ThreadHandle' objects>",
                                                                "<method 'acquire' of '_thread.lock' objects>")
    total = sum(tt for (fn, _, nm), (_, _, tt, _, _) in st.stats.items() if not idle(fn, nm))
    lines = [header, f'profiled self-time total {total:.2f}s (wall {wall:.1f}s)', '', 'Inclusive time of components:']
    for suffix, func, label in COMPONENTS:
        cum = sum(ct for (fn, _, nm), (_, _, _, ct, _) in st.stats.items() if fn.endswith(suffix) and nm == func)
        if cum:
            lines.append(f'  {cum:9.2f}s {100 * cum / total:5.1f}%  {label}')
    byfile = Counter()
    for (fn, _, nm), (_, _, tt, _, _) in st.stats.items():
        byfile[os.path.basename(fn) if fn != '~' else nm] += tt
    lines += ['', 'Self time by file:'] + [f'  {t:9.2f}s {100 * t / total:5.1f}%  {f}' for f, t in byfile.most_common(15)]
    top = sorted(st.stats.items(), key=lambda kv: -kv[1][2])[:30]
    lines += ['', 'Top self-time functions (calls, self s, cum s):']
    lines += [f'  {cc:10d} {tt:8.2f} {ct:8.2f}  {os.path.basename(fn)}:{ln} {nm}' for (fn, ln, nm), (_, cc, tt, ct, _) in top]
    return '\n'.join(lines)


if __name__ == '__main__':
    kind, mode = sys.argv[1], sys.argv[2]
    tmp = tempfile.mkdtemp(prefix='native_profile_')
    t0 = time.perf_counter()
    if kind == 'captured':
        cap = float(sys.argv[3]) if len(sys.argv) > 3 else 1.0
        workers = int(sys.argv[4]) if len(sys.argv) > 4 else 11
        work = load_captured()
        chunks = [work[i::workers] for i in range(workers)]
        jobs = [(mode, cap, c, os.path.join(tmp, f'c{i}.prof')) for i, c in enumerate(chunks)]
        with Pool(workers) as p:
            res = sum(p.map(captured_chunk, jobs), Counter())
        header = f'captured queries ({len(work)}), mode {mode}, cap {cap}s: {dict(res)}'
        tag = f'captured_{mode}'
    else:
        excess = int(sys.argv[3]); seconds = float(sys.argv[4]) if len(sys.argv) > 4 else 30
        workers = int(sys.argv[5]) if len(sys.argv) > 5 else 11
        names = sorted({json.loads(l)['key'].split('|')[0] for l in open(os.path.join(HERE, 'results', 'excess3_ladder.jsonl'))
                        if json.loads(l)['key'].endswith('|free')})
        if len(sys.argv) > 6:
            names = [nm for nm in names if nm in set(sys.argv[6].split(','))]
        jobs = [(nm, mode, seconds, excess, os.path.join(tmp, f'{nm}.prof')) for nm in names]
        status = Counter()
        with Pool(workers, maxtasksperchild=1) as p:
            for nm, r in p.imap_unordered(layout_job, jobs):
                status[r['status']] += 1
                print(f"{nm:22} {r['status']} {r['result']} {r['seconds']}s", flush=True)
        header = f'layout excess {excess}, mode {mode}, {len(names)} cores, cap {seconds}s: {dict(status)}'
        tag = f'layout_{mode}_e{excess}'
    text = report([os.path.join(tmp, f) for f in os.listdir(tmp)], header, time.perf_counter() - t0)
    print(text, flush=True)
    with open(os.path.join(HERE, 'logs', f'native_profile_{tag}.txt'), 'w', encoding='utf-8') as fh:
        fh.write(text + '\n')
