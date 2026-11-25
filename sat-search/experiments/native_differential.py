"""Differential test and matched timing: native regional kernel (theory/regional_native.py) vs the Python reference.

  captured [workers] [cap] [output]   1443 captured signed queries (547 held-out + 896 dev).  Per query, each under its own
                             regional_deadline.timed cap:  production local_blocks (row-quotient flags) signed and
                             monotone-relabelled (signed=False), and the phase-first adaptive completion, Python vs
                             native.  Decided pairs must agree on verdict, on every search counter (rec, cover_nodes,
                             port_allocations, partition_checks, ...), and on the witness tree itself (same search
                             order); witnesses are checked by regional_production_adapter.check_tree.
  random [n] [workers]       random multislice queries with an independent formula-column oracle (as
                             regional_completion_check.test_independent_multislice_oracle, different seed).
  deadline                   a native call interrupted by regional_deadline.timed returns TIMEOUT, never UNSAT.
  layout <excess> <seconds> <base_mode> <native_mode> [workers] [subset] [output]
                             end-to-end free-NOT search (excess 3: solve3, else layout_projection.search_exact) on the
                             48 corpus cores, as experiments/phase_first_layout.py: every solve in a fresh process,
                             base first, native capped at min(seconds, max(10, 1.5 x base)) (early stop); decisions
                             must agree, witnesses rebuilt and checked.  Records wall time, peak working set, import
                             time and completion counters.
  startup                    interpreter start-up / import overhead and per-call overhead of the native module.
  percy <output>             serial cold Percy CLI timing, including process startup and JSON output.
Writes results/native_differential_<kind>.jsonl and prints a summary.  Reports per-worker peak working set."""
import ctypes, json, os, sys, time
from collections import Counter
from multiprocessing import Pool
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))
FLAGS = dict(port_first=True, witness_cover=True, row_quotient=True)


def peak_working_set_mb():
    from ctypes import wintypes
    class PMC(ctypes.Structure):
        _fields_ = [('cb', ctypes.c_ulong), ('PageFaultCount', ctypes.c_ulong), ('PeakWorkingSetSize', ctypes.c_size_t),
                    ('WorkingSetSize', ctypes.c_size_t), ('QuotaPeakPagedPoolUsage', ctypes.c_size_t),
                    ('QuotaPagedPoolUsage', ctypes.c_size_t), ('QuotaPeakNonPagedPoolUsage', ctypes.c_size_t),
                    ('QuotaNonPagedPoolUsage', ctypes.c_size_t), ('PagefileUsage', ctypes.c_size_t),
                    ('PeakPagefileUsage', ctypes.c_size_t)]
    c = PMC(); c.cb = ctypes.sizeof(PMC)
    k32 = ctypes.WinDLL('kernel32'); psapi = ctypes.WinDLL('psapi')
    k32.GetCurrentProcess.restype = wintypes.HANDLE
    psapi.GetProcessMemoryInfo.argtypes = (wintypes.HANDLE, ctypes.POINTER(PMC), wintypes.DWORD)
    psapi.GetProcessMemoryInfo(k32.GetCurrentProcess(), ctypes.byref(c), c.cb)
    return c.PeakWorkingSetSize / 2**20


def run(fn, cap):
    from regional_deadline import timed
    st = Counter(); t0 = time.perf_counter()
    r = timed(cap, lambda: {'status': 'done', 'w': fn(st)}, lambda: {})
    dt = time.perf_counter() - t0
    if r['status'] == 'TIMEOUT':
        return 'timeout', None, dt, st
    return ('sat' if r['w'] is not None else 'unsat'), r['w'], dt, st


def compare(name, py, nat, check, out, agg):
    ps, pw, pt, pst = py
    ns, nw, nt, nst = nat
    rec = dict(py=ps, native=ns, py_s=round(pt, 5), native_s=round(nt, 5), rec_py=pst.get('rec', 0), rec_native=nst.get('rec', 0))
    agg[name, 'py', ps] += 1; agg[name, 'native', ns] += 1
    if ps != 'timeout' and ns != 'timeout':
        assert ps == ns, (name, ps, ns)
        same_stats = {k: v for k, v in pst.items() if v} == {k: v for k, v in nst.items() if v}
        rec['same_stats'] = same_stats; rec['same_tree'] = pw == nw
        agg[name, 'both'] += 1; agg[name, 'same_stats'] += same_stats; agg[name, 'same_tree'] += pw == nw
        agg[name, 'py_s'] += pt; agg[name, 'native_s'] += nt
        for k in ('rec', 'cover_nodes', 'port_allocations', 'partition_checks'):
            agg[name, 'py_' + k] += pst.get(k, 0); agg[name, 'native_' + k] += nst.get(k, 0)
        assert same_stats and pw == nw, (name, out, pst, nst, pw, nw)
    if nw is not None:
        check(nw)
    if pw is not None:
        check(pw)
    out[name] = rec


def captured_job(a):
    src, idx, q, cap = a
    from regional_block_completion import local_blocks
    from regional_native import (completion_native, local_blocks_native, native_adaptive_completion, native_prelude,
                                 prelude)
    from regional_phase_first import adaptive_completion
    from regional_production_adapter import check_tree
    m, ports, pats, targets = q[0], tuple(q[1]), tuple(q[2]), tuple(q[3])
    out = dict(source=src, idx=idx, m=m, ports=len(ports), rows=len(pats)); agg = Counter()
    for signed in (True, False):
        assert prelude(m, targets, signed) == native_prelude(m, targets, signed), (m, targets, signed)
        agg['prelude_equal'] += 1
    for signed in (True, False):
        name = 'blocks_signed' if signed else 'blocks_mono'
        py = run(lambda st: local_blocks(m, ports, pats, targets, signed, st, True, **FLAGS), cap)
        nat = run(lambda st: local_blocks_native(m, ports, pats, targets, signed, st, True), cap)
        compare(name, py, nat, lambda w: check_tree(w, m, ports, pats, targets, signed), out, agg)
        if signed:   # stage B, plain local_blocks: same Python run, full native call
            nat = run(lambda st: completion_native(m, ports, pats, targets, True, st, True, adaptive=False), cap)
            compare('b_blocks_signed', py, nat, lambda w: check_tree(w, m, ports, pats, targets, True), out, agg)
    py = run(lambda st: adaptive_completion(m, ports, pats, targets, True, st, True), cap)
    nat = run(lambda st: native_adaptive_completion(m, ports, pats, targets, True, st, True), cap)
    compare('phase_first', py, nat, lambda w: check_tree(w, m, ports, pats, targets, True), out, agg)
    nat = run(lambda st: completion_native(m, ports, pats, targets, True, st, True, adaptive=True), cap)
    compare('b_phase_first', py, nat, lambda w: check_tree(w, m, ports, pats, targets, True), out, agg)
    out['peak_mb'] = round(peak_working_set_mb(), 1)
    return out, agg


def random_job(a):
    seed, count = a
    from random import Random
    from conditional_provider import formula_columns
    from module_contraction import vars as truth_variables
    from regional_block_completion import local_blocks
    from regional_native import (completion_native, local_blocks_native, native_adaptive_completion, native_prelude,
                                 prelude)
    from regional_phase_first import adaptive_completion
    from regional_production_adapter import check_tree
    from two_sharing_core import ANY
    rng = Random(seed); agg = Counter()
    for _ in range(count):
        m = rng.randrange(4)
        q = rng.randrange(max(1, 2 - m), 6 - min(m, 2))
        signed = bool(rng.randrange(2))
        ports = tuple(rng.randrange(min(q, 3)) * 2 + 1 for _ in range(q))
        providers = tuple(sorted(set(ports)))
        pats = tuple(sum((mask >> j & 1) << i for j, i in enumerate(providers))
                     for mask in range(1 << len(providers)) if rng.random() < .65) or (0,)
        width = 1 << m; ones = (1 << width) - 1; total = (1 << (len(pats) * width)) - 1
        columns = tuple(sum(v << (j * width) for j in range(len(pats))) for v in truth_variables(m))
        columns += tuple(sum((ones if p >> i & 1 else 0) << (j * width) for j, p in enumerate(pats)) for i in ports)
        known = formula_columns(tuple(sorted(columns)), total, signed)
        for target in (rng.choice(sorted(known)), rng.randrange(total + 1)):
            values = tuple((target >> (j * width)) & ones if rng.random() < .8 else ANY for j in range(len(pats)))
            expected = any(all(v == ANY or t >> (j * width) & ones == v for j, v in enumerate(values)) for t in known)
            sp, sn = Counter(), Counter()
            wp = local_blocks(m, ports, pats, values, signed, sp, True, **FLAGS)
            wn = local_blocks_native(m, ports, pats, values, signed, sn, True)
            assert (wn is not None) == expected == (wp is not None), (m, ports, pats, values, signed)
            assert wn == wp and {k: v for k, v in sp.items() if v} == {k: v for k, v in sn.items() if v}
            if wn is not None:
                check_tree(wn, m, ports, pats, values, signed)
            assert prelude(m, values, signed) == native_prelude(m, values, signed)
            sb = Counter()
            wb = completion_native(m, ports, pats, values, signed, sb, True, adaptive=False)
            assert wb == wp and {k: v for k, v in sp.items() if v} == {k: v for k, v in sb.items() if v}
            if signed:
                sa, sn2, sb2 = Counter(), Counter(), Counter()
                wa = adaptive_completion(m, ports, pats, values, True, sa, True)
                wn2 = native_adaptive_completion(m, ports, pats, values, True, sn2, True)
                wb2 = completion_native(m, ports, pats, values, True, sb2, True, adaptive=True)
                assert (wa is not None) == expected and wa == wn2 == wb2
                assert {k: v for k, v in sa.items() if v} == {k: v for k, v in sn2.items() if v}                     == {k: v for k, v in sb2.items() if v}, (sa, sn2, sb2)
                if wa is not None:
                    check_tree(wa, m, ports, pats, values, True)
            agg['queries'] += 1; agg['feasible'] += expected; agg['m%d' % m] += 1
    return agg


def layout_job(a):
    name, mode, seconds, excess = a
    t_import = time.perf_counter()
    from module_contraction import simplify
    from signed_bound_compare import cases, restrict_essential
    from ordered_quotient_core import make_completion, solve3, materialize3, reconstruct
    from layout_projection import search_exact
    from regional_deadline import timed
    comp = make_completion(mode)
    t_import = time.perf_counter() - t_import
    fr = {nm: (n, f) for nm, _, n, f in cases()}
    n, f, _ = restrict_essential(*fr[name]); m, core, _ = simplify(n, f, True)
    st = Counter()

    def job():
        if excess == 3:
            r = solve3(m, core, True, st, completion=comp)
            if r is not None:
                materialize3(m, core, r, True)
            return {'status': 'done', 'result': None if r is None else r[0]}
        r = search_exact(m, core, excess, True, st, completion=comp)
        if r is not None:
            reconstruct(m, core, *r, excess)              # asserts truth table and gate count
        return {'status': 'done', 'result': None if r is None else 'witness'}
    t0 = time.perf_counter(); r = timed(seconds, job, lambda: {})
    met = comp.metrics()
    keep = ('rec', 'cover_nodes', 'partition_checks', 'port_allocations', 'monotone_calls', 'phase_first_calls', 'local')
    return name, mode, dict(status=r['status'], result=r.get('result'), seconds=round(time.perf_counter() - t0, 3),
                            core_n=m, import_s=round(t_import, 3), peak_mb=round(peak_working_set_mb(), 1),
                            cache_misses=met.get('cache_misses', 0), queries=met.get('queries', 0),
                            **{k: met.get(k, 0) for k in keep})


def layout(excess, seconds, base_mode, native_mode, workers, subset, output=None):
    names = sorted({json.loads(l)['key'].split('|')[0] for l in open(os.path.join(HERE, 'results', 'excess3_ladder.jsonl'))
                    if json.loads(l)['key'].endswith('|free')})
    if subset:
        names = [nm for nm in names if nm in set(subset.split(','))]
    tag = f'native_layout_e{excess}_{native_mode}' + ('_subset' if subset else '')
    out = open(output or os.path.join(HERE, 'results', tag + '.jsonl'), 'x', encoding='utf-8')
    t0 = time.perf_counter()
    with Pool(workers, maxtasksperchild=1) as p:
        base = {}
        for nm, _, r in p.imap_unordered(layout_job, [(nm, base_mode, seconds, excess) for nm in names]):
            base[nm] = r
            print(f"base {nm:22} {r['status']} {r['result']} {r['seconds']}s peak {r['peak_mb']}MB [{time.perf_counter() - t0:.0f}s]", flush=True)
        caps = {nm: seconds if base[nm]['status'] == 'TIMEOUT' else min(seconds, max(10.0, 1.5 * base[nm]['seconds']))
                for nm in names}
        nat = {}
        for nm, _, r in p.imap_unordered(layout_job, [(nm, native_mode, caps[nm], excess) for nm in names]):
            nat[nm] = r
            print(f"native {nm:22} {r['status']} {r['result']} {r['seconds']}s peak {r['peak_mb']}MB [{time.perf_counter() - t0:.0f}s]", flush=True)
    agg = Counter()
    for nm in names:
        b, c = base[nm], nat[nm]
        if c['status'] == 'TIMEOUT' and caps[nm] < seconds:
            c['status'] = 'stopped-worse'
        agg['base_' + b['status']] += 1; agg['native_' + c['status']] += 1
        if b['status'] == c['status'] == 'done':
            assert (b['result'] is None) == (c['result'] is None), (nm, b, c)
            agg['both'] += 1; agg['base_s'] += b['seconds']; agg['native_s'] += c['seconds']
            for k in ('rec', 'cover_nodes', 'partition_checks', 'monotone_calls', 'cache_misses'):
                agg['base_' + k] += b[k]; agg['native_' + k] += c[k]
        agg['base_peak'] = max(agg['base_peak'], b['peak_mb']); agg['native_peak'] = max(agg['native_peak'], c['peak_mb'])
        agg['base_import'] += b['import_s']; agg['native_import'] += c['import_s']
        out.write(json.dumps(dict(case=nm, base=b, native=c, cap=round(caps[nm], 1))) + '\n')
    print(f"DONE excess {excess} cap {seconds}s {base_mode} vs {native_mode}: {dict(agg)}", flush=True)
    if agg['both']:
        print(f"both decided {agg['both']}: base {agg['base_s']:.2f}s native {agg['native_s']:.2f}s "
              f"({agg['base_s'] / max(agg['native_s'], 1e-9):.1f}x); rec {agg['base_rec']} vs {agg['native_rec']}", flush=True)


def startup():
    import subprocess
    py = sys.executable

    def wall(code, reps=5):
        best = 1e9
        for _ in range(reps):
            t = time.perf_counter(); subprocess.run([py, '-c', code], check=True, cwd=HERE)
            best = min(best, time.perf_counter() - t)
        return best
    path = "import sys; sys.path[:0]=['theory','experiments']; import ordered_quotient_core as o; "
    print(f"bare interpreter: {wall('pass'):.3f}s", flush=True)
    print(f"import ordered_quotient_core + make_completion('phase-first'): {wall(path + 'o.make_completion(\"phase-first\")'):.3f}s", flush=True)
    print(f"import ordered_quotient_core + make_completion('native-phase-first'): {wall(path + 'o.make_completion(\"native-phase-first\")'):.3f}s", flush=True)
    print(f"import _regional_native alone: {wall('import sys; sys.path.insert(0, \"native\"); import _regional_native'):.3f}s", flush=True)
    from regional_native import completion_native
    from regional_block_completion import local_blocks
    q = (1, (0, 0), (0, 1), (0, 1), True)
    for name, fn in (('native', lambda: completion_native(*q, adaptive=False)),
                     ('python', lambda: local_blocks(*q, port_first=True, witness_cover=True, row_quotient=True))):
        t = time.perf_counter()
        for _ in range(20000):
            fn()
        print(f"per-call cost, trivial query (m=1, two occurrences of one provider), {name}: "
              f"{(time.perf_counter() - t) / 20000 * 1e6:.1f} us", flush=True)


def percy_startup(output):
    import subprocess
    from statistics import median

    sys.path.insert(0, os.path.join(HERE, 'baselines'))
    from run_baselines import PERCY, parse_percy_chain, peak_of, verify

    with open(output, 'x', encoding='utf-8') as out:
        for n, tt in ((2, '8'), (4, '6996'), (4, '8ff0'), (5, '80000000')):
            cmd = [PERCY, '--n', str(n), '--tt', tt, '--solver', 'satoko', '--method', 'cegar', '--start', '1']
            overheads = []
            for trial in range(7):
                started = time.perf_counter()
                with subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True) as child:
                    try:
                        stdout, _ = child.communicate(timeout=5)
                    except subprocess.TimeoutExpired:
                        child.kill()
                        child.communicate()
                        raise
                    wall = time.perf_counter() - started
                    peak = peak_of(child)
                    assert child.returncode == 0, (cmd, stdout)
                records = [json.loads(line) for line in stdout.splitlines() if line.startswith('{')]
                final = records[-1]
                assert final['final'] == 'SAT' and final['aig']
                gates, root = parse_percy_chain(n, final)
                assert len(gates) == final['steps'] and verify(n, int(tt, 16), (1 << (1 << n)) - 1, gates, root)
                overheads.append(wall - final['seconds'])
                out.write(json.dumps(dict(n=n, tt=tt, trial=trial, wall_seconds=wall, peak_bytes=peak,
                                          records=records, witness_verified=True)) + '\n')
                out.flush()
            print(f'Percy n={n} tt={tt} steps={final["steps"]}: median outside timed search {median(overheads):.4f}s',
                  flush=True)


def deadline_check():
    from random import Random
    from regional_deadline import timed
    from regional_native import completion_native, local_blocks_native
    best = None
    for l in open(os.path.join(HERE, 'results', 'phase_first_captured.jsonl')):
        for q in json.loads(l)['queries']:
            m, ports, pats, targets = q[0], tuple(q[1]), tuple(q[2]), tuple(q[3])
            t0 = time.perf_counter(); local_blocks_native(m, ports, pats, targets, True); dt = time.perf_counter() - t0
            if best is None or dt > best[0]:
                best = (dt, m, ports, pats, targets)
    dt, m, ports, pats, targets = best
    cap = dt / 20
    r = timed(cap, lambda: {'status': 'done', 'w': local_blocks_native(m, ports, pats, targets, True)}, lambda: {})
    print(f'slowest captured native query {dt:.3f}s; under timed({cap:.4f}s): {r["status"]}', flush=True)
    assert r['status'] == 'TIMEOUT'
    r = timed(10 * dt + 1, lambda: {'status': 'done', 'w': local_blocks_native(m, ports, pats, targets, True)}, lambda: {})
    assert r['status'] == 'done'
    # 4,096 labels activate phase-first. The random slices make the clause
    # build expensive, before any monotone query is attempted.
    rng = Random(91000)
    q = (8, (0, 0, 1, 2, 3), tuple(range(16)), tuple(rng.getrandbits(256) for _ in range(16)), True)
    st = Counter()
    started = time.perf_counter()
    r = timed(0.005, lambda: {'status': 'done', 'w': completion_native(*q, st)}, lambda: {})
    elapsed = time.perf_counter() - started
    print(f'phase clause build under timed(0.005s): {r["status"]} in {elapsed:.3f}s', flush=True)
    assert r['status'] == 'TIMEOUT' and not st['monotone_calls'] and elapsed < 0.25, (r, st, elapsed)
    print('deadline check passed', flush=True)


if __name__ == '__main__':
    kind = sys.argv[1]
    if kind == 'deadline':
        deadline_check(); sys.exit()
    if kind == 'startup':
        startup(); sys.exit()
    if kind == 'percy':
        percy_startup(sys.argv[2]); sys.exit()
    if kind == 'layout':
        layout(int(sys.argv[2]), float(sys.argv[3]), sys.argv[4], sys.argv[5],
               int(sys.argv[6]) if len(sys.argv) > 6 else 11, sys.argv[7] if len(sys.argv) > 7 else '',
               sys.argv[8] if len(sys.argv) > 8 else None)
        sys.exit()
    if kind == 'random':
        n = int(sys.argv[2]) if len(sys.argv) > 2 else 2000; workers = int(sys.argv[3]) if len(sys.argv) > 3 else 11
        per = -(-n // (2 * workers))
        with Pool(workers) as p:
            agg = sum(p.map(random_job, [(91000 + i, per) for i in range(workers)]), Counter())
        print('random oracle', dict(agg), flush=True); sys.exit()
    workers = int(sys.argv[2]) if len(sys.argv) > 2 else 11
    cap = float(sys.argv[3]) if len(sys.argv) > 3 else 2.0
    W = []
    for fn, tag in (('phase_first_captured_heldout.jsonl', 'heldout'), ('phase_first_captured.jsonl', 'dev')):
        for l in open(os.path.join(HERE, 'results', fn)):
            r = json.loads(l)
            W += [(tag, f"{r['case']}:{r['kind']}:{i}", q, cap) for i, q in enumerate(r['queries'])]
    output = sys.argv[4] if len(sys.argv) > 4 else os.path.join(HERE, 'results', 'native_differential_captured.jsonl')
    out = open(output, 'x', encoding='utf-8')
    agg = Counter(); peak = 0.0; done = 0; t0 = time.perf_counter()
    with Pool(workers) as p:
        for r, a in p.imap_unordered(captured_job, W, chunksize=4):
            out.write(json.dumps(r) + '\n'); agg.update(a); peak = max(peak, r['peak_mb']); done += 1
            if done % 200 == 0:
                print(f'{done}/{len(W)} {time.perf_counter() - t0:.0f}s', flush=True)
    print('prelude equal (Python vs native)', agg['prelude_equal'], flush=True)
    for name in ('blocks_signed', 'blocks_mono', 'b_blocks_signed', 'phase_first', 'b_phase_first'):
        dec = {side: {s: agg[name, side, s] for s in ('sat', 'unsat', 'timeout')} for side in ('py', 'native')}
        both = agg[name, 'both']
        print(f"{name}: py {dec['py']} native {dec['native']} | both decided {both}: same stats {agg[name, 'same_stats']}, "
              f"same tree {agg[name, 'same_tree']}; time py {agg[name, 'py_s']:.2f}s native {agg[name, 'native_s']:.2f}s "
              f"({agg[name, 'py_s'] / max(agg[name, 'native_s'], 1e-9):.1f}x); rec py {agg[name, 'py_rec']} native "
              f"{agg[name, 'native_rec']}, cover {agg[name, 'py_cover_nodes']}/{agg[name, 'native_cover_nodes']}, "
              f"partitions {agg[name, 'py_partition_checks']}/{agg[name, 'native_partition_checks']}", flush=True)
    print(f'max worker peak working set {peak:.0f} MB', flush=True)
