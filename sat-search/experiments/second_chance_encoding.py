"""Second-chance screening: normalized signed-skeleton encoding (theory/phase_budget_cnf.py) versus the existing
direct counted-NOT encoding, on harder instances (6-9 inputs, several families), at-most-G total gates.

Instances: complete corpus targets with 6..8 essential inputs (budgets M-1 and M when the NOT-enabled minimum M
is known, else the best lower bound L, which is the hardest UNSAT-or-unknown budget), plus scaled families:
parity n = 4..7, thresholds T(n, k) n = 6..9, random nonmonotone n = 6..7 (budget = signed/first-gate total
lower bound and +1). One fresh process per solve (maxtasksperchild=1) so peak working set is per job;
maplechrono; time limit -> open. Witnesses decoded and checked on every row.
Writes results/second_chance_encoding.jsonl. Usage: python experiments/second_chance_encoding.py [workers] [seconds]"""
import ctypes, ctypes.wintypes, json, os, random, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))
from phase_budget_compare import baseline_cnf, solve
from phase_budget_cnf import encode, decode, evaluate
from signed_bound_compare import cases, restrict_essential
from signed_region_bounds import Bound
from first_gate_bound import lower as fg_lower


class PMC(ctypes.Structure):
    _fields_ = [('cb', ctypes.wintypes.DWORD), ('PageFaultCount', ctypes.wintypes.DWORD),
                ('PeakWorkingSetSize', ctypes.c_size_t), ('WorkingSetSize', ctypes.c_size_t),
                ('QuotaPeakPagedPoolUsage', ctypes.c_size_t), ('QuotaPagedPoolUsage', ctypes.c_size_t),
                ('QuotaPeakNonPagedPoolUsage', ctypes.c_size_t), ('QuotaNonPagedPoolUsage', ctypes.c_size_t),
                ('PagefileUsage', ctypes.c_size_t), ('PeakPagefileUsage', ctypes.c_size_t)]


def peak_bytes():
    c = PMC(); c.cb = ctypes.sizeof(PMC)
    ctypes.windll.psapi.GetProcessMemoryInfo(ctypes.windll.kernel32.GetCurrentProcess(), ctypes.byref(c), c.cb)
    return c.PeakWorkingSetSize


def job(args):
    name, fam, n, P, N, G, enc, seconds = args
    t0 = time.time()
    if enc == 'baseline':
        clauses, nv = baseline_cnf(n, P, N, G); meta = None
    else:
        c, meta = encode(n, G, G, P, N, atmost=True, total=G); clauses, nv = c.clauses, c.n
    build = time.time() - t0
    r, dt, conf, model, _ = solve(clauses, 'maplechrono', seconds)
    st = 'open' if r is None else 'SAT' if r else 'UNSAT'
    ok = None
    if st == 'SAT' and meta is not None:
        g, v = decode(n, meta, set(l for l in model if l > 0)); f = evaluate(n, g, v)
        ok = f & P == P and not f & N and len(g) <= G
    return dict(case=name, family=fam, n=n, G=G, encoding=enc, status=st, verified=ok, vars=nv, clauses=len(clauses),
                conflicts=conf, build_seconds=round(build, 2), solve_seconds=round(dt, 2),
                total_seconds=round(time.time() - t0, 2), peak_mb=round(peak_bytes() / 2 ** 20, 1))


def pair_job(args):
    """Early stopping: baseline first (full limit), then the phase encoding with limit
    max(10, 1.5 x baseline time); hitting that limit is recorded as 'stopped-worse'. If the baseline is
    open, the phase encoding gets the full limit."""
    name, fam, n, P, N, G, seconds = args
    b = job((name, fam, n, P, N, G, 'baseline', seconds))
    limit = seconds if b['status'] == 'open' else min(seconds, max(10.0, 1.5 * b['total_seconds']))
    ph = job((name, fam, n, P, N, G, 'phase', limit))
    if ph['status'] == 'open' and limit < seconds:
        ph['status'] = 'stopped-worse'
    ph['limit'] = round(limit, 1)
    return [b, ph]


def lower_total(n, f):
    b = Bound(n, f)
    return max(n - 1 + b.lower(), fg_lower(n, f, 1) if n <= 8 else 0) + b.not_lower()


if __name__ == '__main__':
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 18
    seconds = float(sys.argv[2]) if len(sys.argv) > 2 else 600
    iv = {json.loads(l)['case']: json.loads(l) for l in open(os.path.join(HERE, 'results', 'signed_bound_compare.jsonl'))}
    jobs = []

    def add(name, fam, n, f, budgets):
        P, N = f, ((1 << (1 << n)) - 1) & ~f
        for G in budgets:
            jobs.append((name, fam, n, P, N, G, seconds))
    for name, fam, n0, f0 in cases():
        n, f, _ = restrict_essential(n0, f0)
        if not 6 <= n <= 8:
            continue
        r = iv.get(name, {})
        lo = max(r.get('support', 0), r.get('existing') or 0, r.get('sat_lower') or 0, r.get('signed') or 0)
        hi = r.get('upper'); hi = None if hi in (None, 10 ** 9) else hi
        add(name, fam, n, f, (lo - 1, lo) if hi is not None and lo >= hi else (lo,))
    rng = random.Random(77)
    for n in range(4, 8):
        par = sum(1 << a for a in range(1 << n) if bin(a).count('1') % 2)
        L = lower_total(n, par); add(f'parity-{n}', 'parity', n, par, (L, L + 1))
    for n in range(6, 10):
        for k in (2, n // 2, n - 1):
            f = sum(1 << a for a in range(1 << n) if bin(a).count('1') >= k)
            L = lower_total(n, f) if n <= 8 else n - 1 + Bound(n, f).lower()
            add(f'threshold-{n}-{k}', 'threshold', n, f, (L,))
    for n in (6, 7):
        for i in range(3):
            while True:
                f = rng.getrandbits(1 << n)
                if all(any((f >> a & 1) != (f >> (a ^ 1 << j) & 1) for a in range(1 << n)) for j in range(n)):
                    break
            L = lower_total(n, f); add(f'random-{n}-{i}', 'random-nonmonotone', n, f, (L,))
    print(f'{len(jobs)} matched pairs, {workers} workers, {seconds}s baseline limit, phase early-stopped at 1.5x',
          flush=True)
    out = open(os.path.join(HERE, 'results', 'second_chance_encoding.jsonl'), 'w', encoding='utf-8')
    with Pool(workers, maxtasksperchild=1) as p:
        for k, (b, ph) in enumerate(p.imap_unordered(pair_job, jobs), 1):
            for r in (b, ph):
                out.write(json.dumps(r) + '\n')
            out.flush()
            print(f'[{k}/{len(jobs)}] {b["case"]} G={b["G"]}: baseline {b["status"]} {b["total_seconds"]}s '
                  f'c={b["conflicts"]} | phase {ph["status"]} {ph["total_seconds"]}s c={ph["conflicts"]} '
                  f'(limit {ph["limit"]}s)', flush=True)
    print('DONE', flush=True)
