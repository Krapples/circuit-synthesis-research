"""Unified exact-synthesis baseline harness: AIG size (= free-NOT binary AND/OR gate count, De Morgan).

Every tool call is a fresh (cold) process on this machine, under one wall-clock deadline per (target, tool) job that
covers the whole increasing-budget search, including process start-up and preprocessing. Peak working set is read from
the process handle (GetProcessMemoryInfo); for tools driven one budget per process (ABC) the job reports the maximum.
Every witness is re-simulated here against the target's care set; every gate must be AND-type (1 or 3 minterms).

Budgets start at the trivial lower bound L = (essential inputs) - 1 for every tool. Targets are first restricted to
their essential inputs (common preprocessing, identical for all tools). Trivial targets (constants, literals) are
size 0 and are not timed. Optimality = SAT at k with every budget L..k-1 decided UNSAT in the same job. ABC and Percy
fixed budgets mean "exactly k gates, all used"; minimum-size optimality from L upward is unaffected.

Tools / configs (see VERSIONS.md for exact commits and flags):
  percy-std-{bsat,satoko,bmcg}, percy-cegar-{bsat,satoko,bmcg}   SSV encoder, set_primitive(AIG) (percy_run.exe)
  abc-two, abc-two-g, abc-two-onu, abc-two-gonu    twoexact -a [-g] [-o -n -u] -I n -N k   (complete functions only)
  abc-all, abc-all-i                               allexact -a -K 2 [-i] -I n -N k        (complete functions only)
  cirbo-maplechrono, cirbo-cadical195              Cirbo CircuitFinderSat, 8 AND-type gates
  ours-sat                                         phase_budget_cnf free-NOT encoding (u = n + b), maplechrono
  ours-hybrid                                      production ladder + SAT on the core (complete functions only)
usage: python run_baselines.py <workload> <out.jsonl> [--tools t1,t2,...] [--deadline 60] [--workers 16] [--limit N]
workloads: npn4 | corpus | file:<path.jsonl with n, tt (hex), optional care (hex), name, family>"""
import ctypes, ctypes.wintypes, json, os, re, subprocess, sys, time
from multiprocessing import Pool
BASE = os.path.dirname(os.path.abspath(__file__))
HERE = os.path.dirname(BASE)
ROOT = os.path.dirname(HERE)
EXT = os.path.join(ROOT, 'external')
SCRATCH = os.environ.get('BASELINE_SCRATCH', os.path.join(EXT, 'scratch'))  # ABC writes .bool files to cwd
PERCY = os.path.join(EXT, 'percy-build', 'percy_run.exe')
ABC = os.path.join(EXT, 'abc-build', 'abc.exe')
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))

ALL_TOOLS = ['percy-std-bsat', 'percy-std-satoko', 'percy-std-bmcg', 'percy-cegar-bsat', 'percy-cegar-satoko',
             'percy-cegar-bmcg', 'abc-two', 'abc-two-g', 'abc-two-onu', 'abc-two-gonu', 'abc-all', 'abc-all-i',
             'cirbo-maplechrono', 'cirbo-cadical195', 'ours-sat', 'ours-hybrid']
COMPLETE_ONLY = ('abc-', 'ours-hybrid', 'hpercy-', 'mpercy-', 'hpercyr-', 'hpercyc-')
# hybrid-Percy (runners.py): our signed modules + lower bounds [+ ladder for hpercy], then percy_run.exe with the same
# method/solver as the matching standalone percy-<method>-<solver> tool. Not in ALL_TOOLS; select with --tools.


# ---------------------------------------------------------------- process control
class PMC(ctypes.Structure):
    _fields_ = [('cb', ctypes.wintypes.DWORD), ('PageFaultCount', ctypes.wintypes.DWORD),
                ('PeakWorkingSetSize', ctypes.c_size_t), ('WorkingSetSize', ctypes.c_size_t),
                ('QuotaPeakPagedPoolUsage', ctypes.c_size_t), ('QuotaPagedPoolUsage', ctypes.c_size_t),
                ('QuotaPeakNonPagedPoolUsage', ctypes.c_size_t), ('QuotaNonPagedPoolUsage', ctypes.c_size_t),
                ('PagefileUsage', ctypes.c_size_t), ('PeakPagefileUsage', ctypes.c_size_t)]


def peak_of(proc):
    c = PMC(); c.cb = ctypes.sizeof(PMC)
    ok = ctypes.windll.psapi.GetProcessMemoryInfo(ctypes.wintypes.HANDLE(int(proc._handle)), ctypes.byref(c), c.cb)
    return c.PeakWorkingSetSize if ok else None


def launch(cmd, seconds, cwd=None):
    """Run cmd; return (stdout, elapsed, peak_bytes, timed_out). Kills the process tree on timeout."""
    t0 = time.perf_counter()
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, cwd=cwd,
                         creationflags=subprocess.CREATE_NEW_PROCESS_GROUP)
    try:
        out, _ = p.communicate(timeout=max(0.01, seconds))
        timed_out = False
    except subprocess.TimeoutExpired:
        subprocess.run(['taskkill', '/F', '/T', '/PID', str(p.pid)], capture_output=True)
        out, _ = p.communicate()
        timed_out = True
    dt = time.perf_counter() - t0
    peak = peak_of(p)
    return out or '', dt, peak, timed_out


# ---------------------------------------------------------------- witness verification
def verify(n, tt, care, gates, out):
    """Simulate a common-format gate list on all assignments; True iff it matches tt on care and all gates AND-type."""
    full = (1 << (1 << n)) - 1
    vals = []
    for i in range(n):
        vals.append(sum(1 << a for a in range(1 << n) if a >> i & 1))
    for f4, a, b in gates:
        if bin(f4).count('1') not in (1, 3) or not (0 <= a < len(vals)) or not (0 <= b < len(vals)):
            return False
        x, y = vals[a], vals[b]
        v = 0
        for i in range(4):
            if f4 >> i & 1:
                v |= (x if i & 1 else full ^ x) & (y if i >> 1 else full ^ y)
        vals.append(v)
    node, inv = out
    v = vals[node] ^ (full if inv else 0)
    return (v ^ tt) & care == 0


def parse_percy_chain(n, rec):
    gates = [[op, a, b] for op, a, b in rec['chain']]      # Percy fanin ids: < n input, else step id - n -> node id
    var, inv = rec['out']
    return gates, [var - 1, inv]                            # var 0 = constant (not produced for non-trivial targets)


ABC_LINE = re.compile(r"^([A-Z]|\d+) = 4'b([01]{4})\( ([A-Za-z]|\d+) ([A-Za-z]|\d+) \)")


def parse_abc(n, text, second_major=False):
    """ABC realization lines. Inputs are letters a.. = x0..; twoexact names gates A.. (gate j = node n + j),
    allexact names gates by decimal node id. 4'bWXYZ lists outputs for operand index 3,2,1,0, where the index is
    2*first + second for twoexact and 2*second + first for allexact (checked on asymmetric functions)."""
    rows = [m.groups() for m in map(ABC_LINE.match, text.splitlines()) if m]
    if not rows:
        return None
    node = lambda c: (ord(c) - 97 if c.islower() else n + ord(c) - 65) if c.isalpha() else int(c)
    rows.sort(key=lambda r: node(r[0]))
    gates = []
    for name, bits, p, q in rows:
        if node(name) != n + len(gates):
            return None
        f4 = 0
        for i in range(4):
            va, vb = i & 1, i >> 1
            idx = 2 * vb + va if second_major else 2 * va + vb
            f4 |= int(bits[3 - idx]) << i
        gates.append([f4, node(p), node(q)])
    return gates, [n + len(gates) - 1, 0]


# ---------------------------------------------------------------- jobs
def hexstr(n, x):
    return format(x, f'0{max(1, (1 << n) // 4)}x')


def run_job(arg):
    tgt, tool, deadline = arg
    n, tt, care = tgt['n'], tgt['tt'], tgt['care']
    full = (1 << (1 << n)) - 1
    L = max(1, n - 1)
    rec = dict(name=tgt['name'], family=tgt.get('family'), n=n, tool=tool, deadline=deadline, start=L,
               partial=care != full, budgets=[], status='TIMEOUT', size=None, verified=None)
    if care != full and tool.startswith(COMPLETE_ONLY):
        rec['status'] = 'UNSUPPORTED'; return rec
    t0 = time.perf_counter(); peak = 0
    if tool.startswith('percy-'):
        _, method, solver = tool.split('-')
        cmd = [PERCY, '--n', str(n), '--tt', hexstr(n, tt), '--solver', solver, '--method', method, '--start', str(L)]
        if care != full:
            cmd += ['--dc', hexstr(n, full ^ care)]
        out, dt, pk, to = launch(cmd, deadline)
        peak = pk or 0
        for line in out.splitlines():
            if not line.startswith('{'):
                continue
            r = json.loads(line)
            if 'k' in r:
                rec['budgets'].append([r['k'], r['status'], r['seconds']])
            elif 'final' in r and r['final'] == 'SAT':
                g, o = parse_percy_chain(n, r)
                rec['verified'] = verify(n, tt, care, g, o) and r.get('aig', False)
                rec['size'] = len(g); rec['status'] = 'OPTIMAL'
    elif tool.startswith('abc-'):
        flags = {'abc-two': 'twoexact -a', 'abc-two-g': 'twoexact -a -g', 'abc-two-onu': 'twoexact -a -o -n -u',
                 'abc-two-gonu': 'twoexact -a -g -o -n -u', 'abc-all': 'allexact -a -K 2',
                 'abc-all-i': 'allexact -a -K 2 -i'}[tool]
        k = L
        while True:
            left = deadline - (time.perf_counter() - t0)
            if left <= 0:
                break
            out, dt, pk, to = launch([ABC, '-c', f'{flags} -I {n} -N {k} {hexstr(n, tt)}'], left, cwd=SCRATCH)
            peak = max(peak, pk or 0)
            if to:
                break
            parsed = parse_abc(n, out, second_major=tool.startswith('abc-all'))
            if parsed:
                rec['budgets'].append([k, 'SAT', round(dt, 6)])
                g, o = parsed
                rec['verified'] = verify(n, tt, care, g, o); rec['size'] = len(g); rec['status'] = 'OPTIMAL'
                break
            if 'has no solution' in out or 'cannot be implemented' in out:
                rec['budgets'].append([k, 'UNSAT', round(dt, 6)]); k += 1
                continue
            if 'Running exact synthesis' in out and 'Total runtime' in out:
                # ABC sometimes finishes a budget with neither a realization nor a "no solution" line (seen on
                # trivially infeasible encodings, e.g. XOR2 with 1 gate); counted as UNSAT and flagged.
                rec['budgets'].append([k, 'UNSAT', round(dt, 6)]); rec['silent_unsat'] = rec.get('silent_unsat', 0) + 1
                k += 1
                continue
            rec['status'] = 'ERROR'; rec['error'] = out[-400:]; break
    else:
        cmd = [sys.executable, os.path.join(BASE, 'runners.py'), tool, str(n), hexstr(n, tt),
               '-' if care == full else hexstr(n, care), str(L)]
        out, dt, pk, to = launch(cmd, deadline)
        peak = pk or 0
        for line in out.splitlines():
            if not line.startswith('{'):
                continue
            r = json.loads(line)
            if 'k' in r:
                rec['budgets'].append([r['k'], r['status'], r['seconds']])
            elif r.get('stage') == 'preprocessed':
                rec.update(core_n=r.get('core_n'), trace=r.get('trace'), bound=r.get('bound'), core_start=r.get('start'),
                           pre_seconds=r.get('pre_seconds'))
            elif 'final' in r:
                for key in ('pre_seconds', 'synth_seconds', 'core_n', 'trace', 'bound'):
                    if key in r:
                        rec[key] = r[key]
                if r['final'] == 'SAT':
                    rec['size'] = r['steps']; rec['status'] = 'OPTIMAL'; rec['stage'] = r.get('stage')
                    if r.get('gates') is not None:
                        rec['verified'] = verify(n, tt, care, r['gates'], r['out'])
                    elif r.get('core_gates') is not None:
                        m = r['core_n']; ct = int(r['core_tt'], 16)
                        rec['verified'] = verify(m, ct, (1 << (1 << m)) - 1, r['core_gates'], r['core_out'])
                        rec['verified_scope'] = 'core'
                    else:
                        rec['verified_scope'] = r.get('verified_scope')
        if 'Traceback' in out:
            rec['status'] = 'ERROR'; rec['error'] = out[-600:]
    rec['seconds'] = round(time.perf_counter() - t0, 4)
    rec['peak_mb'] = round(peak / 2 ** 20, 1)
    sats = [b for b in rec['budgets'] if b[1] == 'SAT']
    rec['first_witness_seconds'] = rec['seconds'] if sats else None
    if rec['status'] == 'OPTIMAL' and rec['verified'] is False:
        rec['status'] = 'WRONG'
    return rec


# ---------------------------------------------------------------- workloads
def essential_restrict(n, tt, care):
    keep = []
    for i in range(n):
        for a in range(1 << n):
            b = a | (1 << i)
            if not a >> i & 1 and care >> a & 1 and care >> b & 1 and (tt >> a & 1) != (tt >> b & 1):
                keep.append(i); break
    if len(keep) == n:
        return n, tt, care
    m = len(keep); t2 = c2 = 0
    for a in range(1 << m):
        full_a = sum(((a >> j) & 1) << i for j, i in enumerate(keep))
        # For partial functions, a dropped input may be non-essential only on the care set: pick any cared row.
        rows = [full_a | sum(((r >> j) & 1) << i for j, i in enumerate([i for i in range(n) if i not in keep]))
                for r in range(1 << (n - m))]
        cared = [r for r in rows if care >> r & 1]
        if cared:
            c2 |= 1 << a; t2 |= (tt >> cared[0] & 1) << a
    return m, t2, c2


def npn4_classes():
    from itertools import permutations
    maps = []
    for perm in permutations(range(4)):
        for neg in range(16):
            maps.append([sum((((a >> perm[i]) & 1) ^ (neg >> i & 1)) << i for i in range(4)) for a in range(16)])
    seen = set(); reps = []
    for f in range(1 << 16):
        if f in seen:
            continue
        orbit = set()
        for mp in maps:
            g = sum(((f >> mp[a]) & 1) << a for a in range(16))
            orbit.add(g); orbit.add(g ^ 0xffff)
        seen |= orbit; reps.append(min(orbit))
    return reps


def targets(workload, limit=None):
    T = []
    if workload == 'npn4':
        for i, f in enumerate(npn4_classes()):
            n, tt, care = essential_restrict(4, f, 0xffff)
            T.append(dict(name=f'npn4-{f:04x}', family='npn4', n_orig=4, n=n, tt=tt, care=care))
    elif workload == 'corpus':
        from signed_bound_compare import cases, restrict_essential
        for name, fam, n0, f0 in cases():
            n, f, _ = restrict_essential(n0, f0)
            T.append(dict(name=name, family=fam, n_orig=n0, n=n, tt=f, care=(1 << (1 << n)) - 1))
    elif workload.startswith('file:'):
        for line in open(workload[5:], encoding='utf-8'):
            r = json.loads(line); n0 = r['n']; tt = int(r['tt'], 16)
            care = int(r['care'], 16) if r.get('care') else (1 << (1 << n0)) - 1
            n, tt, care = essential_restrict(n0, tt, care)
            T.append(dict(name=r['name'], family=r.get('family'), n_orig=n0, n=n, tt=tt, care=care))
    return T[:limit] if limit else T


if __name__ == '__main__':
    args = sys.argv[1:]
    workload, outp = args[0], args[1]
    opt = dict(zip(args[2::2], args[3::2]))
    tools = opt.get('--tools', ','.join(ALL_TOOLS)).split(',')
    deadline = float(opt.get('--deadline', 60)); workers = int(opt.get('--workers', 16))
    T = targets(workload, int(opt['--limit']) if '--limit' in opt else None)
    trivial = [t for t in T if t['n'] <= 1]
    jobs = [(t, tool, deadline) for t in T if t['n'] > 1 for tool in tools]
    print(f'{len(T)} targets ({len(trivial)} trivial, not timed), {len(jobs)} jobs, {workers} workers, '
          f'deadline {deadline}s', flush=True)
    os.makedirs(SCRATCH, exist_ok=True)
    out = open(outp, 'w', encoding='utf-8')
    for t in trivial:
        out.write(json.dumps(dict(name=t['name'], family=t['family'], n=t['n'], tool='*', status='TRIVIAL', size=0)) + '\n')
    done = 0
    with Pool(workers) as p:
        for r in p.imap_unordered(run_job, jobs):
            out.write(json.dumps(r) + '\n'); out.flush(); done += 1
            if r['status'] in ('WRONG', 'ERROR'):
                print('!!!', r['name'], r['tool'], r['status'], r.get('error', '')[:300], flush=True)
            if done % 50 == 0 or done == len(jobs):
                print(f'[{done}/{len(jobs)}]', flush=True)
    print('DONE', flush=True)
