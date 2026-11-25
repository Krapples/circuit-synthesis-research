"""Python-side solvers for the external-baseline harness (run_baselines.py). Each runs in its own process, decides
budgets k = start, start+1, ... in the free-NOT AND/OR basis (= AIG node count), and prints one JSON line per budget
plus a final JSON line with a witness in the common gate format (see run_baselines.verify):
    gates = [[f4, a, b], ...]   node ids: 0..n-1 inputs, n+j gate j; f4 bit (va | vb << 1) = gate output
    out   = [node, inv]
usage: python runners.py <tool> <n> <tt_hex> <care_hex|-> <start> [max]
tools: cirbo-maplechrono, cirbo-cadical195   (Cirbo CircuitFinderSat, 8 AND-type binary gates, fixed budget per k)
       ours-sat      theory/phase_budget_cnf.encode(n, b, u = n + b, ...) (unbounded inverters = free NOT), maplechrono
       ours-hybrid   production ladder: signed module reduction -> one-sharing -> two-sharing -> solve3 (excess <= 3,
                     completion 'phase-first'), then ours-sat on the core from excess 4 (complete functions only)"""
import json, os, sys, time
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOT = os.path.dirname(HERE)
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))
sys.path.append(os.path.join(ROOT, '.scratch-sat'))

T0 = time.perf_counter()


def emit(**kw):
    print(json.dumps(kw), flush=True)


def AND_TYPE(f4):
    return bin(f4).count('1') in (1, 3)


# ---------------------------------------------------------------- Cirbo
def run_cirbo(solver, n, tt, care, start, kmax):
    sys.path[:0] = [os.path.join(ROOT, 'external', 'cirbo'), os.path.join(ROOT, 'external', 'cirbo-env')]
    from cirbo.core.truth_table import TruthTableModel
    from cirbo.synthesis.circuit_search import CircuitFinderSat, Operation
    from cirbo.synthesis.exception import NoSolutionError
    B = [Operation.and_, Operation.or_, Operation.nand_, Operation.nor_, Operation.gt_, Operation.lt_, Operation.geq_,
         Operation.leq_]
    # Cirbo row r assigns input j the bit (n-1-j) of r (MSB first); row r is our assignment with x_j = that bit.
    rows = []
    for r in range(1 << n):
        a = sum(((r >> (n - 1 - j)) & 1) << j for j in range(n))          # our assignment index
        rows.append('*' if not care >> a & 1 else '1' if tt >> a & 1 else '0')
    model = TruthTableModel([rows])
    for k in range(start, kmax + 1):
        t = time.perf_counter()
        try:
            c = CircuitFinderSat(model, k, basis=B).find_circuit(solver)
        except NoSolutionError:
            emit(k=k, status='UNSAT', seconds=round(time.perf_counter() - t, 6)); continue
        emit(k=k, status='SAT', seconds=round(time.perf_counter() - t, 6))
        ids = {}
        for j, name in enumerate(c.inputs):
            ids[name] = j          # rows were passed in Cirbo's MSB-first order, so Cirbo input j is our x_j
        gates = []
        for name in c.gates:
            g = c.get_gate(name)
            if g.gate_type.name == 'INPUT':
                continue
            if len(g.operands) != 2:
                raise RuntimeError(f'unexpected gate {g}')
            a, b = (ids[o] for o in g.operands)
            f4 = sum(int(bool(g.gate_type.operator(bool(i & 1), bool(i >> 1)))) << i for i in range(4))
            ids[name] = n + len(gates); gates.append([f4, a, b])
        emit(final='SAT', steps=k, seconds=round(time.perf_counter() - T0, 6), gates=gates, out=[ids[c.outputs[0]], 0])
        return
    emit(final='UNSAT', steps=-1, seconds=round(time.perf_counter() - T0, 6))


# ---------------------------------------------------------------- ours: signed-skeleton SAT with free NOTs
def free_not_sat(n, P, N, b, seconds=None):
    """Decide 'exactly b binary gates, free NOTs' with phase_budget_cnf; returns (status, gates, out) in common format."""
    from phase_budget_cnf import encode, decode
    from pysat.solvers import Solver
    c, meta = encode(n, b, n + b, P, N)
    with Solver(name='maplechrono', bootstrap_with=c.clauses) as s:
        if not s.solve():
            return 'UNSAT', None, None
        model = set(l for l in s.get_model() if l > 0)
    circ, out = decode(n, meta, model)
    lit = {i: (i, 0) for i in range(n)}; gates = []           # wire -> (node, inv)
    for w, g in enumerate(circ, n):
        if g[0] == 'NOT':
            node, inv = lit[g[1]]; lit[w] = (node, inv ^ 1)
            continue
        op, x, y = g
        (na, ia), (nb, ib) = lit[x], lit[y]
        f4 = 0
        for i in range(4):
            va, vb = (i & 1) ^ ia, (i >> 1) ^ ib
            f4 |= (va & vb if op == 'AND' else va | vb) << i
        lit[w] = (n + len(gates), 0); gates.append([f4, na, nb])
    return 'SAT', gates, list(lit[out])


def run_ours_sat(n, tt, care, start, kmax, offset=0):
    P, N = tt & care, care & ~tt
    for k in range(max(start, 1), kmax + 1):
        t = time.perf_counter()
        st, gates, out = free_not_sat(n, P, N, k)
        emit(k=k + offset, status=st, seconds=round(time.perf_counter() - t, 6))
        if st == 'SAT':
            return k, gates, out
    return None, None, None


def run_hybrid(n, tt, care, start, kmax):
    full = (1 << (1 << n)) - 1
    if care != full:
        raise SystemExit('ours-hybrid: complete functions only')
    from module_contraction import simplify
    from one_sharing_core import solve_core
    from two_sharing_core import solve as solve2
    from ordered_quotient_core import solve3, make_completion
    m, core, tr = simplify(n, tt, True)
    stage = None
    if m <= 1:
        best, stage = len(tr), 'trivial-core'
    else:
        one = solve_core(m, core, True, False)
        if one is not None:
            best, stage = one[0] + len(tr), 'one-sharing'
        elif solve2(m, core, True) is not None:
            best, stage = m + 1 + len(tr), 'two-sharing'
        elif solve3(m, core, True, completion=make_completion('phase-first')) is not None:
            best, stage = m + 2 + len(tr), 'solve3'
        else:
            emit(stage='ladder-exhausted', core_n=m, trace=len(tr), seconds=round(time.perf_counter() - T0, 6))
            k, gates, out = run_ours_sat(m, core, (1 << (1 << m)) - 1, m + 3, kmax - len(tr), offset=len(tr))
            best = None if k is None else k + len(tr)
            stage = 'sat-on-core'
            emit(final='SAT' if best is not None else 'UNSAT', steps=-1 if best is None else best, stage=stage,
                 core_n=m, trace=len(tr), verified_scope='core', core_tt=hex(core), core_gates=gates, core_out=out,
                 seconds=round(time.perf_counter() - T0, 6))
            return
    # Ladder witnesses are rebuilt and asserted inside the ladder (reconstruct / materialize3); scope is internal.
    emit(final='SAT', steps=best, stage=stage, core_n=m, trace=len(tr), verified_scope='internal',
         seconds=round(time.perf_counter() - T0, 6))


# ---------------------------------------------------------------- hybrid-Percy: our preprocessing, Percy on the core
PERCY = os.path.join(ROOT, 'external', 'percy-build', 'percy_run.exe')


def core_lower_bound(m, core):
    """Proved lower bound on the free-NOT binary gate count (= AIG size) of a complete essential core:
    max(n - 1, signed regional bound n - 1 + Bound.lower(), free-NOT first-gate bound (mode 1, n <= 9))."""
    from signed_region_bounds import Bound
    lb = max(m - 1, m - 1 + Bound(m, core).lower())
    if m <= 9:
        from first_gate_bound import lower as fg_lower
        lb = max(lb, fg_lower(m, core, 1))
    return lb


def cofactor_bounds(m, core):
    """Per input: sound free-NOT lower bounds of both cofactors and whether each cofactor is nonconstant
    (input for the minimum-preserving reader caps, theory/primary_reader_caps.py)."""
    from module_contraction import cofactor1
    from ssv_aig import sound_lower
    full = (1 << (1 << (m - 1))) - 1; out = []
    for i in range(m):
        g = [cofactor1(m, core, i, a) for a in (0, 1)]
        out.append(f'{sound_lower(m - 1, g[0])},{sound_lower(m - 1, g[1])},{int(g[0] not in (0, full))},{int(g[1] not in (0, full))}')
    return ';'.join(out)


def run_percy_core(m, core, start, method, solver, offset, extra=()):
    """percy_run.exe (SSV, set_primitive(AIG)) on the core from a proved lower bound; budgets re-emitted with offset.
    extra: optional minimum-preserving driver flags (--noreapply-full, --cofactor-lb ...), valid only because the search
    increases from a proved lower bound."""
    import subprocess
    hx = format(core, f'0{max(1, (1 << m) // 4)}x')
    t = time.perf_counter()
    p = subprocess.run([PERCY, '--n', str(m), '--tt', hx, '--solver', solver, '--method', method, '--start', str(start),
                        *extra], capture_output=True, text=True)
    final = None
    for line in p.stdout.splitlines():
        if not line.startswith('{'):
            continue
        r = json.loads(line)
        if 'k' in r:
            emit(k=r['k'] + offset, status=r['status'], seconds=r['seconds'], extra_clauses=r.get('extra_clauses', 0))
        elif 'final' in r:
            final = r
    return final, time.perf_counter() - t


def run_hybrid_percy(tool, n, tt, care, kmax):
    """hpercy-<method>-<solver>: signed modules -> lower bounds -> ladder (one-sharing, two-sharing, solve3) -> Percy.
       mpercy-<method>-<solver>: signed modules -> lower bounds -> Percy (no ladder; ablation of the ladder)."""
    full = (1 << (1 << n)) - 1
    if care != full:
        raise SystemExit(f'{tool}: complete functions only')
    kind, method, solver = tool.split('-')
    from module_contraction import simplify
    m, core, tr = simplify(n, tt, True)
    pre = dict(core_n=m, trace=len(tr))
    if m <= 1:
        emit(final='SAT', steps=len(tr), stage='trivial-core', verified_scope='internal', pre_seconds=round(time.perf_counter() - T0, 6),
             seconds=round(time.perf_counter() - T0, 6), **pre)
        return
    lb = core_lower_bound(m, core); pre['bound'] = lb
    stage = 'percy'
    extra = []
    if kind in ('hpercyr', 'hpercyc'):                 # + full no-reapplication [+ reader caps]
        extra.append('--noreapply-full')
        if kind == 'hpercyc':
            extra += ['--cofactor-lb', cofactor_bounds(m, core)]
    if kind in ('hpercy', 'hpercyr', 'hpercyc'):
        from one_sharing_core import solve_core
        from two_sharing_core import solve as solve2
        from ordered_quotient_core import solve3, make_completion
        one = solve_core(m, core, True, False)
        best = None
        if one is not None:
            best, stage = one[0], 'one-sharing'
        elif solve2(m, core, True) is not None:
            best, stage = m + 1, 'two-sharing'
        elif solve3(m, core, True, completion=make_completion('phase-first')) is not None:
            best, stage = m + 2, 'solve3'
        if best is not None:
            emit(final='SAT', steps=best + len(tr), stage=stage, verified_scope='internal',
                 pre_seconds=round(time.perf_counter() - T0, 6), seconds=round(time.perf_counter() - T0, 6), **pre)
            return
        lb = max(lb, m + 3)                # ladder decided: no circuit with binary excess <= 3
        stage = 'ladder+percy'
    pre_seconds = time.perf_counter() - T0
    emit(stage='preprocessed', start=lb, pre_seconds=round(pre_seconds, 6), **pre)
    final, synth = run_percy_core(m, core, lb, method, solver, len(tr), extra)
    if final and final.get('final') == 'SAT':
        gates = [[op, a, b] for op, a, b in final['chain']]
        var, inv = final['out']
        emit(final='SAT', steps=final['steps'] + len(tr), stage=stage, core_n=m, trace=len(tr), bound=lb,
             verified_scope='core', core_tt=hex(core), core_gates=gates, core_out=[var - 1, inv],
             pre_seconds=round(pre_seconds, 6), synth_seconds=round(synth, 6), seconds=round(time.perf_counter() - T0, 6))
    else:
        emit(final='UNSAT', steps=-1, stage=stage, pre_seconds=round(pre_seconds, 6), seconds=round(time.perf_counter() - T0, 6))


if __name__ == '__main__':
    tool, n, tt = sys.argv[1], int(sys.argv[2]), int(sys.argv[3], 16)
    care = (1 << (1 << n)) - 1 if sys.argv[4] == '-' else int(sys.argv[4], 16)
    start = int(sys.argv[5]); kmax = int(sys.argv[6]) if len(sys.argv) > 6 else 64
    if tool.startswith('cirbo-'):
        run_cirbo(tool[6:], n, tt, care, start, kmax)
    elif tool == 'ours-sat':
        k, gates, out = run_ours_sat(n, tt, care, start, kmax)
        emit(final='SAT' if k else 'UNSAT', steps=k if k else -1, gates=gates, out=out,
             seconds=round(time.perf_counter() - T0, 6))
    elif tool == 'ours-hybrid':
        run_hybrid(n, tt, care, start, kmax)
    elif tool.startswith(('hpercy-', 'mpercy-', 'hpercyr-', 'hpercyc-')):
        run_hybrid_percy(tool, n, tt, care, kmax)
    else:
        raise SystemExit(f'unknown tool {tool}')
