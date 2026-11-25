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
    else:
        raise SystemExit(f'unknown tool {tool}')
