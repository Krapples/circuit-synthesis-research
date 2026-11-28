"""Exact AO2 synthesis for bipartite edge functions, with an optional edge-owned constraint.

Model (IsAO2): gates AND/OR of two earlier wires (distinct wires suffice for minimality), output
the last gate. Edge-owned: every AND gate is false on every input where f_E is false.
CEGAR over input rows: UNSAT on a row subset is UNSAT on all rows (sound); SAT answers are
verified on all 2^N rows before being reported.
Invoked by l18065_sweep.py. The supervising process enforces wall limits.
"""
import time
from pysat.solvers import Solver
from pysat.card import CardEnc
from monotone_frontier import monotone_frontier


def fval(m, edges, x):
    return any((x >> a) & 1 and (x >> (m + b)) & 1 for a, b in edges)


def simulate(N, gates, x):
    w = [(x >> i) & 1 for i in range(N)]
    for op, u, v in gates:
        w.append(w[u] & w[v] if op else w[u] | w[v])
    return w


def solve(m, edges, k, owned, *, row_mode, report, conflict_limit=None):
    wall_start = time.perf_counter()
    cpu_start = time.process_time()
    encode_seconds = 0.0
    solve_seconds = 0.0
    verify_seconds = 0.0
    rounds = 0
    report("encoding", budget=k, owned=owned)
    N = 2 * m
    F = [fval(m, edges, x) for x in range(1 << N)]
    cnt = [0]
    def new():
        cnt[0] += 1
        return cnt[0]
    op = [new() for _ in range(k)]
    sel = []
    for j in range(k):
        d = {}
        for u in range(N + j):
            for v in range(u + 1, N + j):
                d[(u, v)] = new()
        sel.append(d)
    cl = []
    for j in range(k):
        lits = list(sel[j].values())
        enc = CardEnc.equals(lits=lits, bound=1, top_id=cnt[0], encoding=1)
        cnt[0] = max(cnt[0], enc.nv)
        cl += enc.clauses
    # every non-output gate is read by a later gate
    for j in range(k - 1):
        w = N + j
        readers = [sel[t][p] for t in range(j + 1, k) for p in sel[t] if w in p]
        cl.append(readers)
    s = Solver(name='cadical195', bootstrap_with=cl)
    rows_added = set()

    def add_row(x):
        rows_added.add(x)
        vv = [None] * (N + k)
        for i in range(N):
            vv[i] = (x >> i) & 1  # constant
        for j in range(k):
            vv[N + j] = new()
        for j in range(k):
            g = vv[N + j]
            for (u, v), sv in sel[j].items():
                a, b = vv[u], vv[v]
                # AND case (op true)
                for cls in and_or(g, a, b, True):
                    s.add_clause([-sv, -op[j]] + cls)
                for cls in and_or(g, a, b, False):
                    s.add_clause([-sv, op[j]] + cls)
            if owned and not F[x]:
                s.add_clause([-op[j], -g])
        out = vv[N + k - 1]
        s.add_clause([out] if F[x] else [-out])

    def and_or(g, a, b, is_and):
        # returns clauses (lists) encoding g = a op b, where a, b may be 0/1 constants
        if is_and:
            if a == 0 or b == 0:
                return [[-g]]
            if a == 1 and b == 1:
                return [[g]]
            if a == 1:
                return [[-g, b], [g, -b]]
            if b == 1:
                return [[-g, a], [g, -a]]
            return [[-g, a], [-g, b], [g, -a, -b]]
        else:
            if a == 1 or b == 1:
                return [[g]]
            if a == 0 and b == 0:
                return [[-g]]
            if a == 0:
                return [[-g, b], [g, -b]]
            if b == 0:
                return [[-g, a], [g, -a]]
            return [[g, -a], [g, -b], [-g, a, b]]

    try:
        if row_mode == "frontier":
            positive, negative = monotone_frontier(F)
            seeds = sorted(positive + negative)
        else:
            seeds = [0] + sorted({(1 << a) | (1 << (m + b)) for a, b in edges})
        for x in seeds:
            add_row(x)
        encode_seconds = time.perf_counter() - wall_start
        witness = None
        while True:
            stats = s.accum_stats()
            remaining = None if conflict_limit is None else conflict_limit - stats["conflicts"]
            if remaining is not None and remaining <= 0:
                verdict = "CONFLICT_LIMIT"
                break
            report("solving", budget=k, owned=owned, rows=len(rows_added), rounds=rounds,
                   variables=s.nof_vars(), clauses=s.nof_clauses(), **stats)
            if remaining is not None:
                s.conf_budget(remaining)
            rounds += 1
            start = time.perf_counter()
            answer = s.solve() if remaining is None else s.solve_limited()
            solve_seconds += time.perf_counter() - start
            if answer is not True:
                verdict = "UNSAT" if answer is False else "CONFLICT_LIMIT"
                break
            start = time.perf_counter()
            mdl = {lit for lit in s.get_model() if lit > 0}
            gates = []
            for j in range(k):
                u, v = next(pair for pair, sv in sel[j].items() if sv in mdl)
                gates.append((int(op[j] in mdl), u, v))
            bad = None
            for x, target in enumerate(F):
                wires = simulate(N, gates, x)
                if wires[-1] != target or (owned and not target and
                        any(gate[0] and wires[N + j] for j, gate in enumerate(gates))):
                    bad = x
                    break
            verify_seconds += time.perf_counter() - start
            if bad is None:
                verdict, witness = "SAT", gates
                break
            if bad in rows_added or row_mode == "frontier":
                raise RuntimeError(f"encoding accepted an invalid circuit on row {bad}")
            start = time.perf_counter()
            add_row(bad)
            encode_seconds += time.perf_counter() - start
        return {
            "verdict": verdict, "witness": witness, "rows": len(rows_added), "rounds": rounds,
            "encoding_seconds": encode_seconds, "solve_seconds": solve_seconds,
            "verification_seconds": verify_seconds, "wall_seconds": time.perf_counter() - wall_start,
            "cpu_seconds": time.process_time() - cpu_start, **s.accum_stats(),
        }
    finally:
        s.delete()
