"""Check the residual counted-NOT topology after pinning right-hand stars."""
from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import combinations
import json
from pathlib import Path
import runpy
import sys
from threading import Timer
from time import perf_counter

m = runpy.run_path(str(Path(__file__).with_name("search-9748.py")))
cs = m["cs"]
N = m["N"]
NEIGHBORS = {r: {p for p, line in m["EDGES"] if line == r} for r in range(7, 13)}


def setup(core):
    active = set().union(*(NEIGHBORS[r] for r in core))
    raw = sorted(active | set(core))
    providers = {s for r in set(NEIGHBORS) - set(core)
                 for size in (2, 3) for s in combinations(sorted(active & NEIGHBORS[r]), size)}
    for provider in providers:
        assert all(len(NEIGHBORS[r].intersection(provider)) <= 1 for r in core)
    sources = [(i,) for i in raw] + sorted(providers)
    bits = {wire: 1 << i for i, wire in enumerate(raw)}
    source_masks = [sum(bits[i] for i in support) for support in sources]
    edges = [bits[a] | bits[r] for r in core for a in NEIGHBORS[r]]
    return raw, providers, source_masks, edges


def require_even_paths(n, p, out, pool, cnf, ops, select):
    path = {(w, sign): pool.id(("path-to-output", w, sign))
            for w in range(out + 1) for sign in (0, 1)}
    cnf.extend([[path[out, 0]], [-path[out, 1]]])
    routes = {}
    for gate, flags in ops.items():
        neg = flags[2]
        for sign in (0, 1):
            keep, flip = path[gate, sign], path[gate, 1 - sign]
            route = routes[gate, sign] = pool.id(("route-through", gate, sign))
            cnf.extend(((neg, -keep, route), (neg, keep, -route),
                        (-neg, -flip, route), (-neg, flip, -route)))
    for w in range(out):
        for sign in (0, 1):
            reach = path[w, sign]
            reasons = []
            for j in range(max(w + 1, n), out + 1):
                route = routes[j, sign]
                for slot in (0, 1):
                    reason = pool.id(("operand-path", w, j, slot, sign))
                    chosen = select[j, slot][w]
                    cnf.extend(([-reason, chosen], [-reason, route],
                                [-chosen, -route, reason], [-reason, reach]))
                    reasons.append(reason)
            cnf.append([-reach, *reasons])
    cnf.extend([path[w, 0]] for w in range(p))


def run(core, gates, minimum_not, parity):
    raw, providers, masks, edges = setup(core)
    n = len(masks)
    p = len(raw)
    slack = gates + 1 - p
    out, pool, cnf, ops, select = cs.build(n, gates, require_used=False)
    extras = [flags[2] for flags in ops.values()]
    if minimum_not:
        cnf.append(extras.copy())
    for w in range(out):
        reads = [select[j, slot][w] for j in ops if j > w for slot in (0, 1)]
        if p <= w < n:
            active = pool.id(("provider", w))
            cnf.extend([-r, active] for r in reads)
            extras.append(active)
        else:
            cnf.append(reads)
    cnf.extend(cs.CardEnc.atmost(extras, bound=slack, vpool=pool).clauses)
    if parity:
        require_even_paths(n, p, out, pool, cnf, ops, select)
    rows = list(range(1 << p))
    target = {x for x in rows if any(x & edge == edge for edge in edges)}
    seed = [*edges]
    seed.extend(x for x in rows if x not in target and all(x | (1 << i) in target
                                                          for i in range(p) if not (x >> i & 1)))
    full = (1 << len(rows)) - 1
    known = sum(1 << x for x in target)
    columns = [sum(1 << x for x in rows if x & mask) for mask in masks]
    seen = set()
    start = perf_counter()
    with cs.Solver(name="maplechrono", bootstrap_with=cnf) as solver:
        def add_rows(selected):
            for x in sorted(set(selected) - seen):
                wire = [pool.id(("wire", x, j)) for j in range(out + 1)]
                solver.append_formula([[wire[j] if x & mask else -wire[j]]
                                       for j, mask in enumerate(masks)])
                solver.add_clause([wire[out] if x in target else -wire[out]])
                solver.append_formula(list(cs.truth_gate_clauses(x, wire, pool, ops, select)))
                seen.add(x)

        add_rows(seed)
        timer = Timer(65, solver.interrupt)
        timer.start()
        verdict, witness, tries = "OPEN", None, 0
        try:
            while True:
                sat = solver.solve_limited(expect_interrupt=True)
                if sat is None:
                    break
                if not sat:
                    verdict = "UNSAT"
                    break
                tries += 1
                model = set(solver.get_model())
                circuit = [(next(i for i, flag in enumerate(flags) if flag in model),
                            *(next(i for i, flag in enumerate(select[j, side]) if flag in model)
                              for side in (0, 1))) for j, flags in ops.items()]
                values = columns.copy()
                for op, a, b in circuit:
                    values.append(values[a] & values[b] if op == 0 else values[a] | values[b]
                                  if op == 1 else full ^ values[a])
                diff = values[-1] ^ known
                if not diff:
                    witness, verdict = circuit, "SAT"
                    break
                add_rows([x for x in rows if diff >> x & 1][:40])
            stats = solver.accum_stats()
        finally:
            timer.cancel()
    return dict(gates=gates, minimum_not=minimum_not, parity=parity, raw=p, providers=len(providers), verdict=verdict,
                witness=witness, rows=len(seen), attempts=tries, stats=stats,
                seconds=round(perf_counter() - start, 3))


def solve(job):
    core, parity = job
    if len(core) == 2:
        return dict(core=core, checks=[run(core, 6, False, parity)])
    raw, _, _, _ = setup(core)
    return dict(core=core, checks=[run(core, k, True, parity) for k in range(len(raw), 11)])


if __name__ == "__main__":
    jobs = [(core, "--parity" in sys.argv)
            for core in [*combinations(NEIGHBORS, 3), (7, 8), (7, 9)]]
    with Path(sys.argv[1]).open("x", encoding="utf-8") as records:
        with ProcessPoolExecutor(max_workers=22) as pool:
            for task in as_completed(pool.submit(solve, job) for job in jobs):
                line = json.dumps(task.result())
                print(line, file=records, flush=True)
                print(line, flush=True)
