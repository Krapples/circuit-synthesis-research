"""Search for top-form counterexamples to L-meta-4081, relaxing leastness."""
from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import combinations
import json
import runpy
import sys
from threading import Timer

baseline = runpy.run_path(__file__.replace("-structural.py", ".py"))
BASE, N, EDGES, ROWS, POS, LOSING, cs = (
    baseline[name] for name in ("BASE", "N", "EDGES", "ROWS", "POS", "LOSING", "cs")
)


def encode(size, first_op, phased):
    output, pool, clauses, ops, select = cs.build(N, size, colex_from=size if phased else 0)
    cs.add_fanout_rules(N, POS, ops, select, clauses)
    cs.add_readonce_rules(N, size, POS, pool, ops, select, clauses)
    clauses.extend([-neg] for _, _, neg in ops.values())
    if first_op is not None:
        clauses.append([ops[N][first_op]])

    def equivalence(result, literals, conjunction):
        literals = list(literals)
        sign = 1 if conjunction else -1
        clauses.extend([-sign * result, sign * lit] for lit in literals)
        clauses.append([sign * result, *(-sign * lit for lit in literals)])
        return result

    def both(key, *literals):
        return equivalence(pool.id(key), literals, True)

    def any_of(key, literals):
        return equivalence(pool.id(key), literals, False)

    def selected(key, selectors, sources):
        result = pool.id(key)
        for sel, src in zip(selectors, sources, strict=True):
            clauses.extend(([-sel, -result, src], [-sel, result, -src]))
        return result

    truth = []
    for row_id, row in enumerate(ROWS):
        values = [pool.id(("truth", row_id, w)) for w in range(output + 1)]
        clauses.extend([values[v] if row >> v & 1 else -values[v]] for v in range(N))
        clauses.append([values[-1] if row_id < len(POS) else -values[-1]])
        clauses.extend(cs.truth_gate_clauses(row_id, values, pool, ops, select))
        truth.append(values)

    support = [[pool.id(("support", w, v)) for v in range(N)] for w in range(output + 1)]
    for w in range(N):
        clauses.extend([lit if w == v else -lit] for v, lit in enumerate(support[w]))
    false = any_of("false", [])
    has_top = [false] * N
    clean, top, junk, sides, empty, singleton = {}, {}, {}, {}, {}, {}
    for w, (is_and, is_or, _) in ops.items():
        clean[w] = both(("clean", w), *(-values[w] for values in truth[len(POS):]))
        top[w] = both(("top", w), is_and, clean[w])
        junk[w] = both(("junk", w), is_and, -clean[w])
        parents = [selected(("parent_has_top", w, b), select[w, b], has_top) for b in (0, 1)]
        clauses.extend([-is_and, -flag] for flag in parents)
        has_top.append(any_of(("has_top", w), [top[w], *parents]))
        for b in (0, 1):
            side = [selected(("side", w, b, v), select[w, b],
                             (support[src][v] for src in range(w))) for v in range(N)]
            sides[w, b] = side
            nonempty = any_of(("nonempty", w, b), side)
            empty[w, b] = -nonempty
            many = any_of(("many", w, b), (both(("pair", w, b, v, u), side[v], side[u])
                                           for v, u in combinations(range(N), 2)))
            singleton[w, b] = both(("singleton", w, b), nonempty, -many)
        for v in range(N):
            side_union = any_of(("union", w, v), [sides[w, 0][v], sides[w, 1][v]])
            equivalence(support[w][v], [is_or, side_union], True)

    if phased:
        collector = {w: both(("collector", w), clean[w], ops[w][1]) for w in ops}
        for w in ops:
            # Every clean gate has a top ancestor, and an OR is clean iff both inputs are clean.
            for b in (0, 1):
                child_clean = selected(("child_clean", w, b), select[w, b],
                                       [false] * N + [clean[src] for src in range(N, w)])
                equivalence(child_clean, [collector[w]], True)
            if w == output:
                continue
            # A proper prefix computing the target would contradict leastness.
            clauses.append([-clean[w], *(-row[w] for row in truth[:len(POS)])])
            clauses.extend(([-clean[w], clean[w + 1]], [-collector[w], collector[w + 1]]))
            same_class = (
                both(("both_dirty", w), -clean[w], -clean[w + 1]),
                both(("both_top", w), top[w], top[w + 1]),
                both(("both_collector", w), collector[w], collector[w + 1]),
            )
            adjacent = any_of(("same_phase", w), same_class)
            left, right = select[w, 0], select[w, 1]
            next_left, next_right = select[w + 1, 0], select[w + 1, 1]
            for right_id in range(w):
                clauses.extend([-adjacent, -right[right_id], -next_right[smaller]]
                               for smaller in range(right_id))
                for left_id in range(right_id):
                    clauses.extend([-adjacent, -right[right_id], -next_right[right_id],
                                    -left[left_id], -next_left[smaller]] for smaller in range(left_id))

    marked, budget = {}, list(junk.values())
    for w in reversed(ops):
        readers = []
        for reader in range(w + 1, output + 1):
            for b in (0, 1):
                through_or = both(("through_or", w, reader, b), ops[reader][1], marked[reader])
                from_top = both(("from_top", w, reader, b), top[reader], singleton[reader, 1 - b])
                reaches = any_of(("from_reader", w, reader, b), [through_or, from_top])
                readers.append(both(("reader", w, reader, b), select[reader, b][w], reaches))
        marked[w] = any_of(("marked", w), readers)
        lam = both(("lampath", w), marked[w], -empty[w, 0], -empty[w, 1])
        if phased:
            dirty = -clean[w]
        else:
            dirty = any_of(("dirty_or", w), (row[w] for row in truth[len(POS):]))
        budget.append(both(("charged_or", w), ops[w][1], dirty, -lam))
        either_empty = any_of(("either_empty", w), [empty[w, 0], empty[w, 1]])
        budget.extend(both(("centreless", w, copy), top[w], either_empty) for copy in (0, 1))

    covered = []
    for i, (u, v) in enumerate(EDGES):
        cross = []
        witnesses = []
        for w in ops:
            for b in (0, 1):
                cross.append(both(("cross", i, w, b), top[w], sides[w, b][u], sides[w, 1 - b][v]))
            witnesses.append(both(("witness", i, w), junk[w], truth[i][w]))
        covered.append(any_of(("covered", i), cross))
        clauses.append([covered[-1], *witnesses])
    for lits, bound in (([-lit for lit in junk.values()], size - 3),
                        (covered, len(EDGES) - 3), (budget + covered, len(EDGES) - 1)):
        clauses.extend(cs.CardEnc.atmost(lits, bound=bound, vpool=pool).clauses)
    return clauses, ops, select


def check_gates(gates):
    """Check the Lean conditions by direct evaluation and independent set traversal."""
    values = [sum(1 << row for row in range(1 << N) if row >> v & 1) for v in range(N)]
    target = sum(1 << row for row in range(1 << N) if row not in LOSING)
    support = [{v} for v in range(N)]
    cone = [set() for _ in range(N)]
    or_cone = [set() for _ in range(N)]
    top, junk, dirty_or = set(), set(), set()
    for w, (op, a, b) in enumerate(gates, start=N):
        values.append(values[a] | values[b] if op else values[a] & values[b])
        clean = not values[-1] & ~target
        if op:
            if not clean:
                dirty_or.add(w)
        elif clean:
            top.add(w)
        else:
            junk.add(w)
        support.append(support[a] | support[b] if op else set())
        cone.append(cone[a] | cone[b] | {a, b})
        or_cone.append(or_cone[a] | or_cone[b] | {w} if op else {w})
    assert values[-1] == target
    assert all(not cone[w] & top for w in top | junk)
    covered, lam = set(), set()
    centreless = 0
    for w in top:
        _, a, b = gates[w - N]
        centreless += not support[a] or not support[b]
        covered.update(tuple(sorted((x, y))) for x in support[a] for y in support[b])
        for origin, other in ((a, b), (b, a)):
            if len(support[other]) == 1:
                for reader in or_cone[origin] & dirty_or:
                    _, c, d = gates[reader - N]
                    if support[c] and support[d]:
                        lam.add(reader)
    uncovered = [(a, b) for a, b in EDGES if (a, b) not in covered]
    for a, b in uncovered:
        assert any(values[w] >> ((1 << a) | (1 << b)) & 1 for w in junk)
    charge = 2 * centreless + len(junk) + len(dirty_or - lam)
    assert len(junk) >= 3 and len(uncovered) >= 3 and charge < len(uncovered)
    return dict(uncovered=uncovered, charge=charge, junk=sorted(junk), lam=sorted(lam))


def solve(job):
    size, first_op, seconds, phased = job
    clauses, ops, select = encode(size, first_op, phased)
    with cs.Solver(name="maplechrono", bootstrap_with=clauses) as solver:
        timer = Timer(seconds, solver.interrupt)
        timer.start()
        try:
            verdict = solver.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
        gates, checked = None, None
        if verdict:
            model = set(solver.get_model())
            gates = [(int(flags[1] in model),
                      *(next(src for src, sel in enumerate(select[w, b]) if sel in model)
                        for b in (0, 1))) for w, flags in ops.items()]
            checked = check_gates(gates)
        return dict(size=size, first_op=first_op, seconds=seconds, phased=phased, clauses=len(clauses),
                    result={True: "SAT", False: "UNSAT", None: "OPEN"}[verdict],
                    statistics=solver.accum_stats(), gates=gates, checked=checked)


if __name__ == "__main__":
    phased = "--phased" in sys.argv[1:]
    seconds = 180 if phased else 150
    jobs = [(size, op, seconds, phased) for size in range(12, 22) for op in (0, 1)]
    jobs.extend((size, None, seconds, phased) for size in (10, 11))
    assert len(jobs) == 22
    run = "phased" if phased else "structural"
    with (BASE / f"L-meta-4081-{run}.jsonl").open("x", encoding="utf-8") as log:
        with ProcessPoolExecutor(max_workers=22) as pool:
            for future in as_completed(pool.submit(solve, job) for job in jobs):
                result = json.dumps(future.result())
                print(result, file=log, flush=True)
                print(result, flush=True)
