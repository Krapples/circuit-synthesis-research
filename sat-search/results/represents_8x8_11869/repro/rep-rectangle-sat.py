from concurrent.futures import ProcessPoolExecutor, as_completed
import json
from pathlib import Path
import sys
import threading

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / ".scratch-sat"))
from pysat.card import CardEnc
from pysat.formula import IDPool
from pysat.solvers import Solver

TABLE = 7583035862004050432
FULL = (1 << 64) - 1


def rectangles(target):
    rows = [(target >> (8 * r)) & 255 for r in range(8)]
    for rmask in range(1, 256):
        common = 255
        for r in range(8):
            if rmask >> r & 1:
                common &= rows[r]
        cmask = common
        while cmask:
            cover = sum(cmask << (8 * r) for r in range(8) if rmask >> r & 1)
            yield rmask, cmask, cover
            cmask = (cmask - 1) & common


def encode(budget, negative):
    target = TABLE ^ (FULL if negative else 0)
    pool = IDPool()
    clauses, recipes, costs = [], {}, []
    roles = [
        (rows ^ 255 if negative else rows, cols ^ 255 if negative else cols, coverage)
        for rows, cols, coverage in rectangles(target)
    ]
    menus = [
        sorted({sub for row in roles for sub in range(1, 256) if sub & row[side] == sub})
        for side in (0, 1)
    ]
    wires = [
        {mask: pool.id(("wire", side, mask)) for mask in menu if mask.bit_count() > 1}
        for side, menu in enumerate(menus)
    ]
    cover_choices = [pool.id(("rectangle", i)) for i in range(len(roles))]
    for i, ((rows, cols, _), chosen) in enumerate(zip(roles, cover_choices)):
        costs.append(chosen)
        if rows and cols:
            fee = pool.id(("paid_and_or", i))
            clauses.extend(([-chosen, fee], [-fee, chosen]))
            costs.append(fee)
        for side, mask in enumerate((rows, cols)):
            if mask in wires[side]:
                clauses.append([-chosen, wires[side][mask]])
    for point in range(64):
        if target >> point & 1:
            clauses.append([pick for (_, _, cover), pick in zip(roles, cover_choices) if cover >> point & 1])
    for side, maps in enumerate(wires):
        costs.extend(maps.values())
        for mask, wire in maps.items():
            decomps = []
            a = (mask - 1) & mask
            while a:
                b = mask ^ a
                if a < b:
                    pick = pool.id(("merge", side, mask, a, b))
                    decomps.append((pick, a, b))
                    for component in (a, b):
                        if component in maps:
                            clauses.append([-pick, maps[component]])
                a = (a - 1) & mask
            clauses.append([-wire, *(pick for pick, _, _ in decomps)])
            recipes[side, mask] = decomps
    clauses.extend(CardEnc.atmost(costs, bound=budget + 1, vpool=pool).clauses)
    return clauses, roles, cover_choices, recipes


def compile_model(roles, cover_choices, recipes, model, negative):
    gates = []
    signals = {}

    def add(op, a, b):
        gates.append((op, a, b))
        return len(gates) + 15

    def signal(side, mask):
        if mask.bit_count() == 1:
            return 8 * side + mask.bit_length() - 1
        key = (side, mask)
        if key not in signals:
            a, b = next((a, b) for pick, a, b in recipes[key] if pick in model)
            signals[key] = add(1, signal(side, a), signal(side, b))
        return signals[key]

    terms = []
    for (rows, cols, _), pick in zip(roles, cover_choices):
        if pick not in model:
            continue
        sides = [signal(side, mask) for side, mask in enumerate((rows, cols)) if mask]
        terms.append(add(int(negative), *sides) if len(sides) == 2 else sides[0])
    output = terms[0]
    for term in terms[1:]:
        output = add(int(not negative), output, term)
    for u in range(8):
        for v in range(8):
            values = [i in (u, 8 + v) for i in range(16)]
            for op, a, b in gates:
                values.append(values[a] or values[b] if op else values[a] and values[b])
            assert values[output] == (TABLE >> (8 * u + v)) & 1
    return gates, output


def solve(task):
    budget, negative = task
    clauses, roles, choices, recipes = encode(budget, negative)
    with Solver(name="maplechrono", bootstrap_with=clauses) as solver:
        timer = threading.Timer(25, solver.interrupt)
        timer.start()
        try:
            verdict = solver.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
        data = {"budget": budget, "negative": negative,
                "result": "SAT" if verdict else "OPEN" if verdict is None else "UNSAT"}
        if verdict:
            gates, output = compile_model(roles, choices, recipes, set(solver.get_model()), negative)
            assert len(gates) <= budget
            data.update(gates=gates, output=output, size=len(gates))
    return data


def main():
    tasks = [(budget, negative) for budget in range(20, 31) for negative in (False, True)]
    log_path = (ROOT / "sat-search" / "logs").joinpath("L-meta-11869-rectangle-sat.jsonl")
    with log_path.open("x", encoding="utf-8") as log, ProcessPoolExecutor(max_workers=22) as pool:
        print("22 workers for 22 rectangle-cover jobs", flush=True)
        for future in as_completed([pool.submit(solve, task) for task in tasks]):
            row = future.result()
            print(json.dumps(row), file=log, flush=True)
            print(json.dumps({key: value for key, value in row.items() if key not in ("gates", "output")}), flush=True)


if __name__ == "__main__":
    main()
