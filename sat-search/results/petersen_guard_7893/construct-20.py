"""Patch two covered Petersen edges through one input OR."""
from itertools import combinations
import json
from pathlib import Path
import runpy

search = runpy.run_path(str(Path(__file__).with_name("search-7893.py")))
N, POS, GUARD_OFF, evaluate = (search[key] for key in ("N", "POS", "GUARD_OFF", "evaluate"))
EDGES = [(a, b) for a, b in combinations(range(N), 2) if ((1 << a) | (1 << b)) in POS]
OMIT = {(1, 2), (1, 6)}
CENTERS = {0, 3, 7, 8, 9}


def build():
    gates = []

    def gate(op, a, b):
        wire = N + len(gates)
        gates.append((op, a, b))
        return wire

    def reduce_or(wires):
        combined, *remaining = wires
        for wire in remaining:
            combined = gate(1, combined, wire)
        return combined

    guard = gate(0, 1, gate(1, 2, 6))
    oriented = {center: [] for center in sorted(CENTERS)}
    for a, b in EDGES:
        if (a, b) in OMIT:
            continue
        if a in CENTERS:
            oriented[a].append(b)
        else:
            oriented[b].append(a)
    output = reduce_or([gate(0, center, reduce_or(leaves)) for center, leaves in oriented.items()])
    return gates, guard, output


if __name__ == "__main__":
    base, guard, output = build()
    assert len(base) == 19 and output == 28 and guard == 11
    assert all(not evaluate(base, row)[guard] for row in GUARD_OFF)
    assert all(0 not in gate[1:] for gate in base[:2])
    for row in range(1 << N):
        raised = row | int(evaluate(base, row & ~1)[guard])
        assert evaluate(base, raised)[output] == any(row & edge == edge for edge in POS)
    print(json.dumps(dict(base=base, guard=guard, output=output, expanded_gates=len(base) + 1)))
