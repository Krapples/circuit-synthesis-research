"""Check bounded native residual completion against independent AIG reductions."""

from itertools import combinations, product
from pathlib import Path
from random import Random
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'theory'))
from ordered_quotient_core import make_completion
from regional_native import _native
from regional_production_adapter import check_tree


def aig_tables(columns, h, full):
    """Bottom-up merges consume their two wires and create a new AIG wire."""
    current = [(value, i < h) for i, value in enumerate(columns)]
    tables = set()

    def visit(wires):
        if len(wires) == 1:
            value = wires[0][0]
            tables.update((value, value ^ full))
            return
        for i, j in combinations(range(len(wires)), 2):
            a, internal_a = wires[i]
            b, internal_b = wires[j]
            if not (internal_a or internal_b):
                continue
            other = [wire for index, wire in enumerate(wires) if index not in (i, j)]
            for x, y in product((a, a ^ full), (b, b ^ full)):
                visit([*other, (x & y, True)])

    visit(current)
    return tables


def main():
    columns = (0xaa, 0xcc, 0xf0)
    checked = feasible = 0
    for h in (1, 2, 3):
        expected_tables = aig_tables(columns, h, 0xff)
        for labels in product((-1, 0, 1), repeat=8):
            target = sum(1 << i for i, label in enumerate(labels) if label == 1)
            care = sum(1 << i for i, label in enumerate(labels) if label >= 0)
            expected = any((table ^ target) & care == 0 for table in expected_tables)
            result = _native.tight_residual(columns, h, target, care)
            assert result == int(expected), (h, labels, expected, result)
            checked += 1
            feasible += expected

    rng = Random(20261125)
    for _ in range(256):
        columns4 = [rng.randrange(1 << 16) for _ in range(4)]
        h = rng.randrange(1, 5)
        care = rng.randrange(1 << 16)
        tables = aig_tables(columns4, h, 0xffff)
        target = rng.choice(sorted(tables)) if rng.randrange(2) else rng.randrange(1 << 16)
        expected = any((table ^ target) & care == 0 for table in tables)
        assert _native.tight_residual(columns4, h, target, care) == int(expected)
        checked += 1
        feasible += expected

    # Plain phase-first permits H & (c | d). With fixed H=(ab) and M=(c,d),
    # that cherry is forbidden and no alternative tree exists.
    target = columns[0] & (columns[1] | columns[2])
    labels = [(target >> i) & 1 for i in range(8)]
    ports, pats = (0, 1, 2), tuple(range(8))
    complete = make_completion('phase-first')
    tree = complete(0, ports, pats, labels, True)
    assert tree is not None
    check_tree(tree, 0, ports, pats, labels, True)
    assert _native.tight_residual(columns, 1, target, 0xff) == 0
    assert _native.tight_residual(columns, 2, target, 0xff) == 1
    assert _native.tight_residual(columns, 1, target, 0xff, 0) == 2
    assert _native.tight_residual([0] * 6, 1, 0, 0xff) == 1
    assert _native.tight_residual([0] * 7, 1, 0, 0xff) == 2
    print(json.dumps(dict(seed=20261125, checked=checked, feasible=feasible,
                          infeasible=checked - feasible, fringe_counterexample='H & (c | d)',
                          capped_status='unknown')))


if __name__ == '__main__':
    main()
