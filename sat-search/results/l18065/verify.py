"""Check the row frontier against set semantics and optionally verify archived witnesses."""
import argparse
import json
from itertools import product
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "experiments"))
from l18065_sweep import graphs
from monotone_frontier import monotone_frontier


def check_small_tables():
    count = 0
    for n in range(4):
        rows = range(1 << n)
        for table in product((False, True), repeat=len(rows)):
            monotone = all(not table[a] or table[b] for a in rows for b in rows if a & b == a)
            if monotone:
                positive, negative = monotone_frontier(table)
                for row in rows:
                    assert table[row] == any(low & row == low for low in positive)
                    assert table[row] != any(high & row == row for high in negative)
                count += 1
            else:
                try:
                    monotone_frontier(table)
                except ValueError:
                    pass
                else:
                    raise AssertionError("accepted a nonmonotone truth table")
    assert count == 31
    return count


def check_frontiers():
    count = 0
    for m in (3, 4):
        for _, edges in graphs(m):
            vertices = set(range(2 * m))
            pairs = [{a, m + b} for a, b in edges]
            masks = [{v for v in vertices if mask & (1 << v)} for mask in range(1 << (2 * m))]
            table = [any(pair <= support for pair in pairs) for support in masks]
            positive, negative = monotone_frontier(table)
            assert {frozenset(masks[mask]) for mask in positive} == set(map(frozenset, pairs))
            frontier = [masks[mask] for mask in negative]
            for bits in product((False, True), repeat=2 * m):
                support = {v for v, bit in enumerate(bits) if bit}
                positive = any(pair <= support for pair in pairs)
                assert positive != any(support <= row for row in frontier)
                maximal_false = not positive and all(
                    any(pair <= support | {v} for pair in pairs) for v in vertices - support
                )
                assert (support in frontier) == maximal_false
                count += 1
    assert count == 4416
    return count


def check_archived_witnesses(path):
    count = 0
    for line in path.read_text(encoding="utf-8").splitlines()[1:]:
        row, _ = json.JSONDecoder().raw_decode(line)
        m, gates = row["m"], row["owned_circuit"]
        if not isinstance(row["owned"], int):
            continue
        assert len(gates) == row["owned"]
        n = 2 * m
        assert all(op in (0, 1) and 0 <= a < b < n + j
                   for j, (op, a, b) in enumerate(gates))
        for bits in product((False, True), repeat=n):
            target = any(bits[a] and bits[m + b] for a, b in row["E"])
            wires = list(bits)
            for op, a, b in gates:
                wires.append((wires[a] and wires[b]) if op else (wires[a] or wires[b]))
                if op and not target:
                    assert not wires[-1]
            assert wires[-1] == target
        count += 1
    return count


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--legacy-log", type=Path)
    args = parser.parse_args()
    result = {"small_monotone_tables": check_small_tables(), "frontier_assignments": check_frontiers()}
    if args.legacy_log is not None:
        result["verified_archived_owned_witnesses"] = check_archived_witnesses(args.legacy_log)
    print(json.dumps(result))
