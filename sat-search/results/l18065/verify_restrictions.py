"""Check direct-read caps against small independently enumerated AO2 circuits."""
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "experiments"))
from ao2_restriction_bounds import direct_reader_caps, read_once_lower_bound


def check_circuits(n, max_gates):
    inputs = [sum(1 << row for row in range(1 << n) if row & (1 << i)) for i in range(n)]

    @lru_cache(maxsize=None)
    def caps(truth_bits, k):
        table = [bool(truth_bits & (1 << row)) for row in range(1 << n)]
        assert read_once_lower_bound(table) <= k
        baseline = dict(direct_reader_caps(table, k, 3))
        stronger = dict(direct_reader_caps(table, k, 3, lower_bound=read_once_lower_bound))
        assert all(stronger[mask] <= cap for mask, cap in baseline.items())
        return stronger

    def visit(wires, gates):
        k = len(gates)
        if k:
            for fixed, cap in caps(wires[-1], k).items():
                reads = sum(not set(pair).isdisjoint(fixed) for pair in gates)
                assert reads <= cap, (n, gates, wires[-1], fixed, cap, reads)
        if k == max_gates:
            return 1
        count = int(k > 0)
        for a, b in combinations(range(len(wires)), 2):
            pair = (a, b)
            for value in (wires[a] & wires[b], wires[a] | wires[b]):
                count += visit(wires + [value], gates + [pair])
        return count

    return visit(inputs, []), caps.cache_info().currsize


if __name__ == "__main__":
    majority = [row.bit_count() >= 2 for row in range(8)]
    assert read_once_lower_bound(majority) == 3
    for n, k in ((3, 4), (4, 3)):
        circuits, truth_budget_pairs = check_circuits(n, k)
        print(f"{n} inputs through {k} gates: {circuits} circuits, {truth_budget_pairs} truth/budget pairs")
