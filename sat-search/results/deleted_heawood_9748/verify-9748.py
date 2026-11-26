"""Check the star upper bound and the residual induced-path obstructions."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import runpy

source = runpy.run_path(str(Path(__file__).with_name("residual-9748.py")))
original = source["m"]
neighbors = source["NEIGHBORS"]
setup = source["setup"]
edges = set(map(frozenset, original["EDGES"]))


def path(vertices, adjacency):
    return any(sorted(len(adjacency[v].intersection(group)) for v in group) == [1, 1, 2, 2]
               for group in combinations(sorted(vertices), 4))


def verify_shapes():
    counts = Counter()
    for size in (2, 3):
        for core in combinations(neighbors, size):
            raw, providers, _, _ = setup(core)
            vertices = set(raw)
            adj = {u: {v for v in vertices if frozenset((u, v)) in edges} for u in vertices}
            assert all(adj.values())
            connected = {raw[0]}
            while len(connected) < len(raw):
                grown = connected.union(*(adj[u] for u in connected))
                assert grown != connected
                connected = grown
            assert path(vertices, adj)
            if len(raw) == 9:
                assert len({frozenset(a) for a in adj.values()}) == len(raw)
                for u in raw:
                    assert path(vertices - {u}, adj)
                for provider in providers:
                    assert path(vertices.difference(provider), adj)
            counts[size, len(raw)] += 1
    print(f"Checked path obstructions in {dict(counts)}.")


def verify_witness():
    circuit = []
    n = original["N"]

    def emit(op, a, b):
        circuit.append((op, a, b))
        return n + len(circuit) - 1

    stars = []
    for center, leaves in neighbors.items():
        a, b, c = sorted(leaves)
        stars.append(emit(0, center, emit(1, emit(1, a, b), c)))
    root = stars[0]
    for term in stars[1:]:
        root = emit(1, root, term)
    assert len(circuit) == 23
    assert root == n + len(circuit) - 1
    for row in range(1 << n):
        want = any(row & edge == edge for edge in original["POS"])
        assert original["cs"].evaluate(n, circuit, row) == want
    print("Verified the 23-gate right-star circuit on all 8,192 inputs.")


if __name__ == "__main__":
    verify_witness()
    verify_shapes()
