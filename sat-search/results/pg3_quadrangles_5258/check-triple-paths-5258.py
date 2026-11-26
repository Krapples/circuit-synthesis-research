"""Verify the induced paths used after the source-count screen."""
from itertools import combinations
from pathlib import Path
import runpy

data = runpy.run_path(str(Path(__file__).with_name("triple-support-5258.py")))
rows = data["data"]


def path(vertices, adjacency):
    for group in combinations(sorted(vertices), 4):
        degrees = sorted(len(adjacency[v].intersection(group)) for v in group)
        if degrees == [1, 1, 2, 2]:
            return group
    raise AssertionError("No induced four-vertex path")


neg = rows["NEG"]
true_edges = {frozenset(e) for e in rows["EDGES"]}
for a, b in combinations(range(26), 2):
    mask = (1 << a) | (1 << b)
    if {a, b} not in true_edges:
        assert any(q & mask == mask for q in neg)

checked = 0
for active in combinations(rows["POINTS"], 3):
    for by_line in (False, True):
        raw, sources, _ = data["supports"](active, by_line)
        vertices = {v for v, in sources[:raw]}
        adjacency = {v: {w for w in vertices - {v} if {w, v} in true_edges} for v in vertices}
        assert all(adjacency.values())
        seen = {min(vertices)}
        while len(seen) < raw:
            reached = seen.union(*(adjacency[v] for v in seen))
            assert reached != seen
            seen = reached
        path(vertices, adjacency)
        if raw == 12:
            groups = {}
            for v, adjacent in adjacency.items():
                groups.setdefault(frozenset(adjacent), []).append(v)
            for twins in groups.values():
                for size in range(1, len(twins) + 1):
                    for selected in combinations(twins, size):
                        path(vertices.difference(selected), adjacency)
            for provider in sources[raw:]:
                path(vertices.difference(provider), adjacency)
        checked += 1
print(f"Verified the nonedge rows and path obstructions for all {checked} triple scopes.")
