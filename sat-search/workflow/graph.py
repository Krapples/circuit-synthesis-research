"""Exact canonical labels for simple undirected graphs, with a safe bounded fallback."""

from collections import defaultdict
from dataclasses import dataclass


@dataclass(frozen=True)
class Graph:
    n: int
    edges: tuple[tuple[int, int], ...]
    old_to_new: tuple[int, ...]
    canonical: bool
    colors: tuple[str, ...]

    def argument(self):
        return ",".join(f"{a}-{b}" for a, b in self.edges)


def canonical_graph(n, edges, *, colors=None, limit=20_000):
    if type(n) is not int or n < 1 or type(limit) is not int or limit < 0:
        raise ValueError("graph order and canonicalization limit must be valid integers")
    pairs = set()
    neighbors = [set() for _ in range(n)]
    for u, v in edges:
        if type(u) is not int or type(v) is not int or not 0 <= u < n or not 0 <= v < n or u == v:
            raise ValueError(f"invalid simple-graph edge {u!r}, {v!r}")
        pairs.add(tuple(sorted((u, v))))
        neighbors[u].add(v)
        neighbors[v].add(u)
    if colors is None:
        colors = [""] * n
    if len(colors) != n or any(not isinstance(c, str) for c in colors):
        raise ValueError("colors must contain one string per vertex")
    by_color = defaultdict(list)
    for v, color in enumerate(colors):
        by_color[color].append(v)
    partition = tuple(tuple(by_color[c]) for c in sorted(by_color))
    best = None
    mapping = None
    visits = 0

    def refine(cells):
        while True:
            supports = [set(cell) for cell in cells]
            updated = []
            for cell in cells:
                groups = defaultdict(list)
                for v in cell:
                    groups[tuple(len(neighbors[v] & s) for s in supports)].append(v)
                updated.extend(tuple(groups[k]) for k in sorted(groups))
            if len(updated) == len(cells):
                return cells
            cells = tuple(updated)

    class Limit(Exception):
        pass

    def individualize(cells):
        nonlocal best, mapping, visits
        visits += 1
        if visits > limit:
            raise Limit
        cells = refine(cells)
        split = min(((len(c), i) for i, c in enumerate(cells) if len(c) > 1), default=None)
        if split is None:
            labels = [0] * n
            for i, (v,) in enumerate(cells):
                labels[v] = i
            code = tuple(sorted(tuple(sorted((labels[u], labels[v]))) for u, v in pairs))
            if best is None or code < best:
                best, mapping = code, tuple(labels)
            return
        _, i = split
        tried = []
        for v in cells[i]:
            if any(neighbors[v] - {u} == neighbors[u] - {v} for u in tried):
                continue
            tried.append(v)
            rest = tuple(u for u in cells[i] if u != v)
            individualize((*cells[:i], (v,), rest, *cells[i + 1:]))

    try:
        individualize(partition)
    except (Limit, RecursionError):
        return Graph(n, tuple(sorted(pairs)), tuple(range(n)), False, tuple(colors))
    ordered_colors = [""] * n
    for vertex, new in enumerate(mapping):
        ordered_colors[new] = colors[vertex]
    return Graph(n, best, mapping, True, tuple(ordered_colors))
