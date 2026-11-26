"""Independently count incidences outside the support of two quadrangles."""
from collections import Counter
from pathlib import Path
import runpy

data = runpy.run_path(str(Path(__file__).with_name("search-5258.py")))
edges = data["EDGES"]
quadrangles = data["NEG"]
line_masks = {p: sum(1 << l for v, l in edges if v == p) for p in data["POINTS"]}
line_set = ((1 << 13) - 1) << 13
point_set = (1 << 13) - 1
edge_masks = [(1 << p) | (1 << l) for p, l in edges]

for q in quadrangles:
    assert (q & line_set).bit_count() == 3
    assert (q & point_set).bit_count() == 4
    hits = [(mask & ~q).bit_count() for p, mask in line_masks.items() if not (q >> p & 1)]
    assert min(hits) == 2
    assert sum(n >= 3 for n in hits) == 6

counts = Counter(sum(not (e & (a | b)) for e in edge_masks)
                 for a in quadrangles for b in quadrangles)
assert min(counts) == 6
print(dict(sorted(counts.items())))
