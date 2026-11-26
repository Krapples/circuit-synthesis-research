# L-meta-9791, a 24-vertex bipartite edge function

The posted target is a monotone AND/OR circuit with at most 53 gates for
44 edges. Eleven right-hand vertices have degree four. Every pair of their
neighborhoods meets in exactly one vertex. The unrestricted target is open.

Eleven right-hand stars give a Lean-checked 54-gate circuit in
`Near9791.lean`. Each star uses three ORs and an AND, and ten ORs collect
the terms. The adjacent script
`build-near-9791.py` independently evaluates its gate list against
the 44 minimal positive and 423 maximal negative rows. Monotonicity extends
that evaluation to the whole function. The matching
`(0,15), (1,16), (2,13), (3,14), (4,19), (5,20), (6,17), (7,18), (8,23), (10,21), (11,22)`
and the full right part give matching Lean-checked bounds of eleven for vertex
cover. This is a cover result and an unrestricted circuit upper bound.

## Exact projection of the pinned family

The pinned prefix computes the OR of selected right-hand stars, joined to
the suffix by the final OR. Fix the pinned right inputs to zero and every
left input unused by the residual stars to one. The suffix still computes
the residual edge function. The prefix star terms and their collectors
become zero. Each pure prefix OR either becomes one or still computes
exactly the original disjunction on active raw inputs. Constant propagation
leaves a suffix with at most the original gate count and access to just the
active raw inputs and these surviving providers. Conversely, any projected
solution using the original providers lifts by wiring them to its suffix.

For a residual right vertex `b`, a surviving provider contains at least two
left vertices and meets `N(b)` in at most one. Set only `b` to one on the
right and all left vertices outside `N(b)` to one. Starting with every left
vertex in `N(b)` at zero, toggling just `a ∈ N(b)` changes the output while
every provider stays fixed. The raw input `a` must occur directly even
when these providers are freely available. The analogous right-input
requirement follows because the providers depend only on the left.
`Providers9791.lean` kernel-checks the left-input argument and its linear
neighborhood hypothesis.

If the output cone has `k` fan-in-two gates and `p` distinct source wires,
it has `p+k` vertices, at most `2k` edges, and is connected. Thus
`p ≤ k+1`. Equality forces a tree with each source occurring once.
With nine frozen stars, the remaining two stars have nine active inputs and
only eight suffix gates. This would force a read-once formula with no
providers. Each residual pair contains an induced four-vertex path, obtained
by keeping the shared left vertex, both right vertices, and one private
left neighbor. Pinning all other inputs to zero and simplifying preserves
the read-once property. The path edge function is not read-once. An OR
root would split the connected graph because singletons are all negative
and crossing edges would be uncovered. An AND root requires every edge
to cross the partition. Each vertex has an edge, so its singleton is
accepted by its own branch and every crossing pair becomes an edge. A
four-vertex path has no such complete bipartite partition. Thus every
two-star residual needs at least nine suffix gates.

## SAT records

All batches used 22 worker processes and the repository's fan-in-two
encoding. The initial fixed-prefix CEGAR screen and two matched projected
screens each left all 22 selected prefixes open at 105 seconds per solve.
The three screens used 16 prefixes of eight stars, four of seven stars,
and two of six stars. Their suffix budgets were 13, 18, and 23.
`search-9791-direct.jsonl` adds the proved direct raw-input condition to
the middle screen. The separate pair batch reports 55 UNSAT verdicts
with a 65-second solve cap. It makes the unique useful two-leaf provider
available from each frozen star whenever such a pair survives. The
independent argument above proves the entire pair exclusion. These runs
did not retain SAT proof traces or measure peak memory.

Among the 165 three-star cores, 135 have three distinct pair intersections
and 30 have one common intersection. They have 12 and 13 raw inputs,
respectively. At 11 or 12 gates, respectively, the same read-once argument
excludes the core, since restricting the third right input to zero leaves
an induced four-vertex path. The canonical SAT batch allowed every surviving
two- or three-input disjunction consistent with the intersection condition
as a free provider and bounded used providers by the source-count slack.
Its 22 runs across both shapes and five solvers reached the 150-second cap.
The full 13-gate three-star scopes remain open.

Run from the research repository root, with the same Python environment
as `sat-search/cube_search.py`. Pass a fresh path for each output.

```powershell
$dir = 'sat-search/results/c4free_9791'
python -B "$dir/search-9791.py" "$dir/replay-baseline.jsonl"
python -B "$dir/project-9791.py" "$dir/replay-projected.jsonl"
python -B "$dir/project-9791.py" "$dir/replay-direct.jsonl" --direct
python -B "$dir/project-9791.py" "$dir/replay-pairs.jsonl" --pairs
python -B "$dir/triple-9791.py" "$dir/replay-triple.jsonl"
```

The matched projections use the baseline prefix and seed manifest beside
the scripts. Run `lake env lean` on `Cover9791.lean`,
`Providers9791.lean`, and `Near9791.lean` from the public project's Lean
directory.
