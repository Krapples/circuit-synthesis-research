# Fano incidence with a final AND

L-meta-4874 asks whether a 14-input monotone AND/OR circuit with at most 27 gates can
compute the Fano incidence edge function with a final AND whose parents both vanish
on singleton inputs 0 and 7. Points are wires 0 through 6 and lines are wires 7
through 13. Point p is incident to line l when p − l modulo 7 is 0, 1, or 3.
The 21 edge pairs and 37 maximal independent sets characterize the function on the
full cube by monotonicity.

## Verified upper bound

Let H be the OR of the six line stars other than the line on wire 8. The six
stars cost 18 gates and their OR costs 5. The remaining line is incident to
points 1, 2, and 4. The circuit

```text
(H OR x8) AND (H OR (x1 OR x2 OR x4))
```

costs five more gates and both operands vanish at the required singletons.
The JSON witness was independently checked on all 16,384 inputs.
Lean 4.36.0 checked [Upper28.lean](Upper28.lean) against the project definitions.
Its theorem uses only the standard axioms `propext`, `Classical.choice`, and
`Quot.sound`.

## Lower bounds and scope

Each final parent must structurally read both marked inputs and their four other
neighbors. Otherwise an incident pair would have the same value as its marked
singleton. Its support must also be a vertex cover, since the parent is false
on the empty input and true on every edge. The remaining induced graph has a
matching of four edges, giving at least ten support variables and at least
nine gates per parent cone.

At least one parent must read all 14 variables. For every distinct pair of
inputs there is a restriction of the others under which the function is the OR
of the pair. On one side of the incidence graph, set one neighbor of each
variable to one. For opposite sides, choose a neighbor of each variable other
than its partner, with no edge between the chosen neighbors. Such a choice
exists because each variable has degree three and the graph has no 4-cycle.
If opposite parents omitted different variables, their AND on this restriction
would be a product of separate unary functions and could not equal OR.
The SAT support experiment checks all 91 restrictions by enumeration.

A 28-gate minimum holds within the form `(H OR A) AND (H OR B)` where H is a
single-level star cover, A and B are pure input disjunctions, and the two
parent OR gates and the final AND are separate. The cover consists of k stars
from H plus the rectangle A×B. That rectangle is a star since the Fano graph has
no 4-cycle. The incident edge matching requires at least seven star centers,
so k is at least six. Across k+1 star neighborhoods, disjunction gates cost
at least 21 − (k+1). For each center, a union of d distinct leaves at r roots
requires at least d − r joins. Distinct centers cannot share a disjunction
of two or more different leaves, since their neighborhoods intersect in at
most one variable. Adding k star AND gates, k−1 aggregation OR gates, and
the three final gates gives 21+k+1 ≥ 28.

## Search coverage

| Portfolio | Coverage | Outcome |
| --- | --- | --- |
| Left root split | All 33 normalized left-root choices at sizes 26 and 27, 95 s per active solve | 33 open |
| Parent support clauses | 22 reinforced left-root shards, 110 s per active solve | 22 open |
| Six-line completion | 22 restricted 22-gate final-OR windows with two to four frozen stars | 8 UNSAT, 14 open |
| Full Fano completion | 22 restricted 27-gate final-AND windows with three to five frozen stars | 8 UNSAT, 14 open |
| Deletion and rewrites | 22 seeded 65 s runs from the 28-gate witness | One boundary error at best |
| Exact repair | 22 windows around the near witness, each freeing the final ten gates and three to seven earlier gates, 45 s per solve | 22 open |

The window exclusions concern only the stated pinned templates. SAT certificates
were not retained. The unrestricted 27-gate budget remains open.

Run the archived Python scripts with PySAT available through the workspace
environment and pass a new output JSONL path as the sole argument. Each SAT
portfolio uses 22 worker processes. Seeds, elapsed times, and available solver
statistics are stored next to the corresponding scripts.
