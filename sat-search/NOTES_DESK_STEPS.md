# Desk step results

Per-step results for desk and meta steps. Moved word for word from the root RESEARCH_NOTES.md on November 27, 2026.

For the one-hot bipartite representation in L-meta-20754, Lean checked an
eight-gate witness on all 25 promised pairs and proved that seven gates
are impossible in the exact repository model. The lower bound uses
monotone separation and a checked reverse-demand argument that reduces
the circuit to ordinary or once-shared read-once formulas.
[Exact model, axiom audit, and search records](results/promise_5x5_20754/README.md)

For 40 desk rect templates (rect46/rect45b, one-hot promise rows, monotone; solver verdicts only,
no certificates), the native exact search finds 24 steps UNSAT at budget and 16 open at sizes
10-11. An exact tree-decomposition DP (all inputs essential; program verdict) closes 11 more at
n-1+2 gates, with 146/146 agreement with SAT minima. Its generic s ≤ 3 version with checked witnesses
agrees on all 1656 3x3/3x4 targets and shows rect45b 21279, 21288 and 21319 have no circuit of ≤ 11
gates, so all 20 rect45b steps are unreachable at budget. The s = 3 lower-bound direction has no SAT
cross-check. Open: rect46 22162 and 22172 at size 12, where s = 3 needs more than 64 GB.
[Verdicts, scope and runs](results/templates_native/rect_2026-11-27/README.md),
[DP proof](results/templates_native/rect_2026-11-27/TREE_DP.md)

For the cubic-graph case L-meta-5020, Lean checked that a false restriction at the
designated two-reader input saves four gates or leaves one of two local reader
patterns. An exclusive internal operand of the AND reader also yields a
four-gate saving. [Reader analysis and proof scope](results/cubic_gate_elimination_5020/README.md)
[Submitted reduction](https://github.com/open-goat/pequalnp-proofs/pull/22538)

For the 24-vertex bipartite graph in L-meta-9791, Lean checked a 54-gate
witness, also evaluated on the complete monotone boundary. The two-star suffix of any nine-star
fixed prefix needs at least nine further gates before the final OR.
The unrestricted 53-gate budget remains open.
[Projection, lower bound, and search records](results/c4free_9791/README.md)

For the two-output quadrangle separator L-meta-5258, a source-count
bound and induced-path restrictions exclude the posted budget within
all same-side pinned prefixes leaving two or three stars. Lean checked
a gate-criticality condition for minimum-size realizations.
The unrestricted sub-63-gate case remains open.
[Quadrangle tests, scoped bounds, and search records](results/pg3_quadrangles_5258/README.md)

For deleted-line Heawood incidence L-meta-9748, the merged full-graph
bound gives a Lean-checked monotone minimum of 23 together with
an independently evaluated upper bound. Even-path and source-count
arguments exclude the 22-gate budget in the pinned right-star
families with two or three stars left. The unrestricted counted-NOT
budget remains open.
[Basis-specific bounds and search records](results/deleted_heawood_9748/README.md)

For order-four incidence L-meta-4653, the checked conjunction-list
normalization preserves the number of OR gates and exposes the exact
monotone boundary. The 105 positive rows pair with 25,237 maximal
negative rows in 10 projective-symmetry orbits. Lean checked a uniform
40 lower bound for the straight-line AND/OR and common vertex-cover union
models, the surrogate leaf projection, and 104 union instructions when the
marked operand centers induce a forest. Any shorter program would give a
relative OR saving on a cyclic subgraph supported entirely on marked centers.
The unrestricted bound of 104 remains open.
[Reduction audit, geometry, proof, and diagnostics](results/pg4_or_4653/README.md)

For the eleven-vertex top-form graph in L-meta-4081, Lean checked the edge-charge inequality
with at most four uncovered edges. It also checked that one mixing OR with support of size
at least two forces all uncovered edges to share a vertex when there are no centreless tops.
Structural SAT excluded counterexamples through 12 gates and timed out at sizes 13–21.
[Routing proofs and search records](results/top_form_4081/README.md)

For the Petersen OR-substitution case L-meta-7893, Lean checked a 20-gate expanded circuit.
The same cost is optimal when the retained and deleted edges use separate star covers.
The posted 19-gate limit remains open. [Guard restrictions, witness, and search records](results/petersen_guard_7893/README.md)

The one-hot bipartite representation probe L-meta-11869 has a computational lower bound of 17
and a Lean-checked upper bound of 30 AND/OR gates. The requested budget of 20 remains open.
[Representation probe](NOTES_SYNTHESIS_FOLLOWUP.md#one-hot-bipartite-representation)

The deleted-point projective-plane probe L-meta-2216 has a Lean-checked 62-gate two-output
construction and a matching 62-gate lower bound when the graph-output cone is single-level.
The unrestricted budget of 61 remains open. [Witness, proof scope, and SAT records](results/pg3_deleted_point_proxy_2216/README.md)

For the six-input table in L-meta-16102, Lean checked an eight-gate monotone construction.
Two synthesis encodings exclude the requested nine-gate circuit with a NOT reading a gate.
The exclusion is computational evidence. [Exact syntax, coverage, and replay](results/mid_not_16102/README.md)
Update (2026-11-26): Lean now proves that at least 8 binary gates are needed even with free NOTs (`SatBridge.Meta16102Aig.hA`, a first-gate recursion certificate over 95 tables, standard axioms only); `posted_core_closed` carries the reduction. It leaves only the nine-gate excess-3 core, and all 22 first-gate shards of that core have drat-trim-checked DRUP UNSAT proofs. The posted statement is existential and, on this evidence, false. It has no refute twin and is no longer on the desk board, so no upstream PR is possible. [Audit and certificates](results/mid_not_16102/core9_certificate_audit.md)

For the Fano incidence function in L-meta-4874, Lean checked a 28-gate circuit with
the required final AND and singleton constraints. A 28-gate lower bound applies to a
factorized star-cover form. The unrestricted budget of 27 remains open.
[Proof, witness, and search coverage](results/fano_final_and_4874/README.md)

The order-three projective-plane step L-meta-9063 has a merged reduction
to two six-line circuits with budgets 28 and 29. The 29-gate child L-meta-17643
has a merged proof. The 28-gate child L-meta-17641 and the 14-gate probe of its
smaller seeded grid remain open. [Merged reduction](https://github.com/open-goat/pequalnp-proofs/pull/22166)
[Merged 29-gate proof](https://github.com/open-goat/pequalnp-proofs/pull/22337)
[Reduction, search coverage, and related accepted methods](results/pg3_seeded_boundary_9063/README.md)

For L-meta-3754, the clean region of a least, lift-fixed circuit in the
upstream exact fan-in-two AND/OR model has exactly `T - 1` clean OR gates
for `T` clean AND gates, with natural-number subtraction. Global liveness
and a concrete strict deletion for singleton overlap without exposed
centres are also Lean-checked. The remaining one-junk replacements are open.
[Collector proof and verification scope](chatgpt_handoff/meta3754_collector_accounting.md)

For L-meta-3754, `oneJunkSupportsDisjoint` rules out all overlap between
the raw operand supports of the unique dirty AND in a least lift-fixed
exact fan-in-two AND/OR circuit on a bipartite C4-free graph. Lean checks
the singleton case using the merged L-meta-4745 and L-meta-4746 reductions
plus a local bypass. The independent gate-list rebuild `noTwoOverlap`
handles larger intersections and preserves shared providers.
`oneJunkLargeOppositeSupports` uses L-meta-4747, L-meta-4743, and L-meta-4712
to force both supports to have at least two vertices and to lie entirely
in opposite colour classes. A gate reader exposes a vertex adjacent to
every vertex in the other support. The strict circuit replacement for this
remaining one-junk shape starts from `lostEdgesInExposedStars`: setting the
junk to false loses edge inputs only in at most two clean stars.
`compileFalseSuspension` compiles the suspended circuit without constants,
preserves wire values, and charges the suspended junk and every gate
with a false operand on the all-true input. The compiler and star repair
proofs use only Mathlib and `PEqualNP.Defs`. Lean checks strict replacement
when no edges are lost or one star suffices with two immediate readers.
`oneJunkAtMostTwoReaders` rules out three or more immediate readers.
When both repair stars are needed, the replay trims one operand of an
exclusive provider OR, preserves the opposite provider and the
suspended output, and covers all missing edges with at most four new
gates. Three readers, the suspended junk, and the trimmed OR pay for at
least five deletions. The remaining lower-reader cases and the
many-junk reduction are open in Lean.
[Overlap proof and verification](chatgpt_handoff/meta3754_two_overlap_handoff.md)
