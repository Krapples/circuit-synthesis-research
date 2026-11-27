# L-meta-20754 one-hot representation

The posted positive statement asks for at most seven monotone AND/OR gates
on the one-hot promise for the 5 by 5 table with row-major mask 12815360.
The five rows are `00000`, `00000`, `11000`, `11100`, and `00110`.

The last three rows and first four columns suffice for a lower bound. On
these twelve assignments the seven live input columns have masks
`15, 240, 3840, 273, 546, 1092, 2184`, and the target has mask `3187`.
[ActiveBudget.lean](ActiveBudget.lean) checks that a straight-line program
of seven binary AND/OR gates starting with these inputs and both constants
cannot produce the target. Its operands may repeat, missing operands read
zero, and any wire may be the output. Lean checks the SAT certificate
through `bv_decide`. On the pinned Lean 4.36.0, the tactic checks the LRAT
certificate with compiled code and introduces an axiom. This gives
certificate-backed computational evidence for the exclusion. The
project's kernel-only submission rules disallow the tactic.

[ExactModel.lean](ExactModel.lean) links the packed checker to the
project's `RepSizeAtMost` definition. It maps inactive and missing wires to
zero, replaces a unary copy by two reads of one wire, and supplies the
appropriate constant for a nullary gate. Padding shorter programs leaves
their chosen output unchanged. The same file gives the explicit eight-gate
circuit on all 25 promised assignments. The axiom audit of the projection
reported only standard Lean axioms, and the upper bound used only `propext`.

## Kernel proof

[ReadOnce.lean](ReadOnce.lean) proves the two terminal exclusions. In a
candidate OR split, both children are false on every negative row. If
some positive row projects below a negative row on each child's inputs,
both children are false there too. The dual obstruction applies to an
AND split. These two tests eliminate all root partitions of the
ordinary read-once case.

For the shared case, consider any positive and negative pair whose
outside inputs are ordered. The shared subformula must be true on the
positive and false on the negative, or the outside formula would be
monotone on that ordered pair. If an ordered pair of these forced
labels is also comparable on the inside, the whole module support is
excluded. This leaves fourteen proper supports, with one candidate
value each. The full-support case reduces to idempotence of AND and OR.
For the remaining formulas, Lean splits the output rows that either
child may witness, assigns the others to both children, and prunes
inconsistent assignments by monotonicity. The completeness theorem
for this search uses the formula's actual values as witnesses. The
[independent cofactor probe](cofactor_probe.py) confirms the fourteen
candidates and checks them against 429 surviving requirements.

[TraceDemand.lean](TraceDemand.lean) walks backwards through the
gate outputs. A demand is a multiset of truth tables, and duplicate
outputs that were previously available can be discarded. Replacing all
`k ≥ 1` demands for a gate's result by one demand for each operand
increases the multiset size by `2 - k`. Charge `k - 1` for this
transition and one for an unused gate. Including the charge, each
gate increases the size by one. Monotone separation forces all seven
active inputs into the final demand, so a program with at most seven
gates can pay at most one charge. One repeated internal demand yields
the paired formula. With no repeated internal demand, the output is
one formula with at most eight leaves. The possible extra leaf is
either a second occurrence of one active input or a constant, which
can be simplified away.

[KernelExact.lean](KernelExact.lean) connects the packed evaluation to
the distinct-result rule trace and gives the exact negation of the
posted seven-gate statement. The eight-gate circuit in
[ExactModel.lean](ExactModel.lean) gives the matching upper bound.

Run `python -B sat-search/results/promise_5x5_20754/replay.py` from the
research checkout with the proofs checkout at `pequalnp-proofs/` and its
pinned Lake and Mathlib environment available. The runner keeps the Lean
output and axiom report under `.research/ops` and fails the kernel run
if an audited theorem uses a generated axiom. The complete kernel replay
took 28.43 seconds. The lower bound uses only `propext`,
`Classical.choice`, and `Quot.sound`. Use `--mode diagnostic` to replay
the earlier LRAT comparison.

The desk offered a positive prove lease and listed no refute twin. After
the kernel audit passed, the desk acknowledged the official
`statement_seems_false` release on November 26, 2026 (Mountain time).

## Independent mathematical reduction

For each live input, a positive column and a negative column form a
monotonicity obstruction if that input is ignored. Index the twelve
assignments from zero in row-major order, and write the triples as
(live input, positive assignment, negative assignment). The seven pairs are
`(0,0,8)`, `(1,4,8)`, `(2,10,2)`, `(3,0,2)`, `(4,1,2)`,
`(5,6,7)`, and `(6,11,8)`. In each pair the positive assignment is
coordinatewise at most the negative assignment after its designated input
is deleted. Every monotone extension of the restricted promise therefore
uses all seven live inputs.

Delete dead gates and propagate constants, unary copies and repeated
operands. Count edges with multiplicity from a source to its uses. A
rooted cone on seven input vertices and `s` binary gates has `2s`
edges, with each non-root vertex used at least once. The sum of the
excess uses is `2s - (7 + s - 1) = s - 6`. For `s ≤ 7`, the
normalized circuit is a read-once formula or has precisely one vertex
used twice. In the latter case the subcircuit feeding that vertex is
read-once, and replacing its two uses by separate leaves makes the outer
circuit read-once. The module and outer formula use disjoint sets of
original inputs, since otherwise a second vertex would be read twice.

[read_once_core.py](read_once_core.py) enumerates read-once functions on
multisets of truth vectors by all distinct unordered root splits. It
checks all nonempty sets of input variables for the reused module and
passes each distinct module value twice into the corresponding outer
multiset. Its result gives 1,780 ordinary read-once truth vectors and
8,724 module choices across all subsets. Neither case reaches 3187.
Run it through [read-once-batch.json](read-once-batch.json) or directly
with Python. The [recorded result](read-once-result.json) is independent
computational evidence.

The original partial-label SAT search has 22 terminal-selection shards.
All returned UNSAT in 10.874 seconds wall time. That run used MapleChrono
and generated no proof trace.
