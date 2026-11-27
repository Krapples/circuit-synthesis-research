# L-meta-3754 multiple-vertex overlap

This continues [the clean OR collector result](meta3754_collector_accounting.md)
and Section 3a of [the one-junk paper proof](meta3754_one_junk_complete_handoff.md).
The scope is a least lift-fixed exact fan-in-two AND/OR circuit for the edge
function of a C4-free simple graph, with exactly one dirty AND gate. Write
`A` and `B` for the raw supports of its operands and suppose their intersection
contains two distinct vertices. This part uses C4-freeness and does not need a
bipartition.

## Proof milestones

- `twoOverlapCommonCentre` gives a unique common neighbour `c` of the two
  overlap vertices. Leastness forces at least one clean top to carry the junk.
  Otherwise redirecting the junk to an earlier raw input leaves every top
  value and hence the output unchanged. Each vertex in the opposite support
  of any carrying top is adjacent to both overlap vertices. The opposite
  support is nonempty, by evaluating that top on all ones. C4-freeness then
  forces it to be `{c}`.
- `twoOverlapOppositeRaw` identifies the actual opposite operand wire as
  raw input `c`. An internal gate realizing the same singleton function
  would duplicate that earlier wire, contradicting leastness. This rules
  out an internal protected provider on the opposite side of a carrying top.
- `overlapRedirect` establishes the semantic specification of a replacement.
  Choose an operand support `R` omitting `c` and replace the junk signal with
  the OR of `R ∩ N(c)`. Every new positive contribution contains an edge at
  `c`, and every true edge input that used the junk still fires a clean top.
  For the latter, the edge contains `c` and the original junk supplied an
  active vertex in `R`. This vertex must be the other endpoint. The terms
  from raw support on the carrier side are preserved directly.
- `noTwoOverlapWithEarlierFilter` implements this replacement when the
  filtered OR is already available as an earlier wire with the indicated
  raw support. The circuit uses the upstream erasure and reindexing, computes
  the same edge function on all inputs, and is exactly one gate smaller.
- `noExposedTwoOverlap` closes the subcase in which `c` occurs in either
  operand support. If `c ∈ A`, a carrying top tested on `{c,b}` for each
  `b ∈ B` proves `B ⊆ N(c)`, so the existing `B` operand already is the
  required filtered wire. The other orientation is symmetric.

## Remaining construction

When `c` is outside both supports, the original raw provider need not already
equal its filter. For example, take five distinct vertices `c,u,v,a,b` and the
C4-free bipartite graph with edges `c-u`, `c-v`, and `a-b`. Set
`A = {u,v,a}` and `B = {u,v,b}`. The local top
`x_c AND OR(A) AND OR(B)` is clean. Replacing the junk by the unfiltered
`OR(A)` accepts the nonedge pair `{c,a}`, and using `OR(B)` accepts `{c,b}`.
This is a local semantic control, with no claim that the displayed circuit
is least or computes the entire edge function.

The uncovered branch is the unexposed centre with no earlier wire for either
filter. The next proof needs to identify protected original OR gates from
paths avoiding the junk, account for the exclusive provider gates available
for rebuilding, and connect that gate-list construction to `overlapRedirect`.
The [checked support compiler](lean/OneJunkProviders.lean) provides the
filtering cost once those conditions are supplied. The remaining one-junk
branches and the full L-meta-3754 theorem are open.

## Verification

The complete [OneJunkErase.lean](lean/OneJunkErase.lean) source passed the
pinned Lean `v4.36.0` environment documented in the collector handoff, in
52.826 seconds with warnings treated as errors. All 27 printed declarations,
including the five new audits, used only `propext`, `Classical.choice`, and
`Quot.sound`. The checked source SHA-256 is
`433ba60bc40627003cc22333e3cfcf88412a0a0cabb354f0178a80434a653e57`.
