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

## Protected provider reconstruction

- `AvoidJunk` describes a path from a wire to the output avoiding the junk
  after the starting wire. The proof retains all protected pre-junk gates
  with their original values. They form an ancestor-closed prefix selection.
- `protectedPureSupportNeighbour` proves that a protected dirty OR's raw
  support is contained in a single neighbourhood. A path avoiding the junk
  reaches a first clean top. If this path ran through the opposite operand
  of a junk-carrying top, that operand would be the raw centre wire, which
  cannot have a gate ancestor. In the other cases a clean raw product
  supplies the required neighbourhood.
- The compiler computes the masked value of each needed wire separately
  from its original value. A protected OR supported in `N(c)` can reuse its
  original wire. For a different neighbourhood centre, C4-freeness bounds
  its intersection with `N(c)` by one vertex, so the compiler uses a raw
  alias or represents false without a gate. Each unprotected prefix OR
  costs at most one replacement gate. The two selected index sets partition
  the prefix, so the rebuilt prefix costs at most the original prefix length.
- `replayJunkSuffix` redirects the removed junk to the filtered wire and
  replays the suffix one gate per original gate. Its shadow valuation gives
  the interface required by `overlapRedirect`, which preserves the edge
  function on every assignment. `noTwoOverlap` concludes by leastness, since
  the rebuilt gate list has at least one fewer gate. It covers the branch
  with no earlier filtered wire as well as the two special cases above.

## Independent circuit controls

When `c` is outside both supports, the original raw provider need not already
equal its filter. For example, take five distinct vertices `c,u,v,a,b` and the
C4-free bipartite graph with edges `c-u`, `c-v`, and `a-b`. Set
`A = {u,v,a}` and `B = {u,v,b}`. The local top
`x_c AND OR(A) AND OR(B)` is clean. Replacing the junk by the unfiltered
`OR(A)` accepts the nonedge pair `{c,a}`, and using `OR(B)` accepts `{c,b}`.
This is a local semantic control, with no claim that the displayed circuit
is least or computes the entire edge function.

The shared-provider replay checks a six-vertex path graph with exactly one
dirty AND. It checks all 64 inputs. The protected rebuild uses seven gates
in place of ten and preserves the function. Overwriting the shared provider
loses three positive inputs. Reusing the unfiltered operand creates one false
positive. Retaining all providers and appending the filter gives a ten-gate
equivalent circuit. [Manifest](../results/meta3754_shared_provider/batch.json)
and [recorded outcomes](../results/meta3754_shared_provider/replay.json).

## Singleton overlap follow-up

`uniqueExposedOverlapCentre` checks the exposed-centre geometry. Each opposite
support is contained in the neighbourhood of the shared vertex. A centre
exposed in one operand is adjacent to all of the other operand. When each
operand has a second vertex, C4-freeness gives uniqueness within each type.
Triangle-freeness rules out both types occurring, since they and the shared
vertex would form a triangle. The proof checks these conditions starting from
the clean-top semantics.

`protectedSharedSupport` follows an output path avoiding the junk to the
first clean AND. The shared singleton input rules out an opposite operand
carrying the junk. The remaining raw product yields a common neighbour, and
its contribution is preserved by every evaluation satisfying the original
gate equations away from the junk. `adjacentSharedProviderExclusive` uses
triangle-freeness to rule out such a path for a provider containing the shared
vertex and the adjacent exposed centre. `protectedSharedStarSurvives` shows
that a protected provider containing the shared vertex and a second vertex
already supplies its entire star at the exposed centre, using C4-freeness
to identify the common neighbour.

For the other provider, the
[strict trim plan](lean/OneJunkProviders.lean) must be attached to the actual
retained wires and the cost of adding a clean star. The exposed singleton
replacement, disjoint-support branches and the many-junk case remain open.

## Verification

The complete [OneJunkErase.lean](lean/OneJunkErase.lean) source passed the
pinned Lean `v4.36.0` environment documented in the collector handoff,
using the strict research runner from the repository root.

```powershell
python -B sat-search/workflow/research.py lean .research/one-junk-upstream/lean --source sat-search/chatgpt_handoff/lean/OneJunkErase.lean --strict --timeout 240
python -B sat-search/results/meta3754_shared_provider/replay.py
```

For the multiple-overlap checkpoint, Lean ran for 66.507 seconds with
warnings treated as errors. All 34 printed declarations, including
`noTwoOverlap`, used only `propext`,
`Classical.choice`, and `Quot.sound`. The checked source SHA-256 is
`68588953fad1132afc95e7440c16f2c66b12c3e6a2a3d187f74ba41785b5cf78`.
The local strict-run evidence is in
`.research/ops/1795765643102984300-lean-check/`. The earlier 52.826-second
check covered a smaller source and is a separate verification record.

The follow-up check took 68.142 seconds with the same settings and passed
all 35 axiom audits, including `uniqueExposedOverlapCentre`. The checked
source SHA-256 is
`23b0de0bcd48c5291d2582c359b3abd7429d043158b7e3a0be50931144318a71`.
The local evidence is in `.research/ops/1795765822150491100-lean-check/`.

The protected-provider check took 71.988 seconds with the same settings and
passed all 38 axiom audits. The checked source SHA-256 is
`8040125fb4208026d9d831712d9d9986a2c4b3b4d6ef1f38014f2c7343f4b811`.
The local evidence is in `.research/ops/1795766092882371500-lean-check/`.
