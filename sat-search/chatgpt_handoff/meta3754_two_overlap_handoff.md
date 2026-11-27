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

`exposedSingletonRedirect` classifies the edges potentially lost by
replacing the junk with the shared input. Every lost edge joins the exposed
centre to a non-shared vertex in the opposite provider. The redirected
evaluation remains sound on every input. `noExposedSingletonProtectedProvider`
closes the case where the opposite provider is protected: its raw product
already covers those edges, so the shared-input alias deletes one gate and
requires no replacement star.

When the opposite provider is unprotected, the
[strict trim plan](lean/OneJunkProviders.lean) must be attached to the actual
retained wires. `firstUnprotectedSingletonOr` follows the active wire on
the shared singleton input back to an unprotected OR with an active raw or
protected operand. The shared raw input is omitted. If the operand is a
protected provider, its star is already covered. Either way, the trimmed
OR can reuse its other operand once the concrete trim marks this input as
false. `compileAvailablePrefixBudget` excludes such an OR from the appended
gate count. `noExposedSingletonWithTrimmedStar` checks the other end of the
construction. Given a redirected circuit with at least three gates removed
and a wire for the trimmed support that covers the missing edges, it appends
one AND and one OR and proves that the result computes the graph edge function.

To finish that standalone construction, compute the per-wire trimmed supports,
prove coverage of every omitted contribution, and bind the two skipped
prefix indices to the mixed root and the zero-cost OR. The replay must
carry the trimmed wire's value through the suffix to the final star.

## Bridge to the upstream reductions

The [local bridge](upstream/OneJunkUpstream.lean) uses the merged
[L-meta-4745](https://github.com/open-goat/pequalnp-proofs/blob/3db0136bf094e975baaf20214b01e4b4579059f2/lean/PEqualNP/Outside/L_meta_4745.lean)
and [L-meta-4746](https://github.com/open-goat/pequalnp-proofs/blob/3db0136bf094e975baaf20214b01e4b4579059f2/lean/PEqualNP/Outside/L_meta_4746.lean)
in the exposed singleton case. The two reductions split on whether a
junk-carrying AND reader has an opposite operand activated by both the
exposing unit input and a second unit input. Each returns a strictly smaller
circuit in the same exact AND/OR basis that computes the full graph function.

For the case with no exposed reader, suspend the junk equation, set its
value to true, and set every raw input to false. A dirty operand with its
junk flag set evaluates to true. Tracing that value backwards through
strictly earlier dirty wires gives an OR path to the unique dirty AND.
This connects the local semantic flag to the upstream reader predicate and
discharges the premise of the checked no-exposure bypass.

`oneJunkSupportsDisjoint` combines that singleton argument with
`noTwoOverlap`. Under leastness, lift fixedness, C4-freeness, a proper Boolean
two-colouring, and exactly one junk AND, the two operand supports are
disjoint. `oneJunkFalseOnUnit` packages the consequence that the junk is false
on every unit input. Applying
[L-meta-4747](https://github.com/open-goat/pequalnp-proofs/blob/3db0136bf094e975baaf20214b01e4b4579059f2/lean/PEqualNP/Outside/L_meta_4747.lean)
contrapositively then gives `oneJunkHasEdgeReader`. A remaining candidate
must have a clean AND later than the junk, an OR path from one of its
operands to the junk, and an edge `{u, z}` on which the junk is true and
the other operand is already true at the unit input `z`. This witness
identifies a case to analyze in the disjoint-support replacement. It does
not assert that the edge would be lost on deleting the junk, since the
same reader or another reader may cover it.

`oneJunkLargeOppositeSupports` uses that witness to narrow the two raw
supports further. If the exposing vertex `z` belongs to one support,
pairing it with any vertex of the other support makes the junk and the
clean reader true. The clean reader forces adjacency to `z`, so all
vertices of the opposite support have the same colour.
[L-meta-4743](https://github.com/open-goat/pequalnp-proofs/blob/3db0136bf094e975baaf20214b01e4b4579059f2/lean/PEqualNP/Outside/L_meta_4743.lean)
excludes a mixed-colour support paired with a monochromatic one. The edge
witness puts the two monochromatic supports in opposite classes.
[L-meta-4712](https://github.com/open-goat/pequalnp-proofs/blob/3db0136bf094e975baaf20214b01e4b4579059f2/lean/PEqualNP/Outside/L_meta_4712.lean)
then excludes a singleton on either side. The theorem keeps the exposing
vertex and its reader as witnesses for the next circuit-replacement proof.

The bridge is a local research dependency on accepted upstream modules.
Check the desk's permitted imports for the exact submission before using
this dependency there. The remaining one-junk case has two large disjoint
supports in opposite colour classes, with at least one exposed centre.
The strict replacement must account for shared OR providers and the
gate budget. The many-junk reduction also remains open in Lean.

## Suspended circuit and strict repair

`lostEdgesInExposedStars` gives the classification used by the
[paper argument](meta3754_one_junk_complete_handoff.md#5-disjoint-large-supports-exposed-stars-and-deletion-budget).
For any valuation satisfying the original gate equations apart from the
junk set to false, an edge input that is lost must hit a raw support of
each junk operand. A firing clean AND in the original circuit supplies
an exposing endpoint in one of those supports. Its opposite endpoint
lies in the other support. Each exposed endpoint is adjacent to every
vertex of its opposite support, and C4-freeness bounds each support to
one such endpoint. The soundness result `suspendedFalseSound` holds on
every input and requires neither support-size nor colour hypotheses.

`compileFalseSuspension` compiles this valuation back into the exact
constant-free model by inductively appending AND and OR gates. It
certifies each original wire as identically false or represents its
value by an available wire in the compiled gate list. It charges the
junk and every gate with an operand false on the all-true suspended
input. An immediate reader AND becomes false and a reader OR forwards
its other operand, so each saves a gate.

`noOneJunkWithoutLostEdges` closes the case where all edge inputs survive.
`noOneJunkOneStarWithTwoReaders` closes the case where one star covers
all lost edges and at least two distinct gates read the junk directly.
The compiler keeps a wire for the opposite support. The repair adds an
AND and, when the suspended output is nonzero, an OR. At least three
original gates are charged and at most two are added. The edge-input
coverage test and monotonicity establish equality on the whole input cube.
The repair compiler now accepts a list of stars. Each star reuses
its provider wire and costs one AND with at most one OR. The first
star needs no collector OR when the suspended output is false. The
compiler preserves previously available providers across appends.
`noOneJunkWithStarBudget` checks function equality and strictness for
these budgets. The existing one-star theorem uses the same proof.

`oneJunkAtMostThreeReaders` applies the compiler to the at-most-two-star
classification and charges the junk and all of its immediate readers.
Four readers give at least five charges against a maximum repair cost of
four. `oneJunkReaderBudget` rules out three readers when the suspended
output is false, since the two-star repair then costs at most three.

The false-operand accounting can also charge downstream gates. When
an immediate AND reader becomes false and the suspended output survives,
that AND is clean and has a downstream clean OR reader. The OR cannot directly
read the dirty junk because its operands are clean. It supplies a
distinct extra charge. `oneJunkAtMostTwoWithAndReader` therefore rules
out three readers including an AND. The remaining three-reader shape
has three OR readers, a nonzero suspended output, and requires both
stars. The lower-reader branches and many-junk reduction remain open.

The suspended compiler and the underlying strict zero-, one-, and
two-star repair proofs are in the core file, which imports Mathlib and
`PEqualNP.Defs`. The local adapter applies them to the reader cases and
still imports five accepted upstream lemmas for the one-junk support
geometry.

For the three-OR branch, the remaining step is to save an exclusive OR
from one provider while preserving the other star and the surviving clean
products. Protection must follow uses in the suspended circuit. A path in
the original circuit can avoid the junk itself and still pass through an
AND whose other operand becomes false under suspension.

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

The alias and strict-deletion check took 73.501 seconds and passed all 40
axiom audits. The exact checked source was transferred from a scratch file
to `OneJunkErase.lean` with identical SHA-256
`440f6e90d55daf8d05a1d5b40741124b7638223dea7c569445e5020afbce05ff`.
The local evidence is in `.research/ops/1795766222329408600-lean-check/`.

The gate-budget and star construction check took 72.730 seconds and passed
all 43 axiom audits. The checked source SHA-256 is
`8b9e5838674130a76b2d0b4106350a8ecc50ae97776b36057ded9bf7a58d720e`.
The local evidence is in `.research/ops/1795766662384002400-lean-check/`.

To replay the upstream bridge, use the same pinned Lake project at
`3db0136bf094e975baaf20214b01e4b4579059f2`. A sparse checkout needs the
`PEqualNP/MetaComplexity/Helpers` directory, `PEqualNP/MetaComplexity/L2604.lean`
and the five imported `PEqualNP/Outside` files in addition to the
definitions. From the research repository root, run these commands with
the pinned dependencies available.

```powershell
$workspace = (Resolve-Path '.research/one-junk-upstream/lean').Path
$src = (Resolve-Path 'sat-search/chatgpt_handoff/lean/OneJunkErase.lean').Path
$srcRoot = Split-Path -Parent $src
$lake = Join-Path ([Environment]::GetFolderPath('UserProfile')) '.elan/bin/lake.exe'
foreach ($step in '4712', '4743', '4745', '4746', '4747') {
  python -B sat-search/workflow/research.py lean $workspace --module "PEqualNP.Outside.L_meta_$step" --timeout 240
  if ($LASTEXITCODE -ne 0) { throw "Upstream L-meta-$step build failed" }
}
Push-Location $workspace
try {
  & $lake env lean "--root=$srcRoot" '-DwarningAsError=true' -o '.lake/build/lib/lean/OneJunkErase.olean' $src
  if ($LASTEXITCODE -ne 0) { throw 'Local OneJunkErase module build failed' }
} finally { Pop-Location }
python -B sat-search/workflow/research.py lean $workspace --source sat-search/chatgpt_handoff/upstream/OneJunkUpstream.lean --strict --timeout 240
```

The strict local core check took 85.480 seconds and passed all 44 axiom
audits. Its exact SHA-256 is
`c6a8488627b4ece2d61e04d30226ae36f1b34a081520417765a096d86dc04cdf`.
The strict bridge check took 37.667 seconds and passed all five audits,
including the three public conclusions about disjointness, unit inputs,
and edge readers. Its exact SHA-256 is
`da26e631fb689fb16c619dec026032976dab4e95abe7041e15ed0b2c1bf55a6f`.
Both audits report only `propext`, `Classical.choice`, and `Quot.sound`.
The logs and machine-readable audit records are under
`.research/ops/1795768110084459100-lean-check/` and
`.research/ops/1795768275005188200-lean-check/`, respectively.

The follow-up with the two colour and size reductions took 39.447 seconds
and passed all six bridge audits, including the exposing-reader witness
in `oneJunkLargeOppositeSupports`. The checked bridge SHA-256 is
`a688d17f9dc266905a7619bc249e5a4227d53c182527e38ecfee461ebbd95c77`.
The evidence is in `.research/ops/1795768613970960300-lean-check/`.

The suspended-circuit checkpoint passed the strict core check in 70.259
seconds with 46 audited declarations and the bridge check in 39.188
seconds with nine. Both checks report only `propext`, `Classical.choice`,
and `Quot.sound`. The exact core SHA-256 is
`17aa055368460a0b9e694f425d41b7986e376e83d9524f041c11fa941d4fb63c`
and the bridge SHA-256 is
`9ae5e8ac206e6f49cbd9f80c5b9233853061e7269399a325e71902efb058f9d0`.
The logs and audits are in `.research/ops/1795768918355008700-lean-check/`
and `.research/ops/1795769255343341300-lean-check/`.

The shared repair compiler and reader bounds passed the strict bridge
check in 39.879 seconds. All 15 audited declarations use only
`propext`, `Classical.choice`, and `Quot.sound`. The checked SHA-256 is
`0f44bc7548a624fd049b5dc44073c70015007f892a53e1ec1bf8209c4a7c025d`.
The earlier checked core source is the dependency for this run.
The log and audit are in `.research/ops/1795769890789684500-lean-check/`.

The independent repair compiler passed the strict core check in 70.251
seconds with 50 axiom audits. The dependent bridge passed in 38.992
seconds with 10 audits after rebuilding the local core module. Both
audits report only `propext`, `Classical.choice`, and `Quot.sound`.
The checked core SHA-256 is
`7b5e13a019736c89804f2e0e69c9e20af09b3901448e2e2173cb8febd4c3924b`.
The checked bridge SHA-256 is
`e9f57d7555b1612dab3e9969aa88d848be66e62345c2ab03d271fd49745aceeb`.
The evidence is in `.research/ops/1795771140241605200-lean-check/`
and `.research/ops/1795771365907966600-lean-check/`, respectively.
