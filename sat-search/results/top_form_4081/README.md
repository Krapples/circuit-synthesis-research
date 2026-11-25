# Top-form graph synthesis and routing for L-meta-4081

The posted statement concerns a least fan-in-exactly-two AND/OR circuit for the eleven-input
graph function with the following edges.

```text
09 0a 14 18 25 2a 36 37 48 4a 58 59 67 6a 79 89
```

Here `a` is vertex 10. Let `U` be the edges absent from the cross products of the raw OR
supports of the clean AND gates, and let `J` be the dirty AND gates. The target is
`|U| ≤ Q`, where `Q = 2·|centreless| + |J| + |orN \\ lam|`. The posted premises
include at most 21 gates, top form, at least three junk gates, and junk-gate coverage
of every edge of `U`. A counterexample has `Q < |U|`, which implies the additional
posted premise `Q < 2·|U|`.
[Exact project statement](https://data.pequalnp.com/data/lemma/L-meta-4081.0f872808203b.json)

## SAT runs

Each run used 22 workers and the repository's `cube_search` encoding with MapleChrono.
The graph has 16 minimal true rows and 24 maximal false rows. Monotonicity makes these
40 rows sufficient for functional equality. For each internal gate, all 24 maximal
false rows also determine whether the gate is below the target. The independent
witness decoder evaluates the full 2,048-row cube and calculates the structural
quantities by direct set traversal.
[Accepted boundary-verification pattern](https://github.com/open-goat/pequalnp-proofs/blob/cf3e0737b74e5103a45bfdf5d2bbab705f2dab91/lean/PEqualNP/Outside/L_meta_8029.lean)

| Run | Work per shard | Solved | Open |
| --- | --- | --- | --- |
| [Synthesis baseline](L-meta-4081-search.jsonl) | 95 s cap, CEGAR boundary rows | 0 | All 22 shards at sizes 19–21 |
| [Structural search](L-meta-4081-structural.jsonl) | 150 s cap, full boundary, top form and `Q < \|U\|` | 4 UNSAT, all of sizes 10–12 | Both first-operator shards at every size 13–21 |
| [Phased structural search](L-meta-4081-phased.jsonl) | 180 s cap, clean and dirty phases with separate colex ordering | 4 UNSAT, all of sizes 10–12 | Both first-operator shards at every size 13–21 |

Every input is essential, so a connected binary circuit on eleven inputs needs at least
ten gates. The searches disallow unread wires and duplicate operands, which a least
circuit can eliminate. The baseline fixes the first operator and a subset of possible right
operands. The structural encoding tracks OR support with a forward recurrence, and membership
in `lam` by a backward recurrence from top-gate operands whose opposite side has singleton
support. Its cardinality constraint counts covered edges plus the duplicated centreless
charges, junk gates, and dirty ORs outside `lam`, with a cap of 15. It relaxes leastness
after the shared minimum-circuit simplifications. All UNSAT results are solver verdicts.
There were no models and no proof certificates or peak-memory measurements.

In the phased variant a clean OR reads only clean wires. Each of these wires has a clean
AND ancestor because no primary input is clean. A dirty AND cannot read a clean wire.
A dirty OR cannot read a clean wire either. Any path from such an OR to the output would
either reach an AND and violate top form, or consist entirely of ORs and make the output
true on a negative row. A clean AND also reads only dirty wires or primary inputs by top
form. These facts permit reordering the circuit into dirty gates, clean ANDs, and clean
ORs, keeping colex symmetry within each group. A proper prefix whose last gate computes
the target would contradict leastness. The phased encoding adds that necessary condition.

The scripts expect Python with the same dependencies as `sat-search/cube_search.py`.
Run from this directory with the output files moved aside, as the scripts create logs
exclusively.

```powershell
python search-4081.py
python search-4081-structural.py
python search-4081-structural.py --phased
python one-mixer-4081.py
```

## Analytic scope

The graph has no four-cycle and maximum degree four. Direct enumeration of its 2,048
vertex subsets gives minimum cover size seven, with 22 minimum covers. An ordinary
star-cover construction with seven used centers can compute the full graph function in
`16 + 7 − 1 = 22` gates. Its restriction is a sum of stars with separately constructed
leaf ORs. The published 21-gate question allows general shared top-form circuits.
[Accepted minimum-cover proof](https://github.com/open-goat/pequalnp-proofs/blob/52572f6a5a6aae6385c0ced34037fbdf72f804e4/lean/PEqualNP/Outside/L_meta_2693.lean)

The existing reduction establishes a residual-cover invariant by peeling a junk gate
whose footprint has just one residual edge. The cardinalities of the remaining junk
gates and residual edges decrease together. The new routing argument concerns a different
restriction: an uncovered edge must fire either a centreless top or a mixing OR in one
operand of a firing top. If both operand supports contained an endpoint set by the edge,
the edge would be a cross pair. A firing operand with nonempty support disjoint from the
edge reaches a mixing OR by following true OR operands until one child has empty support.
Mixing ORs are dirty ORs outside `lam`. If both kinds of exception are absent, `U` is
empty. Consequently three or more junk gates suffice for the target inequality whenever
at most four edges are uncovered.
[Accepted footprint reduction](https://github.com/open-goat/pequalnp-proofs/pull/21926)

With no centreless top and a unique mixing OR, any uncovered edge has an active endpoint
adjacent to all inputs in that mixing gate's raw support. Neither a firing top with both
operands routing through the same mixer nor a shared primary input in its two supports
is possible, since the top would fire at a singleton. If the mixer support contains at
least two inputs, no four-cycle implies that all uncovered edges meet the same vertex.
For this graph that bounds the residual edge count by four.
[Accepted routing tools](https://github.com/open-goat/pequalnp-proofs/blob/13f3d3447f6ae30076544637de9fbe37cbb3be92/lean/PEqualNP/Outside/L_meta_7467.lean)

Lean 4.36.0 checked both restrictions in [Route4081.lean](Route4081.lean) against
the public project definitions and the accepted routing module above. Both theorems
use only `propext`, `Classical.choice`, and `Quot.sound`. To reproduce from the public
project's Lean workspace with its dependency cache built, build the routing module
and run the local file under the same Lake environment.

```powershell
lake build PEqualNP.Outside.L_meta_7467
lake env lean -DmaxHeartbeats=5000000 -DmaxRecDepth=10000 <absolute-path-to-Route4081.lean>
```

The one-mixer enumeration examines the five-uncovered-edge case with no centreless
top, three junk ANDs, and one exceptional OR. In this configuration all dirty AND
outputs must reach the sole mixing gate on their way to the output. Its empty-support
operand is an AND of at most four distinct pure OR supports. The relaxation chooses
the mixer's singleton support and the set of pins on the opposite sides of receiving tops.
For the residual edges it chooses OR masks meeting every one of those edges, and asks
that their conjunction reject each maximal independent row meeting the pin set.
Of 77 candidate triples of singleton, pin set, and residual edge set, 47 need more
than four clauses or have no solution, 12 need four, 17 need three, and one needs two.
These 30 feasible relaxed triples ignore the gate count for constructing the supports
and receiving tops. The relaxation alone leaves the five-edge case open.
