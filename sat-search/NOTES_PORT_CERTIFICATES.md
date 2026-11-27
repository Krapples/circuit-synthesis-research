# Regional certificate port bounds

*November 24, 2026*

## Results

The regional certificate test strengthened the ordered-region bound on 44 of 90 complete
monotone targets in the frozen corpus. The incompatibility test accounts for 42 improvements.
Numerical rank accounts for two more. Clique search and exact rectangle partitioning gave
no additional target-level gains. The partial-function targets were excluded from this ablation.

Two unresolved hypergraph intervals advanced in the SAT replay. Both the unchanged lazy backend
and the port-enabled backend returned the exclusions.

| Target | Prior interval | Independently checked exclusion | Interval after exclusion |
| --- | --- | --- | --- |
| `hypergraph-09` | [11, 21] | 11 gates, six shapes, 7,265 RUP additions on the baseline | [12, 21] |
| `hypergraph-10` | [12, 21] | 12 gates, six shapes, 7,208 RUP additions on the baseline | [13, 21] |

The next budgets returned UNKNOWN for `hypergraph-09` and reached the wall cap for
`hypergraph-10`. The construction follow-up below narrowed both upper endpoints.
The replay recovered the known eight-gate
`hypergraph-12` witness and verified it against every target row.

## Proof and scope

Cut each repeated wire into a terminal that supplies one leaf occurrence per reader. The resulting
regions are trees. Each primary input belongs to the region it reaches before crossing a repeated
wire. In a complete monotone function, the set of primaries in a true certificate on a minterm row
is exactly that minterm. Any strict subset would be a smaller true certificate. The dual argument
holds for minimal zero certificates.

Fix the primary set $S$ of a region. A global certificate with a nonempty projection onto $S$
visits that region. Choose one global certificate for each distinct nonempty projection on each
axis. For any two such certificates, their restrictions in the region share exactly one leaf
occurrence. At an AND node the false certificate takes one child and the true certificate takes
both. At an OR node the true certificate takes one and the false certificate takes both. This
gives a unique common path in the tree, ending at a primary or a port occurrence. At the output
region every global certificate visits, so empty projections can also be included there.

If a projected minterm and zero certificate share two primaries, the region is impossible.
Equivalently, a primary pair is forbidden whenever it occurs together in some minterm and some
minimal zero certificate. For compatible $S$ the residual matrix is $D_{A,B}=1-|A\cap B|$.
Each port occurrence gives a rectangle whose rows and columns select that occurrence. These
rectangles partition the one-cells of $D$. Repeated reads of the same source count as distinct
occurrences. Deleting duplicate and all-zero rows and columns preserves the partition number.
A partition restricts to the reduced matrix and extends back by copying representative memberships.

Over any field a rectangle has rank at most one. The maximum of ranks modulo 101 and 2
therefore lower-bounds the port count. Two one-cells cannot share a rectangle when either
cross-cell is zero, so the size of any clique in that conflict graph is also a lower bound.
The exact solver enumerates all all-one rectangles and uses disjoint exact cover. It attempts
matrices up to eight rows by eight columns and 32 one-cells, with a 20,000-state cap. At the cap it
keeps the largest bound already proved. All regional port bounds are combined by maximum.

If $r$ wires repeat and the circuit has $e=B-m+1$ excess reads on $m$ essential inputs,
the $r+1$ regions have $e+r$ port occurrences in total. Every region without a primary
has at least one port occurrence. Thus the $k$ nonempty primary regions need
$e\ge\max(k-1,\sum_i p(S_i)-k+1)$. The existing ordered partition DP checks this
inequality, including a separate empty-output case when output-region costs are enabled.

The proof requires complete monotone certificate families. For a partial example, take positive
row `11` and negative row `00`. Treating both row masks as certificates would reject the
two-primary region. A single AND gate satisfies the labels, and one zero input suffices for its
false certificate. The new bounds stay out of arbitrary partial-domain and NOT-enabled synthesis.

## Implementation and independent checks

The cube driver exposes `--portcertrank` with `compatibility`, `rank`, `clique`, and `exact`
levels. Rank is the default level when the option is present. `--portcertoutput` adds the
output-region refinement at a numerical level. The former cost table and partition DP remain
available. Matrix bounds and minimal zero certificates are cached.

With local intersections enabled, SAT models already satisfy the local rectangle counting
identity. A post-model port test is therefore redundant in that backend. The implementation adds
guarded owner exclusions and cardinality constraints before SAT as optional propagation. It
enumerates exact primary subsets only up to eight inputs. On larger targets it adds only the
primary-pair exclusions. Without local intersections it learns the guarded cuts from candidate
models. A count clause is conditional on the exact primary support because another primary can
fill a residual one-cell. The backend checks completeness by recomputing minimal zero certificates.

An independent circuit traversal checked 397 concrete circuits, 1,097 primary regions and
25,421 certificate pairs. It verified the concrete common-port count, all lower bounds and
the excess inequality. Output projections strengthened 192 concrete output bounds. The
ordered DP was also checked against concrete gate counts on the small circuits.
Exact cover matched a separate set-based enumerator on all 512 binary three-by-three matrices.
A four-by-four cycle gives rank 3 and clique and partition number 4. A six-by-six regression
has rank and maximum clique 5 and partition number 6, so exact partitioning is strictly
stronger in general even though the corpus showed no gain.

The known-answer tests passed with and without the new options. Independent Python and MiniSat
unit-propagation checkers agreed on the small Glucose DRUP traces, and MiniSat rejected a
deliberately invalid trace. The two hypergraph exclusions were checked by MiniSat with no
synthesis search in the checker. The original Python proof replay hit the five-second cap
on both jobs. The MiniSat replay completed in roughly 1.3 to 2.0 seconds per budget, including
synthesis and proof checking. The final CNFs, traces and SHA-256 digests are archived.

## Matched ablation

The fixed corpus contains 100 targets, of which 90 have complete monotone labels. Each ordered
profile ran in its own process. Improvements below compare against the preceding level, except
for output-aware rank, which compares against rank.

| Ordered profile | Target bounds raised | Wall time | Peak memory |
| --- | ---: | ---: | ---: |
| Existing monotone ports | — | 0.942 s | 37.3 MiB |
| Certificate compatibility | 42 | 0.376 s | 37.3 MiB |
| Rank | 2 | 0.450 s | 37.4 MiB |
| Clique | 0 | 0.471 s | 37.3 MiB |
| Exact partition | 0 | 0.450 s | 37.8 MiB |
| Output-aware rank | 0 | 0.513 s | 39.4 MiB |

Compatibility excluded 3,652 candidate primary subsets and raised 17 bounds above the
archived endpoint records. Numerical rank raised 192 surviving regional costs. The two global
rank gains were `random-monotone-09` and `generated-09`, both from 7 to 8 gates, matching
their existing endpoints. Clique raised one local cost from 5 to 6 for primary mask 116 of
`hypergraph-15`. After applying the stronger endpoint revisions already recorded in the research
notes, nine unresolved targets still gained analytically, including `threshold-7-4` from 9 to 12,
`threshold-8-5` from 10 to 14, and `comparator-05` from 10 to 14.

The local-intersection SAT benchmark ran eight fixed budgets serially per variant with a
two-second wall cap and a 2,500-conflict limit per shape. Every variant returned four UNSAT
results, one verified SAT result, and three timeouts. The summed times, including timeouts,
ranged from 6.81 to 6.88 seconds. The largest measured process peaks ranged from 73.7 to
74.4 MiB. Port rank, clique and exact each added 3,814 static clauses across the completed
jobs. Output-aware rank added 4,877. These runs established no SAT speedup.

In the weaker lazy encoding without local intersections, numerical port cuts did fire.
Rank learned 92 cuts during the completed unresolved-endpoint searches and 28 in the small
known-answer replay. The matched verdicts were unchanged, and the weaker encoding completed
fewer of the harder probes. The expensive levels remain opt-in. Compatibility is the best
candidate from this round for a cheap analytical prescreen.

## Construction follow-up

The improved analytical bounds still left wide intervals, so the next experiment targeted the upper
ends. For each complete minterm family, recursively factor out each possible input. Try the
same factorization on minimal zero certificates and dualize it. Compile the best resulting
expressions with identical gates shared. This keeps one subexpression per subproblem and uses
six deterministic tie-breaking orders. It is an upper-bound heuristic. All candidates were
checked bit-parallel against the frozen truth tables.

Factoring improved nine of eleven construction upper bounds in about four seconds. Probing the
lower endpoints with the reference regional solver then produced one new exact minimum and
three further checked lower-bound advances.

| Target | Before this investigation | After construction and checked endpoints |
| --- | ---: | ---: |
| `hypergraph-05` | [10, 19] | [13, 14] |
| `hypergraph-15` | [10, 23] | [13, 15] |
| `hypergraph-19` | [9, 18] | **10** |
| `hypergraph-20` | [10, 25] | [13, 16] |
| `hypergraph-09` | [11, 21] | [12, 14] |
| `hypergraph-10` | [12, 21] | [13, 15] |
| `hypergraph-04` | [12, 21] | [12, 14] |
| `comparator-05` | [10, 31] | [14, 21] |
| `comparator-09` | [9, 28] | [11, 14] |

The ten-gate `hypergraph-19` circuit verifies under both the regional evaluator and the
independent bit-parallel gate evaluator. All four relevant nine-gate shapes have archived
proofs, totaling 142 checked additions. The checked exclusions for `hypergraph-05`,
`hypergraph-15`, and `hypergraph-20` cover budget 12. Their 13-gate probes reached the
four-second cap. The remaining open cases offer tests for bounds on which upstream signals
can supply the required port occurrences.

## Reproduction and records

```powershell
python sat-search/experiments/port_certificates_check.py -v
python sat-search/cube_search.py --n 4 --edges 0-1,1-2,2-3 --size 4 --workers 1 --symmetry --monotone --portcertrank exact --portcertoutput
python sat-search/experiments/port_certificates_check.py --benchmark fresh-port-ablation.jsonl --seconds 2 --conflicts 2500 --levels baseline compatibility rank clique exact rank-output
python sat-search/experiments/port_certificates_check.py --benchmark fresh-port-proofs.jsonl --seconds 12 --conflicts 2500 --proof --proof-dir fresh-port-packets --levels baseline --job hypergraph-09 11 --job hypergraph-10 12
python sat-search/experiments/port_certificates_check.py --benchmark fresh-lazy-cuts.jsonl --seconds 2 --conflicts 2500 --without-local-intersection --levels baseline rank clique exact rank-output --job hypergraph-12 8 --job threshold-5-3 9 --job hypergraph-09 11 --job hypergraph-10 12
python sat-search/experiments/port_certificate_construction.py --output fresh-port-constructions.jsonl
python sat-search/experiments/port_certificates_check.py --benchmark fresh-hypergraph-19.jsonl --seconds 4 --conflicts 2500 --proof --levels baseline --job hypergraph-19 9 --job hypergraph-19 10
python sat-search/experiments/certify_synthesis.py --verify <cnf.gz> <drup.gz>
```

[Final ablation](results/port_certificate_static_ablation.jsonl) ·
[Initial model-check ablation](results/port_certificate_ablation.jsonl) ·
[Initial proof-check caps](results/port_certificate_frontier_proofs.jsonl) ·
[Lazy cut ablation](results/port_certificate_lazy_cuts.jsonl) ·
[Weak encoding known answers](results/port_certificate_lazy_known_answers.jsonl) ·
[Next-budget probe](results/port_certificate_next_frontier.jsonl) ·
[Proof packet index](results/port_certificate_proof_packets.jsonl) ·
[Proof files](results/port_certificate_proofs/) ·
[Matched checked replay](results/port_certificate_verified_frontier.jsonl) ·
[Construction witnesses](results/port_certificate_constructions.jsonl) ·
[Construction frontier](results/port_certificate_constructed_frontier.jsonl) ·
[Next construction budgets](results/port_certificate_constructed_next.jsonl) ·
[Nine-gate proof index](results/port_certificate_constructed_minima.jsonl) ·
[Ten-gate circuit](results/port_certificate_exact_witness.jsonl)

The read-once intersection property is classical. The rank, fooling-set and biclique-partition
tools also have established antecedents. [Karchmer et al.](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/KLNSW93/paper.pdf) ·
[Schneider et al.](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SEA.2025.18)

## Provider-compatible certificate bounds

Each residual cell retains its full minterm $A$ and minimal zero certificate $B$. A provider
whose structural input support is $W$ can satisfy this pair only if $A\cap B\cap W$ is
nonempty. Otherwise the restriction of the positive assignment to $W$ is below the
restriction of the negative assignment, contradicting monotonicity. The same test on every
cross pair of the combined positive and negative obligations is sufficient for an arbitrary
monotone provider truth table. Take the upward closure of the projected positive assignments.
It avoids each projected negative assignment by the cross-pair condition.

Full certificate identities matter even when both projections onto the region coincide.
For $(a\land c)\lor(b\land c)\lor d$, the minterms $ac$ and $bc$ both project to $c$
on $S=\{c,d\}$. Against the zero certificate $abd$, a provider supported on $a$ can
serve the first row and cannot serve the second.

### Tests and integration

- **Eligibility** rejects any residual one-cell with an empty provider list.
- **Matching** takes cliques of cells that cannot use the same rectangle. Two cells conflict
  when a cross-corner is zero or when the four corners have no provider in common. Every
  clique needs distinct port occurrences, so capacitated bipartite matching must saturate
  it. The implementation samples up to 80 cells and 16 cliques. It also checks all cross
  pairs of obligations forced by singleton provider lists. [Hall's matching theorem](https://math.mit.edu/~goemans/18453S17/matching-notes.pdf)
- **Exact partition** assigns disjoint all-one rectangles to provider occurrences within
  the capacities. It retains the union of positive and negative obligations for each
  provider and checks their cross pairs, including cross pairs at zero cells of the
  residual matrix. It attempts active matrices up to seven rows by seven columns and
  24 one-cells with up to eight providers and 12,000 search states. A capped query keeps
  the cheaper results.

The ordered DP exposes `--portproviders`. Its state knows the union of earlier primary
groups. That union contains every possible upstream provider support, so a residual cell
missed by the union rules out the transition. Per-provider capacities require a concrete
layout and are checked in the lazy backend, where each port has a source and owner.

Without local intersections, the lazy backend reconstructs the structural cone of each
source from the model's owner assignments. It checks all visited positive-negative pairs
for the source, across all its readers. A failed pair yields a guarded clause requiring
one visit to change or the cone to gain a distinguishing atom. The permitted changes
include a new primary owner inside the cone or a port entering it from outside. It can
also rule out a fully fixed owner layout by an eligibility, matching, or exact-partition
obstruction. Primary incompatibility stays with the existing local formula check.

The local-intersection encoding already implies the provider tests once a model is
complete. Starting from a jointly visited source, follow a common leaf in each successive
provider region. Acyclicity guarantees this reaches a common primary in the source's
cone. The selected common-port occurrences also witness a compatible local rectangle
partition. This backend uses the option to add ancestry implications before SAT for
propagation and avoids repeating the implied tests on complete models.

### Verification and measurements

An independent enumeration of monotone provider truth tables agreed on 240 small
queries, including 45 feasible cases. The tests checked 139 concrete circuits,
394 regions and 420 combined provider cross pairs. Regressions distinguish empty-list,
matching, forced-consistency, and exact-partition exclusions. Both lazy encodings and
all provider levels preserved the five-cycle minimum and its checked six-gate exclusion.
The existing ordered, rank, and lazy-compatibility regression suites also passed.

On 793 sampled nontrivial ancestor and capacity hypotheses from the 90 complete frozen
targets, the successive tests had these effects. These samples measure local exclusion
power on proposed layouts.

| Level | Additional exclusions | Cumulative wall time |
| --- | ---: | ---: |
| Empty eligibility lists | 367 | 0.0024 s |
| Capacitated matching | 79 | 0.041 s through matching and forced consistency |
| Forced-provider consistency | 34 | Included above |
| Exact partition | 11 | 0.291 s through all levels |

The exact stage found 267 feasible local partitions and skipped or capped 35 further
queries. Feasibility here concerns the rectangle relaxation under the sampled supports.

The ordered ablation made 22,278 eligibility checks and rejected 359 transitions.
The 90 target lower bounds all agreed. The profiles took 0.368 s and 0.397 s with
peaks of 37.2 MiB and 37.8 MiB.

The serial SAT ablation used ten budgets spanning graphs, thresholds, comparators,
hypergraphs, and random monotone functions. Each had a 1.25-second wall cap and
1,800 conflicts per shape. Without local intersections, eligibility learned 130
shared-provider consistency cuts in completed jobs and verified the known seven-gate
threshold witness where the reference reached its conflict limit. Timing including
timeouts was 4.18 s for the reference, 4.22 s with eligibility, and 4.24 s with matching.
Peak memory was 45.2–46.3 MiB. Matching yielded the same verdicts as eligibility.
The initial replay also tried replacing primary-incompatibility checks with owner blocks.
That changed the six-gate threshold job from UNSAT to UNKNOWN at the same conflict cap.
The final replay preserved the existing primary-incompatibility check.

With local intersections, both variants produced the same ten verdicts. The eight
completed provider jobs recorded 3,466 added ancestry clauses. The two variants took
about 2.59 s each and peaked at 46.6–46.9 MiB. The optional
exact SAT run matched the matching-only verdicts on four selected budgets, with
0.801 s versus 0.793 s total. This round established no new minima or target lower
endpoints. The results support retaining the levels as opt-in. A next experiment is
to obtain stronger provider support limits earlier in the search, where the matching
exclusions seen on standalone layouts could affect whole budgets.

```powershell
python sat-search/experiments/provider_certificates_check.py -v
python sat-search/experiments/provider_certificates_check.py --benchmark fresh-provider-ablation.jsonl --seconds 1.25 --conflicts 1800
python sat-search/experiments/provider_certificates_check.py --benchmark fresh-provider-queries.jsonl --query-profile
python sat-search/experiments/provider_certificates_check.py --benchmark fresh-provider-exact-queries.jsonl --query-profile --exact
python sat-search/experiments/provider_certificates_check.py --benchmark fresh-provider-exact.jsonl --exact --seconds 1.25 --conflicts 1800 --job cycle-5 7 --job threshold-4-3 6 --job hypergraph-19 10 --job comparator-02 8
```

[Matched ablation](results/provider_certificate_ablation.jsonl) ·
[Initial ablation](results/provider_certificate_ablation_initial.jsonl) ·
[Standalone inexpensive checks](results/provider_certificate_queries.jsonl) ·
[Standalone exact checks](results/provider_certificate_queries_exact_detail.jsonl) ·
[Optional exact SAT replay](results/provider_certificate_exact.jsonl)

## Global provider capacity prescreen

### Proof and regression

For each provider $j$, fix its primary group $S_j$ and an overestimate $W_j$ of
its structural support. The ordered prefix of primary groups gives such an
overestimate. Every full minterm $A_0$ meeting $S_j$ makes provider $j$ true,
because its true certificate uses the input and visits the region. Every full
minimal zero certificate $B_0$ meeting $S_j$ makes the provider false by the
dual argument. These give mandatory positive and negative obligations.

For a residual pair $(A,B)$, a candidate provider must distinguish the pair on
$W_j$. It must also distinguish $A$ from every mandatory negative and every
mandatory positive from $B$, all on the same support. The code evaluates these
tests with full certificate identities. Exact duplicate full masks can share an
identity. Equal projections onto a primary region can have different eligibility.

For a subset $T$ of providers, in each receiving region take a clique of residual
cells whose eligibility lists are contained in $T$. Every clique member needs a
distinct occurrence, and an occurrence belongs to a single receiving region.
The sum of the regional clique sizes therefore fits within the combined outgoing
capacity of $T$. The clique checks retain the eligibility of all cross-corners,
including corners whose lists extend outside $T$.

For $f(a,b,c,d)=abc\lor bd\lor cd$, take the ordered primary groups
$\{d\},\{a,b\},\{c\}$ with outgoing capacities 2 and 3. The middle region
needs one occurrence of $d$ for $(bd,ad)$. The output pairs $(bd,cd)$ and
$(cd,ad)$ can only use the $d$ provider once the mandatory obligations of the
middle provider are included. They need separate occurrences because the cross
cell $(cd,cd)$ is already covered by the output primary $c$. Each receiving
region has a feasible exact partition under the full per-provider capacities
considered separately. Together they require three occurrences from a provider
with capacity two. The regression also checks that the solver recovers a
five-gate circuit for the function using a different layout. An independent
direct SAT encoding supplies a checked UNSAT proof for four gates.

### Integration and scope

`--providercapacity` enables the global prescreen in the lazy regional runner.
`singletons` tests one provider at a time. The default `subsets` checks those
first and then checks every subset through five providers. Above that it checks
the full set and, up to eight providers, pairs. Each rejection records actual
regional cliques, so sampling fewer cliques or subsets weakens pruning safely.

Small full primary layouts can be screened exhaustively before SAT. For larger
local-intersection shapes, the solver checks up to 96 candidate prefixes before
SAT. A rejected prefix gives a clause guarded by the primary groups it fixes.
No later group can supply a port to a region in that prefix. Local intersection
already implies these conditions on complete models, so this path leaves the
model loop free of repeated capacity checks. Without local intersections, larger
shapes check and cache each primary layout when it first appears in a model.
The prescreen uses the ordered support overestimate and leaves port owners and
certificate memberships free to change under its guards.

The optional `exact` level covers all residual cells with disjoint rectangles
of their respective receiving regions. Capacity is shared across all regions, and
each provider's combined obligations include its mandatory rows and every
rectangle assigned to it. The allocator checks every positive–negative cross pair
in that union. It attempts at most eight providers and 24 residual cells across
regions, with at most seven active rows and columns per region and a 12,000-state
cap. Successful allocations certify feasibility of this relaxation under the
specified supports. The regional formula and circuit constraints still govern
the synthesis verdict.

### Verification and ablation

Independent enumeration of monotone provider truth tables agreed on all 440
small complete layouts, including 400 feasible ones. Concrete verification
covered 130 circuits, 102 with repeated wires, and 228 fixed prefixes. The
exact allocator accepted all 260 full-layout checks, which used both actual
structural supports and their ordered overestimates. The five-cycle known
minimum and its checked exclusion passed at every level in both lazy encodings.

The frozen sample contained 1,800 layouts across 90 complete targets. Mandatory
obligations rejected 1,297, primary conflicts rejected 115, and 388 survived.
The capacity tests made zero additional exclusions in that sample. To check
whether the specified regression generalizes, a second sweep used all 114
essential four-input monotone functions, every ordered partition into three
nonempty groups, and both capacities 2 and 3 for each provider.

| Level | Layouts checked | Capacity exclusions beyond mandatory and primary checks | Wall time |
| --- | ---: | ---: | ---: |
| Singletons | 16,416 | 96 | 0.314 s |
| Subsets | 16,416 | 96 | 0.361 s |
| Joint exact allocation | 16,416 | 96 | 0.738 s |

On ten frozen SAT budgets, the reference, singletons, and subsets each returned
four UNSAT results, four verified SAT results, and two timeouts. Each job used a
1.25-second wall cap and 1,800 conflicts per shape. Summed wall times were
2.593, 2.614, and 2.620 seconds. Peak process memory ranged from 46.2 to 47.3 MiB.
In the completed prescreen jobs, 728 checked prefixes yielded 206 mandatory
obstruction clauses and zero capacity-overload clauses. The initial post-model
check in the local-intersection backend yielded zero cuts, motivating the
prefix integration.

The weak encoding's five-job replay also had identical verdicts, with 167
mandatory layout cuts and some added runtime. The optional exact SAT replay
matched the subset variant on four budgets. The data establishes a layout
separation and leaves the options experimental for synthesis performance.
Tighter provider support overestimates are a more promising next variable
than increasing the enumeration limits on this evidence.

```powershell
python sat-search/experiments/provider_capacity_check.py -v
python sat-search/experiments/lazy_certificates_check.py --job cycle-5 6 lazy-local-intersection --providercapacity --proof
python sat-search/experiments/provider_capacity_check.py --benchmark fresh-capacity.jsonl --seconds 1.25 --conflicts 1800
python sat-search/experiments/provider_capacity_check.py --benchmark fresh-capacity-layouts.jsonl --layouts
python sat-search/experiments/provider_capacity_check.py --benchmark fresh-capacity-four-inputs.jsonl --all-four-inputs
python sat-search/experiments/provider_capacity_check.py --benchmark fresh-capacity-exact.jsonl --all-four-inputs --exact
```

[Frozen SAT ablation](results/provider_capacity_ablation.jsonl) ·
[Initial post-model replay](results/provider_capacity_ablation_initial.jsonl) ·
[Frozen layout sample](results/provider_capacity_layouts.jsonl) ·
[Four-input sweep](results/provider_capacity_four_inputs.jsonl) ·
[Four-input exact sweep](results/provider_capacity_four_inputs_exact.jsonl) ·
[Weak SAT replay](results/provider_capacity_weak.jsonl) ·
[Optional exact SAT replay](results/provider_capacity_exact.jsonl)

## Allocating unknown outgoing capacity

For an ordered layout with $r$ repeated providers, set $d_i=2+x_i$. The
subset-clique certificates give $h(T)=\max(0,F(T)-2|T|)$ and the constraints
$\sum_{i\in T}x_i\ge h(T)$. The deficit mode takes the largest individual
constraint. The packing mode uses a subset DP to maximize the sum of deficits
on pairwise disjoint sets in $O(3^r)$. Exact mode enumerates nonnegative vectors
within the remaining overhead, checking all constraints. The bound on layout
excess is $r+\sum_i x_i$ at the optimum of this relaxation.

For $abc\lor bd\lor cd$ the three-region regression gives $F=(0,3,2,5)$.
Unrestricted incoming-port counts permit excess two. Each allocation mode
requires three. Synthetic overlapping constraints distinguish exact allocation
from packing. An independent vector enumerator agreed on 200 small queries,
and the typed/capacity tests were checked on 101 concrete circuits.

`--capacityallocation` also checks complete small layouts when raising a
whole-function lower bound. Empty regions remain in the enumeration. A size
is excluded only if every eligible layout fails. The driver caps this stage
at six primaries, checked excess at most five, and 6,000 layouts. The matched
profile used a smaller 900-layout cap and checked the current lower endpoint.

The 56-target comparison used the existing ordered formula, profile, exact
port and provider bounds. Running the same layout enumeration without capacity
allocation gave zero whole-target gains. Deficit raised three ordered
bounds by one gate, on `hypergraph-07`, `hypergraph-18`, and `graph-01`.
Independent evidence already covered all three new endpoints. Packing and
exact allocation gave zero further whole-target gains. The reference setup
took 0.191 s, structural layout screening 0.206 s, and allocation 0.226–0.228 s.
This closes the follow-up experiment. Revisit larger allocation modes with
evidence of new target bounds or a solver gain. [Results](results/regional_algebra_ablation.jsonl)

## Quick-reference summary

Moved word for word from the root RESEARCH_NOTES.md on November 27, 2026.

| Topic | Result |
| --- | --- |
| Regional certificate ports | Compatibility raised the ordered bound on 42 of 90 complete targets, and rank raised it on two more. Clique and exact partition gave no additional target-level gains. The SAT ablation found no speedup. Factoring improved nine construction upper bounds, and the follow-up certified `hypergraph-19` at **10 gates**. [Proofs, benchmarks, and reproduction](NOTES_PORT_CERTIFICATES.md) |
| Provider-compatible ports | Full certificate identities preserve provider eligibility and shared-provider consistency. Of 793 sampled layouts, empty lists excluded 367, matching and forced consistency excluded 113 more, and exact partition excluded 11 more. The ordered and SAT replay left target lower bounds and minima unchanged. [Proof, checks, and ablation](NOTES_PORT_CERTIFICATES.md#provider-compatible-certificate-bounds) |
| Global provider capacity | Mandatory certificate obligations refine provider lists. Singleton capacity tests excluded 96 of 16,416 ordered four-input layouts beyond the primary and mandatory checks. The ten frozen SAT budgets produced matching verdicts across variants. [Proof, regression, and ablation](NOTES_PORT_CERTIFICATES.md#global-provider-capacity-prescreen) |
| Unknown capacity allocation | Deficit raised three whole-target ordered bounds on a 56-case replay, all already covered by independent evidence. Packing and exact allocation added zero whole-target gains. [Conditional bound and benchmark](NOTES_PORT_CERTIFICATES.md#allocating-unknown-outgoing-capacity) |
