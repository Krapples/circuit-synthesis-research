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
