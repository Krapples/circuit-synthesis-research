# Circuit Synthesis Quick Reference

*Updated November 25, 2026*

The project uses exact synthesis and analytical lower bounds to study small Boolean circuits. The
latest cross-family benchmark shows that frontier bounds transfer beyond graph functions, including
to 3-uniform hypergraphs. The main open shard is L-meta-1343 at size 19.

For the cubic-graph case L-meta-5020, Lean checked that a false restriction at the
designated two-reader input saves four gates or leaves one of two local reader
patterns. An exclusive internal operand of the AND reader also yields a
four-gate saving. [Reader analysis and proof scope](sat-search/results/cubic_gate_elimination_5020/README.md)
[Submitted reduction](https://github.com/open-goat/pequalnp-proofs/pull/22538)

For the 24-vertex bipartite graph in L-meta-9791, Lean checked a 54-gate
witness, also evaluated on the complete monotone boundary. The two-star suffix of any nine-star
fixed prefix needs at least nine further gates before the final OR.
The unrestricted 53-gate budget remains open.
[Projection, lower bound, and search records](sat-search/results/c4free_9791/README.md)

For the two-output quadrangle separator L-meta-5258, a source-count
bound and induced-path restrictions exclude the posted budget within
all same-side pinned prefixes leaving two or three stars. Lean checked
a gate-criticality condition for minimum-size realizations.
The unrestricted sub-63-gate case remains open.
[Quadrangle tests, scoped bounds, and search records](sat-search/results/pg3_quadrangles_5258/README.md)

For deleted-line Heawood incidence L-meta-9748, the merged full-graph
bound gives a Lean-checked monotone minimum of 23 together with
an independently evaluated upper bound. Even-path and source-count
arguments exclude the 22-gate budget in the pinned right-star
families with two or three stars left. The unrestricted counted-NOT
budget remains open.
[Basis-specific bounds and search records](sat-search/results/deleted_heawood_9748/README.md)

For order-four incidence L-meta-4653, the checked conjunction-list
normalization preserves the number of OR gates and exposes the exact
monotone boundary. The 105 positive rows pair with 25,237 maximal
negative rows in 10 projective-symmetry orbits. Lean checked a
34-instruction lower bound in the common vertex-cover union model.
The required unrestricted bound is 104.
[Reduction audit, geometry, proof, and diagnostics](sat-search/results/pg4_or_4653/README.md)

For the eleven-vertex top-form graph in L-meta-4081, Lean checked the edge-charge inequality
with at most four uncovered edges. It also checked that one mixing OR with support of size
at least two forces all uncovered edges to share a vertex when there are no centreless tops.
Structural SAT excluded counterexamples through 12 gates and timed out at sizes 13–21.
[Routing proofs and search records](sat-search/results/top_form_4081/README.md)

For the Petersen OR-substitution case L-meta-7893, Lean checked a 20-gate expanded circuit.
The same cost is optimal when the retained and deleted edges use separate star covers.
The posted 19-gate limit remains open. [Guard restrictions, witness, and search records](sat-search/results/petersen_guard_7893/README.md)

The one-hot bipartite representation probe L-meta-11869 has a computational lower bound of 17
and a Lean-checked upper bound of 30 AND/OR gates. The requested budget of 20 remains open.
[Representation probe](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md#one-hot-bipartite-representation)

The deleted-point projective-plane probe L-meta-2216 has a Lean-checked 62-gate two-output
construction and a matching 62-gate lower bound when the graph-output cone is single-level.
The unrestricted budget of 61 remains open. [Witness, proof scope, and SAT records](sat-search/results/pg3_deleted_point_proxy_2216/README.md)

For the six-input table in L-meta-16102, Lean checked an eight-gate monotone construction.
Two synthesis encodings exclude the requested nine-gate circuit with a NOT reading a gate.
The exclusion is computational evidence. [Exact syntax, coverage, and replay](sat-search/results/mid_not_16102/README.md)

For the Fano incidence function in L-meta-4874, Lean checked a 28-gate circuit with
the required final AND and singleton constraints. A 28-gate lower bound applies to a
factorized star-cover form. The unrestricted budget of 27 remains open.
[Proof, witness, and search coverage](sat-search/results/fano_final_and_4874/README.md)

The order-three projective-plane step L-meta-9063 has a merged reduction
to two six-line circuits with budgets 28 and 29. The 29-gate child L-meta-17643
has a merged proof. The 28-gate child L-meta-17641 and the 14-gate probe of its
smaller seeded grid remain open. [Merged reduction](https://github.com/open-goat/pequalnp-proofs/pull/22166)
[Merged 29-gate proof](https://github.com/open-goat/pequalnp-proofs/pull/22337)
[Reduction, search coverage, and related accepted methods](sat-search/results/pg3_seeded_boundary_9063/README.md)

**Current priority: mathematical and algorithmic improvements.** About 80% of effort goes to research, 15%
to targeted verification of changed components, and 5% to documentation. The research targets are:

- stronger general lower bounds;
- exact synthesis algorithms that shrink the search space;
- nonmonotone AND/OR/NOT circuits;
- practical complete-function FPT synthesis;
- shared-subexpression construction;
- adaptive analytical branch-and-bound;
- hybrids with SAT that show measurable gains.

The [verification audit](sat-search/verify/AUDIT.md) supplies the reference, the differential harnesses and
the evidence manifests. Rule combinations without coverage stay disabled. Historical verification gaps are
recorded there and do not block new work.

## Results at a glance

| Topic | Result |
| --- | --- |
| Signed bounds, modules, fast FPT | The signed regional and first-gate bounds raise the best NOT-enabled lower bound on 26 and 20 of 106 complete targets (for example threshold-8-5: 14 → 16). Exact module preprocessing reduces 57 targets, and solving their cores exactly closes open intervals. Ten NOT-enabled intervals close in total (for example random-monotone-03 = 7, certified; comparator-10 = 9). The partial counted-NOT bound is exact on 92% of 3-input partial tables. Cotree NOT costs speed up FPT 3.3×. Skeleton NOT optimization matches the counted optimum on every checked 3-input function. The exact low-excess ladder (modules, then one-sharing, then two-sharing) finds 50 monotone and 58 free-NOT minima without SAT, matching SAT on all 16 cores checked at about 400× lower runtime; it closes no new intervals because every open target has excess above 2. An excess-three stage (ordered quotient reconstruction) closes hypergraph-14 = 9 and hypergraph-23 = 9 (monotone and NOT-enabled) and, with SAT confirmation, complete-4 = 7 and threshold-4-3 = 7 (NOT-enabled). The module reduction (raw pair and peel steps) is proved in Lean. Lower bounds that rely on uncertified core minima stay provisional unless marked certified. [Results and statuses](sat-search/NOTES_SIGNED_MODULES.md) |
| Provider-first projection | Verified monotone minima of **8** for `graph-01` and **9** for `hypergraph-08`, with eight rechecked exclusion packets. The six-core excess-three run needed 117 fixed-layout calls. Higher-excess search complements production SAT under the tested caps. [Coverage and replay](sat-search/NOTES_SIGNED_MODULES.md#provider-first-layout-projection) |
| Regional obligation completion | Bounded canonical caching, block completion, and monotone row propagation reduced matched excess-three projection time from **4.18 s to 0.13 s**. Three of eight higher-excess layout probes recovered independently verified witnesses at known minima (`hypergraph-12` and `hypergraph-21` at 8 gates, `hypergraph-03` at 9). Five timed out and no certified interval changed. [Proof, independent oracle, and benchmarks](sat-search/NOTES_SIGNED_MODULES.md#regional-obligation-caching-and-block-completion) |
| Port-first and witness-guided completion | The combined opt-in mode completed all 20 generated signed queries under the 0.35 s per-query cap, up from 13. Its corpus exclusions led to independently certified monotone minima of **11 for `graph-03`** and **12 for `random-monotone-10`**. Input symmetry helped exhaust `comparator-09` at 11 gates. The independent replay excluded 12 as well, leaving **[13, 14]**. [Coverage, proofs, and ablations](sat-search/NOTES_SIGNED_MODULES.md#port-first-partition-propagation-and-witness-guided-completion) |
| Packed regional tables | Packed cofactor checking reduced the time on 23 completed six- to ten-input local queries from **0.476 s to 0.206 s**. Ordered-block pruning remains optional after a whole-layout regression. An opt-in row quotient exhausted the stalled nine-gate `comparator-04` core in **2.06 s**, consistent with the original target's certified 12-gate minimum. [Profiles, proofs, and ablations](sat-search/NOTES_SIGNED_MODULES.md#packed-regional-tables-and-ordered-block-propagation) |
| Regional CDCL fallback | MapleChrono cograph search was slower than the row-quotiented solver on captured port-heavy queries. Lazy row generation reduced peak working set from **274 to 59 MiB**. An absorption construction exposed a five-leaf CDCL core and reconstructed the stalled 12-occurrence signed query in **4.2 ms**. The root portfolio had mixed gains and remains opt-in. No certified interval changed. [Proofs, benchmarks, and reproduction](sat-search/NOTES_SIGNED_MODULES.md#regional-cdcl-and-root-split-portfolios) |
| External baselines (AIG) | On 165 four-input NPN classes (60 s cap, same machine, cold processes, every witness verified, no size disagreements), Percy (SSV, satoko) solved **160** with a 0.087 s median on commonly solved targets, ABC `twoexact -a -g` 150 (0.50 s), our production hybrid 149 (0.20 s), our SAT encoding 149 (1.13 s), Cirbo 117. Our ladder is 2.1x faster than ABC at excess <= 3, but at excess 4 we are 11x slower than Percy, and Percy's whole solved-count lead is at excess 5-6. Next lever: a stronger SAT stage for excess >= 4. Hybrid-Percy (our modules, bounds and ladder, then Percy on the core) beats standalone Percy with the same configuration: 22 vs 20 of a 32-target corpus sample, 8x less matched time, and 27 vs 26 hard four-input classes. Primary-reader caps cut UNSAT time 19% in an SSV encoder on top of full no-reapplication. Restoring no-reapplication inside Percy's AIG mode (which Percy disables) is the biggest gain: hybrid-Percy with it solves 32 of 43 hard four-input classes vs 23 for Percy; the caps add nothing inside Percy. [Setup, records, and caveats](sat-search/NOTES_BASELINES.md) |
| Phase-first signed completion | On 896 signed regional queries captured from free-NOT layout searches, phase-first over the production solver decided **896 vs 873** in 8.5 s vs 22.3 s, losing none; it is slower only on wide queries without repeated providers. It is now the opt-in completion mode `phase-first`. On 547 held-out queries it decided 546 vs 528, and it finished all 48 free-NOT excess-4 layout searches (production: 41) in 3.2x less time on the shared 41. The bounded-multiplicity backend (optional leaves, graft padding, exact fallback) is about 3× faster at finding witnesses but about 4× slower at the exclusions that dominate layout searches; it stays opt-in. The optional-occurrence lemma (extra copies of a repeated provider can always be absorbed) is proved and supports allocation pruning. [Benchmarks and proof](sat-search/NOTES_SIGNED_MODULES.md#phase-first-signed-regional-completion-theoryregional_phase_firstpy-optional) |
| Certificate prescreen | Opt-in `phase-certificate` mode: on 547 held-out signed queries it decided 547 vs 546 and cut UNSAT time from 9.3 s to 4.0 s with 25x fewer local solver calls. The 12 excess-five timeouts remain; profiling shows completion-cache canonicalization, not solving, dominates them. A cheaper, larger cache (`phase-certificate-fastkey`) is up to 2.1x faster but closes no further excess-five search. [Details](sat-search/NOTES_SIGNED_MODULES.md#certificate-propagation-prescreen-for-phase-first-theoryregional_certificate_propagationpy-opt-in) |
| Constructive padding | The optional SAT-free prepass completed **58/60** surplus-heavy queries versus **37/60** for packed row quotient. It reconstructed the signed `wide-8-1-1` query in **5.6 ms**. Five whole-layout jobs gave the same outcomes and slightly higher total time, so the prepass stays optional. [Graft proof and benchmarks](sat-search/NOTES_SIGNED_MODULES.md#constructive-regional-padding) |
| Native regional completion | Opt-in C++20 kernel and phase-first completion match the Python reference and the independent small-query oracle. Matched free-NOT layout time fell **2.19× at excess 4** and **1.17× at excess 5** for phase-first, with higher peak working sets. Twelve excess-5 jobs still timed out. A profile attributes 46.6% of time to cache normalization. An opt-in port of its row packing passed the exact-key differential and awaits idle-machine timing. [Build, checks, and matched records](sat-search/NOTES_NATIVE.md) |
| First-layer constraints in Percy | Optional cared-pair distinctions and a trimmed boundary bound matched all 130 exact-budget oracle checks. Combined constraints cut conflicts **39.6%** on 34 jointly excluded hard-set budgets, with more propagations. All 40 hard-set jobs reached a limit before establishing a minimum. [Proof, encoding, and ablation](sat-search/NOTES_FIRST_LAYER.md) |
| Tight first-layer boundary | Equality reduces the residual to a read-once formula with no sibling pair of directly read primaries. Native completion matched **19,939** independent queries and Percy flags matched **113** fixed-budget oracle jobs. Position-independent set clauses used 98 cuts versus 956 position-specific cuts on 35 jointly excluded budgets. The set-cut configuration completed one fewer size-seven exclusion than the control. No new minimum. [Proof, slack identity, and ablations](sat-search/NOTES_FIRST_LAYER.md#exact-residual-completion-at-the-boundary-bound) |
| Slack-one first-layer boundary | Native completion and extension cuts matched **1,000** slack-one DAG oracle queries and **120** generated extension decisions. On 43 hard Percy targets the opt-in cuts closed **17 vs 13** size-seven budgets, with total wall time **34.8 vs 32.0 s**. No minimum changed. The work cap left 148 of 246 slack-one queries open. [Proof, captured boundaries, and replay](sat-search/NOTES_FIRST_LAYER.md#slack-one-completion-and-boundary-extension) |
| Slack-two first-layer boundary | Exact provider-region completion, parity, failed-frontier caching, and optional singleton unateness. On 44 unique captured Percy boundaries, the full mode excluded **35** at 100k work and **44** at 2M under the same 25 ms limit. The 43-target screen closed **41 size-seven budgets vs 19** with directed slack-one, with wall time **42.1 vs 39.6 s** as more targets reached size eight. The mode remains opt-in. [Proof, extension clauses, and matched records](sat-search/NOTES_FIRST_LAYER.md#exact-slack-two-completion) |
| Singleton phase screen for slack two | Optional packed phase feasibility closed **44/44 vs 35/44** captured exclusions at the existing cap and reduced replay time from **113.4 to 80.3 ms**. Phase alone closed all **43** size-seven budgets. With distinct-type set cuts it closed **40**, found the known eight-gate optimum for `npn4-016a`, and reduced whole-screen time from **44.4 to 36.8 s**. Repeated-set caching reduced work with essentially unchanged local time. [Proof, validation, and four-way ablation](sat-search/NOTES_FIRST_LAYER.md#singleton-phase-screening-and-slack-two-presence-cuts) |
| Slack-three boundary extensions | Optional cuts test every slack-three extension (up to three mixed primaries, or one occurrence plus at most one) with the lower-slack exact recognizers, retaining unknowns. They matched **14,080** native DAG-oracle comparisons and **104** Percy fixed-budget checks. On 43 hard targets the cuts excluded **4-8** size-eight budgets that no slack-two mode excluded (all agree with plain Percy), at **67-86 s vs 34.7 s** wall time; extension recognizers, not the exact query, hit the 25 ms deadline. The vendored occurrence-symmetric tree solver gave **178 vs 175/200** and **1.39x** on the bundle benchmark but no gain on 168 captured production boundaries. [Rule, checks, and matched screen](sat-search/NOTES_FIRST_LAYER.md#slack-three-boundary-extensions-and-occurrence-symmetric-trees) |
| Lazy weighted slack-three cuts | After an exact slack-three exclusion, learn `NOT A OR (W >= w+d)` through a reified weight counter, where every extension costing less than `d` was proved infeasible. Opt-in policies: exact-only, cost-one lift, and adaptive. All four policies agree on the 168 captured boundaries; exact-only takes 20-28% of full's time. On 43 hard targets, **lift1** keeps full's four 25 ms size-eight exclusions with **95 vs 8,720** extension calls (68.3 vs 76.3 s); adaptive at 100 ms matches full's 8 exclusions. No policy beats slack-two on wall time. [Rule, proof, and matched screen](sat-search/NOTES_FIRST_LAYER.md#lazy-weighted-slack-three-cuts) |
| Termination reasons and tiers | Percy and the harness now record why every incomplete budget stopped (`conflict_limit`, `wall_deadline`, `memory`, `harness_kill`) with elapsed time, conflicts and the open budget, and split inner residual unknowns into deadline/work/capacity. The 20k (and 200k) conflict limit is **per CEGAR call** and binds before the wall clock at the rapid and long tiers. At 300 s / 2M only slack-three lift1 established all **10/10** hard-target minima (incl. `166b` = 10); base 8, slack-two 9, slack-three 9. Unknown is never read as UNSAT. [Audit, tiers, and binding-limit tests](sat-search/NOTES_FIRST_LAYER.md#termination-reasons-and-benchmark-tiers) |
| Last-provider decoder phase screen | At the last shared provider, an opposing cared-row pair that agrees on the repeated decoder wires must be split by a singleton literal or by opposite provider values; provider values are parity-component orientations. Opt-in (`--decoder-phase 1`). On 168 captured slack-three boundaries it cut exact tree calls **143,680 -> 13,104** and exact-query time **1,088 -> 519 ms** at 25 ms, with identical verdicts; 28,160 decoder-mode oracle comparisons passed. In the 60 s / 200k tier the residual is 1-4 s of 300-530 s SAT time, so minima are unchanged up to SAT variance. [Proof, checks, and benchmarks](sat-search/NOTES_FIRST_LAYER.md#last-provider-decoder-phase-screen-opt-in) |
| Restriction (gate-elimination) certificates | For a constant or (complementary) identification pi, gates that become constants or aliases are deletable, so `B >= L(f o pi) + D` with exact three-input costs. A deletion caused by a constant operand or by equal/complementary operands needs only the operand-pair selector. Opt-in (`--restriction-cuts cut`). On captured hard size-8/9 CEGAR models, 89-97% of models are certified, with cores of about 5-7 literals. An independent replay of 145,978 models agrees exactly, and 1,418,260 mutations preserve the cores. As local cuts they need 400-1,100 models per row and lose minima time-matched: lift1 300 s 10 -> 7, base 8 -> 6. Stays off; reopen with position-independent or eager encodings. [Rule, checks, captures, tiers](sat-search/NOTES_FIRST_LAYER.md#restriction-gate-elimination-certificates-on-cegar-models-opt-in-negative-end-to-end) |
| Eager restriction counters | Each budget's CNF caps the gates with a provably constant operand under every constant restriction: `sum D <= K - L(f o pi)`. Flags are one-way and reuse shared operand-selection literals; a negative cap is UNSAT directly. Opt-in (`--restriction-counters const`). Oracle 368/368, with caps cross-checks clean in every tier. const8 excludes 99.57% of the 145,978 captured models; about 800 variables at k=8. Time-matched gains in every tier: base 60 s minima 6 -> 9, lift1 60 s 4 -> 8, lift1 300 s 10/10 in 49% of the wall time. Refutes 6996 k=8 in 274 conflicts versus 161k for base. Input-complement normalization alone is negative. [Encoding, coverage, tiers](sat-search/NOTES_FIRST_LAYER.md#eager-constant-only-restriction-counters-in-the-percy-encoding-opt-in-positive-end-to-end) |
| Restricted-output cone counters | Opt-in `--restriction-live all\|N` and `--restriction-essential` (with `--restriction-counters`). Live cone: `sum(R_g AND NOT D_g) >= L(f o pi)`; every input essential to `f o pi` must reach the output. Proven on chains: Percy's ssv encoder has exactly one selection per step (ALO plus pairwise AMO), so symmetry breaks cannot break it. Oracle 160/160. On 145,978 captured models live8+ess8 excludes 556 of const8's 625 survivors. Against lift1+const it cuts hard-budget UNSAT conflicts 2.2-3.7x (1686 k=8, 166b k=9, 1669 k=9), but the witness calls are noisy: 9/10 vs 10/10 at 300 s. Mixed result, stays opt-in. [Rule, replay, tiers](sat-search/NOTES_FIRST_LAYER.md#restricted-output-cone-counters-and-essential-reachability-opt-in-mixed-end-to-end) |
| SAT-encoding explicit bounds (review) | Paper review of ChatGPT's six-bit fragment `11x10y` plus `110100`, which restricts `SAT_n` (pequalnp `encodeCNF`) to q disjoint XNORs. With `C(F_q)=4q-1`, three-gate absorbing elimination and cycle-rank excess monotonicity, it gives free-NOT `B >= floor(4n/3)-3` for even n>=16, which transfers to the Lean counted size (L041 has `5k+1` at `4k+2`). Proofs reviewed with no gap found; finite premises checked with an independent decoder; Percy small minima match. Not Lean-checked, no novelty claim. [Review](sat-search/NOTES_SAT_ENCODING_BOUNDS.md) |
| Projected roots and provider parity | All three opt-in filter modes excluded **34/34** captured Percy boundaries at the offline cap, including the four still open in the baseline. At the production cap, they excluded **22 vs 18**. End to end, each closed **18 vs 17** size-seven budgets while increasing whole-workload elapsed time from **35.1 to 40.9–41.1 s**. No minimum changed. [Proofs, oracle, and ablations](sat-search/NOTES_FIRST_LAYER.md#projected-roots-and-provider-parity) |
| Target-directed residual completion | At the production allowance, the opt-in native backend excluded **34/34** captured boundaries versus **22/34** for full columns, in **14.5 vs 73.4 ms** of summed medians. In the matched 43-target Percy screen it closed **19 vs 18** size-seven budgets and reduced residual time from **2.30 to 0.41 s**. No minimum changed. [Proof, witness checks, and benchmarks](sat-search/NOTES_FIRST_LAYER.md#target-directed-partial-obligations) |
| Complete frontier audit | Checked 1,063 complete-function decisions and 540 direct multislice queries, including counted NOT. The guarded family has rank $3e-1$ and optimum $7e$ by an explicit certificate minor. Affine completion replaced 56 local reconstructions in the matched solver sample. [Proofs and limitations](sat-search/NOTES_COMPLETE_FRONTIER.md) |
| Verification audit | An independent reference solver shares no code with `cube_search` and agrees with brute force on 2,780 cases. Rules were differentially tested through `run_cube` and through the production command line, at M−1, M, M+1, M+2 and M+4 and on pinned and redundant prefixes. Analytical bounds had no violations in 48,130 evaluations. Five defects were found, minimized and fixed or disabled. None affects a recorded result. The rank-tight family closes the universal rank(H) ≤ 2e direction (tested for e ≤ 30). Historical exclusions remain rule-dependent until they have manifests. [Audit, statuses, and revalidation list](sat-search/verify/AUDIT.md) |
| Cross-family benchmark | 100 functions, 2,085 solver jobs, and 583 verified witnesses in the full sweep. Certified minima for 55 monotone cases and 45 NOT-enabled cases. |
| Endpoint follow-up | Retested all 45 open monotone intervals at their lower endpoints. Narrowed 39 intervals and certified 10 more minima, bringing the total to **65 of 100**. Four exclusions have independently checked DRUP certificates. |
| Sharing parameter | Partial monotone synthesis is NP-hard already at zero sharing with every input mandatory and the exact hitting number supplied. The opt-in two-coloring shortcut applied to 121 of 20,439 output-formula query calls in 316 completed benchmark jobs. [Proof and reproduction](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md#hardness-at-zero-sharing) |
| Formula obligations | Typed subtree cuts excluded 929 further output queries on the 316-job replay. Exact obligation search matched exhaustive formula enumeration on 900 partial tables. The replay established no end-to-end speedup. [Proof and measurements](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md#operation-aware-formula-obligations) |
| Regional SAT | A cograph encodes each read-once region with consistent symbolic ports. Joint SAT recovered the five-cycle's seven-gate minimum in 12 port patterns. A proof checker verified every pattern for the six-gate exclusions on the five-cycle and `hypergraph-07`. [Encoding and measurements](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md#cograph-sat-encoding-for-linked-regions) |
| Rectangular distinctions | For `δ = positives × negatives − κ`, the support bound is exact through `δ=3`. A six-label example at `δ=4` needs an extra gate. [Proofs and known answers](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md#distinction-rectangles-and-the-first-sharing-obstruction) |
| Circuit synthesis in `δ` | Certificate intersection, request matching, and bounded extra input choices give exact synthesis with overlapping distinctions and arbitrary monotone sharing in `2^O((δ+1)^4 log(δ+2)) · poly(M,R)` time. A reduction from below-universe Set Cover gives a conditional barrier to polynomial kernels. [Proof, scope, and checks](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md#certificate-reduction-for-overlapping-circuit-distinctions) |
| Certificate intersections | Rank, ordered decomposition, and coexistence coloring give sharing lower bounds on complete functions. The exact terminal encoding closed `complete-5` and `threshold-5-3` at **10 gates each** with checked nine-gate exclusions. [Proofs and reproduction](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md#certificate-intersection-rank-and-regional-decomposition) |
| Lazy certificates | Local intersection constraints and checked spanning-tree clauses gave an exact at-most backend without cograph variables. It matched all eight reference jobs at 0.323 s versus 1.440 s in the serial sample and established five additional non-graph minima. [Proofs and matched comparison](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md#lazy-regional-certificate-compatibility) |
| Regional certificate ports | Compatibility raised the ordered bound on 42 of 90 complete targets, and rank raised it on two more. Clique and exact partition gave no additional target-level gains. The SAT ablation found no speedup. Factoring improved nine construction upper bounds, and the follow-up certified `hypergraph-19` at **10 gates**. [Proofs, benchmarks, and reproduction](sat-search/NOTES_PORT_CERTIFICATES.md) |
| Provider-compatible ports | Full certificate identities preserve provider eligibility and shared-provider consistency. Of 793 sampled layouts, empty lists excluded 367, matching and forced consistency excluded 113 more, and exact partition excluded 11 more. The ordered and SAT replay left target lower bounds and minima unchanged. [Proof, checks, and ablation](sat-search/NOTES_PORT_CERTIFICATES.md#provider-compatible-certificate-bounds) |
| Global provider capacity | Mandatory certificate obligations refine provider lists. Singleton capacity tests excluded 96 of 16,416 ordered four-input layouts beyond the primary and mandatory checks. The ten frozen SAT budgets produced matching verdicts across variants. [Proof, regression, and ablation](sat-search/NOTES_PORT_CERTIFICATES.md#global-provider-capacity-prescreen) |
| Unknown capacity allocation | Deficit raised three whole-target ordered bounds on a 56-case replay, all already covered by independent evidence. Packing and exact allocation added zero whole-target gains. [Conditional bound and benchmark](sat-search/NOTES_PORT_CERTIFICATES.md#allocating-unknown-outgoing-capacity) |
| Non-graph lower bounds | Tight-frontier analysis raised the input-support bound on 61 cases, including 21 of 24 hypergraphs. The ablation raised the monotone lower endpoint beyond every direct SAT job under the cap in 32 cases. |
| Example | `hypergraph-07` has monotone minimum **7**. Antichain search excluded six gates, and direct SAT returned a verified seven-gate circuit. The NOT-enabled interval is **[6, 7]**. |
| L-meta-1343 shard 2 | SAT ruled out sizes through 17. The ordered bound ruled out all 338 size-18 cubes and 315 of 338 size-19 cubes. Splitting the surviving case-A `x0 OR x2` prefix one gate deeper and screening against the budget excluded 204 of 208 continuations in 8.72 s. Four continuations and the other 22 original prefixes remain open. [Deeper split and SAT probes](sat-search/NOTES_L1343.md#one-more-pinned-gate-after-x0-or-x2-2026-11-25) |
| Other graph results | The L-meta-519 seven-cycle with two leaves requires at least 12 gates. The L-meta-1023 Fano-plane search ruled out 13 AND/OR gates in its weights 2–3 model. |
| NOT comparison | All 45 cases with certified minima in both bases agreed. The other 55 NOT-enabled minima remain open. The graph-specific polarity and recursive bounds tightened eight NOT-enabled intervals beyond direct SAT under the cap. |
| pequalnp-proofs review | Their counted-NOT model is identical to our corpus `not` basis. Their lower bounds therefore also bound `mono`, but never AIG. Upstream Lean rows L102/L104/L106/L112 reproduce path-4, C4, cycle-5 and four forest minima. The checked L154 cover circuit lowers recorded upper bounds for `graph-03` (15 → 11), `petersen-10` (29 → 20) and `comparator-08` (22 → 14). Chaining L107 with exact 3-input minima independently matches the first-gate totals parity-5 = 14 and exactly-2-of-5 = 11, but beats no best bound. The L154 cover is now the default upper-bound seed in `synthesis_bench` and skips sizes ≥ the bound in `cube_search`. The native kernels are fixed-budget and need no change. [Model transfer, L-clb-041 analysis, prototypes](sat-search/NOTES_PEQUALNP_PROOFS.md) |

See the [shard proofs and research notes](sat-search/NOTES_L1343.md), [cross-family benchmark report](sat-search/NOTES_SYNTHESIS_BENCH.md), [audit and endpoint follow-up](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md), and [legacy graph results](README.md#results-so-far).

## Techniques and where to find them

| Technique | What to remember |
| --- | --- |
| [SAT cubes and resume](sat-search/cube_search.py) | Pins early gates and verifies witnesses on the truth table. Solver reuse carries learned clauses and counterexample rows across cubes. Monotone run logs record their basis. Resume handling is in [cube_resume.py](sat-search/cube_resume.py). |
| [Partial ordered bounds](sat-search/partial_ordered.py) | Project the suffix onto viable input sets and count ordered terminal groups. Pinned gates can force repeated reads, extra fan-out, and empty regions. Coupled projections make the before and after bounds use compatible feature sets. |
| [Regional synthesis](sat-search/experiments/regional_synthesis.py) and [forward search](sat-search/experiments/regional_search.py) | Fix a regional layout and resolve port values or sources. Local dominance removes dominated formulas once signal values are known. Formula dominance removed 93% of distinct six-leaf boundary tables in the sampled leaf sets. State matching remains opt-in. |
| [Antichain synthesis](sat-search/experiments/antichain_search.py) | Solves monotone at-most budgets with unrestricted fan-out. Exact hitting sets bound remaining gates. A tight budget forces a read-once formula. Direct one- and two-sharing completions are optional. |
| [Subtree cuts](sat-search/experiments/subtree_formulas.py) | Enabled by default. Check tree feasibility before Boolean enumeration. On the excluded six-cycle budget, two-sharing enumeration fell from 16,801 distinct queries to 45, and median time fell from 7.2 s to 35 ms. Survivors still need exact formula synthesis. |
| [Matching interfaces](sat-search/monotone_interface.py) and [relaxed list coloring](sat-search/experiments/interface_coloring.py) | Use crossing matching widths on eligible independent cuts, or test monotone providers with specified ancestor sets. The Heawood example needs seven monotone interface signals against an information lower bound of six. |

## How to interpret the benchmarks

- The full sweep used a **0.5 s** cap per solver job with six concurrent cases. A **12-case serial** sample used a **1 s** cap. Timeouts leave intervals open. [Full sweep](sat-search/results/synthesis_ablation.jsonl) · [Serial sample](sat-search/results/synthesis_serial.jsonl)
- Hitting sets gave the largest reduction in benchmark timeouts. Subtree cuts reduced Boolean formula enumeration from **761 to 83** across 233 jobs with matching verdicts. One-sharing completion resolved two more exclusions under the cap.
- Monotone searches can use boundary rows. NOT-enabled SAT checks every declared label. A pinned-shard exclusion applies to its specified prefix and budget. The conjectured **22-gate lower bound for the full L-meta-1343 function** remains open.

## Reproduce the checks

Run from the repository root using the [Python and SAT setup](README.md#setup). The benchmark runner creates a new output file, so give it a fresh path.

```powershell
python sat-search/experiments/partial_ordered_check.py -v
python sat-search/experiments/antichain_search_check.py -v
python sat-search/experiments/interface_check.py -v
python sat-search/experiments/synthesis_bench_check.py -v
python sat-search/experiments/synthesis_followup_check.py -v
python sat-search/experiments/twocolor_completion_check.py -v
python sat-search/experiments/twocolor_completion_check.py --profile
python sat-search/experiments/label_formulas_check.py --profile
python sat-search/experiments/cograph_formulas_check.py --profile
python sat-search/experiments/cograph_formulas_check.py --frontier-profile
python sat-search/experiments/cograph_formulas_check.py --certify-frontier
python sat-search/experiments/distinction_rectangles_check.py -v
python sat-search/experiments/distinction_circuits_check.py -v
python sat-search/experiments/certificate_rank_check.py -v
python sat-search/experiments/certificate_rank_check.py --profile
python sat-search/experiments/certificate_rank_check.py --endpoint complete-5 9 --proof
python sat-search/experiments/certificate_rank_check.py --endpoint threshold-5-3 9 --proof
python sat-search/experiments/lazy_certificates_check.py --compare --seconds 6 --conflicts 1500
python sat-search/experiments/lazy_certificates_check.py --frontier --seconds 6 --rounds 2 --proof
python sat-search/experiments/summarize_synthesis.py sat-search/results/synthesis_ablation.jsonl
python sat-search/experiments/synthesis_bench.py --family hypergraph --seconds 1 --output fresh-hypergraph.jsonl
```

The [100-case manifest](sat-search/results/synthesis_cases.json) stores labels and construction witnesses. For future runs, record the solver configuration, basis, time cap, and raw results alongside any change to a certified interval.
