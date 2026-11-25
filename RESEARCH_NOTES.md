# Circuit Synthesis Quick Reference

*Updated November 24, 2026*

The project uses exact synthesis and analytical lower bounds to study small Boolean circuits. The
latest cross-family benchmark shows that frontier bounds transfer beyond graph functions, including
to 3-uniform hypergraphs. The main open shard is L-meta-1343 at size 19.

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
| External baselines (AIG) | On 165 four-input NPN classes (60 s cap, same machine, cold processes, every witness verified, no size disagreements), Percy (SSV, satoko) solved **160** with a 0.087 s median on commonly solved targets, ABC `twoexact -a -g` 150 (0.50 s), our production hybrid 149 (0.20 s), our SAT encoding 149 (1.13 s), Cirbo 117. Our ladder is 2.1x faster than ABC at excess <= 3, but at excess 4 we are 11x slower than Percy, and Percy's whole solved-count lead is at excess 5-6. Next lever: a stronger SAT stage for excess >= 4. Hybrid-Percy (our modules, bounds and ladder, then Percy on the core) beats standalone Percy with the same configuration: 22 vs 20 of a 32-target corpus sample, 8x less matched time, and 27 vs 26 hard four-input classes. Primary-reader caps cut UNSAT time 19% in an SSV encoder on top of full no-reapplication. [Setup, records, and caveats](sat-search/NOTES_BASELINES.md) |
| Phase-first signed completion | On 896 signed regional queries captured from free-NOT layout searches, phase-first over the production solver decided **896 vs 873** in 8.5 s vs 22.3 s, losing none; it is slower only on wide queries without repeated providers. It is now the opt-in completion mode `phase-first`. On 547 held-out queries it decided 546 vs 528, and it finished all 48 free-NOT excess-4 layout searches (production: 41) in 3.2x less time on the shared 41. The bounded-multiplicity backend (optional leaves, graft padding, exact fallback) is about 3× faster at finding witnesses but about 4× slower at the exclusions that dominate layout searches; it stays opt-in. The optional-occurrence lemma (extra copies of a repeated provider can always be absorbed) is proved and supports allocation pruning. [Benchmarks and proof](sat-search/NOTES_SIGNED_MODULES.md#phase-first-signed-regional-completion-theoryregional_phase_firstpy-optional) |
| Certificate prescreen | Opt-in `phase-certificate` mode: on 547 held-out signed queries it decided 547 vs 546 and cut UNSAT time from 9.3 s to 4.0 s with 25x fewer local solver calls. The 12 excess-five timeouts remain; profiling shows completion-cache canonicalization, not solving, dominates them. A cheaper, larger cache (`phase-certificate-fastkey`) is up to 2.1x faster but closes no further excess-five search. [Details](sat-search/NOTES_SIGNED_MODULES.md#certificate-propagation-prescreen-for-phase-first-theoryregional_certificate_propagationpy-opt-in) |
| Constructive padding | The optional SAT-free prepass completed **58/60** surplus-heavy queries versus **37/60** for packed row quotient. It reconstructed the signed `wide-8-1-1` query in **5.6 ms**. Five whole-layout jobs gave the same outcomes and slightly higher total time, so the prepass stays optional. [Graft proof and benchmarks](sat-search/NOTES_SIGNED_MODULES.md#constructive-regional-padding) |
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
| L-meta-1343 shard 2 | SAT ruled out sizes through 17. The partial ordered bound alone ruled out all 338 size-18 cubes and 315 of 338 size-19 cubes. Forced repeats excluded none of the remaining 15 case-A and 8 case-B cubes. [Size-19 replay](sat-search/NOTES_L1343.md#size-19-ordered-only-replay-2026-11-24) |
| Other graph results | The L-meta-519 seven-cycle with two leaves requires at least 12 gates. The L-meta-1023 Fano-plane search ruled out 13 AND/OR gates in its weights 2–3 model. |
| NOT comparison | All 45 cases with certified minima in both bases agreed. The other 55 NOT-enabled minima remain open. The graph-specific polarity and recursive bounds tightened eight NOT-enabled intervals beyond direct SAT under the cap. |

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
