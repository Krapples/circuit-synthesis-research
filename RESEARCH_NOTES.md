# Circuit Synthesis Quick Reference

*Updated November 24, 2026*

The project uses exact synthesis and analytical lower bounds to study small Boolean circuits. The
latest cross-family benchmark shows that frontier bounds transfer beyond graph functions, including
to 3-uniform hypergraphs. The main open shard is L-meta-1343 at size 19.

## Results at a glance

| Topic | Result |
| --- | --- |
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
