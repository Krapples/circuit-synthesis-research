# Techniques and reproduction

Search techniques, how to read the benchmarks, and reproduction commands. Moved word for word from the root RESEARCH_NOTES.md on November 27, 2026.

## Techniques and where to find them

| Technique | What to remember |
| --- | --- |
| [SAT cubes and resume](cube_search.py) | Pins early gates and verifies witnesses on the truth table. Solver reuse carries learned clauses and counterexample rows across cubes. Monotone run logs record their basis. Resume handling is in [cube_resume.py](cube_resume.py). |
| [Partial ordered bounds](partial_ordered.py) | Project the suffix onto viable input sets and count ordered terminal groups. Pinned gates can force repeated reads, extra fan-out, and empty regions. Coupled projections make the before and after bounds use compatible feature sets. |
| [Regional synthesis](experiments/regional_synthesis.py) and [forward search](experiments/regional_search.py) | Fix a regional layout and resolve port values or sources. Local dominance removes dominated formulas once signal values are known. Formula dominance removed 93% of distinct six-leaf boundary tables in the sampled leaf sets. State matching remains opt-in. |
| [Antichain synthesis](experiments/antichain_search.py) | Solves monotone at-most budgets with unrestricted fan-out. Exact hitting sets bound remaining gates. A tight budget forces a read-once formula. Direct one- and two-sharing completions are optional. |
| [Subtree cuts](experiments/subtree_formulas.py) | Enabled by default. Check tree feasibility before Boolean enumeration. On the excluded six-cycle budget, two-sharing enumeration fell from 16,801 distinct queries to 45, and median time fell from 7.2 s to 35 ms. Survivors still need exact formula synthesis. |
| [Mixed-rank cuts](NOTES_MIXED_RANK_CUTS.md) | Opt-in (`percy_run --mixed-rank-cuts F`, `direct_sat(mixed_cuts=...)`). Uses the scalar ceiling R <= 2^(t+1)-2 (paper proof, not Lean checked) to force at least floor(R) mixed AND gates per input cut of a complete function. Sound and checked, C++ = Python on all 4-input tables. Excludes 19% of captured Percy candidates but gives no matched speedup, because the floors are at most 3. Also lists the handoff results that do not apply, and the open bottlenecks. |
| [Matching interfaces](monotone_interface.py) and [relaxed list coloring](experiments/interface_coloring.py) | Use crossing matching widths on eligible independent cuts, or test monotone providers with specified ancestor sets. The Heawood example needs seven monotone interface signals against an information lower bound of six. |

## How to interpret the benchmarks

- The full sweep used a **0.5 s** cap per solver job with six concurrent cases. A **12-case serial** sample used a **1 s** cap. Timeouts leave intervals open. [Full sweep](results/synthesis_ablation.jsonl) · [Serial sample](results/synthesis_serial.jsonl)
- Hitting sets gave the largest reduction in benchmark timeouts. Subtree cuts reduced Boolean formula enumeration from **761 to 83** across 233 jobs with matching verdicts. One-sharing completion resolved two more exclusions under the cap.
- Monotone searches can use boundary rows. NOT-enabled SAT checks every declared label. A pinned-shard exclusion applies to its specified prefix and budget. The conjectured **22-gate lower bound for the full L-meta-1343 function** remains open.

## Reproduce the checks

Run from the repository root using the [Python and SAT setup](../README.md#setup). The benchmark runner creates a new output file, so give it a fresh path.

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

The [100-case manifest](results/synthesis_cases.json) stores labels and construction witnesses. For future runs, record the solver configuration, basis, time cap, and raw results alongside any change to a certified interval.
