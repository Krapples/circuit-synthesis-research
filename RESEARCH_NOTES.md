# Circuit Synthesis Quick Reference

*Updated November 27, 2026*

The project uses exact synthesis and analytical lower bounds to study small Boolean circuits. The
latest cross-family benchmark shows that frontier bounds transfer beyond graph functions, including
to 3-uniform hypergraphs. The main open shard is L-meta-1343 at size 19.

This page is an index. Each result, with its exact scope and grade, lives in the linked topic note.
Bounds hold only in the basis named; do not transfer them between bases.

## Desk steps: strongest result and open endpoint

Full statements: [desk step results](sat-search/NOTES_DESK_STEPS.md).

| Step | Strongest checked result | Open |
| --- | --- | --- |
| L-meta-20754 | Lean: 8-gate witness on all 25 promised pairs; 7 gates impossible in the exact repository model | — |
| rect46/rect45b templates | Solver verdicts (no certificates): 24 UNSAT at budget; tree-DP closes 11 more; all 20 rect45b unreachable at budget | rect46 22162, 22172 at size 12 |
| L-meta-5020 | Lean: false restriction at the two-reader input saves four gates or leaves one of two reader patterns | [submitted reduction](https://github.com/open-goat/pequalnp-proofs/pull/22538) |
| L-meta-9791 | Lean: 54-gate witness; nine-star prefix suffix needs ≥ 9 more gates | 53-gate budget |
| L-meta-5258 | Budget excluded within same-side pinned prefixes leaving two or three stars | unrestricted sub-63 |
| L-meta-9748 | Lean: monotone minimum 23 | unrestricted counted-NOT budget |
| L-meta-4653 | Lean: uniform 40 lower bound; 104 when marked centres induce a forest | unrestricted 104 |
| L-meta-4081 | Lean: edge-charge inequality; structural SAT excluded counterexamples through 12 gates | sizes 13–21 timed out |
| L-meta-7893 | Lean: 20-gate circuit, optimal with separate star covers | 19-gate limit |
| L-meta-11869 | Computational lower bound 17; Lean upper bound 30 | budget 20 |
| L-meta-2216 | Lean: 62-gate construction; 62 lower bound for single-level graph-output cone | budget 61 |
| L-meta-16102 | Lean: 8-gate monotone construction; ≥ 8 binary gates even with free NOTs; excess-3 core shards DRUP-checked UNSAT | posted statement false on this evidence; no PR possible |
| L-meta-17889 | Lean: posted statement is false (K_{2,2} counterexample; the 4-cycle-free hypothesis was dropped); released | no refute twin; no PR possible |
| L-meta-4874 | Lean: 28-gate circuit; 28 lower bound in factorized star-cover form | budget 27 |
| L-meta-9063 | Merged reduction; 29-gate child L-meta-17643 merged | 28-gate child L-meta-17641 |
| L-meta-3754 | Lean: clean-region accounting (`T - 1` ORs), singleton and two-overlap cases | remaining one-junk replacements, many-junk reduction |
| L-meta-1343 shard 2 | SAT through 17; ordered bound kills all 338 size-18 and 315/338 size-19 cubes | 4 continuations + 22 prefixes |
| L-meta-519, L-meta-1023 | Seven-cycle with two leaves needs ≥ 12 gates; Fano search excludes 13 AND/OR gates (weights 2–3 model) | — |

## Benchmark corpus

100 functions; certified minima for **65 of 100** monotone cases after the endpoint follow-up, and
45 NOT-enabled cases. All 45 cases certified in both bases agree. Details:
[cross-family benchmark](sat-search/NOTES_SYNTHESIS_BENCH.md),
[audit and endpoint follow-up](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md),
[legacy graph results](README.md#results-so-far).

## Topic notes

Each note ends with a "Quick-reference summary" table of its headline results.

| Note | What it covers |
| --- | --- |
| [NOTES_DESK_STEPS](sat-search/NOTES_DESK_STEPS.md) | Per-step statements, scopes and evidence links for the table above. |
| [NOTES_THEORY_RESULTS](sat-search/NOTES_THEORY_RESULTS.md) | L-clb-036 degree bound, quadratic witness lookups, sparse routing, cubic cluster, Andreev projection, SAT weight slice, coupled first-gate audit, fork mode cores. |
| [NOTES_SIGNED_MODULES](sat-search/NOTES_SIGNED_MODULES.md) | Signed regional bounds, provider-first projection, regional and phase-first completion, certificate prescreen, padding. |
| [NOTES_FIRST_LAYER](sat-search/NOTES_FIRST_LAYER.md) | First-layer boundaries (tight, slack one to three), restriction certificates and counters, residual completion. |
| [L18065 sweep triage](sat-search/results/l18065/README.md) | Exact AO2 replay with hard worker limits and frontier rows. [Cofactor reader bounds](sat-search/results/l18065/RESTRICTIONS.md) reduced conflicts from 48,197 to 229 at one 7-gate budget; the matched 8-gate replay still hit its wall limit. |
| [NOTES_NATIVE](sat-search/NOTES_NATIVE.md), [NOTES_BASELINES](sat-search/NOTES_BASELINES.md) | Native C++ kernels; external AIG baselines. |
| [NOTES_SYNTHESIS_BENCH](sat-search/NOTES_SYNTHESIS_BENCH.md), [NOTES_SYNTHESIS_FOLLOWUP](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md) | Frozen corpus, endpoint verification, sharing hardness, regional certificates. |
| [NOTES_PORT_CERTIFICATES](sat-search/NOTES_PORT_CERTIFICATES.md) | Port ranks, provider eligibility, global capacity. |
| [NOTES_COMPLETE_FRONTIER](sat-search/NOTES_COMPLETE_FRONTIER.md) | Complete-function FPT, counted NOTs, rank-tight certificates. |
| [NOTES_COFACTOR_WITNESS](sat-search/NOTES_COFACTOR_WITNESS.md), [NOTES_ORIENTATION_QUOTIENT](sat-search/NOTES_ORIENTATION_QUOTIENT.md), [NOTES_SAT_ENCODING_BOUNDS](sat-search/NOTES_SAT_ENCODING_BOUNDS.md) | Cofactor upper bounds, target-directed orientations, SAT-encoding bound review. |
| [NOTES_L1343](sat-search/NOTES_L1343.md) | Fixed-prefix and cube-search work with exact shard scope. |
| [NOTES_PEQUALNP_PROOFS](sat-search/NOTES_PEQUALNP_PROOFS.md) | Comparison with the pequalnp-proofs counted-NOT model. |
| [Verification audit](sat-search/verify/AUDIT.md) | Reference solver, differential harnesses, evidence manifests, historical gaps. |
| [Techniques and reproduction](sat-search/RESEARCH_TECHNIQUES.md) | Search techniques, how to read the benchmarks, reproduction commands. |
| [Research direction](sat-search/workflow/DIRECTION.md) | Priorities, effort split, closed directions. |

See the [shard proofs and research notes](sat-search/NOTES_L1343.md), [cross-family benchmark report](sat-search/NOTES_SYNTHESIS_BENCH.md), [audit and endpoint follow-up](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md), and [legacy graph results](README.md#results-so-far).
