# Certificate preflight beyond graph targets

Sol paired the same complete monotone budget queries with and without a
certificate preflight. Luna located the previously checked budgets and
reviewed the existing coloring implementation. All benchmarks count
two-input AND and OR gates. Full synthesis uses the monotone mode of the
existing [direct SAT encoder](../../experiments/synthesis_bench.py). Both
routes get the same frontier rows and a five-second worker wall limit.
The preflight tries certificate rank and coexistence coloring, then
regional decomposition at low wire-sharing excess. It runs full
synthesis if the preflight leaves the budget open.

## Matched transfer screen

The times below are seconds inside the worker from one run per
configuration. The two SAT preflight results were decoded into circuits
and checked on every assignment.

| Target | Budget | Full synthesis | With preflight |
| --- | ---: | --- | --- |
| hypergraph-07 | 6 | UNSAT, 1.066 s | UNSAT, 0.014 s |
| hypergraph-07 | 7 | SAT, 0.648 s | SAT, 0.056 s |
| threshold-5-3 | 9 | Wall limit | UNSAT, 1.123 s |
| threshold-5-3 | 10 | Wall limit | SAT, 2.037 s |
| comparator-02 | 8 | Wall limit | UNSAT, 0.087 s |
| comparator-05 | 13 | Wall limit | UNSAT by coloring, 0.001 s |

These are transfer controls with prior evidence. The screen measures
whether the earlier graph workflow helps on a different model family
within the same gate basis. It establishes no new minimum. Fresh replays
independently checked the decomposition exclusions for threshold-5-3 at
nine gates and comparator-02 at eight, accepting seven traces with 513
proof additions total.

## Put pair incompatibility directly into the decomposition

If a pair of primary inputs occurs together in some minterm and in some
minimal zero certificate, those inputs cannot be in the same read-once
region. In the local-intersection encoding, the two owner literals already
participate in an at-most-one constraint for that certificate cell. The
opt-in `static_coexistence` setting adds the implied binary clause once
per pair and region, so unit propagation can use the restriction
immediately. It preserves the reference encoding and is measured on its
own with the lazy local-intersection backend.

| Target | Budget | Local intersections | With pair clauses |
| --- | ---: | --- | --- |
| hypergraph-07 | 7 | SAT, 14 conflicts, 0.010 s | SAT, 14 conflicts, 0.010 s |
| threshold-5-3 | 9 | UNSAT, 390 conflicts, 0.286 s | UNSAT, 307 conflicts, 0.248 s |
| threshold-5-3 | 10 | SAT, 1,724 conflicts, 0.373 s | SAT, 885 conflicts, 0.323 s |
| hypergraph-04 | 12 | Wall limit | Wall limit |

The checker accepted six traces covering the nine-gate threshold exclusion
with the added pair clauses. The threshold SAT witnesses were also checked
on all 32 assignments. An exact chromatic-number pass on the coexistence
graphs for all 90 complete frozen targets found no improvement over the
existing clique/bipartite lower bound in this corpus, so exact coloring
was left out of the search path.

## Open probes

At 1,500 requested conflicts per sharing pattern, the terminal and lazy
local backends both reached the five-second worker cap at hypergraph-04
budgets 12 and 13 and threshold-6-4 budget 12. The comparator-05 probe at
budget 14 was skipped under the 400-cell limit. Its 550-cell matrix was
then allowed with a 600-cell limit and static pair clauses, and it
reached the five-second cap. The extended threshold-6-4 probe with the
pair clauses also reached the cap. These queries remain open.

Counting the ordered reader-degree patterns that survive rank and
coloring gives 22 and 64 patterns for hypergraph-04 at budgets 12 and
13, and 29 for threshold-6-4 at budget 12. Comparator-05 at 14 gates
has a single pattern. Its eight mutually incompatible inputs need eight
regions, which forces seven repeated wires. The budget has only seven
extra reads, so each repeated wire has exactly two readers. This case
isolates the cost of assigning and connecting regions within one pattern.

## Reproduction

The [result records](complete-transfer-results.jsonl) contain each
terminal result or wall limit and identify the local runner batch. The
four [transfer](complete-transfer-screen.json),
[open-budget](complete-open-screen.json),
[coexistence](complete-coexistence-screen.json), and
[proof](complete-trace-screen.json) manifests can be replayed with
`python -B sat-search/workflow/research.py run <manifest> --workers 1 --memory-mib 1024`.

```powershell
python -B sat-search/results/l18065/compare_complete.py threshold-5-3 9 --preflight --preflight-only --lazy --static-coexistence --proof
python -B sat-search/experiments/lazy_certificates_check.py
python -B sat-search/experiments/certificate_rank_check.py
```

The circuit argument is at the paper level, solver exclusions have the
proof-check scope stated above, and no Lean or axiom audit was run.
