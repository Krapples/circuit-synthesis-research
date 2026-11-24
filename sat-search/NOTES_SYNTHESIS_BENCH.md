# Cross-family synthesis ablation

The corpus has 100 distinct labeled instances. A fixed seed generates 24 3-uniform hypergraphs,
10 thresholds, 10 random monotone functions, 10 recursive AND/OR trees, 12 outputs of generated
circuits, 10 outputs of comparator networks, 10 partially specified functions, and 14 graphs.
The graphs include complete, complete bipartite, and random instances plus path and cycle controls
and the ten-input Petersen graph. All other cases have four to eight inputs. Each case has a
construction witness. Each partial instance retains labeled pairs that force all its inputs to
be essential, even for a nonmonotone completion.

## What was compared

| Configuration | Method |
| --- | --- |
| SAT | Generic MapleChrono synthesis with exact row semantics and any wire as the output. The budget is at most. |
| A | Available-signal antichains. |
| B | A plus exact frontier hitting sets. |
| C | B plus read-once completion at tight frontiers. |
| D | C plus subtree cuts. |
| E | D plus direct completion with at most one unit of sharing. |
| F | E plus a precomputed structural lower bound for complete graph functions. This combines the existing recursive, ordered-terminal, and matching-interface analyses. |
| N | NOT-enabled direct SAT plus the existing graph-specific polarity and recursive binary-gate lower bounds. |

All antichain configurations turn off the separate non-distinguishing-signal rule to isolate the
requested sequence. The SAT baseline uses the existing gate and truth-row encoding with padding
allowed and the output selected separately. It uses the same declared basis, with no graph pruning.
The monotone jobs use the same reduced boundary labels. The NOT jobs use every declared label and
run SAT and, where applicable, N. The formula completion and dominance algorithms rely on a
monotone downstream function, so they are outside the NOT ablation. A NOT can reverse the effect
of replacing an input signal with a larger value. Even for a monotone target, a nonmonotone
candidate can agree on the monotone boundary and fail at an omitted row.

The input-support lower bound applies to both bases. The analytical pass also records the
monotone hitting-set bound and whether the tight formula test advances it by one. On complete
graph targets it measures the structural bounds with and without the matching charge. The NOT
graph bound counts binary gates with NOT gates free, so it is also a lower bound on total gates.
The fixed-budget F and N jobs reuse the analytical pass. Its time and memory are recorded
separately. Comparing one-off elapsed times for F or N requires including that setup. The F
comparison uses the numerical bound and leaves the optional matching SAT clauses out of the
antichain engine.

## Measurement and certificates

Each case begins with a verified satisfying construction and the support bound. Up to two
independent SAT probes per basis narrow that interval before selecting shared ablation budgets.
When the reference interval is exact, the ablation evaluates the minimum and one gate below it.
When it remains open, the runner uses the certified endpoints and can add a probe near the
analytical bound. A verified monotone upper bound also applies to the NOT-enabled basis. Both
solvers' outputs are checked by a separate circuit evaluator on every declared row. Complete
cases therefore receive full truth-table verification, and partial cases are checked on their
declared domain. A timeout adds no certificate. Final exact minima require lower and upper
certificates to meet.

Each job uses a fresh spawned process. The fixed cap starts after the worker is ready. Runtime
excludes interpreter startup and parent verification. Peak resident memory includes the worker
and native solver, including at timeout when supported by the host. Formula counters are reported
for completed jobs. They count distinct queries reaching Boolean enumeration, which is different
from the number of gate-search visits or Boolean operations. The full run uses six concurrent
cases for throughput. Its wall times describe that run. The separate serial sample supports
paired wall-time comparisons. Both runs use the same deterministic corpus.

## Full sweep results

The full sweep completed all 100 cases with a 0.5 second cap per job and six concurrent cases.
It recorded 2,085 solver jobs, 583 verified witnesses, and a peak resident-memory value for
every job. Two analytical passes hit the cap, on the eight-input complete bipartite graph and
the Petersen graph. Their unmeasured structural bounds remain blank. [Raw full-sweep records](results/synthesis_ablation.jsonl)

| Family | Cases | Reference exact mono / NOT | Final exact mono / NOT | Tight bound raises support bound |
| --- | ---: | ---: | ---: | ---: |
| Hypergraph | 24 | 6 / 5 | 8 / 5 | 21 |
| Threshold | 10 | 5 / 5 | 6 / 5 | 5 |
| Graph | 14 | 5 / 5 | 6 / 5 | 9 |
| Random monotone | 10 | 3 / 2 | 4 / 2 | 9 |
| Read-once | 10 | 10 / 10 | 10 / 10 | 0 |
| Generated circuit | 12 | 6 / 10 | 10 / 10 | 4 |
| Comparator | 10 | 3 / 3 | 3 / 3 | 7 |
| Partial | 10 | 4 / 5 | 8 / 5 | 6 |
| **Total** | **100** | **42 / 45** | **55 / 45** | **61** |

The improved lower certificates are substantive on this corpus. Exact antichain searches and
structural bounds raised the monotone lower endpoint beyond all recorded direct SAT jobs in
32 cases, including nine hypergraphs. For `hypergraph-07`, with triples 023, 123, 124, and 134,
both the input-support and root tight bounds leave room for six gates. Antichain search proved
six gates impossible within the cap, and direct SAT produced a verified seven-gate circuit.
The final monotone minimum is seven. The NOT-enabled interval for this case remains [6, 7].

| Monotone configuration | SAT | UNSAT | Timeout | Median peak resident MiB |
| --- | ---: | ---: | ---: | ---: |
| SAT | 54 | 104 | 100 | 30.9 |
| A | 80 | 63 | 115 | 30.1 |
| B | 96 | 147 | 15 | 30.2 |
| C | 96 | 137 | 25 | 30.2 |
| D | 96 | 147 | 15 | 30.2 |
| E | 96 | 149 | 13 | 30.2 |
| F, complete graph targets with a measured bound | 14 | 27 | 3 | 30.2 |

Among 233 budgets completed by both C and D with the same verdict, subtree cuts reduced the
distinct formula queries reaching Boolean enumeration from 761 to 83. Tight completion without
cuts added timeouts relative to hitting sets alone. Direct sharing recovered two additional
UNSAT jobs relative to D, at the cost of more formula work. The combined graph-specific analytical
bound exceeded the general tight bound on 10 of 17 complete graph targets where analysis finished.
Adding the matching-interface charge did not raise that combined whole-function bound on this
sample. This comparison does not measure per-cube pruning or the optional structural SAT clauses.

The NOT-enabled polarity and recursive bounds raised the certified lower endpoint beyond all
recorded direct NOT SAT jobs in eight cases. The 45 cases with exact minima in both bases agreed.
No case certified a strict size advantage from NOT, and none of the returned NOT-enabled
witnesses in this sweep used a NOT gate. The cap leaves 55 NOT-enabled minima open, so the run
does not resolve the general question of whether negation helps these functions.

## Serial timing sample

The serial sample covered 12 cases across all eight families, including four hypergraphs. It used
a one-second cap, two reference probes per basis, and one case at a time. It recorded 225 jobs
and 80 verified witnesses. The timing ratios below use only the same case and budget pairs
completed with identical verdicts by both configurations. Timeout counts are shown separately.
[Raw serial records and selected case IDs](results/synthesis_serial.jsonl)

| Change | Paired completions | Median wall-time ratio, before / after |
| --- | ---: | ---: |
| A to B, add hitting sets | 21 | 1.61× |
| B to C, add tight formulas | 26 | 0.96× |
| C to D, add subtree cuts | 27 | 1.07× |
| D to E, add direct one-sharing | 27 | 1.04× |

The serial hypergraph pairs alone showed median ratios of 9.38× for A to B on seven paired
completions and 1.65× for C to D on ten. Across the serial sample, SAT, A, B, C, D, and E timed
out at five, seven, two, one, one, and one of the 28 monotone budgets, respectively. The small
serial sample supports a runtime benefit from hitting sets outside graphs. The larger sweep
shows that the usefulness of sharing and formula completion varies with the family and budget.

## Reproduction

Use a fresh output path to preserve the recorded runs.

```sh
python sat-search/experiments/synthesis_bench.py --manifest fresh-cases.json
python sat-search/experiments/synthesis_bench.py --seconds 0.5 --probes 2 --workers 6 --output fresh-ablation.jsonl
python sat-search/experiments/summarize_synthesis.py fresh-ablation.jsonl
python sat-search/experiments/synthesis_bench_check.py -v
```
