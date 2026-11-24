# P vs NP desk work (pequalnp.com)

Tools and results from working steps of the [pequalnp.com](https://pequalnp.com) attack, mostly exact
circuit-size searches for graph "edge functions" (true iff both ends of some edge are true).

See [Circuit Synthesis Quick Reference](RESEARCH_NOTES.md) for the latest results, open questions, and reproduction commands.

## Layout

| Path | What it is |
|---|---|
| `sat-search/cube_search.py` | Main exact-circuit SAT search (AND/OR/NOT, fan-in 2, every wire used) with many sound pruning rules and analytical lower bounds. `--fast` turns on the benchmarked best set. |
| `sat-search/cube_resume.py` | Resume a stopped search from its logs (skips proven pieces). |
| `sat-search/mono_shard.py` | Monotone (AND/OR) shard search, used for L-meta-1343. |
| `sat-search/fano_search.py` | Multi-output search for the Fano-plane line functions (L-meta-1023). |
| `sat-search/l1343_full.py` | L-meta-1343 shard-2 driver (seed pinned, cases a/b, persistent solvers, straggler racing). |
| `sat-search/range2_graphs.py`, `range2_scan.py` | Enumerate L-meta-519 range-2 graphs and scan them for counterexamples. |
| `sat-search/hard_bench.py`, `solver_bench.py` | Benchmarks on hard pieces (rule comparisons, solver comparisons), with early stopping. |
| `sat-search/results/` | Logs of finished proofs (see below). |
| `sat-search/NOTES_L1343.md` | Theory notes: lower-bound techniques and the open monotone question. |
| `sat-search/experiments/` | One-off tests and checks kept for reference. |
| `gct-086-probe/` | Numerical probe of permanent level spaces (L-gct-086, L-gct-229). |
| `gpu-circuit-search/` | CUDA hybrid exact search (correct but slower than SAT; kept for reference). |

## Results so far

- **L-meta-519** (7-cycle with leaves on two adjacent vertices): minimum circuit size is at least 12
  (sizes 9, 10, 11 UNSAT), so the conjectured bound holds there; the ordered-terminal bound in
  `cube_search.py` now also proves 12 analytically. Logs: `results/c7_two_leaves_*.log`.
- **L-meta-1343** shard 2 (monotone, seed x6|x9, x7|x10, AND): the recorded searches rule out sizes
  through 17. The partial ordered bound rules out size 18 across both shard cases. The analytical
  bound for the whole function is 17. See `sat-search/NOTES_L1343.md` for the size-18 calculation.
- **L-meta-1023** (Fano plane, weights 2–3): no 13-gate AND/OR circuit. Log: `results/fano_p13.log`.

## Setup

Python 3.15 with python-sat vendored into `.scratch-sat/` (the scripts add it to `sys.path`):

    pip install python-sat --target .scratch-sat

`cube_search.py` defaults to 11 worker processes. The L-meta-1343 driver uses 22. Both default to
MapleChrono, which was fastest in the original solver benchmark.

## Cube search options

Search for a four-gate AND/OR circuit for the four-vertex path with the following command.

```sh
python sat-search/cube_search.py --n 4 --edges 0-1,1-2,2-3 --size 4 --fast --monotone --cert --reuse
```

- `--reuse` keeps an incremental solver and its learned clauses and counterexample rows per worker.
  With `--fast`, cubes are passed as assumptions so the solver can switch between them.
- `--monotone` limits the search to AND/OR circuits. `--cert` uses the monotone certificate encoding for
  truth rows. Resume a monotone search with `--monotone --skip-log PATH`.
- `--frontier` adds an experimental fixed-prefix bound and clauses that require the suffix to read signals
  that distinguish opposite target values. The L-meta-1343 driver also accepts `frontier` in its extra flags.
- `--partialordered` projects onto candidate suffix-input sets and bounds the number of ordered terminal
  groups. It requires `--monotone` and analyzes prefixes with up to 16 available features. The L-meta-1343
  driver accepts `partialordered` in its extra flags.
- `--partialrepeat` uses each contiguous pinned gate to identify suffix inputs that must be read again.
  It applies the ordered-group bound with those inputs fixed as singleton groups and reuses the partition
  search across next-gate choices.
- `--partialmultiplicity` counts readers across contiguous pinned gates. `--partialempty` also counts
  repeated internal terminals whose regions contain no suffix inputs. `--coupledprojections` counts
  readers using compatible feature sets before and after the pinned block and combines their bounds
  before taking the minimum. Combine it with `--partialempty` to use both refinements.
- `--matchinginterface` uses crossing matching widths at independent cuts with a C4-free crossing
  graph. It requires `--monotone`. It charges fixed pure gates against excess fan-out and requires
  sufficiently many distinct exported wires in the structural SAT model.

The partial-function options use the same 16-feature limit. The shard driver accepts the analytical
flags as extra flags. Run `python sat-search/experiments/partial_ordered_check.py` to reproduce the
seed, size-18, and size-19 pruning checks without writing to the search logs. Run
`python sat-search/experiments/interface_check.py -v` for the interface checks, including the Heawood
example and the relaxed list-coloring model.

## Regional synthesis experiment

`sat-search/experiments/regional_synthesis.py` checks fixed ordered regions on partial monotone truth
tables. It compares free port values, consistent monotone port signals, and ports wired to earlier
terminals with reader limits. The table backend supports up to six leaves per region. The optional
[cograph SAT backend](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md#cograph-sat-encoding-for-linked-regions)
supports wider regions.
Run `python sat-search/experiments/regional_synthesis_check.py -v` for small exact-minimum, one-port,
and signal-consistency checks. The experiment runs separately from cube search.

The forward search in `sat-search/experiments/regional_search.py` enumerates canonical regional
layouts and prunes dominated concrete boundary-row tables. For example, find the five-cycle minimum
with the following command.

```sh
python sat-search/experiments/regional_search.py --n 5 --edges 0-1,1-2,2-3,3-4,0-4 --max-gates 7
```

The default memoization uses equality. `--state-dominance` enables matching failed states under
dominance and reader limits. The separate `--monouseful` mode searches increasing sizes using gate
usefulness and equality memoization.
An unsupported region width yields `INCONCLUSIVE` in the forward backend if the searched layouts
provide no witness. `--formula-backend cograph` selects the SAT encoding for each candidate layout.
`--formula-backend joint-cograph` also chooses the primary partition inside SAT.
Run `python sat-search/experiments/regional_search_check.py -v` for the forward-search checks.

## Antichain circuit search

The unrestricted at-most-budget experiment keeps only nondominated available signals. It uses an
exact hitting-set bound and switches to read-once formulas when the bound leaves no room for sharing.
The graph CLI verifies returned circuits on every input.

```sh
python sat-search/experiments/antichain_search.py --n 6 --edges 0-1,1-2,2-3,3-4,4-5,0-5 --budget 8
```

Use `--no-tightfrontier` to measure hitting-set pruning alone. `--sharing 1` and `--sharing 2`
enable direct formula completions at small sharing allowances. By default, `--subtreecuts` checks
structural admissibility before enumerating formulas in all three completion modes. Use
`--no-subtreecuts` for an unfiltered comparison. `--nondegenerate` is enabled by
default for targets with both positive and negative rows. `--sharing-order` tries gates that
preserve the allowance first, and `--state-dominance` enables experimental state matching.
`--twocolorcompletion` enables the [two-coloring shortcut](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md#two-coloring-formula-completion)
when every single-zero leaf assignment is labeled positive. `--typedsubtreecuts` propagates
operation-specific labels, and `--labelcompletion` searches final formulas by assigning
ambiguous labels. `--jointcompletion` chooses the suffix inputs and regions together inside SAT
at completion states. The options and replay results are in the
[formula obligations notes](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md#operation-aware-formula-obligations). Run
`python sat-search/experiments/antichain_search_check.py -v` to reproduce the exactness and witness checks.

`--certrank` uses complete graph-function certificates to bound sharing at the root.
`--certdecomp` also uses the certificate co-occurrence coloring bound and a capped SAT
relaxation through excess three. See the [certificate bounds and checked endpoints](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md#certificate-intersection-rank-and-regional-decomposition).

For complete corpus targets, the exact `lazy-certificates` backend checks regional
certificate compatibility and learns spanning-tree clauses. The local-intersection variant
is available in the [matched experiment](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md#lazy-regional-certificate-compatibility).

```powershell
python sat-search/experiments/lazy_certificates_check.py --job hypergraph-12 7 lazy-local-intersection --proof
```

## Cross-family synthesis benchmarks

The deterministic corpus has 100 functions, including 24 3-uniform hypergraphs. It covers four to
eight inputs and includes the ten-input Petersen graph as a separate stress case. The manifest in
`sat-search/results/synthesis_cases.json` stores labels and verified construction witnesses.

```sh
python sat-search/experiments/synthesis_bench.py --family hypergraph --seconds 1 --output hypergraph-run.jsonl
python sat-search/experiments/summarize_synthesis.py hypergraph-run.jsonl
```

Each job runs in a fresh process with a fixed wall-time cap. The runner records solver time,
peak resident memory, verified witnesses, and formula work where available. Timeouts preserve
unresolved intervals. See [the benchmark report](sat-search/NOTES_SYNTHESIS_BENCH.md) for the
configurations, methodology, and recorded results.

The [audit and endpoint follow-up](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md) has the frozen baseline,
the harder-budget comparison, independently checked UNSAT certificates, and a separate signed corpus.
