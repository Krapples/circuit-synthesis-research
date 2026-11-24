# P vs NP desk work (pequalnp.com)

Tools and results from working steps of the [pequalnp.com](https://pequalnp.com) attack, mostly exact
circuit-size searches for graph "edge functions" (true iff both ends of some edge are true).

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
- **L-meta-1343** shard 2 (monotone, seed x6|x9, x7|x10, AND): no circuit genuinely using the seed with
  17 or fewer gates. The analytical bound for the whole function is 17. Logs: `results/l1343_shard2*.log`.
- **L-meta-1023** (Fano plane, weights 2–3): no 13-gate AND/OR circuit. Log: `results/fano_p13.log`.

## Setup

Python 3.15 with python-sat vendored into `.scratch-sat/` (the scripts add it to `sys.path`):

    pip install python-sat --target .scratch-sat

Searches use 22 worker processes by default on a 12-core / 24-thread machine; MapleChrono is the default
solver (benchmarked fastest on these instances).
