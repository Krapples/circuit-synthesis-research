# Native (C++20) regional completion: staged migration (2026-11-25)

The Python implementations stay as the reference implementations and correctness oracles. Native code is opt-in,
reached through the normal completion entry point (`ordered_quotient_core.make_completion`), and every native
component is checked against its Python reference before the next one is started.

## Summary

| | Result |
| --- | --- |
| Profile | Regional completion is 89-96% of the free-NOT layout searches at excess 4-5 under `row-quotient` / `phase-first` at excess 5, and 44% under `phase-first` at excess 4 (the rest is the Python layout search). Inside completion, `local_blocks` dominates (`port_partitions` and the witness cover); cache-key normalization is 13% at excess 5 and 2% at excess 4; the phase-first clause build is 3.5-11%. |
| Native library | `sat-search/native`: C++20 core (`regional_core`, Python-free) + pybind11 module `_regional_native`, CMake + Ninja + MSVC 14.51 (`native/build_native.bat`). |
| Ported | Stage A: the recursive kernel `local_blocks` with the production flags (partition generation, provider multiplicities, row obligations, row quotient, witness cover, bounded LRU memoization identical to the reference). Stage B: the read-once prelude, phase-first (`phase_problem`, `phase_domains`, virtual-port recoding, lift) and the adaptive routing, so one native call answers one completion-cache miss. |
| Modes | `native-row-quotient` (= `row-quotient`), `native-phase-first` (= `phase-first`), `native-a-phase-first` (stage A only). |
| Differential | Same verdicts, witness trees and search counters on jointly decided captured queries (547 held out and 896 development). Two independent multislice oracle runs checked 2,000 and 2,002 queries. Layout replay checked complete free-NOT cores. Interrupted native calls return TIMEOUT through `regional_deadline.timed`. |
| Speed | See [Matched measurements](#matched-measurements). |

## 1. Profile (before porting)

`experiments/native_profile.py` (cProfile per worker, merged; the deadline timer thread excluded from the totals;
cProfile inflates small-function cost about 2x, so read the shares). Raw reports: `logs/native_profile_*.txt`.

| Workload | completion share | `local_blocks` | phase-first Python (excl. kernel) | cache normalization | rest |
| --- | --- | --- | --- | --- | --- |
| captured queries, `phase-first` (1,443, 1 s cap) | 100% | ~85% | ~13% (`phase_problem` 11.5%) | 0.6% | |
| captured queries, `row-quotient` | 100% | 99.7% | - | 0.4% | |
| layout e4, `phase-first` (48 cores, 30 s cap) | 44% | 32.5% | ~9% (`phase_problem` 7.4%) | 1.8% | layout search 45% (DP `fixed`, `layout_projection`, `two_sharing_core`), imports 9% |
| layout e5, `phase-first` (48 cores, 30 s cap; 30 done, 18 timeouts) | 95.7% | 62.2% | ~16% (`phase_problem` 3.5%) | 12.6% | ObligationCache wrapper ~4% |
| layout e4, `row-quotient` (39 done, 9 timeouts) | 88.5% | 88.4% | - | 0.1% | |

Inside `local_blocks` (e5): `port_partitions` 30.5% of all time, witness `cover`/`branch` 18.6%, `complete` self
6.4%; the hot spots are the generator machinery (`port_mask` sums, `support_demands`, `row_order`,
`prune_constant_branches`, `require`). Earlier sampling profiles that put normalization at ~80% were taken on the
`phase-certificate` mode, where the solver itself is cheap.

Decision: port `local_blocks` first (stage A), then the phase-first layer around it (stage B), keeping the
ObligationCache normalization in Python for now.

## 2. Native library and build

```
sat-search/native/
  CMakeLists.txt          regional_core (static, C++20, no Python) + _regional_native (pybind11 module)
  build_native.bat        vcvars64 + bundled CMake/Ninja; copies the .pyd next to the sources
  src/regional_kernel.hpp Query / Node / Stats / Result; solve, prelude, solve_completion
  src/regional_kernel.cpp kernel (stage A) and prelude + phase-first + routing (stage B)
  src/bindings.cpp        pybind11: solve_blocks, solve_completion, prelude
theory/regional_native.py Python entry points, fallbacks, completion contract
```

Prerequisites: pybind11 3.1.0 installed into the git-ignored `external/pybind11-pip`
(`python -m pip install --target external/pybind11-pip "pybind11>=3.0"`). Build from PowerShell (the `=` in `P=NP`
breaks plain cmd argument passing):

```powershell
& "sat-search\native\build_native.bat"
```

The module is built for the interpreter on PATH (pyenv 3.15.2, `.cp315-win_amd64.pyd`); a missing module makes
`make_completion('native-...')` raise, and `regional_native.available()` reports it. Build outputs are git-ignored.

### Interface

One Python -> C++ call per completion query, never inside the recursion:

- `completion_native(m, ports, pats, targets, signed, stats, module_filter, adaptive=True|False)` - the full solver
  call behind `ObligationCache` (stage B). `adaptive=True` is `regional_phase_first.adaptive_completion`,
  `adaptive=False` is `local_blocks(..., port_first=True, witness_cover=True, row_quotient=True)`.
- `local_blocks_native(...)` - stage A: Python prelude, native kernel.
- Inputs are compacted in Python (providers renumbered 0..P-1 in sorted order, patterns re-bitted, truth tables
  split into four 64-bit words); witness leaves carry the original provider ids.
- Native ranges: m <= 8 (tables of up to 256 bits; templates for 1, 2, 4 words), <= 64 rows, <= 32 providers
  (<= 16 real providers on the phase-first path, whose virtual ports double them), multiplicity <= 255. Anything
  else falls back to the Python reference (`stats['native_fallbacks']`). No fallback occurred in any workload here.

### Semantics preserved

- **Same algorithm and search order.** Partition enumeration in `itertools.product` order (last provider fastest;
  free blocks with the first one slowest), the port anchor, the component order, the row-option order, the
  dominance pruning, the witness cover (visited cap 4096), the phase-class enumeration (unit propagation, branching
  variable = first maximum of (weight, -domain size)), the virtual-port product. The bounded memoization is an exact
  LRU with `functools.lru_cache` semantics and the same capacities (`complete` 8192, row quotient 4096), so even the
  recursion counters (`rec`, `cover_nodes`, `partition_checks`, `port_allocations`, `quotient_dropped`, ...) agree
  with Python exactly.
- **Exact occurrence semantics** and **signed phases**: unchanged code paths; every witness is checked by
  `regional_production_adapter.check_tree` in the tests, and the phase-first witness is re-checked in production as
  the reference does.
- **Witnesses** in the reference format `('x', i, neg)` / `(op, a, b)`; identical to the Python witness on every
  decided query.
- **Prelude.** The read-once recognition (`one_sharing_core.tree`) and `learn` only contribute leaf phases and the
  lowest-common-ancestor operation of each leaf pair (child order and canonical flattening change neither), which the
  native prelude computes; it equals the Python prelude on all 2,886 captured (query, basis) pairs and on every random
  query.
- **Deadlines / UNSAT vs unknown.** The recursive kernel polls every 1,024 work units. Phase-first also polls during
  row collection, clause generation, sorting and subsumption, and phase and multiplicity enumeration. A poll briefly releases the GIL (so the
  `regional_deadline.timed` alarm thread can run and call `interrupt_main`) and calls `PyErr_CheckSignals()`, which
  raises the resulting `KeyboardInterrupt` out of the native call, exactly as for Python code; `timed` returns
  TIMEOUT. The first version did not release the GIL: the alarm thread could never wake while a native call ran, and
  a pool worker kept running a capped query (found by py-spy, fixed before any measurement below). `work_limit`
  raises `CompletionWorkLimit`; an optional native deadline returns ABORTED, which the wrapper raises, never None.

## 3. Differential tests

| Test | Scope | Result |
| --- | --- | --- |
| `pytest experiments/regional_completion_check.py -k "multislice or canonical"` | 2,000 multislice queries vs an independent formula-column oracle, every mode incl. `native-row-quotient`, `native-phase-first` | pass |
| `native_differential.py random 2000` | 2,002 random queries (m <= 3), oracle verdict; Python vs stage A vs stage B: same tree, same counters (plain and adaptive), same prelude | pass |
| `native_differential.py captured 11 2.0` | 1,443 captured signed queries; plain kernel signed and monotone-relabelled, phase-first; stage A and B | all decided pairs identical (verdict, tree, every counter); see below |
| `native_differential.py deadline` | slowest captured kernel query under `timed(t/20)` must time out and finish under a generous cap. A seeded 4,096-label query must time out during phase-first clause preparation | pass |
| end-to-end layout (below) | 48 cores, excess 4 and 5 | jointly completed decisions agree. Witnesses were rebuilt by `reconstruct` and checked. Aggregate search counters match on jointly completed jobs |

## Matched measurements

Machine: Ryzen 9 5900X; 11 workers; another session's benchmark finished before these runs (checked: no other
Python / Percy / ABC processes). Python 3.15.2, MSVC /O2.

The 2 s captured replay compares exact queries and checks every returned tree. The original timed replay gave
1,419 jointly decided signed block queries and 1,443 each for monotone blocks and signed phase-first.
Signed blocks decided 1,434 natively versus 1,419 in Python. Both phase-first implementations decided all 1,443
(51 feasible and 1,392 infeasible). A separate serial in-process run, without per-query alarm startup, measured
17.74 s → 1.061 s (**16.7×**) on the 1,419 signed block queries that Python decided and 11.63 s → 0.900 s
(**12.9×**) on all signed phase-first queries. The replay after adding clause-preparation cancellation had
1,418 jointly decided signed block queries and 1,443 phase-first queries, with identical trees and counters
throughout. The 4,096-label cancellation regression returned TIMEOUT in 10 ms under a 5 ms alarm.
[Original per-query records](results/native_differential_captured.jsonl)

Whole-layout runs use 48 fully reduced complete cores, the free-NOT basis, and budget `core_n - 1 + excess`.
The Python wall-clock cap was 60 s. Native used the same cap on baseline timeouts and
`min(60 s, max(10 s, 1.5 × Python time))` on completed cases. Totals sum per-job wall times for jointly
completed jobs. Peak working set is the maximum over all 48 jobs for each mode, including timeouts.

| Pair | Excess | Finished Python / native | Joint finishes | Joint time Python → native | Peak MiB Python → native | Raw rows |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| Phase-first | 4 | 48 / 48 | 48 | 55.37 → 25.30 s (2.19×) | 49.1 → 55.4 | [JSONL](results/native_layout_e4_native-phase-first.jsonl) |
| Row quotient | 4 | 41 / 44 | 41 | 64.19 → 17.04 s (3.77×) | 41.6 → 177.3 | [JSONL](results/native_layout_e4_native-row-quotient.jsonl) |
| Phase-first | 5 | 35 / 36 | 35 | 112.58 → 96.18 s (1.17×) | 348.2 → 439.5 | [JSONL](results/native_layout_e5_native-phase-first.jsonl) |

The additional completed searches returned empty results for `comparator-02`, `comparator-04`, and
`random-monotone-10` at excess 4 in row-quotient mode and for `hypergraph-04` at excess 5 in phase-first mode.
These are results of the tested layout search at a fixed allocation, with provisional exclusions at higher excess.
Twelve phase-first excess-5 jobs still timed out. The higher native peak working sets include runs that made more
search progress within the cap. The contribution of the native arena to peak memory remains unmeasured.

On a two-core excess-5 profile after migration, normalization used 46.6% of sampled execution time, completion
on cache miss used 0.2%, and the rest was predominantly Python layout work. `ObligationCache._pack` alone
accounted for 33.17 s of inclusive time over 649,130 calls on that sample. The next candidate is a bounded native
port of normalization, with the Python version as the oracle for normalized rows, column grouping, exact tie-breaking,
and the inverse witness map. [Profile](results/native_profile_layout_native-phase-first_e5.txt)

## 5. Direct Percy integration (investigation)

The existing driver uses Percy's C++ API with the SSV encoder and `spec.set_primitive(AIG)`. An in-process
binding could keep that code in a callable library and expose budget results and chains to the hybrid runner.
The current runner gives each child an enforceable wall-clock cap, and the driver supports per-budget solver
conflict limits. A direct binding would need equivalent wall-clock interruption and an explicit unknown status
for a matched benchmark. Any comparison should preserve independent chain simulation and the driver's
primitive, no-reapplication, and reader-cap settings. The cold process experiment measures time outside the
driver's timed search, including launch, I/O, and witness serialization.
[Baseline configuration](baselines/VERSIONS.md) · [Driver](baselines/percy_driver/percy_run.cpp)

Seven cold single-worker trials per complete table used Satoko CEGAR with a five-second process cap.
All 28 returned AIGs passed independent simulation. Median elapsed time outside the driver's timed search was
18.4 ms (two-input AND), 21.8 ms (four-input parity), 20.3 ms (four-input table `8ff0`), and
19.4 ms (five-input AND). This measures the potential latency saving for short runs. Long runs motivated by
hard-core coverage would benefit from improved SAT search first. A process inventory with access to other
sessions later found a previous Percy run on `e8808000` that the initial process check had missed. Treat these cold
measurements as exploratory. A duplicate pilot on that table exceeded its five-second cap and was stopped by PID.
[Raw trial records](results/native_percy_cold.jsonl)

## 6. Stage C: native row packing within Python normalization

`make_completion('native-phase-first-pack')` uses the stage-B solver and replaces only
`ObligationCache._pack`. For each row index `r`, the packed key has bit `i` equal to bit `r` of column `i`.
Sorting these packed keys gives the same target order as Python because equal packed keys raise the same
row-identity assertion. The binding returns the existing Python target objects and the same occurrence map.
This preserves arbitrary-size target truth tables and the lift's provider indices and phases. Inputs with
more than 64 rows or columns use Python packing.

Checks compare all three parts of the normalized key and normalization counters on 1,443 captured queries
in each of the monotone and free-NOT bases. They also cover the 64-bit boundary, the 65-bit fallback, duplicate
packed rows, and the independent 2,000-query multislice witness oracle. Two complete free-NOT excess-5 cores
compare the exact layout result and completion metrics with stage B. The `comparator-02` witness is
reconstructed at nine binary gates. The empty `exactly-2-of-5` layout result is provisional.

The stage-C timing run is pending an idle machine. Start with `exactly-2-of-5`, `parity-5`,
`threshold-6-4`, and `hypergraph-04`, which exercised substantial normalization work in stage B.
Compare stage C directly with stage B before expanding the port to column grouping or canonical tie-breaking.

## Reproduction

```powershell
& "sat-search\native\build_native.bat"
cd sat-search
python experiments/native_profile.py captured phase-first 1.0 11
python experiments/native_profile.py layout phase-first 5 30 11
python -m pytest experiments/regional_completion_check.py -q -k "multislice or canonical"
python experiments/native_differential.py random 2000 11
python experiments/native_differential.py deadline
python experiments/native_differential.py captured 11 2.0 logs/native_captured_replay.jsonl
python experiments/native_differential.py layout 4 60 phase-first native-phase-first 11 - logs/native_e4_phase_replay.jsonl
python experiments/native_differential.py layout 5 60 phase-first native-phase-first 11 - logs/native_e5_phase_replay.jsonl
python experiments/native_differential.py layout 4 60 row-quotient native-row-quotient 11 - logs/native_e4_row_replay.jsonl
python experiments/native_differential.py layout 5 60 native-phase-first native-phase-first-pack 4 'exactly-2-of-5,parity-5,threshold-6-4,hypergraph-04' logs/native_e5_pack_replay.jsonl
python experiments/native_kernel_timing.py
python experiments/native_differential.py startup
python experiments/native_differential.py percy logs/native_percy_replay.jsonl
```
