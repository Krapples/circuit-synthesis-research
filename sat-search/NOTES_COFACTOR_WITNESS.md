# Constructive upper bounds from cofactor two-signal decompositions (2026-11-25)

Source: ChatGPT's `cofactor_witness_native` bundle (kept untracked in `external/cofactor-witness/`; it was
reproduced in a scratch copy, not run in place). This page covers the importer, the external-upper-bound proof
ladder in Percy, the native C++20 port, and the Lean step done alongside.

## Construction (proved, elementary)

Fix a variable x and the cofactors f0 = f|x=0 and f1 = f|x=1 over the other inputs Y. Suppose (f0, f1) is
constant on every fiber of a pair of signals (a(Y), b(Y)) (only care rows count for a partial target). Then
f(x, Y) = d(a(Y), b(Y), x) for some three-input function d. That gives C(f) <= M(a, b) + C_partial(d), where M is the
joint (two-output, free output phases) cost. This is an upper-bound identity only. Nothing here is used to exclude
a budget.

The bundle computes exact M(a, b) for all pairs of three-input functions by a BFS over sets of normalized columns.
Depth 7 reaches 15,548 of 16,384 ordered pairs; 836 are not attained within 7 gates. The decoder is the
minimum-cost completion of the induced partial table, over 6,561 partial labelings. The four-input search
tries, for every split variable:

* separate Shannon;
* the joint recipe of both cofactors;
* every attained pair whose fibers respect the cofactors ("cut").

## Reproduction of the bundle

The bundle was rebuilt with MSVC (`cl /std:c++20 /O2 /EHsc /FIstring`) in a scratch copy, then `pair_recipes 7`,
`cofactor_witness.py --all` and `export_witnesses.py` were run.

* Pair statistics are identical.
* Costs are byte-equal for all 16,384 entries. Recipe codes differ for 13,502 entries because hash iteration order differs.
* Witness sizes are equal for all 222 NPN classes; the cut-mode total is 1,541.
* Generation takes about 3.3 s.

The exported library is copied to `results/cofactor_witness/npn4_witnesses.json`.

## Importer and independent verification

`experiments/witness_import.py` loads the 222 representatives and simulates each one row by row. It indexes all
65,536 four-input functions by (representative, permutation, input mask, output complement). For each target it
rewrites the chain's input literals and re-simulates the result against the target. The witness is used as an
upper bound only. It is not a pinned prefix and need not follow Percy's canonical ordering.

`python -B experiments/witness_import.py results/cofactor_witness/npn4_witnesses.json --all` verifies 65,536 functions
(maximum size 11) in about 4.4 s.

## Percy: proof-only ladder below an external upper bound

`percy_run --upper-witness "a,b;a,b;...|out"` takes a chain in the bundle literal convention (wire 0 is constant
zero, wires 1..n are inputs, wire n+1+j is gate j).

* It rejects the chain (exit 2) if any operand is a constant, if there is a forward reference, if n > 6, if it is combined with `--budget` or `--hybrid-witness`, or if the chain does not compute the target on its care set. The check is a 64-bit simulation in C++.
* It then sets U = |chain| and runs only budgets lo..U-1, each with the full proof configuration.
  * If every budget is UNSAT, U is the minimum and the external chain is printed (`external_chain: true`).
  * If some budget is SAT, the solver's smaller chain is printed.
  * If a budget times out, the interval [k, U-1] is reported open (never read as UNSAT).
* Percy budgets are not monotone, so every budget below U is solved; a known minimum is never used.
* The harness (`first_layer_check.run(..., upper_witness=spec)`) re-verifies every printed chain independently.

**End-to-end check** (`experiments/external_upper_check.py`, mode cone+cond, 60 s per call, ladders from k=1):

* Inputs: all 153 classes with verified minima in `screen_npn4_clean.jsonl`, plus 100 random NPN-transformed members (seed 20261125).
* Result: 253 jobs, **0 mismatches and 0 unknown**.
  * In 235 jobs the witness was proved minimal.
  * In 18 jobs the solver found a chain one gate smaller (for example 066b 10 -> 9).
* Maximum wall time 3.7 s.
* Record: `results/cofactor_witness/external_upper_check.jsonl`.

## Priority targets (`experiments/external_upper_bench.py`)

Setup:

* Extended tier: 300 s and 2M conflicts per call.
* Ladders from k=1, with no witness pass.
* 10 concurrent workers and 3 repeats per configuration. The repeats were identical: the solver is deterministic and every job finished far below the caps.
* Time to upper bound: library load 1.8 s once, then at most 0.1 ms per import and verification.
* No budget stayed open.

Mode names: const = `slack-three-phase-set-lift1-count-const`; +cond adds `-cond`; cone+cond = `...-const-liveall-ess-cond`.

| Target | Witness U | Result | const: proof s / conflicts | +cond | cone+cond | Hardest budget (cone+cond) |
| --- | ---: | --- | --- | --- | --- | --- |
| 0116 | 9 | **9 optimal** | 0.11 / 2,888 | 0.08 / 1,445 | 0.10 / 1,767 | k=8 UNSAT 1,767 |
| 1699 | 8 | **8 optimal** | 0.04 / 1,330 | 0.03 / 856 | 0.03 / 563 | k=7 UNSAT 563 |
| 016a | 8 | **8 optimal** | 0.12 / 4,151 | 0.10 / 3,624 | 0.11 / 3,434 | k=7 UNSAT 3,381 |
| 1669 | 10 | **10 optimal** | 2.06 / 61,102 | 2.03 / 61,867 | 0.66 / 21,546 | k=9 UNSAT 21,333 |
| 1686 | 9 | **9 optimal** | 11.8 / 254,432 | 2.08 / 68,315 | 1.62 / 51,639 | k=8 UNSAT 51,514 |
| 166b | 10 | **10 optimal** | 15.9 / 308,536 | 5.14 / 138,702 | 1.76 / 50,631 | k=9 UNSAT 50,253 |
| 1668 | 11 | **9** (solver SAT at k=9, k=8 UNSAT) | 2.15 / 66,547 | 2.07 / 55,277 | 0.33 / 11,133 | k=9 SAT 10,963 |

Total time to optimality is about 1.8 s (library load) plus the proof time. Comparison with the archived
ascending ladders in the same tier (lift1+const, NOTES_FIRST_LAYER.md, proof-only cone schedule):

* 1686: 224 s (151 s hybrid);
* 1669: 66 s;
* 166b: 66 s, on a lucky k=10 witness. Three control runs of 166b k=10 timed out at 2.2-2.6M conflicts each.

The external bound removes exactly the heavy-tailed SAT call at k = U. The remaining cost is the UNSAT proofs
below U. Their conflict counts match the fixed-budget ablation, where cone+cond was strongest on every hard target.
Caveat: these controls were not rerun (they are expensive and heavy-tailed). The comparison is across sessions
on the same machine.

## Native C++20 port (general targets)

The port is opt-in:

* `native/src/cofactor_witness.hpp`: in-memory pair BFS (depth 7, about 3.1 s, 7,838 unordered pairs), recipe replay and the partial decoder;
* `native/tools/cofactor_synth.cpp`: CLI, one target or `--stdin`;
* `native/build_cofactor.bat`: build script.

It takes any target on 3..6 inputs, with an optional care set:

* m = 3: exact partial completion.
* m = 4: the bundle's search (separate, joint, cut), applied to the projected cofactors and their care masks.
* m >= 5: a recursive heuristic.
  * The signal pair (a, b) is (g0, g1) and, for fully specified cofactors, also (g0, g0^g1) and (g1, g0^g1).
  * Each signal is solved at level m-1, with memoization.
  * The decoder is computed row by row on the completed columns.

A column-hashed builder guarantees built size <= planned estimate. Each chain is pruned to the output cone and
re-simulated in C++, and the checker re-simulates it again in Python.

**Check** (`experiments/native_cofactor_check.py`):

* 222/222 NPN representatives have the library's size (total 1,541 = 1,541).
* All 65,536 four-input functions have exactly the library size of their class (13.6 s including Python verification).
* Random tiers, 200 partial and 200 complete targets per n (seed 20261125), all correct on their care sets:

  | n | Mean complete size | Max size | Max time per target |
  | ---: | ---: | ---: | ---: |
  | 4 | 6.98 | 10 | |
  | 5 | 15.2 | 21 | 2.5 ms |
  | 6 | 30.0 | 37 | 22 ms |

* Frozen corpus, 62 cases with 3 <= n <= 6 (complete and partial). Eleven have verified minima: native U equals the minimum on 8, is +1 on 2 and +4 on 1. None is below a minimum.
* Record: `results/cofactor_witness/native_cofactor_check.jsonl`.

**Assessment:**

* At m = 4 the port is the bundle's search, now for any function and care set, with no library.
* At m >= 5 the candidate pairs are few; random five-input means of 15 are well above typical five-input optima.
* A stronger m >= 5 stage needs a pair search over four-input signals. The joint four-input cost is not tabulated, so candidates would come from the m = 4 plans of the cofactors and their XOR.

Root recombination was not pursued.

## Stronger m >= 5 stage (2026-11-26)

Two opt-in additions to `cofactor_witness.hpp`. Each has a legacy toggle, and n = 4 behaviour is unchanged.

* **a-first partial b** (default on; `--no-a-first` restores legacy):
  * The signal a ranges over the inputs of Y, g0, g1 and g0^g1 (care set c0&c1).
  * On each a-side, b only has to separate two cofactor patterns P (b = 0) and Q (b = 1) that cover that side's rows. Rows compatible with both patterns are don't-cares for b. If one pattern covers a side, b is free there.
  * At most `--b-cap` options are kept (default 8; on these tests the cap never binds).
  * Note: for a complete target, (f0, f1) usually takes all four values. Then (a, b) must be a bijective re-encoding, which the legacy pairs (g0, g1), (g0, g0^g1) and (g1, g0^g1) already cover up to complement. The gain therefore comes from partial and structured targets.
* **root build-and-measure** (`--root-slack K`, default off):
  * Every root candidate within K of the best estimate is built with the column-hashed builder, and the smallest pruned chain is kept.
  * The estimate ignores sharing between a, b and the decoder; the build does not.

Check (`native_cofactor_check.py --random 200`, new `--exe-args` passthrough). All configurations match the library on all 65,536 four-input functions, and every chain is correct on its care set.

| Configuration | n=5 mean / max | n=6 mean / max | Max s per target (n=6) | Corpus gap to 11 verified minima |
| --- | --- | --- | ---: | --- |
| legacy (`--no-a-first`) | 15.18 / 21 | 30.04 / 37 | 0.025 | 0: 8, +1: 2, +4: 1 |
| a-first (default) | 15.10 / 21 | 29.72 / 37 | 0.17 | **0: 11** |
| legacy + `--root-slack 2` | 15.03 / 20 | 29.65 / 36 | 0.025 | 0: 8, +1: 2, +2: 1 |
| a-first + `--root-slack 2` | 14.97 / 20 | 29.29 / 36 | 0.16 | **0: 11** |

Records:

* `results/cofactor_witness/native_cofactor_check_rootslack2.jsonl`;
* summaries in `logs/ncc_{legacy,afirst,rootonly,new}.out`.

### Proof ladders below native bounds, 5-input corpus (`experiments/native_upper_bench.py`)

Setup:

* Native chain: a-first + `--root-slack 2`, re-simulated in C++ and in Python.
* `percy_run --upper-witness` from k=1, extended tier (300 s, 2M conflicts per call), 10 workers. Known minima are not consulted.
* Complete targets use `slack-three-phase-set-lift1` with cegar. The restriction counters (cone+cond) accept only 4-input complete tables.
* Partial targets use `base` with std. First-layer options need std on partial tables. Cegar on partial-07 looped at k=1 (242,754 CEGAR rows, 0 conflicts in 300 s), which is a separate Percy issue.

Results, all 22 five-input corpus cases (total 390 s):

* **20 cases: native U proved minimal** (every budget below U UNSAT).
  * Hardest: complete-5 = 10 (73.8 s; k=9 UNSAT, 990k conflicts) and comparator-02 = 9 (14.9 s).
  * The other 18 finish in at most 0.2 s.
* **partial-07: solver chain of 6** below native U = 7 (SAT at k=6, k=5 UNSAT), 0.4 s.
* **threshold-5-3 = 10.** Ladder: k <= 9 UNSAT (k=9: 1.31M conflicts); k=10 timed out at 2.06M conflicts.
  * An externally supplied 10-gate chain closes the interval. It was verified by row-by-row simulation (importer logic at n=5) and by `percy_run --upper-witness --start 10`, which accepts the chain without solving any budget.
  * The lower bound rests on solver UNSAT verdicts, not on checked certificates.
  * Record: `results/cofactor_witness/threshold_5_3_witness.json`.

Record: `results/cofactor_witness/native_upper_bench_n5.jsonl` (`logs/native_upper_bench_n5.out`).
Reproduce: `python -B sat-search/experiments/native_upper_bench.py OUT [--n 5] [--names ...]`.

## Lean: cascaded constant deletions (formally checked)

`lean/CircuitLemmas/GateElim.lean` adds:

* `ConstUnder`, `Ref.ReadsConst`, `cascade`: gates with an operand whose wire is constant once z := b. This includes z itself and every gate the restriction forces constant.
* `degenerate_of_readsConst`, `degCount_cascade`: every such gate becomes a literal after restriction.
* `readers_le_cascade`: the cascade count contains every reader of z.
* `cascade_restriction`: |C'| + cascade <= |C|, C' computes f|z=b, and functions computed inside C survive, restricted.
* `conditional_counter_cascade`: |C| - cascade(z := b) >= M(f|z=b, H) for every set H of z-independent functions computed in C.

This extends the soundness of the conditional restriction counters from first-level readers to the full cascade
D. `#print axioms` lists only propext, Classical.choice and Quot.sound. Compile:
`cd sat-search/lean; ~/.elan/bin/lake.exe env lean CircuitLemmas/GateElim.lean`.

## Reproduction

```
python -B sat-search/experiments/witness_import.py sat-search/results/cofactor_witness/npn4_witnesses.json --all
python -B sat-search/experiments/external_upper_check.py sat-search/results/cofactor_witness/external_upper_check.jsonl
python -B sat-search/experiments/external_upper_bench.py sat-search/results/cofactor_witness/external_upper_bench.jsonl
sat-search/native/build_cofactor.bat   (call from a path without '=' or via a wrapper .bat)
python -B sat-search/experiments/native_cofactor_check.py sat-search/results/cofactor_witness/native_cofactor_check.jsonl --random 200
```

## Open questions

* m >= 5 on complete random targets is still about 3-4 gates above typical optima. Bijective re-encodings are exhausted, so further gains need joint (a, b) synthesis with sharing or decompositions beyond one split variable.
* Six-input corpus ladders below native bounds (not run).
* Percy cegar on partial tables loops at k=1 (partial-07).
* Whether the existing percy cascade counter D counts exactly the gates `cascade` admits. The Lean bound covers every gate with a constant operand under the restriction, so any D that is a subset of these is sound.
