# Mixed-rank cuts: audit of the ChatGPT handoffs against the synthesis engines (2026-11-26)

This audit checked the latest results in [chatgpt_handoff/](chatgpt_handoff/) against the existing synthesis, pruning and
lower-bound code. One result became a sound pruning rule, the scalar mixed-rank ceiling. It is implemented in C++
(Percy driver) and in Python (reference and direct SAT). It stays **opt-in**: it is sound, but the matched benchmarks
below do not show a speedup.

## Status of each handoff result

| Result | Status | Used for pruning? |
| --- | --- | --- |
| Scalar mixed-rank ceiling R(f, X) <= 2^(t+1) - 2 ([first_gate_translation_proof_handoff.md](chatgpt_handoff/first_gate_translation_proof_handoff.md)) | Paper proof (square-zero first-gate induction). **Not Lean checked.** Sharp: the rank-one chain gives 2, 6, 14 (checked here). | Yes, opt-in: `--mixed-rank-cuts F` (C++), `mixed_cuts=` (Python). |
| Joint (multi-output) mixed-rank ceiling ([joint_translation_rank_handoff.md](chatgpt_handoff/joint_translation_rank_handoff.md)) | Conjecture, reduced to a direction bound. | No. |
| Mixed-dependency rank recurrence and ledger ([mixed_dependency_rank_handoff.md](chatgpt_handoff/mixed_dependency_rank_handoff.md)) | rho0: R+2, rho1: 2R+2, rho2: 3R+2+C(R,2). The two-gate ceiling of 6 is a special case of the scalar theorem. | Only through the scalar theorem. |
| Two-sided degree-rank bound L+M <= t+1 ([two_sided_degree_rank_handoff.md](chatgpt_handoff/two_sided_degree_rank_handoff.md)) | Proven. As a lower bound on the total gate count it is **dominated by the support bound n-1**: a probe of the corpus found no case above n-1. | No (no gain). |
| Response periods and ingress compression ([response_period_handoff.md](chatgpt_handoff/response_period_handoff.md)) | Invariant in a communication model. It does not charge AND gates, so it has no counterpart in the exact gate-count engines. | No (does not apply). |
| Multi-baseline intersection ([multi_baseline_transversal_handoff.md](chatgpt_handoff/multi_baseline_transversal_handoff.md)) | Negative theorem: changing the baseline cannot add operand information. | No (nothing to gain). |
| Affine-prefix rank reserves ([affine_prefix_rank_reserve_handoff.md](chatgpt_handoff/affine_prefix_rank_reserve_handoff.md)) | Per-prefix reserves for the graph-selector families. They need a pinned affine prefix, which the generic engines do not expose. | No (not applicable to the generic engines yet). |

## The rule

Split the inputs into a side X and its complement Q. Define H(x, q) = f(x,q) ^ f(x,0) ^ f(0,q) ^ f(0,0), and let
R = rank_GF(2)(H). If t AND gates of a circuit read both sides structurally, then R <= 2^(t+1) - 2, so
t >= floor(R) = bit_width(R+1) - 1.

Scope:
- Complete functions only. A partial table has no fixed completion rank. Percy rejects `--mixed-rank-cuts` together
  with `--dc`.
- Bases: AIG, and AND/OR/NOT with free NOT. Structural reading over-approximates semantic dependence, which can only
  increase t.
- The count is restricted to the output cone. In both encodings, cone membership is a least fixpoint, so gates that
  are not in the cone cannot be counted as mixed.

Implementation:
- [native/src/mixed_rank.hpp](native/src/mixed_rank.hpp): word-row GF(2) rank, and per-cut ranks cached on the
  per-class counts of swap-symmetric inputs (symmetry reduction). It selects up to 8 cuts per table.
- [baselines/percy_driver/percy_run.cpp](baselines/percy_driver/percy_run.cpp) `--mixed-rank-cuts F` encodes, per cut:
  pure-X and pure-Q literals per step, defined from the SSV selection variables; reach literals for the output cone;
  and an at-most constraint on the non-mixed steps (at most k - floor). Each budget's JSON record reports
  `mixed_cuts`, `mixed_vars`, `mixed_clauses`, `mixed_seconds` and `mixed_floors`. Build with
  `$env:PERCY_BUILD_DIR="percy-build-mixed"; & baselines/percy_driver/build_percy.bat`.
- [mixed_rank_cuts.py](mixed_rank_cuts.py): the Python reference, plus the CNF for the cube_search and direct_sat
  encodings. `synthesis_bench.direct_sat(..., mixed_cuts=...)` gets the padded/cone version. A cube_search flag is
  kept only as a patch:
  [results/mixed_rank_cuts/cube_search_mixedrankcuts.patch](results/mixed_rank_cuts/cube_search_mixedrankcuts.patch).

## Verification

- [experiments/mixed_rank_cuts_check.py](experiments/mixed_rank_cuts_check.py) (about 4 s) checks:
  - the rank against a dense reference;
  - the floor values;
  - the chain ranks [2, 6, 14];
  - that the theorem holds on every n=4 circuit with at most 3 gates (14,816 circuits, 103,712 cuts) and on 3,000
    random n=5–6 circuits;
  - that the encoding is exact: with the circuit pinned, the CNF is SAT iff count >= floor (288 exact-size and 208
    padded CNFs);
  - that every corpus witness satisfies its floors (90 complete cases).
- C++ vs Python: `experiments/mixed_rank_cuts_native.py differential --all4 --n5 200` found 0 mismatches. It compared
  the cut lists Percy prints with `select_cuts` on all 65,536 four-input tables and 200 random five-input tables
  (65,736 tables, 65,704 with cuts). Log: `logs/mixed_rank_native_diff.out`.
- Coverage replay on 145,978 captured Percy CEGAR candidate chains (`logs/restriction_capture`): the floor >= 1 cuts
  exclude 28,261 of them (19.4%) and the floor >= 2 cuts exclude 28. This count is independent of the CNF.
  [results/mixed_rank_cuts/captured_replay.jsonl](results/mixed_rank_cuts/captured_replay.jsonl).

## Benchmarks (matched, same binary or same encoder)

- Python direct_sat, n=6 corpus, budgets n-1 … n+4, 15 s cap
  ([bench_n6_low.jsonl](results/mixed_rank_cuts/bench_n6_low.jsonl)):
  - No verdict disagreements.
  - Over the 114 jobs both arms decided, mean time ratio vs base: cuts2 6.6x (SAT) and 3.7x (UNSAT); cuts1 14.2x and
    4.0x.
  - Conflicts: +4% (SAT) and +21% (UNSAT).
  - Under the cap, cuts decided 3–4 jobs that base timed out on and lost 4–5 that base decided.
  - Verdict: slower.
- Native Percy CEGAR, npn4 hard targets, budgets 8 and 9, 120 s cap
  ([native_bench_npn4.jsonl](results/mixed_rank_cuts/native_bench_npn4.jsonl)): no verdict disagreements; 166b and 1686 at k=9 time out in all arms. Only 016a has floor-2 cuts, so cuts2 is identical to control elsewhere. Wall ratios vs control over the 16 decided pairs: cuts1 geomean 0.93 (0.11–1.86), cuts2 0.99. On UNSAT, the proof direction, cuts1 ranges 0.75–1.70: 1669 k=9 71.6→53.9 s, 166b k=8 14.9→12.0 s, but 1668 k=8 12.6→19.8 s and 16a9 k=8 11.2→19.0 s. The large SAT ratios (1699 k=9 5.9→0.7 s, 016a k=8 cuts2 1.2→7.4 s) are search-order noise. Verdict: neutral; keep opt-in. Single seed and single run per arm, so a 20% difference is within noise.

Why the cuts do not pay off: the floors are logarithmic in the rank. On the corpus the maximum floor is 3, and on
n=4 tables it is at most 2. Most candidates already satisfy them. The extra pure/reach variables (about 560 variables
and 5,600 clauses per budget on 1668 k=7) cost more propagation than the pruning saves.

## Bottlenecks for the research agents

1. **Rank-two and higher gates.** The ceiling is 2^(t+1) - 2 because each mixed gate can at most double the rank and
   add 2. A floor that grows linearly in R needs a charge for rank-two gates, which the mixed-dependency ledger leaves
   open. That would give strong cuts.
2. **The joint ceiling.** A proof of the multi-output version would allow several cuts to be combined into one count
   (shared mixed gates), instead of the current per-cut maximum.
3. **Partial functions.** Practical targets with don't-cares need a lower bound on the minimum completion rank
   (a min-rank completion over GF(2)). This is NP-hard in general, but small instances may be tractable.
4. **Cone-local floors.** A floor for sub-functions at fixed internal wires (for example, cut ranks of a pinned
   prefix's residual) would interact with cube pinning, where the global floor is already satisfied.

## Reproduce

```powershell
python -B sat-search/experiments/mixed_rank_cuts_check.py
python -B sat-search/experiments/mixed_rank_cuts_native.py differential --all4 --n5 200
python -B sat-search/experiments/mixed_rank_cuts_replay.py sat-search/logs/restriction_capture --output sat-search/results/mixed_rank_cuts/captured_replay.jsonl
python -B sat-search/experiments/mixed_rank_cuts_native.py bench --targets 0116,016a,0196,1668,1669,166b,1686,1699,16a9 --budgets 8,9 --seconds 120 --workers 10 --output <fresh path>
python -B sat-search/experiments/mixed_rank_cuts_bench.py --output <fresh path> --max-n 6 --seconds 15 --workers 10 --deltas low
```
