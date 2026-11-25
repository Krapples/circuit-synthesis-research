# External exact-synthesis baselines (Percy, ABC, Cirbo)

Status: bounded screen on the four-input NPN classes, stopped early by request once the measurement was clear.
The corpus sample and the larger workloads (five-input NPN sample, DSD, resub functions, 6-8 input families) were
not run.

## Setup

- **Basis.** AIG size = free-NOT binary AND/OR gate count (De Morgan). Every configuration allows exactly the eight
  AND-type two-input gates with free complementation and no XOR; see [baselines/VERSIONS.md](baselines/VERSIONS.md)
  for the exact commits, builds, flags and why other modes (Percy fence/DITT/MSV, ABC `exact`, Cirbo `lnot_`)
  are excluded. Free-NOT results are not counted-NOT minima and are not compared with monotone decisions.
- **Harness.** [baselines/run_baselines.py](baselines/run_baselines.py): one cold process per tool call on the same
  machine (Ryzen 9 5900X, Windows 11), 60 s wall-clock deadline per (target, tool) job covering the whole
  increasing-budget search including process start-up and preprocessing, 20 jobs in parallel. Every tool starts at
  the trivial lower bound (essential inputs - 1); optimal = SAT at k with every smaller budget UNSAT in the same job.
  Every witness is re-simulated in Python and every gate checked AND-type. PAR-2 charges 2 x 60 s per unsolved job.
- **Tools.** Percy SSV with `set_primitive(AIG)` (standard and CEGAR, solvers bsat2 / satoko / ABC Glucose),
  ABC `twoexact -a` (default, `-g`, `-o -n -u`, both), ABC `allexact -a -K 2` (with and without `-i`), Cirbo
  `CircuitFinderSat` (MapleChrono, CaDiCaL 1.9.5), ours-sat (signed-skeleton encoding with free NOT,
  `theory/phase_budget_cnf.py`), ours-hybrid (production ladder: signed modules, one-sharing, two-sharing,
  `solve3` with `phase-first` completion, then ours-sat on the core from excess 4).

## Records

| File | Contents |
| --- | --- |
| `results/baselines/screen_npn4_clean.jsonl` | **The measurement.** 165 four-input NPN targets with all 16 tool records from the clean (idle-machine) run. |
| `results/baselines/screen_npn4.jsonl` | The full clean run as stopped (3,515 of 3,520 jobs). From record 2,728 on, every ABC call returned empty output (293 records marked `ERROR`), an infrastructure failure, so the 55 targets touched after that point are excluded from the clean subset. |
| `results/baselines/screen_npn4_contended.jsonl` | An earlier complete run (all 222 classes) that shared the machine with another heavy task for its first ~2,000 jobs. Timings are not used; it confirms sizes and witnesses on all classes. |
| `results/baselines/*_cactus.json` | Sorted solve times per tool (cactus-plot data). |
| `results/baselines/corpus_sample.jsonl` | The prepared 32-target corpus sample (seed 20261125); not run. |

Of the 222 NPN classes, 2 are trivial after essential-input restriction (constant, single literal) and are not timed.

## Results (clean subset: 165 targets, 60 s cap)

Verified computational results. No size disagreement between any two tools on any target, in either run; every
reported witness re-simulates correctly; no tool reported a wrong optimum.

| Tool | Solved | PAR-2 (s) | Median on the 117 targets all tools solved | Total on those 117 |
| --- | --- | --- | --- | --- |
| percy-cegar-satoko | **160** | **8.3** | **0.087 s** | 30.5 s |
| percy-std-satoko | 158 | 8.7 | 0.120 s | 34.3 s |
| percy-std-bmcg | 158 | 8.7 | 0.107 s | 43.4 s |
| percy-cegar-bmcg | 153 | 11.9 | 0.108 s | 44.6 s |
| percy-std-bsat / cegar-bsat | 152 / 150 | 12.8 / 13.9 | 0.125 / 0.116 s | 70.9 / 68.8 s |
| abc-two-g (`twoexact -a -g`) | 150 | 13.0 | 0.499 s | 75.2 s |
| abc-two, -onu, -gonu | 149-150 | 13.2-14.1 | 0.50 s | 77-81 s |
| abc-all, abc-all-i | 149 / 150 | 14.7 / 15.2 | 0.52 / 0.58 s | 87 / 122 s |
| **ours-hybrid** | 149 | 17.7 | **0.204 s** | 212.0 s |
| ours-sat | 149 | 19.8 | 1.132 s | 458.7 s |
| cirbo-cadical195 / maplechrono | 117 / 117 | 40.4 / 46.6 | 1.99 / 7.94 s | 902 / 1,936 s |

Peak working set: ABC 22-36 MB, Percy 23-56 MB, our Python solvers about 63 MB, Cirbo 63-70 MB.

**By excess** (excess = optimum - essential inputs + 1; matched over the six representative tools):

| Excess band | Targets | percy-cegar-satoko | percy-std-bmcg | abc-two-g | ours-hybrid | ours-sat | cirbo-cadical195 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| <= 3 | 66 | 0.029 s | 0.039 s | 0.371 s | 0.174 s | 0.472 s | 1.122 s |
| 4 | 51 | 0.392 s | 0.586 s | 0.981 s | 4.283 s | 8.617 s | 14.86 s |

Solved counts by excess are identical for all tools up to excess 4 (51/51 for every tool except Cirbo). At excess 5,
Percy (cegar-satoko) solves 33, ABC 33, ours 32; at excess 6 (optimum 9 gates) only Percy solves anything (10).
Two clean targets are unsolved by every tool.

## Conclusions

1. **Percy is the strongest exact AIG synthesizer here.** With satoko it solves the most targets (160/165) and is
   2.3x faster than our hybrid at the median overall. Its whole lead in solved count is in the high-gate-count
   classes: the 11 targets it solves and we do not are 10 at excess 6 (9 gates) and 1 at excess 5 (8 gates).
2. **Our ladder region is competitive.** At excess <= 3 the hybrid decides every target analytically (one-sharing,
   two-sharing, `solve3`) in 0.17 s median, 2.1x faster than ABC. Most of that is Python start-up and imports
   (the trivial-core cases take about the same time); Percy's compiled SSV still takes 0.03 s.
3. **Our weakness is SAT at excess >= 4.** There the hybrid falls back to the signed-skeleton encoding (83 of the
   149 hybrid optima came from `sat-on-core`), and it is 11x slower than Percy and 4.4x slower than ABC at the
   median. The ladder halves ours-sat's time (4.3 s vs 8.6 s) but does not close the gap. The highest-value
   improvement is a stronger exact SAT stage for excess 4-6: Percy's SSV encoding with its symmetry breaking
   (co-lexicographic fanin order, operator order, all-steps-used, no re-application) and CEGAR row generation is
   the reference to beat, or the hybrid could hand excess >= 4 to an SSV-style encoder seeded with the ladder's
   lower bound.
4. **ABC** `twoexact -a` is a solid middle: same solved count as us, about 4x faster than us at excess 4, slower
   than Percy everywhere. `-g` (Glucose) is its best variant; `-o -n -u` gives no gain on these instances.
   `twoexact -t` starts at N = n + 1 and cannot certify optima of n gates or fewer; the harness drives fixed budgets.
5. **Cirbo** (pure-Python CNF generation) is the slowest and solves nothing above excess 4 within 60 s.

Caveats: four-input functions only; a 60 s cap; ABC is driven one budget per process (start-up included, as for
every tool); the clean subset excludes 55 mostly hard targets after the ABC launch failure, which removes some of
the high-excess classes where Percy leads, so the solved-count gap on all 220 is likely somewhat larger (the
contended run shows the same ordering on all classes).

## Hybrid-Percy: our preprocessing, Percy's SAT engine (2026-11-25)

Tools (`baselines/runners.py`; select with `--tools`): `hpercy-<method>-<solver>` = signed module reduction, then
proved lower bounds on the core (max of n - 1, signed regional bound, free-NOT first-gate bound), then the low-excess
ladder (one-sharing, two-sharing, `solve3` with phase-first completion; excess <= 3 decided exactly), then
`percy_run.exe` on the unresolved core starting at max(bound, n_core + 3). `mpercy-<method>-<solver>` = modules +
bounds, no ladder (ablation). Percy runs with exactly the method and solver of the matching standalone tool. Runners
report `pre_seconds` (our preprocessing, after interpreter start-up) and `synth_seconds` (Percy) separately; the
harness wall time includes cold start-up. Percy's start budget must be a proved lower bound (it decides "exactly k,
all steps used" upward), so optimality is preserved. Complete functions only.

Matched run (`percy-cegar-satoko` vs `mpercy-` vs `hpercy-cegar-satoko`, same 20-worker pool, 120 s cap, every witness
verified, no size disagreements; `results/baselines/hpercy_corpus.jsonl`, `hpercy_hard_npn4.jsonl`):

| Workload | Percy | modules + bounds -> Percy | modules + bounds + ladder -> Percy |
| --- | --- | --- | --- |
| corpus sample (32 targets, 2-10 inputs) | 20 solved, PAR-2 94.5 s | 19, 99.6 s | **22**, **75.2 s** |
| corpus, 19 solved by all | total 42.7 s (median 0.05 s) | 66.6 s (0.21 s) | **5.1 s** (0.21 s) |
| hard 4-input classes (43: unsolved by our old hybrid or by every tool) | 26 solved, PAR-2 127.0 s | 26, 118.8 s | **27**, **115.6 s** |
| hard 4-input, 24 solved by all | total 1,186 s (median 47.3 s) | 919 s (35.7 s) | **918 s** (35.5 s) |

- The ladder decides 18 of the 32 corpus targets without SAT (11 trivial cores after module reduction, 1 one-sharing,
  2 two-sharing, 4 `solve3`), including targets where standalone Percy is slow or times out: graph-02 21.7 s -> 0.4 s,
  random-monotone-09 100.7 s -> 0.3 s, hypergraph-14 and hypergraph-23 timeout -> 0.5 s.
- Preprocessing costs 0.05-0.07 s median (max 2.5 s, first-gate bound on 8 inputs) after a ~0.15 s Python start-up;
  the hybrid's median is therefore 0.2 s against Percy's 0.05 s on easy targets.
- On 4-input cores modules do nothing; the bound start skips UNSAT budgets and cuts the matched total 23%.
- **Percy's per-budget time depends on history.** The same final budget is much faster after the lower budgets
  were solved in the same process (4-input parity, k = 9 SAT, CEGAR + satoko: 0.36 s from start 3 vs 4.4 s from start 9;
  graph-02, k = 8 SAT: 1.0 s after 10.4 s of UNSAT budgets vs 25.4 s cold). The standard method varies in both
  directions (parity 6.0 s vs 2.1 s; graph-02 3.9 s vs 6.0 s). So starting Percy at our lower bound can lose on single
  targets (graph-02 mpercy 55.5 s, random-monotone-09 mpercy timeout; 2 hard classes solved only by standalone Percy),
  and per-target timings are heavy-tailed; the aggregate comparisons above are the robust ones.
- Conclusion: our mathematical preprocessing adds to Percy (+2 corpus targets, +1 hard class, 8x less matched time on
  the corpus, 23% on hard 4-input classes); the ladder is the main contributor, the bound start a smaller one.

## Primary-reader caps in an SSV encoder (2026-11-25)

`theory/ssv_aig.py` is our Python SSV encoder for the free-NOT basis (normal AND-type operators, alonce, colex,
operator order, CEGAR rows, partial functions). It is correct (all 218 essential 3-input functions vs the exhaustive
oracle; 20 four-input classes vs Percy) but much slower than Percy's compiled SSV (4-input parity 59 s), so it is the
vehicle for constraint experiments, not a production stage. Two **minimum-preserving** options, kept separate from
exact-size and pinned-prefix constraints (their UNSAT answers mean "no minimum circuit of size k" and are only used in
the increasing search from a proved lower bound):
- `noreapply_full`: no step reads a node and one of that node's own fanins. Sound: h = op(x, g), g = op'(x, y) is an
  AND-type function of (x, y) or a literal, so h can be rewired to (x, y) at equal size; fanin indices decrease.
- reader caps (`theory/primary_reader_caps.py`): at budget B, input i has at most B - max_a L(f|x_i=a) readers, and
  at most B - L(f|x_i=a) - 1 if some reader absorbs at a and f|x_i=a is nonconstant (needs no reapplication and
  all steps used). L = `ssv_aig.sound_lower` (essential restriction, signed regional, first-gate bounds).
  The prototype's 696 optimal 3-input circuit constructions pass.

Matched run (`experiments/reader_caps_ssv.py`, `results/reader_caps_ssv.jsonl`; 20 four-input classes at excess 4-5,
CaDiCaL 1.9.5, same start bound, 12 workers, 120 s cap; all solved, all sizes agree):

| Configuration | total | median | UNSAT budgets | conflicts | clauses (median) |
| --- | --- | --- | --- | --- | --- |
| base (alonce, colex, oplex, consecutive AND/OR noreapply) | 88.4 s | 2.81 s | 39.6 s | 2.63 M | 19,877 |
| + full no-reapplication | 39.5 s | 1.33 s | 23.0 s | 1.43 M | 16,800 |
| + reader caps | **34.7 s** | **1.07 s** | **18.6 s** | **1.15 M** | 23,418 |

First measured SAT benefit of the caps: -12% total, -19% UNSAT time and conflicts on top of full no-reapplication,
with a larger encoding (cardinality networks). Percy already uses no-reapplication clauses, so the caps' 12-19% is the
part that could transfer to Percy; adding them requires access to Percy's selection/operator variables in the driver.

## Reproduction

```
python sat-search/baselines/run_baselines.py npn4 sat-search/results/baselines/screen_npn4.jsonl --deadline 60 --workers 20
python sat-search/baselines/analyze.py sat-search/results/baselines/screen_npn4_clean.jsonl --by size
```
Run on an otherwise idle machine; see [baselines/VERSIONS.md](baselines/VERSIONS.md) for building the tools.
Workloads: `npn4` (all 222 classes by brute-force NPN canonicalization), `corpus`, or `file:<jsonl>`.

## Not done (next, if the comparison is resumed)

- Corpus sample (`results/baselines/corpus_sample.jsonl`), 1,000 stratified five-input NPN classes, six-input DSD
  benchmarks, single-output functions from https://github.com/alanminko/resub, generated 6-8 input families.
- Diagnose the ABC empty-output failure late in the clean run before any further ABC runs.
