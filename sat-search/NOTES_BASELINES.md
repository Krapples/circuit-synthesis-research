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
