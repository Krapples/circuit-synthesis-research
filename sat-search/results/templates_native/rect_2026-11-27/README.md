# Desk rect templates: native exact synthesis, 2026-11-27

40 desk steps (20 `rect46-andor-search`, 20 `rect45b-andor-search`; ids in `units.txt`) of the form
`RepSizeAtMost (fun (u : Fin n) (v : Fin m) => MASK.testBit (m*u+v)) s`.

**Target and basis.** Monotone AND/OR circuits, fan-in 2, on the **partial label** given by the
one-left-one-right promise rows only (n*m cared rows; all other inputs unconstrained). Wires
0..n-1 are left inputs and n..n+m-1 are right inputs, as in the Lean statement.

**Grade: solver verdicts only.** No DRAT/LRAT certificates and no Lean proofs. These are not
checked proofs.

## Verdicts (`verdicts.jsonl`)

| template | UNSAT at budget (SAT) | + closed by tree DP | open |
| --- | --- | --- | --- |
| rect45b | 13 | 7 (3 of them at s = 3: 21279, 21288, 21319 have min ≥ 12, budget 11) | 0 |
| rect46 | 11 | 7 | 2 (22162, 22172: min ≥ 12, budget 12) |

The tree-DP column is a separate exact method with its own grade (section "Tree DP"). `verdicts.jsonl`
holds only the SAT verdicts.

`unsat_at_budget` means every exact size 1..budget is UNSAT. That rules out a circuit of at most
`budget` gates: a minimum circuit has every non-output gate read and no gate repeating an earlier
wire on the cared rows, which are the encoding's normal forms. For an `open` unit,
`first_open_size` is the first size that timed out. All smaller sizes are UNSAT, so the minimum is
at least `first_open_size`. Every open unit reached a size of 10 or 11.

## Encoding

`sat-search/native/tools/template_synth.cpp` (commit a8ec18a) with default flags. This is an exact-k
gate model: the output is the last gate, and the sound normal forms are used gates, distinct
gates, colex order of adjacent independent gates, essential inputs for partial labels (see the
source), and the read-slot count. CaDiCaL 2.2 runs with congruence closure off. After a probe,
a size is split into one cube per gate-0 choice. SAT at a size requires a SAT cube; UNSAT
requires every cube to be UNSAT.

## Runs (reproduce from the repo root, built with `sat-search/native/build_template.bat`)

1. `run_120s.jsonl`: `template_synth.exe --threads 22 --seconds 120 < units.txt`, with sizes from
   the sketch floor (field 4) to the budget (field 5), default probe of 10 s.
2. `run_600s_resume.jsonl`: `--threads 22 --seconds 600 --probe 120 < units_resume.txt`. This covers
   the 18 timeouts from run 1, resuming at the size that timed out.
3. `run_below_floor.jsonl`: `--threads 22 --seconds 300 < units_below_floor.txt`. This covers sizes
   1..floor-1 for the 25 units whose sketch floor exceeds 1, all UNSAT within 0.4 s. As a result
   no verdict depends on the desk's stated floor.

Input line format: `ID N GENERAL START BUDGET hexrow:target,...`.

## Checks

- On the 22 nontrivial fixture units, the native minimum size agrees with the independent pysat
  encoding (`template_synth.synth`, maplechrono): UNSAT at k-1 and SAT at k, with and without cube
  splitting.
- L-meta-20891 independently agrees with the Python verdict in `../../templates/verdicts.jsonl`
  (UNSAT, 106 s).
- `solver_cmp.jsonl` / `solver_cmp.py` time the same whole-size CNFs, single-threaded with a
  300 s cap, on three solvers: native CaDiCaL 2.2, pysat cadical195 and maplechrono.
  - The fastest solver was always one of the two CaDiCaL builds: native 2.2 on 20891, 21771 and
    21050, and cadical195 on 21782 (25.1 s vs 30.7 s) and 21319 (64.5 s vs 88.8 s).
  - Maplechrono was never fastest, but it beat native 2.2 once (21319: 83.6 s).
  - The two CaDiCaL builds are within about 1.4x of each other. Native 2.2 is kept because it runs
    in-process with the cube splitting.
  - The run was stopped early once the outcome was clear.

## Tree DP (2026-11-27)

`sat-search/native/tools/tree_dp.cpp` is an exact enumeration of every circuit with at most n-1+S gates,
S ≤ 3 (S ≤ 2 before the generic version), for units whose n inputs are all essential. The proof and scope are in [TREE_DP.md](TREE_DP.md).
It is a program verdict, not a checked proof, and it is independent of the SAT encoding.

- Results: `tree_dp_rect45b.jsonl` (`--smax 2`) and `tree_dp_rect46.jsonl` (`--smax 2 --to-budget`).
  `min_k` means a circuit of that size exists (the generic version also prints a checked witness). `gt: g` means no circuit with at
  most g gates exists. L-meta-20888, 20892 and 23850 have an inessential input and are skipped; all three
  are already UNSAT by SAT.
- Newly closed at budget:
  - rect45b, budget 10: 21127, 21140, 21143, 21160.
  - rect46, budget 10: 23530, 23570, 23680, 23832.
  - rect46, budget 11: 23606, 23625, 23659.
- Raised floors: 22162 and 22172 have min ≥ 12 (SAT had ≥ 10 and ≥ 11). Their budget 12 needs S = 3.
- **S = 3 (generic shapes, witness output).** `tree_dp_rect45b_s3.jsonl` (log `tree_dp_rect45b_s3_log.txt`,
  input `units_rect45b_open.txt`) was run with `--smax 3 --to-budget --threads 11 --heavy 3 --verbose`
  and took 1950 s. 21279, 21288 and 21319 have **no circuit with at most 11 gates**, so they are closed at
  budget. The largest DP had 313M tables, about 5 GB per heavy shape. Validation is in
  `tree_dp_checks/README.md`, section "s ≤ 3". All s ≤ 2 verdicts are reproduced, 1656 exhaustive
  3x3/3x4 targets agree with SAT minima, and every witness passes an independent simulation. The s = 3
  lower-bound direction has no SAT cross-check: SAT at k = 10 timed out on every 4x4 unit the DP called
  > 10.
- rect46 at S = 3 was not run. Going from 4x5 to 4x6 multiplied the p = 2 table counts by about 13 at
  S = 2, so an S = 3 p = 2 DP for 4x6 would hold about 4G tables (over 64 GB). Closing it needs a smaller
  state, for example meeting in the middle on the output tree instead of storing every key.
- Consistency: wherever both methods decided a size, they agree. For example, 21050 and 21051 have DP
  min 10 above their SAT-UNSAT budget, and 22172 is SAT-UNSAT at 10 and DP min > 11.
- Differential checks (`tree_dp_checks/`): on 146 random all-essential 4x5 units with the same rows, the
  DP minimum equals the native `template_synth` SAT minimum: 80 in `rand80` and 66 harder units in
  `hard45_sel`, including 6 with min n+1. The s ≤ 1 levels also agree with the Python reference
  `tree_dp.py` on `rand80`.
- Cost: the tables depend only on the wires, not on the target, so units with the same rows share one
  DP per structure. Each S = 2, p = 2 case is its own DP, which caps memory at about 20 GB for 4x6.
  The 20 rect46 units take 15 min on 22 threads (`--heavy 4`), and the 26-unit 4x5 batch takes 1 min.

Reproduce from `sat-search/native` (built with `build_tree_dp.bat`):
`tree_dp.exe --smax 2 --to-budget --threads 22 --heavy 4 < UNITS`, where UNITS is the rect46 lines of
`units.txt`.

## Read-set cubes: `template_synth --split-reads` (2026-11-27, opt-in)

This option is motivated by the tree DP's slack s = k − (n − 1). After the probe, a size is split on
S, the exact set of wires that carry an extra read. An extra read is a second or later reader of an
essential input or a gate, or any reader of a non-essential input. Two cases make up a cube:

- Each wire in S has at least one extra read.
- Each wire outside S has none. Gates and essential inputs then have exactly one reader, and the
  other inputs have none.

Every circuit determines one S, and the read-slot count gives |S| ≤ k + 1 − E. So the cubes
partition the size: 20 cubes at rect46 k = 10, and 172 at rect45b k = 10. Without the flag the
encoding is unchanged.

- **Check** (`split_reads_check.jsonl`): 11 rect45b units with DP-known minimum m (9 or 10), sizes
  m−1 and m, `--probe 0.01` to force the cube path. Both modes give UNSAT at m−1 and SAT at m,
  and every witness is re-simulated. Wall time: 62 s split vs 85 s gate-0.
- **Matched bench** (`split_reads_bench.jsonl`): one unit at a time, 22 threads, single size
  k = 10. Gate-0 is capped at 1.5× the split time + 10 s.

  | unit | split | gate-0 |
  | --- | --- | --- |
  | 23530 | UNSAT 102.6 s | UNSAT 130.1 s |
  | 23570 | UNSAT 85.6 s | TIMEOUT at 138 s |
  | 23832 | UNSAT 126.1 s | UNSAT 150.1 s |
  | 21127 | UNSAT 536.1 s | UNSAT 527.9 s |

  The split gains 1.2–1.6× at slack 1 and is neutral at slack 2. Run alone, gate-0 also closes these
  sizes. The earlier 600 s timeouts came from units that shared the cube pool. The SAT verdicts at
  k = 10 agree with the tree DP: 23530, 23570 and 23832 (budget 10) and 21127 (budget 10).
- Reproduce: `template_synth.exe --threads 22 --seconds 600 --split-reads < UNIT`, with the unit line
  edited to START = BUDGET = 10.

## Open obligation

After the tree DP (S ≤ 3 on rect45b, S ≤ 2 on rect46), 2 units stay open: rect46 22162 and 22172 at
size 12. SAT sizes 10 and 11 take more than 500 s per size. This needs pruning for
partial labels that is shown to be sound, such as row/column permutations that preserve the mask
or partial-label reader bounds (`cube_search.py --partial*`, monotone only). It also needs
certificates (LRAT) before any of these verdicts are used as proofs.

## Closed direction: mask-automorphism symmetry breaking (2026-11-27)

Left-row × right-column permutations that preserve the mask are sound symmetries for partial labels.
Brute-force group sizes over all 40 units: the 16 open units have |Aut| = 1 (5 units), 2 (5), 4 (4),
12 (1) and 16 (1). The large groups (8-48) all belong to units that are already UNSAT. A symmetry
reduction saves at most a factor |Aut| (typically 1-4), but sizes 10-11 cost 5-10x per extra gate, so
it was not implemented. `cube_search.py --minimal` (no duplicate gates, no absorption or idempotence)
is implied by this encoding's semantic distinct-gate normal form and adds nothing.
Reopen if a family with large mask groups remains open.
