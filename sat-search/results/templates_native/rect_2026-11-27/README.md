# Desk rect templates: native exact synthesis, 2026-11-27

40 desk steps (20 `rect46-andor-search`, 20 `rect45b-andor-search`; ids in `units.txt`) of the form
`RepSizeAtMost (fun (u : Fin n) (v : Fin m) => MASK.testBit (m*u+v)) s`.

**Target and basis.** Monotone AND/OR circuits, fan-in 2, on the **partial label** given by the
one-left-one-right promise rows only (n*m cared rows; all other inputs unconstrained). Wires
0..n-1 are left inputs and n..n+m-1 are right inputs, as in the Lean statement.

**Grade: solver verdicts only.** No DRAT/LRAT certificates and no Lean proofs. These are not
checked proofs.

## Verdicts (`verdicts.jsonl`)

| template | UNSAT at budget | open |
| --- | --- | --- |
| rect45b | 13 | 7 |
| rect46 | 11 | 9 |

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
  300 s cap, on three solvers: native CaDiCaL 2.2, pysat cadical195 and maplechrono. CaDiCaL won
  on every finished CNF. The run was stopped early once the outcome was clear.

## Open obligation

Sizes 10 and 11 on the 16 open units take more than 500 s per size. This needs pruning for
partial labels that is shown to be sound, such as row/column permutations that preserve the mask
or partial-label reader bounds (`cube_search.py --partial*`, monotone only). It also needs
certificates (LRAT) before any of these verdicts are used as proofs.
