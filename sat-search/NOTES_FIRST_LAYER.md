# First-layer constraints in Percy SSV

## Implemented scope

The C++20 driver supports `--first-layer edges`, `--first-layer all`, and the independent
`--first-layer-budget`. Codes 2, 4, 8 and 14 are Percy's four normalized AIG operators. Typed
primary-primary and mixed-primary presence variables are equivalent to the selected fanins and operator
bits. A shared native C++ routine computes target-side clauses once per specification, then deduplicates and
removes supersets by subset testing on packed boundary masks. The driver installs the result before CEGAR
adds simulation rows. All options are opt-in. This is free-NOT binary cost.

For any chosen fanins, the remaining circuit receives information from the primary-primary gate outputs
and the primary coordinates it reads directly. If every selected feature agrees on two cared assignments,
topological induction gives equal outputs. A pair with different labels must therefore distinguish on
one of the selected features. At Hamming distance one this also enforces the first-layer projection of the
derivative reader rule. A masking first-layer gate cannot itself supply the required distinction.

For the budget bound, let `h` be the number of first-layer gate **occurrences**, `m` the number of distinct
mixed primaries, and `r=B-h` the number of remaining gates. In a trimmed circuit with `r>0`, each of the
`h+m` boundary signals and each non-output remaining gate needs one reader among the remaining gates.
There are `2r` fanin slots, so `2r >= h+m+r-1`, or `B >= 2h+m-1`. The degenerate trimmed `r=0` case has
one first-layer gate and no mixed primaries. The counter charges twice for each selected first-layer step,
including duplicate typed gates. This bound needs trimming and works at fixed budgets under that assumption.
It neither requires no-reapplication nor makes the existing minimum-preserving reader caps exact-size rules.

The driver bounds the packed prototype to two through five inputs. Partial tables use only cared pairs
and are supported in standard SSV when row zero is labeled. Percy's CEGAR simulator compares the full
table and its normalized basis fixes row zero, so the new options reject unsupported partial driver
combinations explicitly. The complete-table cycle cutoff and signed automorphism symmetry remain
disabled. The two named Python prototype scripts were absent from the available checkout. Existing
symmetry clauses stay on for this experiment because these first-layer conditions hold for every
circuit represented by the trimmed encoding. The budget option rejects `--nosym`, which disables trimming.

## Verification and screening

An independent AIG enumerator checked 130 exact fixed-budget jobs on three inputs at two and three gates,
including output-complemented functions and one partial care set. 60 were feasible and 70 infeasible.
All five configurations matched the expected verdict, and each returned chain was simulated independently.
[Raw correctness replay](results/baselines/first_layer_oracle.jsonl)

The initial hard-set screen used the first eight complete four-input cases from the frozen hard-NPN file,
four workers, Satoko CEGAR, an 8 s wall cutoff per job and a 20,000-conflict cutoff per solver call. Clauses
are added to the same SSV encoder. All 40 jobs returned unknown before proving a minimum. Across the 34
budgets finished as UNSAT by every configuration, the recorded search work was:

| Configuration | Conflicts | Decisions | Propagations | CEGAR rows | Added clauses |
| --- | ---: | ---: | ---: | ---: | ---: |
| Percy | 133,308 | 203,932 | 3,618,836 | 223 | 0 |
| Edges | 95,451 | 165,573 | 3,965,246 | 125 | 20,492 |
| All pairs | 93,666 | 163,431 | 3,786,811 | 113 | 21,723 |
| Budget | 139,683 | 212,652 | 4,761,383 | 224 | 7,652 |
| All pairs + budget | 80,488 | 141,576 | 3,875,724 | 116 | 27,983 |

At budget seven, Percy finished 2 exclusions, edges finished 3, and each other mode finished 4. Joint verdicts
agreed. These are solver verdicts without independent UNSAT proof packets. An earlier Percy process remained
active on another job, so the search-work screen supports no conclusions about elapsed speed or PAR-2.
Each record includes encoding time, CNF counts, peak working set, and the per-budget Satoko counters.
The observed increase in propagations motivates reducing the cost of presence clauses before a wider run.
[Raw hard-set screen](results/baselines/first_layer_hard_screen.jsonl)

## Reproduction

```powershell
$env:PERCY_BUILD_DIR = 'percy-first-layer-release'
& 'sat-search/baselines/build/build_percy.bat'
$percy = 'external/percy-first-layer-release/percy_run.exe'
python sat-search/baselines/first_layer_check.py check sat-search/logs/first_layer_oracle_replay.jsonl --exe $percy --workers 4
python sat-search/baselines/first_layer_check.py screen sat-search/logs/first_layer_hard_replay.jsonl --exe $percy --workers 4 --limit 8 --seconds 8 --conflicts 20000
```
