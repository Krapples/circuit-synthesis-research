# Tree DP differential checks

Random monotone 4x5 rect units: the same one-left-one-right rows as rect45b, with random targets taken from
AND/OR circuits that read every input and keep only all-essential units. `tree_dp.exe --smax 2` is compared
with native `template_synth` SAT minima. The check is an exact match when min ≤ n+1, and `gt` otherwise.

| set | units | SAT minima | agree |
| --- | --- | --- | --- |
| `rand80` | 80 | 8 (77), 9 (3) | 80 |
| `hard45_sel` | 66 | 9 (60), 10 (6) | 66 |

- `rand80.txt` comes from an earlier version of the generator (seed 11). `rand80_dp.txt` is the Python
  reference `../tree_dp.py` (s ≤ 1) on it, which agrees.
- `hard45_sel.txt` holds the 66 of `python -B gen_rand.py 400 21 2,3 4 5` (regenerates byte for byte) whose
  minimum is above n-1 = 8.
- `*_native.jsonl` are the `template_synth.exe` records with witnesses. `*_final.jsonl` are the DP results
  of the committed `tree_dp.cpp`.
- To compare: `python cmp_native.py rand80_native.jsonl rand80_final.jsonl`.

These checks have no `gt` cases. The `gt` direction is checked against the SAT-UNSAT sizes of the rect
units themselves (see `../README.md`, section "Tree DP").
