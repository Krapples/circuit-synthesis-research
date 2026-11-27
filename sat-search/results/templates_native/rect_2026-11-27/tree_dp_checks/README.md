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

## s ≤ 3 (generic shapes, 2026-11-27)

The generic version (`--smax 3`, witness output) reproduces every s ≤ 2 verdict above, on `rand80`,
`hard45_sel`, and the 26-unit 4x5 batch of rect45 and random units. Folder `s3/`:

| set | units | reference | result |
| --- | --- | --- | --- |
| `a33` (all 3x3 targets, `gen_all.py 3 3`) | 156 | SAT minima 5-7 | 156 agree |
| `a34` (all 3x4 targets, `gen_all.py 3 4`) | 1500 | SAT minima 6-8 | 1500 agree |
| `t44` (`gen_randT.py 120 11 4 4`) | 120 | 46 SAT minima 7-9, 74 timeouts at 9 | 46 agree; DP gives 9 (42), 10 (26), > 10 (6) |
| `t44b` (`gen_randT.py 1000 12 4 4`) | 1000 | — | DP min 7-9 (768), 10 (193), > 10 (39) |

- Every DP witness (1770 for a33/a34/t44, 961 for t44b) passes the independent row-by-row simulation in
  `check_wit.py`. That settles the upper-bound direction.
- The s = 3 witnesses of `t44b` use every shape family: (p, e) = (0, 3) 27, (1, 2) 20, (2, 1) 88, (3, 0) 58.
- Not checked: the s = 3 lower-bound direction. No 3x3 or 3x4 target needs s = 3. On the 39 `t44b` units
  with DP > 10, `template_synth` at exactly k = 10 (`t44b_gt10_k10.txt`) timed out after 120 s on all 39,
  so SAT cannot confirm them.
