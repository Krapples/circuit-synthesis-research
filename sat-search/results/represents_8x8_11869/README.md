# L-meta-11869 reproduction

The target is the 8-by-8 table with row-major word `7583035862004050432`. Bit `8*u + v`
labels the input with exactly row `u` and column `v` active. The declared basis is AND/OR with
fan-in at most two. The requested exclusion is size at most 20. Row zero has no positive labels.

Run the Python scripts in [repro](repro/) from the repository root with the bundled PySAT build
in `.scratch-sat`. Each run uses 22 workers and writes a fresh JSONL record under
`sat-search/logs`. Each `OPEN` result denotes a solver time cap.

| Script | Scope | Result |
| --- | --- | --- |
| `rep-sat.py` | At most 20 gates, 161 normalized first-gate shards, 24 seconds per shard | 161 open |
| `rep-connected-sat.py` | Exact-size connected circuits, 24 first-gate orbits per size, 25 seconds per shard | At size 15, 19 UNSAT and 5 open. At each size 16 through 20, all 24 open |
| `rep-rectangle-sat.py` | Positive and dual negative rectangle covers with shared disjunctions built from disjoint unions, sizes 20–30, 25 seconds per job | 30-gate positive-cover witness. Restricted budgets 20–23 excluded for positive covers and 20–26 for negative covers |

The unrestricted SAT sweeps certify no entire gate budget. The rectangle exclusions apply to
the encoded construction class. The 30-gate witness was independently evaluated on all 64 labels
and checked by Lean in [the local upper-bound proof](audit-L-meta-11869-upper.lean).

Build `repro/rep-single-shared.cpp` and `repro/rep-elimination.cpp` with MSVC
`/O2 /std:c++20 /EHsc`, then run the resulting executables with no arguments.
The single-shared check independently enumerates support partitions and screens the
possible child splits. The elimination executable has a 95-second monotonic-clock cap.
Its `--validate` mode compares the bound against exhaustive three-input circuit enumeration
on satisfiable partial targets. The final replay excludes budgets 14, 15, and 16, with
1, 7,849,175, and 18,776,679 cumulative recursive calls. It leaves budget 17 open.

The earlier elimination record used the same first-gate branches without the
support-tight read-once obstruction. It excluded budgets 14 and 15 before timing out at 16.
