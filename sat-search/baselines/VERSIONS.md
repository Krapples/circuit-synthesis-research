# External baseline tools: versions, builds and configurations

All tools run natively on the same machine as our solvers: AMD Ryzen 9 5900X (12 cores / 24 threads), Windows 11
Pro N 10.0.26300, Python 3.15.2, python-sat 1.9.dev24 (vendored in `.scratch-sat/`).

Checkouts live in the git-ignored `external/` folder at the repository root.

| Tool | Source | Commit | Commit date |
| --- | --- | --- | --- |
| Percy | https://github.com/whaaswijk/percy | `3931696479a01d0065c84b3089b4fce52b7731fc` | 2019-06-20 |
| Berkeley ABC | https://github.com/berkeley-abc/abc | `bd23a971519f70b1a8dbb8d0a2c0574eeb69af69` | 2026-11-22 |
| Cirbo | https://github.com/SPbSAT/cirbo | `ca19a9f29691459563a8a0a90d8f5b6cdc4e5006` | 2026-10-13 |

Clone: `git clone --recursive https://github.com/<owner>/<repo>.git` inside `external/`, then `git checkout <commit>`.

## Builds

Compiler: MSVC 14.51.36231 (Visual Studio 18 Community, `vcvars64.bat`), CMake 4.3.1-msvc1, Ninja 1.13.2.

- **ABC.** ABC's CMake build shells out to `make`, which is not installed. `build/gen_abc_ninja.py` generates a
  Ninja file from ABC's own `Makefile` module lists (including the conditional CUDD `MODULES +=` line) with the
  defines of ABC's Windows project (`abclib.dsp`): `WIN32 WINDOWS NDEBUG _CONSOLE _CRT_SECURE_NO_DEPRECATE
  ABC_USE_PTHREADS HAVE_STRUCT_TIMESPEC _WINSOCKAPI_ ABC_USE_STDINT_H=1 ABC_USE_CUDD=1`, flags `/O2 /MD /EHsc`,
  linked with `lib/x64/pthreadVC2.lib` (1,548 sources). Commands, from PowerShell (the `=` in the repository path
  breaks `cmd` arguments):
  ```
  python sat-search/baselines/build/gen_abc_ninja.py external/abc external/abc-build
  $env:BUILD_SUBDIR='abc-build'; & "sat-search\baselines\build\build_abc.bat"
  copy external\abc\lib\x64\pthreadVC2.dll external\abc-build\
  ```
- **Percy.** Header-only library; `percy_driver/percy_run.cpp` is our command-line driver, built through Percy's
  own CMake (`percy_driver/CMakeLists.txt`, `/O2`) with `-DCMAKE_POLICY_VERSION_MINIMUM=3.5` (bundled kitty
  declares an old CMake minimum). On Windows Percy disables nauty; available SAT back-ends are bsat2, satoko and
  ABC's Glucose (`bmcg`). Command: `& "sat-search\baselines\build\build_percy.bat"`.
- **Cirbo.** The SAT synthesis (`cirbo.synthesis.circuit_search.CircuitFinderSat`) is pure Python and is imported
  from the checkout; its pure-Python dependencies are installed with
  `pip install --target external/cirbo-env --no-deps more-itertools typing-extensions pebble graphviz sortedcontainers`
  and python-sat comes from `.scratch-sat/`. The wheel build fails on its C++ extensions (ABC and mockturtle
  wrappers for minimization), which exact synthesis does not use.

## Basis and objective

Our free-NOT binary AND/OR gate count equals the AIG AND-node count (De Morgan). All configurations below allow
exactly the eight AND-type two-input gates (one or three minterms) with free complementation, and no XOR:

| Configuration | Command / call | Notes |
| --- | --- | --- |
| `percy-{std,cegar}-{bsat,satoko,bmcg}` | `percy_run.exe --n N --tt HEX [--dc HEX] --solver S --method M --start L` | `spec.set_primitive(AIG)`, SSV encoder. Percy's fence, DITT and MSV encoders ignore the primitive (they would allow XOR) and are not used. |
| `abc-two`, `abc-two-g`, `abc-two-onu`, `abc-two-gonu` | `abc -c "twoexact -a [-g] [-o -n -u] -I N -N k HEX"` | `-a`: AND-type gates only. `-t` starts at N = n+1 and cannot certify smaller optima, so the harness loops k from L. Complete functions only. |
| `abc-all`, `abc-all-i` | `abc -c "allexact -a -K 2 [-i] -I N -N k HEX"` | Complete functions only. Not used: `exact` (Soeken's BMS engine searches all two-input functions, including XOR). |
| `cirbo-{maplechrono,cadical195}` | `CircuitFinderSat(TruthTableModel(rows), k, basis=[and, or, nand, nor, gt, lt, geq, leq]).find_circuit(solver)` | Cirbo's `AIG` basis also contains `lnot_`, a degenerate two-input gate computing NOT of its left input; it is omitted so the count equals AIG size. |
| `ours-sat` | `theory/phase_budget_cnf.encode(n, b, u = n + b, P, N)`, maplechrono | Normalized signed-skeleton encoding with unbounded inverters (free NOT). |
| `ours-hybrid` | `baselines/runners.py ours-hybrid` | Signed module reduction, one-sharing, two-sharing, `solve3` (completion `phase-first`), then `ours-sat` on the core from excess 4. Complete functions only. An empty `solve3` result relies on its excess-3 exhaustiveness claim (prototype, checked on small oracles). |

Conventions verified on asymmetric functions: ABC and Percy read hex truth tables most significant nibble first with
bit a = f(assignment a), x0 = least significant bit of a; ABC `twoexact` gate strings `4'bWXYZ` index operands as
2*first + second, `allexact` as 2*second + first. Cirbo rows are passed most significant input first.

Fixed budgets in ABC and Percy mean "exactly k gates, all used". Minimum-size results are unaffected because every
tool is driven upward from the same trivial lower bound L = (essential inputs) - 1.
