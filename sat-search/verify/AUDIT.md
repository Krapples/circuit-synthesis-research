# Verification audit of cube_search and related encoders

*Started November 24, 2026. Correctness and certification come before new pruning rules and before
expensive searches.*

Since November 24, 2026 (see [AGENTS.md](../../AGENTS.md)), remaining gaps are recorded here
without blocking research. A change gets differential coverage for the components it touches, and
rule combinations without coverage stay disabled.

## Status vocabulary

Every claim in this file carries exactly one status.

| Status | Meaning |
| --- | --- |
| **proved** | A written mathematical argument covers every case. Its location is cited. |
| **independently tested** | It agrees with the independent reference on the stated finite scope. This is evidence, not proof. |
| **provisionally valid** | Production code relies on it with a written argument, but coverage is incomplete in at least one class, or the argument has not been independently reviewed. |
| **unresolved** | Coverage is missing. Open (timed-out) jobs and undecided reference minima are unresolved, never passes. |

## Model and semantic classes

`cube_search` decides the **exact-G model**:

- exactly G gates, on wires n..n+G−1;
- each binary gate reads two distinct earlier wires (l < r);
- NOT reads one wire, in the general basis only;
- the last gate is the output;
- every non-output wire is read.

Facts that link this model to circuit size:

| Fact | Status |
| --- | --- |
| If every input is essential, a minimum circuit lies in the model at its own size. Remove dead gates; essential inputs stay read. | proved (this paragraph) |
| **Padding:** if n + s ≥ 2, an exact-s circuit gives an exact-(s+2) circuit. Append `AND(x0, out)` and then `OR(out, that gate)`; every wire stays read, the function is unchanged, and any pinned prefix is kept. The condition is needed: with one input and no gates, the monotone exact-2 model is UNSAT (the general basis can pad by double negation). Corrected after the independent theory audit. | proved. Independently tested: 721 trimmed programs and 2,825 prefix checks (`verify/theory_audit_checks.py`, `verify/test_theory.py`) |
| Sizes below n − 1 are UNSAT: n + G − 1 wires need reads and there are at most 2G slots. | proved |
| UNSAT at G and G − 1 excludes every size ≤ G, for n ≥ 2 and only with exact-preserving rules. | proved from the two facts above |

A rule's semantic class says which claims it can support:

| Class | Definition | Test points |
| --- | --- | --- |
| whole-min | If G is the minimum, some circuit survives (whole function). | G = M (SAT), M − 1 (UNSAT) |
| whole-exact | If an exact-G circuit exists, one survives (whole function). | M + 1 (reference verdict), M + 2, M + 4 (SAT by padding) |
| prefix-min | Same as whole-min, restricted to circuits beginning with a pinned prefix. | M_P (SAT), M_P − 1 (UNSAT) |
| prefix-exact | Same as whole-exact, for pinned prefixes. | M_P + 2, M_P + 4 (SAT by padding) |

- Shard claims (e.g. L-meta-1343 shard 2) need the prefix classes.
- Skipping sizes with the padding argument needs the exact classes.
- A per-cube verdict means something only as part of the union over its driver's cube enumeration: symmetry
  restrictions keep one canonical form per circuit, and that form may lie in another cube.

## Verification infrastructure

| Component | Role |
| --- | --- |
| [reference.py](reference.py) | Independent exact solver sharing no code with `cube_search`. It has two backends: brute-force enumeration, and a direct CNF (pairwise one-hot gate choices, all rows, no symmetry breaking or implied clauses) solved with Glucose 4, which supports interrupts. It also holds the input contracts. |
| [test_reference.py](test_reference.py) | CNF vs brute force: 2,780 cases agree (all monotone functions on ≤ 3 inputs, all 4-vertex graphs, both bases, with and without every-wire-read, every one-gate prefix). |
| [differential.py](differential.py) | Runs rule configurations through the production `run_cube` over full cube sets. Covers whole-function and pinned-prefix points, padded points, redundant-gate prefixes, per-job limits and resume. |
| [cli_differential.py](cli_differential.py) | Runs the production command line (`cube_search.py` main) as a subprocess. Covers flag handling, port-cost construction, the capacity-allocation floor, certificate type counts, and `--minimal` with manifest evidence. |
| [bounds_check.py](bounds_check.py) | Checks every analytical bound function against reference minima: whole function, first gate, gate pairs, and pinned prefixes up to 5 gates. |
| [mono_shard_check.py](mono_shard_check.py) | Checks the legacy `mono_shard.py` encoder against reference minima. |
| [shard_split_check.py](shard_split_check.py) | Checks the L-meta-1343 case a/b decomposition, mirrored on small functions. |
| [evidence.py](evidence.py), [manifest.py](manifest.py) | Evidence grading. Manifests are verified independently (below). |
| [test_regressions.py](test_regressions.py), [test_theory.py](test_theory.py), [test_constant_simplification.py](test_constant_simplification.py), [test_manifest.py](test_manifest.py), [test_imports.py](test_imports.py), [test_rulesets.py](test_rulesets.py), [test_evidence.py](test_evidence.py) | Regressions with explicit expected verdicts. |
| [inventory.py](inventory.py) → `coverage_inventory.json` | Per-rule coverage in the four classes. Missing coverage is reported as unresolved. |

Reference minima and prefix minima are cached, keyed by the hash of `reference.py`. Each reference call
has a 90 s limit. Ten instance-basis pairs remain undecided and are excluded: K5, the 4-of-5 threshold,
and three dense 3-uniform hypergraphs on 5 inputs, each in both bases.

## Defects found

Each defect was minimized and pinned by a regression with an explicit expected verdict
(`test_regressions.py`). The historical audit for each is in the last column.

| ID | Defect and minimized counterexample | Action | Historical impact |
| --- | --- | --- | --- |
| R1 | A repeated or reversed edge inflated the `typed` OR bound (#OR ≥ ⌈log2 #terms⌉). Counterexample: path 0-1, 1-2 has a 2-gate circuit, but [0-1, 0-1, 1-2] with `typed` returned UNSAT. | Fixed: input contracts in `run_cube` and the CLI. | None. All 31 recorded edge lists are duplicate-free. |
| R2 | `--minimal` with pinned gates. Clause (a) orders AND before OR for adjacent equal-operand gates, which assumes they can be swapped. Counterexample: MAJ3 (minimum 4); OR(0,1), AND(0,1), AND(2,3), OR(4,5) is a minimum circuit, yet the pinned run returned UNSAT. | Disabled: `minimal` with `fixgates` or `colex_from` raises an error. | None. The only use (L-meta-519, size 11) was a whole-function run, also confirmed without `--minimal`. |
| R3 | Graph-only rules crashed on non-graph families: `sens`, `bypass`, `elim` and dependents, `readerbudget`, `closedcone`, `outdec`, `matchinginterface`, fan-out. | Contract: `GRAPH_ONLY_FLAGS` raises a clear error. | None. They crashed rather than returning a verdict. |
| R4 | The `--minimal` prerequisite was only stated in help text, then checked from log lines. | Enforced from **manifests** of complete non-minimal ALL UNSAT runs at G − 1 and G − 2 (selection recomputed). Log lines are rejected. | — |
| R5 | `automorphisms()` checked only pair adjacency. For 3-element terms it accepted every degree-preserving permutation, and orbit reduction then dropped every cube holding a minimum circuit. Counterexample: 5 inputs, terms {0,1,3} and {0,2,4}; 24 permutations accepted, 8 true; UNSAT at the minimum 4. | Fixed: whole terms are checked. Graph groups are unchanged (202 graphs up to 6 vertices match brute force). | None. Every historical caller passes graph edges. |
| H1 | Module shadowing: `.scratch-sat` was prepended to `sys.path`, so `.scratch-sat/port_certificate_construction.py` shadowed the repository module. | Fixed: appended instead; guarded by `test_imports.py`. | None found. Nothing imported that name. |
| H2 | Configuration drift: 7 copies of the `--fast` flag set existed, with 3 distinct bodies (the differences were basis and era, not semantics). | Fixed: `rulesets.py`; drivers import it, contents asserted equal; guarded by `test_rulesets.py`. `solver_bench.py` keeps its older benchmark set on purpose. | None. Contents were identical where shared. |
| H3 | The size-19 survivor driver lived only in the untracked scratch folder. | Archived to `experiments/archive/` with sha256 provenance of the script and its log. | Replay pending (below). |

## Theory audit items (independent theory audit, 2026-11-24)

| Item | Status |
| --- | --- |
| **Rank-tight certificate family.** Explicit witnesses with ranks (3e−1, 3e, 3e−1), so rank(H) = 3e − 1 > 2e for e ≥ 2; the universal bound rank(H) ≤ 2e fails. Each witness row is checked as a minimal certificate. Per AGENTS.md, the universal rank(H) ≤ 2e direction is closed. | independently tested for e = 1..30 (`test_theory.py`). Not proved for general e here. |
| **Complete-function FPT prototypes** (`theory/complete_{sharing,signed}_fpt.py`). These are decision prototypes, not production rules. Their contracts are now enforced: nonconstant target, every input essential, monotone for the sharing version, s ≥ 0. | Independently tested: the supplied checks (218 signed depth-5 queries, 12 generated 4-input witnesses) and every 3-input case against `reference.py`. Provisionally valid as algorithms; their correctness proofs are unreviewed here. |
| **Padding boundary** (n + s ≥ 2). | proved; independently tested (above) |
| **Distinction-gap constant simplification.** Fixing single-polarity inputs must simplify by edge deletions (constant gates, dead cones) and contractions (copy gates, idempotent gates on a doubled operand). Cycle rank, which equals the sharing B − m + 1 for every-wire-read circuits, never increases under these (minor monotonicity). Relocating a representative to an owner that is already read identifies two vertices and can raise the rank by 1 (OR(AND(x0,x1), x2) → OR(AND(x0,x1), x0): rank 0 → 1). The certificate lemma's owner bound x(b − κ_core + 2) must therefore be applied after constant simplification and **before** relocation. NOTES_SYNTHESIS_FOLLOWUP does not state this order explicitly; theory follow-up should make it explicit. | Invariant proved (minor monotonicity) and independently tested exhaustively (7,412 simplifications, `test_constant_simplification.py`). The order of operations in the written proof is unresolved until the text is amended. |

## Evidence and provenance

| Evidence kind | How it is checked | Grade it supports |
| --- | --- | --- |
| verified witness | `reference.check_witness` on every row | upper bound / SAT |
| checked UNSAT | Reference CNF plus DRUP proof accepted by the RUP checker in `experiments/certify_synthesis.py`; negative controls in `test_evidence.py` | certified exclusion |
| analytical | The named bound, re-derivable with SAT disabled (`manifest.py --recheck-analytical`) | rule-dependent |
| unchecked solver UNSAT | — | rule-dependent |
| open / timeout | — | unresolved |

- **Manifests.** `cube_search.py --manifest` records the normalized target, the model, source hashes,
  configuration, the enumeration, the symmetry group, the orbit selection, any cubes skipped by logs, and
  per-cube verdicts. `manifest.py` re-derives all of them independently and grades the run.
- **Certified minima.** A minimum is reported as **certified** only with a verified witness at M and
  checked exclusions at M − 1 and M − 2, for n ≥ 2 with every input essential (`evidence.py`).

## Historical results requiring revalidation

Every claim below rests on log lines, which are not evidence under the new policy. Each needs a manifest,
or a checked proof where feasible.

| Result | Current grade | Needed |
| --- | --- | --- |
| L-meta-1343 shard 2, sizes 4–13 (`mono_shard.py`) | Rule-dependent. The encoder is independently tested (252 jobs, 0 mismatches). | Manifests; the shard-split decomposition audit. |
| L-meta-1343 shard 2, sizes 14–16 (`cube_search --fast`) | Rule-dependent | Manifests |
| L-meta-1343 shard 2, sizes 17–18 (partial ordered bound, analytical) | Rule-dependent. The bound is independently tested on small instances with prefixes up to 5 gates. | Manifest with analytical re-derivation |
| L-meta-1343 shard 2, size 19: 315 of 338 cubes analytical, 23 open | Rule-dependent / unresolved | Replay of the archived driver; manifest |
| L-meta-519 seven-cycle with two leaves ≥ 12 | Rule-dependent (whole-function runs; `--minimal` run also confirmed without it) | Manifests at sizes 10 and 11 |
| L-meta-1023 Fano weights-2–3 model, 13 excluded | Rule-dependent; the `fano_search.py` encoder is untested | Differential coverage of `fano_search.py` |
| Synthesis-corpus minima with DRUP certificates | Certified where proofs exist (NOTES_SYNTHESIS_FOLLOWUP) | — |

## Rule coverage (inventory of 2026-11-24)

`verify/inventory.py` builds `coverage_inventory.json` from all differential records. When a job is
rerun, the later record replaces the earlier one, so the R5 rerun supersedes the defective version's
records.

| Status | Configurations |
| --- | --- |
| **tested** in all four classes, no failures | 76 run_cube configurations: every single rule with its prerequisites, `--fast`, and `--fast` plus each extra |
| tested (command line, whole function) | 7: `capacityallocation` deficit/packing/exact, `certtyperank`, `portcert compatibility`, and `--fast` with capacity or type rank. These are reachable only through `main()`, and the command line never pins prefixes. |
| tested (whole-min only, by design) | `minimal` and `fast+minimal`. Valid only at G ≤ M; disabled with pinned gates (R2). |
| failed / unresolved | none |

Job totals:

- base run: 59,857 jobs;
- whole-function padded run: 11,956 jobs;
- prefix-exact padded and redundant-prefix runs;
- symmetry rerun after R5: 640 jobs;
- command line: 3,708 jobs;
- `mono_shard`: 252 jobs;
- shard split: 903 jobs (152 instance/seed/case minima).

Every job had zero wrong verdicts, apart from R5 before its fix. Open jobs (60 s limit, mostly 5-input
instances at M + 1 or above) are counted as unresolved points, not passes.

**Default guard.** `cube_search.py` refuses any rule combination whose active set (computed after all of
`main()`'s implications and printed as `active rules`) is not in `verified_combinations.json`.
`verify/make_allowlist.py` generates that file from the command line itself and the inventory: 63
combinations, including the plain encoding. `--allow-unverified` runs anything else; it warns and is
recorded in the manifest.

**Remaining gaps.** These do not block research:

- the historical-results table above;
- `fano_search.py` has no coverage;
- drivers that call `run_cube` directly are not guarded by the command-line allowlist and must consult
  the inventory's prefix classes;
- instances whose minimum is about 10 or more are beyond the unpruned reference.
