# Handoff: circuit synthesis research

*Last updated 2026-11-24 (evening), by the Claude Code research agent. Keep this current after every major step.*

Read this first, then [AGENTS.md](AGENTS.md) (role and rules), [RESEARCH_NOTES.md](RESEARCH_NOTES.md) (results)
and [sat-search/verify/AUDIT.md](sat-search/verify/AUDIT.md) (verification status).

## Current priority

Mathematical and algorithmic improvements. Split: 80% research, 15% targeted verification of changed
components, 5% documentation. Do not restart the comprehensive verification audit. Keep rule combinations
without coverage disabled. Prefer proofs, structural insights and small decisive experiments over brute force.

The user's current research queue, in order:

1. **Signed regional lower bound.**
   - `sat-search/theory/signed_region_bounds.py` is integrated as `cube_search --signedregions` (opt-in).
   - Measured; see "Results this session".
2. **Exact functional-module preprocessing.**
   - Files: `theory/module_contraction.py`, `theory/partial_module_contraction.py`, `theory/module_fpt_demo.py`.
   - Contract raw AND/OR modules and peel canalizing inputs before synthesis; keep reconstruction traces.
   - Partial functions: neutral-slice coverage, taking the exact minimum of the contracted and ignored
     branches; apply mandatory-input contractions first.
   - Never apply whole-function reductions to pinned-prefix searches.
3. **Cotree NOT costs in complete-function FPT synthesis.**
   - Files: `theory/readonce_not_cost.py`, `theory/fast_readonce_fpt.py`, `theory/signed_typed_bound.py`.
   - Use exact cotree NOT minimization instead of recursive local synthesis when the regional table is
     complete; use the slice NOT-cost bound for incomplete regions.
   - The typed bound gained nothing on the corpus: keep it, but off by default.
   - `theory/archive/activity_port_bound.py` is archived. Stop adding purely structural compatibility
     constraints: `theory/signed_control_completion.py` shows the signed compatibility test is exact.
4. **Lean 4 pilot** (`sat-search/lean`).
   - Scope: circuit model, connectivity bound, excess identity, then the module-contraction proof
     (restriction and substitution) and the cotree NOT-cost recurrence.
   - Completed proofs only (no `sorry`); inspect axioms (`#print axioms`).
   - Keep formal mathematical proofs separate from verified implementation correctness.
5. **Adaptive analytical branch-and-bound** (parked).
   - `experiments/bnb_depth_probe.py`: pinning one more gate on the size-19 L-meta-1343 survivors rejects
     167/168 children (b:1-1-4) and 177/182 (a:1-4-5). Worth building after items 1–4.
   - Limit: `PARTIAL_FEATURE_LIMIT = 16` features.

## Results this session (2026-11-24)

**Verification infrastructure** (`sat-search/verify/`, committed):

- independent reference solver;
- run_cube and CLI differential harnesses;
- bound checks;
- evidence manifests (`cube_search --manifest`);
- coverage inventory, with a default guard backed by `verified_combinations.json`;
- five defects fixed (R1–R5).

**Theory integration:**

- **Signed bound.** It is sound on every case and never weaker than the existing NOT-enabled bounds.
  - It raises the best prior lower bound in 26 of 106 complete corpus targets and settles 53 budgets.
  - Search in the general basis is 2× faster than plain; it adds nothing over `--fast` on graphs.
  - Records: `results/signed_bound_compare.jsonl`, `results/ablation/signed-ablation-20261124.jsonl`.
- **hypergraph-17.** NOT-enabled minimum = 7, **certified**: verified witness plus RUP-checked exclusions
  at 6 and 5 (`results/hypergraph17_not_certificate.json`).
- **Module preprocessing on the corpus.** 57 of 106 targets are reducible, 195 inputs are removed and 37
  reduce completely (`results/module_corpus.jsonl`). Eleven open cases have smaller cores; solving them
  exactly is in progress (`experiments/module_core_minima.py` → `results/module_core_minima.jsonl`).
- **Fast read-once FPT.** Local completion calls drop from 17,888 to 1,552 and time from 2.16 s to 0.66 s
  on 694 queries (`logs/theory_checks.log`).

## Environment gotchas

- **Python.** The global pyenv is 3.15.2 without pysat. python-sat is vendored in `.scratch-sat/`, which
  `cube_search.py` and `verify/reference.py` append to `sys.path`. Run scripts with plain `python`.
- **Concurrent agent.** Another agent edits the same repository and leaves files uncommitted, notably
  `sat-search/cube_search.py`, `port_certificates.py`, `provider_capacity.py` and some
  `experiments/*_check.py`.
  - Never commit their files.
  - For `cube_search.py`, write a patch against the index (`git show :sat-search/cube_search.py`), apply it
    with `git apply --cached`, and apply the same string-anchored edit to the working tree.
  - Before committing, test the staged state in a clean worktree: `git worktree add` at HEAD, apply
    `git diff --cached`, copy `.scratch-sat` into it, run the tests.
- **Lean.** Mathlib v4.36.0 is already built in `pequalnp-proofs/lean/.lake/packages`.
  - `lake env` hangs; do not use it. Call `lean` directly, from `sat-search/lean`:
    `LEAN_PATH="$(cat .leanpath)" ~/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean.exe CircuitLemmas/Basic.lean`
  - `.leanpath` lists the built package library folders. Expect about 30 s per file.
- **Jobs.**
  - Launch every job as a tracked background task (Bash `run_in_background`) that logs to
    `sat-search/logs/` and prints per-item progress; its exit then notifies you. The user wants fast
    feedback.
  - Size pools at 11 workers, up to 22 in total. Never wrap a Pool in `timeout` (it orphans workers). Stop
    jobs by task ID, never by process name.
  - On Windows, stopping a task kills the bash wrapper but can leave its Python child running. After
    every stop, list Python processes and kill leftovers of your own by explicit PID.
- **Guard.** `cube_search.py` refuses untested rule combinations. Harnesses pass `--allow-unverified`.
  Regenerate the allowlist with `python verify/inventory.py && python verify/make_allowlist.py` after
  adding coverage.

## In flight / uncommitted (update this list)

- **Integration of `cube_search --signedregions`.**
  - Done: patch staged, differential run (1,950 jobs, 0 mismatches), CLI run (336 jobs, 0 mismatches),
    harness configurations added.
  - Needed: regenerate the inventory and allowlist, then commit.
- **New theory prototypes in `theory/`.** Copied with self-checks passing; commit together with the
  experiments and results above.
- **Lean `CircuitLemmas/Basic.lean`: compiles, no `sorry`, only standard axioms.** Proved for the model:
  - the read-count identity;
  - the connectivity bound (B ≥ n − 1 when every wire is read);
  - the excess fan-out identity.

  About 45 minutes of effort; 24 s to check. Not yet committed.
- **`experiments/module_core_minima.py`.** Running. Exact NOT-enabled minima so far:

  | Case | Old interval | Exact minimum |
  | --- | --- | --- |
  | hypergraph-18 | [7, 12] | 8 |
  | hypergraph-24 | [8, 10] | 8 |
  | random-monotone-03 | [7, 12] | 7 |
  | random-monotone-04 | [8, 11] | 9 |
  | random-monotone-08 | [8, 13] | 9 |

  Monotone minima are the same. Upper bounds are verified by witnesses lifted from the core. Lower
  bounds rest on the module theorem, which is provisional. Next: certify with checked exclusions where n
  is small.

## Jobs running at last update

- `experiments/module_core_minima.py`: 6 of 11 cases left, working on random-monotone-10 (7-input core).
- `experiments/certify_module_minima.py 6 900`: checked exclusions at M−1 and M−2 for the n ≤ 6 module
  minima → `results/module_minima_certificates.jsonl`.
- `experiments/module_fpt_bench.py 5 5`: FPT on the original vs on the core vs the reference →
  `results/module_fpt_bench.jsonl`.

## Lean: module-contraction proof plan (deferred)

- **Substitution:** a circuit for the contracted function plus one AND/OR gate is a circuit for f. Short.
- **Restriction:** fix x_j to the neutral value of the module; at least one reader of x_j becomes a copy
  and is removed under constant propagation; rename x_i as the module input. This needs a formal
  constant-simplification on `Circuit n m` with semantics preservation and a gate count. Estimate:
  several hundred lines.
- Needs evaluation semantics added to `CircuitLemmas/Basic.lean`.

## Next steps

1. Finish the Lean basics, then formalize the module-contraction theorem and the cotree NOT-cost
   recurrence.
2. Report the module core minima. Certify new minima with checked proofs where n is small: `evidence.py`
   or `verify/reference.py` with `proof=True`, plus the RUP checker.
3. Integrate module preprocessing into the whole-function pipeline (FPT, then SAT). Report reduced inputs,
   newly resolved budgets and runtime.
4. Practical FPT: measure live-provider width and a hybrid with SAT.
5. Return to adaptive analytical branch-and-bound (item 5 above).
