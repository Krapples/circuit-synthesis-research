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
   - Scope: circuit model, connectivity bound, excess identity, and the module-contraction proof
     (restriction and substitution; done, `Module.lean`). Next: the cotree NOT-cost recurrence.
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
  - `Module.lean` imports `Basic`. Compile it first:
    `lean CircuitLemmas/Basic.lean -o .lake/build/lib/lean/CircuitLemmas/Basic.olean`. Then append
    `;.lake/build/lib/lean` to `LEAN_PATH`. Do the same for `Module.lean` and `CircuitLemmas.lean`
    before running `AxiomsCheck.lean`.
- **Jobs.**
  - Launch every job as a tracked background task (Bash `run_in_background`) that logs to
    `sat-search/logs/` and prints per-item progress; its exit then notifies you. The user wants fast
    feedback.
  - Size pools at 11 workers, up to 22 in total. Never wrap a Pool in `timeout` (it orphans workers). Stop
    jobs by task ID, never by process name.
  - On Windows, stopping a task kills the bash wrapper but can leave its Python child running, and
    killing a pool parent leaves its `spawn_main` workers alive. After every stop, list Python processes
    (filter workers on `parent_pid=<pid>`) and kill your own leftovers by explicit PID.
  - PowerShell output lines end in ``. Pipe through `tr -d ''` before `while read p; do taskkill
    //PID $p ...`, or every kill silently fails.
  - Keep about 22 threads busy. Split single-threaded work: one worker per case, or split an exact-G
    exclusion by first gate.
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
  bounds rest on the module theorem (now proved in Lean) and the uncertified core minimum. Next: certify
  the core exclusions; a full-size exclusion is no longer needed.

## Jobs running at last update

- `experiments/certify_split.py 18 900 8`: exclusions at M−1 and M−2 for the new minima (module cores plus
  4 intervals closed by monotone witnesses).
  - Each exclusion is split exhaustively by first gate, and every piece gets a RUP-checked proof.
  - Pieces persist in `results/certified_pieces.jsonl`; a restart resumes. Exclusions go to
    `results/certified_exclusions.jsonl`.
  - Easiest first, 900 s per piece. Open pieces should be retried with a longer limit.
- `experiments/l1343_bnb.py 4 1800`: `bnb.py` on the 23 size-19 survivors as a validation case. One tree
  per survivor in `results/bnb_l1343/`; resumable.

## Newest results (committed in e50971c unless noted)

- **Phase-budget encoding** (normalized signed skeletons): 54% fewer conflicts but 6.2× more clauses, 26%
  slower overall and 2.7× slower on monotone UNSAT. The existing encoder is kept.
- **`bnb.py`:** passes `verify/test_bnb.py` (whole-function and seeded, against the reference).
- **10 NOT-enabled intervals close** using cross-basis monotone witnesses and today's lower bounds; see
  NOTES_SIGNED_MODULES.md.

- **More exact minima from module cores**, each with a verified lifted witness: generated-08 = 6
  (was [6, 10]), comparator-07 = 8 (was [7, 14]), generated-09 = 8 (was [7, 13]).
- **random-monotone-03 = 7, certified** in both bases (RUP-checked proofs at 6 and 5).
- **First-gate bound** (`theory/first_gate_bound.py`, `experiments/first_gate_compare.py`):
  - beats the strongest production binary bound on 21 of 106 complete targets;
  - raises the NOT-enabled lower endpoint on 20 (threshold-7-4: 12 → 14; threshold-8-5: 14 → 16;
    parity-5: 11 → 14);
  - resolves hypergraph-07 to 7;
  - partial-09 rises 7 → 8 (monotone) and 6 → 8 (NOT-enabled);
  - recursive combination beats taking the maximum in only 1 case; XOR stripping adds nothing extra;
  - at most 0.94 s per target.
  - Integrated as `cube_search --firstgate`: opt-in, adaptive, skipped above 9 inputs.
- **XOR factors** (`theory/xor_factor.py`): C(x ⊕ h) = C(h) + 3 holds in 284 checks
  (`verify/test_xor_factor.py`).
- **Partial counted-NOT bound** (`theory/partial_counted_bound.py`): binary plus exact inversion count.
  - Exact on 92% of 3-input and 76% of checked 4-input partial tables, against 23% and 8% for the binary
    bound alone. No violations.
  - The NOT term adds on 235 of 273 partial nonmonotone corpus labels.
  - The inversion bound is provably 0 for monotone targets with input access, so it adds nothing in
    `cube_search`.
- **`theory/prefix_restriction_bound.py`:** kept for branch-and-bound. Depth 1 gains on 53 of 1,160
  cases; depth 2 adds nothing.

## Lean: module contraction (done 2026-11-24)

- **`CircuitLemmas/Module.lean` proves `module_contraction` and `peel_contraction`:** min(f) = min(g) + 1
  in the counted-NOT and monotone bases. No `sorry`; standard axioms only (`AxiomsCheck.lean`).
  - Covers every raw `pair`/`peel` step used by `module_core_minima`.
  - About 1.5 h of effort, 807 lines, 30–45 s to check.
  - Scope, hypotheses and what is not formalized: NOTES_SIGNED_MODULES.md, "Formal proof".

## Next steps

1. Lean: the module-contraction theorem is done. Next: the cotree NOT-cost recurrence, and optionally
   counted-basis completeness and dead-gate removal (output-convention equivalence).
2. Report the module core minima. Certify new minima with checked proofs where n is small: `evidence.py`
   or `verify/reference.py` with `proof=True`, plus the RUP checker.
3. Integrate module preprocessing into the whole-function pipeline (FPT, then SAT). Report reduced inputs,
   newly resolved budgets and runtime.
4. Practical FPT: measure live-provider width and a hybrid with SAT.
5. Return to adaptive analytical branch-and-bound (item 5 above).
