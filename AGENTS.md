# Autonomous Research Workflow

Build machine-verified knowledge about exact Boolean circuit synthesis: structural theorems,
circuit transformations, sound pruning, certificates, and Lean proofs that make later problems
easier. Build toward a solution in checked pieces instead of attempting the whole solution at once.
Let mathematics guide the work, computation challenge it, and Lean verify it. "No verified
progress" is an acceptable, honest session outcome.

## Roles: Sol leads, Luna does bounded work

The workflow is the same in Claude Code and ChatGPT. Map the roles to models here:

| Tool | Sol (lead) | Luna (bounded work) |
| --- | --- | --- |
| Claude Code | Opus | Haiku subagent (`model: haiku`) |
| ChatGPT | the lead reasoning model | a smaller, faster model or lightweight task |

Use the role names Sol and Luna in records, reports and messages. Don't mix them with model names
(write "Luna", not "Haiku (Luna)"; write "Sol", not "Opus").

- **Sol decides.** Sol selects and pins the target, classifies the bottleneck, designs proofs and
  reductions, assigns verification grades, and approves every submission. Sol reviews Luna's
  output before it is graded, committed, or submitted.
- **Luna executes checkable tasks:** repository, doc and prior-evidence scans, file and log summaries,
  desk, lease, PR and CI status, the first error and goal of a Lean build, verbatim statement or
  negation files generated from desk JSON, staged-diff hygiene checks, batch launches from a
  Sol-written manifest, and the mechanical submission checklist in
  [PROOF_WORKFLOW.md](sat-search/workflow/PROOF_WORKFLOW.md#package-and-submit).
  Sol delegates every sweep of several files to Luna; a single read of a known path stays with Sol.
  Give Luna exact paths, the output format, and a word limit, and reuse one Luna for follow-ups.
  Luna reports facts with paths and line numbers, and returns an "open" verdict when unsure.
  Luna never weakens a statement, changes a target, or assigns a grade above "computationally
  tested".
- When Claude and ChatGPT both work on a question, their Sols split it into theory and
  implementation/independent review, and they hand off through the repository record.

## Modes

- **Desk mode** (a leased pequalnp unit, tools in `pequalnp-proofs/tools/pnp.sh`). The lease
  deadline outranks the research priorities. Start `bash .pnp/keepalive.sh <step> 300 6` (in `pequalnp-proofs/`) when
  the step is taken. Run one CPU-heavy search at a time (up to 22 threads), and take proof-only steps in parallel.
  When the exact packaged file passes `tools/pnp.sh check` and the axiom and `sorry` audit, and
  upstream has not merged the step, submitting is pre-authorized. Release undoable steps
  promptly with an honest reason. Keep the desk clone current: `main` and `submit-base` track
  `upstream/main`, so `git pull --ff-only` works before every step. Never commit to them; step
  files stay untracked or on their step branch. If a fast-forward fails, back up the local
  commits on a `backup/` branch, move the branch to `upstream/main` with `git reset --keep`, and
  report it. Every session and script shares one desk handle, so a plain
  `next` returns a unit someone else already holds: take every unit with `next --another`
  (`another=1`), and release only a unit you took yourself. Losing a lease does not stop the
  work: keep proving, and `tools/pnp.sh submit` asks the desk for the unit again before
  sending (`--unleased` sends anyway, for the 10-point floor). Stop only on a 410 with
  `withdrawn: true` or when the unit's file is already on upstream main. After an unexpected
  410, find out who released the unit.
- **Research mode** (everything else). Choose work in this order: general structural theorems,
  reusable transformations and gate-elimination lemmas, stronger bounds and reductions, sound
  pruning, reusable Lean and certificate infrastructure, finishing partial results, isolated
  witnesses. Explicitly assigned objectives come first.

## Session loop

1. Resume from the record: `python -B sat-search/workflow/research.py status --task <step>`.
   Check [RESEARCH_NOTES.md](RESEARCH_NOTES.md), recent commits, and whether the target or a
   stronger result is already proved or held by another agent. Keep this proportionate to the task.
   On a new step, Luna goes first, in this order: pull the desk clone and this repository
   (fast-forward only), search the repository, then search the internet for evidence, and return
   one report. Its length follows the evidence and has no fixed word cap; it gives facts with
   paths, line numbers and URLs, each marked found or open. Sol pins the target only after it.
2. Pin the target: exact statement, upstream commit and definitions, circuit model and basis,
   gate counting, complete-function or partial-promise semantics, permitted imports and axioms.
   An alternative formulation needs an explicit reduction to the original.
3. Classify the bottleneck and use its playbook. Reclassify when the evidence changes.
   - *Theory*: the argument is unknown. Use small examples, counterexample search, conjecture refinement.
   - *Reduction*: find sound restrictions, normal forms, decompositions, gate eliminations.
   - *Search*: see [SEARCH_WORKFLOW.md](sat-search/workflow/SEARCH_WORKFLOW.md). Choose the SAT
     solver and its settings for the instance family with its
     [solver-selection steps](sat-search/workflow/SEARCH_WORKFLOW.md#choose-the-solver-and-settings-for-the-instance)
     before any long run.
   - *Proof*: see [PROOF_WORKFLOW.md](sat-search/workflow/PROOF_WORKFLOW.md).
   Do not use Lean iteration to compensate for a missing argument or an unfinished search.
4. Work the critical-path obligation. Test a novel claim on small cases before formalizing it.
5. Verify independently, grade the result, integrate reusable pieces, update the record, commit.
6. Reassess. Stop when a lemma is refuted, the budget is spent, a stronger result exists, the
   lease ends, or progress needs human input. Preserve the strongest verified result, the exact
   remaining obligation, and the failed approaches.

## Rules that always apply

- Never weaken the target, add hypotheses, or change the circuit model silently. Never transfer
  bounds between incompatible bases.
- Grades: conjectured → computationally tested → paper proved → stubbed → conditionally compiled
  → verified → integrated → submitted → accepted → merged. A proof using `sorryAx`, a forbidden
  axiom, or an unfinished dependency is not verified. Permitted axioms are `propext`,
  `Classical.choice`, and `Quot.sound`. Keep solver verdicts, checked witnesses, checked
  certificates, and formal proofs distinct. A timeout leaves its scope open; finite testing is
  evidence, not proof.
- `sorry` belongs only in scratch workspaces, never in a committed target or submission.
- Preserve existing implementations and frozen corpora as references. New pruning or
  performance rules go through the normal entry points, opt-in, measured one at a time. Rule
  combinations without coverage stay disabled (allowlist from `sat-search/verify/make_allowlist.py`).
- Every SAT, search or Lean batch answers a stated question. Check prior runs first and record
  why a repeat or a longer cap is justified. Keep full logs on disk and return bounded summaries.
- Effort split: about 80% mathematics and algorithms, 15% targeted verification of the touched
  components, 5% documentation. Record historical verification gaps in
  [AUDIT.md](sat-search/verify/AUDIT.md) without blocking research.

## Records, reports, commits

Keep one compact record per active step in the research runner: target, mode, bottleneck,
dependency graph and open obligations with grades, strongest checked result, evidence paths,
failed approaches, next action, and active jobs or lease. Resume from it after compaction or handoff.

Update [RESEARCH_NOTES.md](RESEARCH_NOTES.md) when a bound, minimum, default, or priority
changes. Put proofs, assumptions, counterexamples, scope, and commands in the topic notes; raw
results and proof artifacts beside their manifests in `sat-search/results`; transient logs in
`sat-search/logs`. Commit after each milestone with focused commits, after inspecting the staged
diff and running the applicable checks. End each session with: objective, strongest verified
result and its grade, Lean and axiom status, computational scope, open obligations, failed
approaches, files and commits, and next direction.

## Research map

| Start here | What it contains |
| --- | --- |
| [RESEARCH_NOTES.md](RESEARCH_NOTES.md) | Current results, open endpoints, and links to the detailed records. |
| [workflow/README.md](sat-search/workflow/README.md) | Research runner: records, manifests, Lean, heartbeat, PR status. |
| [PROOF_WORKFLOW.md](sat-search/workflow/PROOF_WORKFLOW.md) | Proof-bound playbook, transformation checklist, packaging and submission. |
| [SEARCH_WORKFLOW.md](sat-search/workflow/SEARCH_WORKFLOW.md) | Search-bound playbook and the theory–search–proof loop. |
| [DIRECTION.md](sat-search/workflow/DIRECTION.md) | Current priorities, closed directions, and what would reopen them. |
| [NOTES_SYNTHESIS_BENCH.md](sat-search/NOTES_SYNTHESIS_BENCH.md), [NOTES_SYNTHESIS_FOLLOWUP.md](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md) | Frozen corpus, endpoint verification, sharing hardness, regional certificates. |
| [NOTES_PORT_CERTIFICATES.md](sat-search/NOTES_PORT_CERTIFICATES.md) | Port ranks, provider eligibility, global capacity, regressions, negative ablations. |
| [NOTES_COMPLETE_FRONTIER.md](sat-search/NOTES_COMPLETE_FRONTIER.md) | Complete-function FPT, counted NOTs, rank-tight certificates, affine completion. |
| [NOTES_SIGNED_MODULES.md](sat-search/NOTES_SIGNED_MODULES.md) | Module contraction, free-NOT core minima, ordered quotients, branch-and-bound. |
| [NOTES_L1343.md](sat-search/NOTES_L1343.md) | Fixed-prefix and cube-search work with exact shard scope. |
| [sat-search/experiments](sat-search/experiments), [sat-search/results](sat-search/results) | Implementations and references; frozen targets, run records, witnesses, proof packets. |
