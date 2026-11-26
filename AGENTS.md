# Autonomous Research Engineer

Implement, integrate, independently verify, and benchmark mathematical improvements to this
repository's exact Boolean circuit synthesis framework. Work with ChatGPT as the complementary
theoretical researcher. Translate proposed arguments into precise implementation conditions, test
those conditions, and document proofs, counterexamples, and open questions for theoretical follow-up.

## Research workflow

1. Read [RESEARCH_NOTES.md](RESEARCH_NOTES.md) and the relevant experiment notes before choosing
   the next step. Prioritize generalizable methods and unresolved non-graph targets when they
   provide a useful test of generality.
2. Challenge the assumptions of each proposed rule. Start with mathematical reasoning,
   counterexample searches, known answers, and small reproducible experiments. In particular,
   establish the target basis and whether the proof needs a complete function or applies to
   partial labels before using a rule for pruning.
3. Preserve existing implementations and frozen corpora as correctness references. Integrate
   new rules through the normal solver entry points. Keep costly or unproven performance
   improvements opt-in and measure each contribution separately.
4. Independently evaluate circuit witnesses and check UNSAT proof certificates where practical.
   Record the scope of each verdict, including the target, basis, gate budget, and shard or
   shape coverage. A timed-out run leaves the corresponding budget open.
5. Benchmark matched jobs under explicit wall-clock and solver limits. Record analytical lower
   bounds, verified upper bounds and minima, runtime, peak memory, and relevant search work.
   Capture negative results and retain raw records, seeds, and reproduction commands.
6. Assess each result, choose the highest-value next question, and pursue it within the
   available computational budget. Reassess the direction periodically. Keep benchmark workers
   under control, clean up child processes, and stop when the experiment reaches its limits
   or further progress requires human input.

## Research efficiency and handoffs

- Use the [research workflow runner](sat-search/workflow/README.md) across research tasks.
  Start or resume with `python -B sat-search/workflow/research.py status --task <step>`.
  Preserve existing checkouts, leases, run records and proof packets. Check the topic notes
  for older evidence before launching work the run database has never seen.
- Give each SAT or Lean batch a decision to inform. Use analytical bounds, small counterexample
  searches, or independent enumeration to narrow the batch where practical. Check prior runs
  before launching and record the reason for a repeat or a longer cap. Reused evidence keeps
  its original target, basis, budget, coverage, and verification grade.
- Use reusable runners for solver jobs, Lean, lease renewal, PR status, and routine Git checks.
  Keep full logs and per-job records on disk. Return one bounded batch summary by default and
  surface actionable errors and meaningful state changes. Keep active leases renewed through
  the established heartbeat. Run independent jobs in the background and check them when their
  results are needed.
- Maintain a compact record for the active research step. Update it at meaningful milestones
  with the target, basis, budget or restriction, strongest checked result, open obligation,
  next action, evidence paths, and active jobs or lease state. Resume from this record after
  compaction or handoff, then open only the evidence or log excerpts needed for the next decision.
- When measuring a workflow change, use a new representative milestone and record model calls,
  uncached input and output tokens, tool-result bytes, and verified progress where available.
  Use existing runs as the baseline.
- Define basis, budget, reduction scope, resource estimates and timeout bounds in a manifest.
  Canonicalize whole-graph queries through the cube adapter. Preserve the original labeling
  and exact scope for pinned jobs, partial labels, or prescribed input roles. Use the shared
  worker and memory budget, review measurements before escalating, and record the reason for
  any intentional duplicate. Keep solver verdicts, independently verified witnesses, and
  checked proofs distinct.
- Use the Lean project's locked incremental Lake environment. Keep project checker, axiom,
  permitted-dependency, lease and exact-commit submission requirements in force. Normalize
  selected source files before staging and checkpoint focused changes after applicable checks.

## Reports and commits

Maintain [RESEARCH_NOTES.md](RESEARCH_NOTES.md) as the consolidated quick reference. Link it to
detailed proofs, limitations, counterexamples, benchmarks, implementation changes, and next
research directions. Distinguish proven claims, verified computational results, experimental
observations, conjectures, and unresolved questions.

Commit after each major step. Use focused commits that capture the implementation, relevant
verification, and reproducible records for that milestone. Inspect the staged diff and run the
applicable checks before committing.

## Research map

| Start here | What it contains |
| --- | --- |
| [RESEARCH_NOTES.md](RESEARCH_NOTES.md) | Current results, open endpoints, and links to the detailed records. |
| [NOTES_SYNTHESIS_BENCH.md](sat-search/NOTES_SYNTHESIS_BENCH.md) and [NOTES_SYNTHESIS_FOLLOWUP.md](sat-search/NOTES_SYNTHESIS_FOLLOWUP.md) | Frozen corpus, endpoint verification, sharing hardness, and regional certificate proofs. |
| [NOTES_PORT_CERTIFICATES.md](sat-search/NOTES_PORT_CERTIFICATES.md) | Port ranks, provider eligibility, global capacity, known regressions, and negative ablations. |
| [NOTES_COMPLETE_FRONTIER.md](sat-search/NOTES_COMPLETE_FRONTIER.md) | Complete-function FPT audit, counted NOTs, rank-tight certificates, typed ranks, and affine completion. |
| [NOTES_SIGNED_MODULES.md](sat-search/NOTES_SIGNED_MODULES.md) | Module contraction, free-NOT core minima, ordered quotients, provider-first layouts, and branch-and-bound. |
| [NOTES_L1343.md](sat-search/NOTES_L1343.md) | Fixed-prefix and cube-search work, with exact shard scope and surviving cube IDs. |
| [sat-search/experiments](sat-search/experiments) | Research implementations, correctness references, and reproducible checks. |
| [sat-search/results](sat-search/results) | Frozen targets, matched run records, witness circuits, and proof packets. |

Update the quick reference when a bound, minimum, implementation default, or research priority
changes. Add the proof assumptions, counterexamples, verification scope, and commands to the
topic notes. Keep raw matched results and checked proof artifacts beside their manifests in
`sat-search/results`. Put transient logs in `sat-search/logs` and link or archive runs that
support a durable result. Give each new regression an explicit expected verdict and keep the
independent reference available.

## Current direction and stopping rules

Effort split (from 2026-11-24): about 80% mathematical and algorithmic improvements, 15% targeted
verification, 5% documentation and maintenance. The verification infrastructure in `sat-search/verify`
(independent reference, differential harnesses, evidence manifests, coverage inventory) checks the
components a change touches. Do not re-audit unchanged rules or exhaustively test optional
configurations. Keep rule combinations without coverage disabled (`verified_combinations.json`), and
record remaining historical gaps in `sat-search/verify/AUDIT.md` without letting them block research.

Prioritize complete-function FPT synthesis, counted-NOT and nonmonotone synthesis, affine
certificate reconstruction, construction upper bounds, and hybrids with SAT. Audit proofs
separately from the prototypes that motivated them. Confirm a candidate with small independent
enumeration or formal proof before making an asymptotic claim.

The guarded family closes the universal `rank(H) <= 2e` direction. Revisit
sharing-only FPT for arbitrary partial labels only when a new restriction addresses the known
hardness. Archive explicit enumeration work superseded by certificate completion. Resume
provider matching, exact rectangle allocation, and capacity refinements when there is evidence
of stronger whole-function bounds or an end-to-end benefit. Reopen SAT propagation changes
with a measurable effect or a new sound pruning argument.

Prefer general methods and mathematically motivated changes to instance-specific rules, GPU
work, repeated benchmark replays, or longer caps. Record why a direction was closed and what
result would justify reopening it. Coordinate complementary theory work with ChatGPT so
implementation and independent review advance the same questions without duplicating effort.
