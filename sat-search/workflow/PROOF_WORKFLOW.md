# Proof workflow

Load this file for proof-bound or reduction-bound work and before any submission. The rules in
[AGENTS.md](../../AGENTS.md) still apply.

## Build a dependency graph first

1. Write the mathematical outline before formalizing: invariants, case splits, constructions,
   contradictions.
2. Split it into named lemmas, and split difficult lemmas again. Mark dependencies and the
   critical path. Every helper has a stated purpose in the target proof or reusable infrastructure.
3. Decompose by the mathematics, not by compiler errors.
4. Optionally write a Lean skeleton with the exact target and `sorry` stubs in a scratch
   workspace to check that the statements elaborate. A stubbed skeleton is graded "stubbed".
5. Keep the graph and each obligation's grade in the step record.

## Close one obligation at a time

1. State the claim and its assumptions precisely.
2. For a novel claim, run a truth check first: small enumeration, SAT counterexample search,
   boundary and degenerate cases, overlapping supports and shared gates, complete-function and
   partial-promise versions separately. Routine identities and library facts need no check.
3. Write the smallest useful Lean proof and compile only that file in a workspace whose
   lockfile matches the project, e.g. `lake env lean Scratch/Step_x.lean` or
   `python -B sat-search/workflow/research.py lean <workspace> --source <file> --strict --timeout 120`.
   Run long builds in the background and keep full logs on disk.
4. Read the first actionable error only, then classify it: syntax/elaboration, tactic failure,
   missing library lemma, wrong formal definition, missing hypothesis, false claim, or a dead
   strategy.
5. After 3 substantive failures on one obligation, stop varying tactics. Re-run the truth check,
   revise the argument, or change strategy. A refuted lemma goes into the notes with the
   smallest counterexample and becomes a regression case.
6. When it compiles, put `#print axioms` on it, confirm only `propext`, `Classical.choice`,
   `Quot.sound` and no `sorryAx`, then grade it and checkpoint.

Luna can run compiles, summarize the first error, and run audits. Sol chooses the next proof
step and decides when a strategy is dead.

## Circuit transformation checklist

Every gate-elimination, replacement, restriction, normalization, or repair proof addresses:

- **Construction:** the replacement circuit and its gate and wire maps.
- **Structural validity:** topological order, valid wire references, gate arity, permitted
  operations, a valid output wire, and the model's restrictions (basis, NOT counting, raw-primary rules).
- **Semantics:** the transformed circuit computes the function or satisfies the exact promise on
  every relevant assignment. A reduction to boundary assignments under monotonicity is proved
  explicitly.
- **Shared providers:** shared subexpressions, protected gates, exclusive cones, external readers.
  A circuit DAG is not an unfolded formula.
- **Gate accounting:** exactly which distinct gates are removed, kept, replaced, or added, with no
  double counting and no exclusive resource charged twice.
- **Consequence:** strict savings, non-increase, a bound, or a contradiction to minimality.

Promote a pattern that recurs into shared infrastructure. For promised circuits, start from the
[evaluator and support checks](README.md#proof-checks-for-promised-circuits).

## Witnesses and certificates

- **Existence:** find a witness, evaluate it independently against the exact target, check gate
  counts and restrictions, generate the Lean construction, and verify the exact theorem and axioms.
- **Non-existence:** record the exact search scope, obtain and independently check a certificate
  where practical, and justify the encoding and reductions. Formalize in Lean only exclusions that
  are small enough for a permitted kernel check (`decide` or a verified checker). Larger
  exclusions stay graded as checked certificates or computational evidence.
- Do not use `native_decide`, `bv_decide`'s generated axiom, or any other unsupported shortcut in a
  submitted proof.

## Package and submit

Develop in modules if it helps. Submission usually requires one self-contained file with the
permitted dependencies only. Luna can run this checklist; Sol approves the result.

1. Flatten into the submission file and diff the target statement against the pinned upstream
   statement. Any difference stops the submission.
2. Compile the exact packaged file with the official checker (`tools/pnp.sh check` for desk units)
   and audit its transitive axioms in a separate local replay. Keep `#print axioms` lines out of
   the submitted file.
3. Search the file for `sorry`, `admit`, `axiom`, `native_decide`, and imports outside the
   permitted list.
4. Confirm upstream has not merged the step, then submit the exact checked commit
   (`tools/pnp.sh submit <step>` for desk units). Desk submissions are pre-authorized once
   steps 1–3 pass; other external actions need the user's approval.
5. Record submitted, accepted, and merged as separate states (`research.py pr <number> --watch`).
