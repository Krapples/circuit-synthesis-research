# Search workflow

Load this file when the bottleneck is finding a circuit, witness, certificate, or computational
exclusion. Runner commands and manifest formats are in [README.md](README.md). The rules in
[AGENTS.md](../../AGENTS.md) still apply.

## Shrink the search before spending more compute

Try these before raising a time limit: analytical lower and upper bounds, normal forms, essential
inputs, sharing allowance and excess, symmetry and canonicalization, reader and fan-out limits,
support restrictions, partial-label structure, dynamic programming, regional decomposition,
incremental SAT, certificate completion, and alternative encodings or solver portfolios.

## Run batches that answer a question

- Write the question and the decision it informs in the manifest, with basis, budget, reduction
  scope, timeouts, worker and memory limits. Canonicalize whole-graph queries through the cube
  adapter. Keep the original labeling for pinned jobs, partial labels, and prescribed input roles.
- Check prior runs and topic notes first. Reused evidence keeps its original target, basis,
  budget, coverage, and grade.
- Test an improvement on a few representative instances before a whole batch. Run about three
  short fixed-budget repeats to measure noise before a long tier, and escalate only when a
  difference exceeds that spread.
- Group hard units by shared structure and bottleneck, not by name.
- Unproven pruning stays experimental and off by default. A prescreen may reject a case only on
  proof of infeasibility; an unknown result never justifies an exclusion.

Luna can launch a Sol-written manifest, watch it, and summarize results as a table of at most 20
lines. Sol chooses the question, the budget, and whether to escalate.

## Theory–search–proof loop

1. Notice a pattern or conjecture, often in the instances that stay hard.
2. Challenge it with enumeration, SAT, and adversarial cases.
3. Refine the hypotheses and prove it on paper.
4. Formalize it incrementally ([PROOF_WORKFLOW.md](PROOF_WORKFLOW.md)).
5. Turn the verified theorem into a sound search improvement, checking that the implementation
   meets the theorem's hypotheses.
6. Benchmark against frozen baselines with matched limits on an idle machine.
7. Feed the remaining hard instances back into step 1.
