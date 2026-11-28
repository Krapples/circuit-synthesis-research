# Search workflow

Load this file when the bottleneck is finding a circuit, witness, certificate, or computational
exclusion. Runner commands and manifest formats are in [README.md](README.md). The rules in
[AGENTS.md](../../AGENTS.md) still apply.

## Shrink the search before spending more compute

Try these before raising a time limit: analytical lower and upper bounds, normal forms, essential
inputs, sharing allowance and excess, symmetry and canonicalization, reader and fan-out limits,
support restrictions, partial-label structure, dynamic programming, regional decomposition,
incremental SAT, certificate completion, and alternative encodings or solver portfolios.

## Choose the solver and settings for the instance

Do this before any long run. Solver performance depends on the instance family, so no one setting
is right everywhere.

1. **Classify the instance.** Note the encoding and generator (`cube_search.py` CNFs versus
   native `template_synth --dump` CNFs), the basis, the size, and the expected answer. Hunting a
   witness (expected SAT) and proving an exclusion (expected UNSAT) favor different settings.
   Note what the run needs: incremental assumptions, a working interrupt or STOP file, or a
   checkable proof (DRUP/LRAT logging costs time but turns a verdict into a certificate).
2. **Start from the recorded winner for that family.**
   - `cube_search.py` and other pysat drivers: `maplechrono`, with `maplecm` as the runner-up.
     It honors `interrupt()`; CaDiCaL 1.9.5 ignores it and breaks the STOP file.
   - Native `template_synth.exe` template CNFs: CaDiCaL 2.2, congruence off.
   - Witness hunting: a small mixed portfolio. `mergesat3` once found a SAT case first.
   - Pruning flags: start from `cube_search.py --fast`. Keep `--bottleneck` off (about 4.5x more
     CPU), and add `--minimal` only after sizes G-1 and G-2 are UNSAT without it.
3. **Re-screen when the family or encoding is new or has changed.** Take two to four
   representative instances, hard ones included, since rules that are neutral on easy cases can
   pay off on hard ones. Run single-threaded with about three seeds. Run the baseline first, cap
   each challenger at max(10 s, 1.5 x the baseline time), and record "stopped-worse". Switch only
   when the gain exceeds the seed spread.
4. **Set the parallel layout and caps.** Fill up to 22 threads with independent pieces (by case,
   cube or first gate) rather than many-thread solving of one CNF; much finer static splitting
   has hurt before (about 25x). Give each job an initial timeout with a factor and a ceiling, and
   estimate memory per worker.
5. **Record the choice.** Put the solver, version, flags, seeds, caps and screen results in the
   manifest or results README, and update the topic note when a family's winner changes.

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
