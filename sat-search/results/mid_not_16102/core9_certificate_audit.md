# L-meta-16102: audit, certified nine-gate core, and upstream status (2026-11-26)

This note continues [README.md](README.md), [two_fork_handoff.md](two_fork_handoff.md) and
[cofactor_reader_handoff.md](cofactor_reader_handoff.md). Evidence grades are kept apart below.

## Summary

| Claim | Grade |
| --- | --- |
| The target needs at least 8 proper binary AND/OR gates, even with free NOTs | Paper proof, audited again here with no gap found. Finite premises replayed exactly. Not Lean checked |
| Any posted ≤9-gate candidate reduces to the nine-gate core (8 binary gates, 1 live internal non-output NOT, NOT-avoiding paths, excess 3) | Paper proof, audited with no gap found. Not Lean checked |
| The nine-gate core CNF is UNSAT for all 22 first-gate representatives | 22/22 DRUP proofs checked by drat-trim. One shard also checked through LRAT by lrat-check |
| No circuit satisfies the posted L-meta-16102 statement | Follows from the two rows above plus the encoder correspondence (audited, not formalized). **Not machine-checked end to end** |
| Upstream closure | **Not possible as posted.** The statement is an existence claim (∃ C ...), which this evidence says is false |

## 1. Upstream statement and rules (checked 2026-11-26)

The desk lease record `pequalnp-proofs/.pnp/L-meta-16102.json` (lease from 2026-11-25, now expired) and the
public lemma page give the statement verbatim:
`∃ C : Circuit, FanInTwo C ∧ NestedCover.ReadsBack 6 C ∧ C.size ≤ 9 ∧ (∀ x, C.eval (List.ofFn x) = tableFun 6 bits x) ∧ (every gate is the output or read later) ∧ (no NOT reads a NOT) ∧ (some NOT reads a gate)`.
The permitted import is `PEqualNP.Defs`. The file is `lean/PEqualNP/Outside/L_meta_16102.lean`. The lemma page lists it as a
fleet conjecture ("Truth NOT known") with no attempts and no checker run. The live `/desk/board` (2441 open gaps,
updated 2026-11-26T23:13Z) no longer includes L-meta-16102. It has no refutation twin, the upstream tree has no
`L_meta_16102.lean`, and a PR search for `16102` found only the unrelated closed PR 16102 (L-meta-11902).

The current `CONTRIBUTING.md` and `join.txt` rules apply. A submission is one file of at most 512 KiB, proves exactly the posted
statement, uses only permitted imports, and contains no `sorry` or `native_decide`. Its axioms must be limited to `propext`, `Classical.choice`
and `Quot.sound`, and it must avoid numerals longer than 20 digits. The check has a 20-minute and 6.5 GB limit. A counterexample is sent only as a proof of a posted
negated twin ("refute" kind). No such twin is posted for this gap. The appropriate desk action is a release with
`statement_seems_false`, which requires holding a lease. This session held none and did not take one.

Re-check, also on 2026-11-26. First, the upstream `GateOp.eval`, `Circuit.eval`, `FanInTwo`, `ReadsBack` and `tableFun` semantics match the
archived encoder exactly. NOT reads only its first input, and an empty NOT is `true`. An empty AND is `true` and an empty OR is `false`. Repeated inputs are allowed and only earlier wires may be read.
Second, the site data (`data.pequalnp.com` lemma record `L-meta-16102.7c12f52db3d4`) lists the gap as a conjecture with no attempts.
Meta refutations exist (5,134 records), but each one is filed by the fleet's intake seat as a separate negated-twin lemma
`¬ (∃ C, ...)`. For example, L-meta-20809 is refuted through the checked twin L-meta-20808. No twin of L-meta-16102 exists; its neighbours
16101 and 16103 are other tables. A local Lean proof of `¬ statement` would therefore have no target file until such a twin is posted.

## 2. Independent audit of the paper reduction

Each step of [two_fork_handoff.md](two_fork_handoff.md) was rederived.

- **Excess identity.** The live graph has 6+b+u vertices and 2b+u operand occurrences, and only the output has outdegree 0. So
  Σ(outdeg−1) over non-output vertices is b−5. With b ≤ 7 there is either one fork of degree ≤ 3 or two of degree 2.
- **Read-once obstruction.** A signed read-once formula computing a monotone function has every essential leaf positive, by
  unateness. A minimal positive certificate and a maximal negative certificate then meet in exactly one variable, using the complement of the negative one. Masks 19 and 20 meet in {0,1}.
  Inessential variables lie in no minimal positive mask and in every maximal negative mask, so cofactor tests are unaffected.
- **First fork.** Every ancestor of the topologically first fork has outdegree 1, so the ancestors form an in-tree and each
  ancestor primary's path is forced through the fork. The residual-count test (exactly two residuals only for singletons
  and the full set) forces a signed singleton or a contradiction with the read-once obstruction.
- **One fork.** Fix the singleton primary. The remainder is a tree, and the non-read-once cofactor certificate contradicts it.
- **Two forks.** U consists of the non-i ancestors of g, and their paths are forced to g. In case t=0, U is a singleton, which gives the exact DP over 8 leaf positions.
  In case t=2, f = g or ¬g, which contradicts the cofactor certificate. In case t=1, the residual and indicator filters are valid necessary
  conditions. If exactly two residuals occur, monotonicity orders them by the all-zero and all-one U rows. The indicator is
  then monotone and equals g or ¬g, so it is read-once. V leaves are positive, by single occurrence and unateness. The DP
  enumerates every binary formula over labelled leaf positions.
- **Core consequences.** A dead NOT is impossible, since its reader is a live proper binary gate. The NOT cannot be the output, because then the circuit computes the complement of a
  monotone function. If every path from some primary passed through the NOT, the output would be antitone in that primary, which contradicts monotonicity and essentiality.
  The last gate is the output by the reader condition, so the encoder's fixed output position is exact.
- **Encoder ordering and symmetry.** Greedily appending a ready gate with the least largest operand index yields a
  nondecreasing order, because newly ready gates reference the gate just appended. The automorphism group is {id, (1 2)}.
  Each lexicographically first orbit representative also has the least maximum in its orbit. A global-minimum
  input-only gate over both labelings therefore lies on a representative and can be placed first. The added
  constraints are invariant under input relabelling.

No gap was found. The audit is a second human-style reading, not a formal check. The finite premises were replayed with
`node two_fork_check.js` and `node cofactor_reader_check.js`. Their output matches [two_fork_replay.json](two_fork_replay.json) and
[cofactor_reader_replay.json](cofactor_reader_replay.json) exactly. `python certify-nine-gate.py --self-test` matches
[nine_gate_constraint_selftest.json](nine_gate_constraint_selftest.json): 14,400 toy cases, 736 accepted, and 14,336 negative path-flag checks.

## 3. Certificate run (Mission 2)

The runs used the workflow runner (`research.py run`) with manifests [manifests/core9-diag.json](manifests/core9-diag.json) (shard 0) and
[manifests/core9-rest.json](manifests/core9-rest.json) (shards 1–21, 11 workers, 110 s wall time). The solver was Glucose 4 through
python-sat with a 300 s cap, which was never reached. Each DRUP proof was checked by drat-trim (commit `2e3b2dc`). Results are in
[core9_certificates.json](core9_certificates.json), which records each shard's CNF and proof SHA-256, solver statistics and verifier log hash.

- 22/22 shards were UNSAT, and all 22 were independently verified (`s VERIFIED`). There were no timeouts and no SAT.
- The longest solve took 21.7 s. The shards used 4,057,882 conflicts in total, and the DRUP proofs total 792 MB, with the largest at 71 MB.
- As a cross-check, drat-trim converted shard 9 to LRAT, and the separate `lrat-check` reported `c VERIFIED`.
- Raw CNFs, proofs and logs are in `sat-search/logs/16102-proof-shards/` and are not committed because of their size. They are
  reproducible from the manifests: the CNF hashes are fixed, while the proofs are solver-dependent.

The Mission 3 pruning (reader caps, pair caps and NOT boundary clauses) was **not needed** and was not integrated.

## 4. Lean status (Mission 4)

**Partial Lean check (2026-11-26).** [`sat-search/lean/SatBridge/Meta16102.lean`](../../lean/SatBridge/Meta16102.lean) is
stated for the upstream model (`PEqualNP.CircuitLowerBounds`, imported from `PEqualNP.Defs`) and builds with
`research.py lean sat-search/lean --module SatBridge.Meta16102`. Its axioms are only `propext`, `Classical.choice` and `Quot.sound`. It checks:
`sandwich`, which says that for an AND/OR/NOT circuit with at most one NOT gate, overriding the NOT output by a bit `y` gives a function
`G x y` monotone in both arguments with `C.eval x = G x v` for some `v`, hence `G x false ≤ C.eval x ≤ G x true`;
`f16102_mono`, which says the posted table is monotone in every input; and `fb_certificates`, the minimal positive and maximal negative certificates.
These are the first premises of the structural route below. They do **not** prove the negation.

**Reduction to two named gaps (Lean, same file).** `transfer_binary` refines `SatBridge.transfer`: an upstream fan-in-two circuit
gives a free-NOT AIG whose gate count is the number of *proper binary* gates (NOT, unary and nullary gates are free).
`posted_core` proves the following. Assume `hA : ¬ Realizes 6 F 7`, the eight-binary-gate bound in the AIG model. Then every circuit meeting the posted
fan-in, size, function and internal-NOT conditions has size exactly 9, exactly 8 proper binary gates, exactly one NOT, and only
AND/OR/NOT gates, so `sandwich` applies. The refutation therefore reduces to (A) `hA` and (B) the one-NOT nine-gate core.

**Attempt on (A).** [first_gate_lb.py](first_gate_lb.py) implements a first-gate recursion with three steps. The first is fan-out ≥ 2 restriction (`conditional_restriction`
in `CircuitLemmas.GateElim` is already formalized). The second is contraction of a fan-out-1 first gate, which requires checking that the function factors through an AND of two literals. The third is the connectivity floor.
It certifies only **B(f) ≥ 7** ([first_gate_lb.out](first_gate_lb.out)), one short of the 8 needed. Closing (A) therefore needs the stronger cascade casework
(a fan-out-2 input whose controlled first gate has a reader outside its readers, or the non-minimal two-gate pair), which the paper
proof replaces with forks, the read-once lemma and the DP.

Kernel-budget estimate for a direct search. Enumerating 8-gate prefixes and looking up the final gate leaves about
2·10^10 canonical prefixes per NOT placement, about 2·10^11 in all, against a kernel budget of roughly 10^8 reductions in 20 minutes. A brute-force
`decide` refutation of even the core is therefore infeasible, and so is any search that does not first use the structural reduction.

No Lean proof of the full statement or its negation was written or submitted. Because the posted statement is existential and false according to this evidence, no
proof of it exists. A refutation could only be submitted against a posted negated twin, and none exists. A Lean proof of the
negation would need the following:

1. Formalize the two-fork reduction. This covers the graph/fork counting, the read-once certificate lemma and the residual argument, with
   the finite premises proved by `decide`. The DP's 12.8M comparisons would require a smaller argument or a kernel-checkable
   enumeration.
2. Prove the core-to-CNF encoding sound and check 22 LRAT proofs in the kernel. Even the smallest proof is 11.6 MB of DRUP, far beyond
   the 512 KiB file limit, so embedding the proofs is impractical.
3. Alternatively, classify the excess-3 core structurally. The cofactor reader caps and the NOT boundary theorem are the
   natural starting point.

Blockers: (a) no posted refute twin, so even a complete proof has no submission target; (b) the proof sizes
exceed the upstream limits by three orders of magnitude.

## 5. Robust SAT lower bound (Mission 5)

`SatBridge.sat_robust_identifier_eventually` (`sat-search/lean/SatBridge/RobustIdentifier.lean:240`) states the following. For every m > 0
there is an N such that, for Q ≥ 1 with N ≤ 6(Q+1), every AND/OR/NOT fan-in-two circuit deciding `SAT` at length 6(Q+1) satisfies
`2m·n ≤ m·size + n`. Upstream has L037, L039 and L041; L041 gives `5k+1 ≤ size` at length 4k+2. The board on 2026-11-26 lists only `meta`
(2432) and `pcx` (9) gaps. In the site's full `clb` program (41 lemmas), the SAT circuit-size entries are L-clb-035 (retired),
L-clb-036 (in work, `¬ ∃ s ≤ O(n^1.01)`) and L-clb-038 (retired: `6q ≤ s(6q)+1`, which `sat_six_lower'` would imply). The remaining
open clb conjectures concern ACC0, TC0 and threshold circuits, so none matches the robust theorem. No contribution route outside posted desk units was found,
because `join.txt` says units come only from the desk. The theorem is a candidate intermediate result. Proposing it requires the
maintainers to post a unit. It does not address L-clb-036.

## Reproduction

```powershell
node sat-search/results/mid_not_16102/two_fork_check.js
python -B sat-search/workflow/research.py run sat-search/results/mid_not_16102/manifests/core9-diag.json --workers 1
python -B sat-search/workflow/research.py run sat-search/results/mid_not_16102/manifests/core9-rest.json --workers 11
```
