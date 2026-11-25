# Signed regional bounds, module preprocessing, and fast FPT (2026-11-24)

Statuses follow [verify/AUDIT.md](verify/AUDIT.md):

- **proved:** a written argument covers every case;
- **independently tested:** it agrees with the independent reference on the stated finite scope;
- **provisional:** relied on with a supplied argument that has not been reviewed here;
- **unresolved:** coverage is missing.

The theory prototypes come from the independent theory audit and live in [theory/](theory/).

## Signed regional lower bound

`theory/signed_region_bounds.py` lower-bounds the binary excess B − n + 1 of AND/OR/NOT circuits for
arbitrary complete functions. It adds, in order:

1. exceptional-pattern incompatibility;
2. output-region unateness with sign consistency (the "sandwich" level);
3. ordered cofactor-diversity port costs.

`not_lower()` bounds the NOT count. Total gates ≥ n − 1 + `lower` + `not_lower`.

**Status:** provisional. Independently tested:

- exact gate-set enumeration for n ≤ 3 (bound = minimum, gap 0);
- 400 reference instances (328 tight);
- 20 decided random nonmonotone 4-input functions (`verify/test_signed_bound.py`);
- no violation of any verified upper bound on the 106 complete corpus targets.

**Integration:** `cube_search --signedregions` (opt-in, on the essential restriction). It rejects budgets
analytically and raises the binary floor, which also tightens the NOT cap. Differential checks: 1,950
run_cube jobs and 336 CLI jobs, 0 mismatches. It is in the command-line allowlist. Its prefix-exact
coverage is still unresolved.

### Measurements (`experiments/signed_bound_compare.py`, `results/signed_bound_compare.jsonl`)

| Measure | Result |
| --- | --- |
| Monotone targets (90) | Never below the existing analytical NOT-enabled bounds (recursive with closure and colouring, polarity formula ports); strictly above on 20 |
| Best prior lower bound (support, existing, SAT endpoint) | Raised on **26 of 106** complete targets: hypergraphs, comparators, random monotone, parity-4/5, mux-4-to-1, exactly-k |
| Budgets settled analytically | **53** budgets, previously open or SAT-dependent |
| Cost | At most 7.7 s and about 15 MiB per target |
| Contribution of each level | Pattern incompatibility adds strength in 56 cases; ordered diversity in 13; the sandwich level in 0 on this corpus |
| Search (`results/archive_20261124/ablation__signed-ablation-20261124.jsonl.gz`) | General basis: 211.5 s → 104.4 s against plain (conflicts halved, analytical rejections 307 → 721). Monotone basis: 93.2 → 89.7 s. No gain over `--fast` on graph functions. |

**hypergraph-17:** the NOT-enabled minimum is **7, certified**. Evidence: a verified 7-gate witness plus
RUP-checked exclusions at 6 and 5 gates (`results/hypergraph17_not_certificate.json`). The signed bound
pointed to the result; the certificate does not depend on it.

### Typed bound

`theory/signed_typed_bound.py` optimizes sharing and NOT requirements jointly, using exact cotree NOT costs
of regional slices.

- **Status:** provisional, independently tested (supplied checks; 444 random circuits).
- **On the corpus:** never above the signed bound, and applying it to the reduced core plus trace isn't
  stronger either. It gains only on read-once-heavy functions (42 of 600 sampled read-once 5-input
  formulas).
- **Decision:** kept, off by default.

## Exact functional-module preprocessing

`theory/module_contraction.py` does two things:

- **Contraction:** a raw AND/OR input module {x_i, x_j}, where f depends on the pair only through
  x_i ∧ x_j or x_i ∨ x_j, is replaced by one new input.
- **Peeling:** a canalizing input is removed.

Claim: each step removes one input and one binary gate, and min(f) = len(trace) + min(core) holds in the
counted-NOT basis and in the monotone basis. Traces allow reconstruction.

- **Status: proved in Lean** for both raw step types (see "Formal proof" below). It was also tested
  independently against gate-set enumeration up to 4 inputs (7,340 combined checks).
- **Partial-function rule** (`theory/partial_module_contraction.py`, neutral-slice coverage, minimum of the
  contracted and ignored branches): tested on 6,360 rule queries.
- **Scope:** whole-function reductions are never applied to pinned-prefix searches.

### Formal proof (`lean/CircuitLemmas/Module.lean`, 2026-11-24)

**Status: proved.** The file has no `sorry`. `#print axioms` (`lean/AxiomsCheck.lean`) lists only
`propext`, `Classical.choice` and `Quot.sound`. This is a formal proof about the mathematical circuit
model of `CircuitLemmas/Basic.lean`, not about the Python implementation.

- **Model.** Circuits are well-formed `Circuit n m` (fan-in 2, AND/OR/NOT). Wire values are defined by
  recursion on the wire index. `minSize b f` is the least number of gates of a circuit in basis `b` with
  some wire computing `f`. The bases are counted-NOT (every gate counts, NOT included) and monotone
  (AND/OR only).
- **`module_contraction`.** Suppose `f(x) = g(update(x without x_j, i', h(x_i, x_j)))` with `h` AND or
  OR, `f` depends on `x_j`, and `g` is computable in the basis. Then `minSize f = minSize g + 1`.
  Stronger form `module_sizeLE`: f has a circuit with at most k + 1 gates iff g has one with at most k.
- **`peel_contraction`.** If `f(x) = h(x_i, g(other inputs))` with `g` nonconstant, then
  `minSize f = minSize g + 1`.
- **`minSize_perm`.** Permuting inputs preserves `minSize` for nonconstant functions, so the convention
  for where `g` receives the module output (Python puts it last) does not matter.
- **Proof.** One pass, `run`, does constant propagation and input substitution. Inputs are bound to
  constants or new wires. A gate with a constant argument, or a binary gate whose arguments became the
  same wire, is dropped and its readers are redirected.
  - `pass_circuit` proves the pass preserves semantics, basis and well-formedness, never adds gates, and
    drops the first gate that reads an input fixed to a constant.
  - **Restriction** (`restrict_const`): fix x_j to the neutral constant of h. Since f depends on x_j,
    some gate reads it, so at least one gate goes; x_i then plays the module output.
  - **Substitution:** prepend (module) or append (peel) one AND/OR gate.
  - No graph-minor machinery is used.
- **Hypotheses compared with the Python rule.** The theorems need less than all inputs essential: only
  dependence on x_j (module) or nonconstant g (peel). The Python steps check both. `hfin`, the
  computability of g in the basis, is automatic in the counted basis (completeness is not formalized
  here); in the monotone basis it holds for monotone g.
- **Not formalized.**
  - The repo's output convention (last gate, every wire read) gives the same minimum as "some wire
    computes f" by deleting dead gates. This is standard but not proved here.
  - Signed (free-NOT) contraction.
  - The cotree NOT-cost recurrence.
- **Consequence for the corpus.** Every trace in `results/module_core_minima.jsonl` uses only raw `pair`
  and `peel` steps (`simplify(..., signed=False)`), and each step's identity is confirmed by the
  verified lifted witness. So min(f) = len(trace) + min(core) is now proved for those cases, by induction
  on the trace. Each lower bound now rests only on the core minimum, which comes from the
  `verify/reference.py` SAT search and is uncertified unless a checked exclusion exists
  (`certify_split.py`).
- **Effort.** About 1.5 hours of agent time for 807 lines. Checking `Module.lean` takes 30–45 s with
  the direct `lean` call; `Basic.lean` must be compiled to an `.olean` first (see `HANDOFF.md`).

### Corpus (`experiments/module_corpus.py`, `results/module_corpus.jsonl`)

- 57 of 106 complete targets are reducible.
- 195 inputs are removed in total.
- 37 targets reduce to a single input, so their exact minimum follows from the trace alone. All 37 were
  already closed.

### Open cases closed through exact cores (`experiments/module_core_minima.py`)

Each core is solved exactly by `verify/reference.py`. A witness for the original function is rebuilt by
lifting the core witness through the trace and checked on every row, so **every upper bound is
independently verified**. Each lower bound rests on the module theorem (now proved in Lean for `pair`
and `peel` steps) plus the core minimum from the uncertified reference SAT search, unless certified
separately (`experiments/certify_module_minima.py`, `experiments/certify_split.py`). Checking the core
exclusion alone is enough: a full-size exclusion is no longer needed.

| Case | Inputs → core | Previous NOT-enabled interval | Exact minimum (NOT-enabled = monotone) |
| --- | --- | --- | --- |
| hypergraph-18 | 6 → 5 | [7, 12] | 8 |
| hypergraph-24 | 8 → 5 | [8, 10] | 8 |
| random-monotone-03 | 6 → 3 | [7, 12] | 7 |
| random-monotone-04 | 7 → 6 | [8, 11] | 9 |
| random-monotone-08 | 6 → 4 | [8, 13] | 9 |

Further exact minima, each with a verified lifted witness:

- generated-08 = 6 (was [6, 10]);
- comparator-07 = 8 (was [7, 14]);
- generated-09 = 8 (was [7, 13]).

**random-monotone-03 = 7 is certified** in both bases with RUP-checked exclusions at 6 and 5 gates. The
remaining module minima are being certified by `experiments/certify_split.py`, which splits each exclusion
exhaustively by first gate and checks a proof for every piece.

## Complete-function FPT (`theory/fast_readonce_fpt.py`)

- **Cotree NOT costs:** exact cotree-based NOT minimization (`theory/readonce_not_cost.py`) replaces
  recursive local synthesis whenever a regional table is complete. Independently tested: exact against
  formula enumeration for n ≤ 5 (15,104 formulas).
- **Speed on 694 queries:** local completion calls fall from 17,888 to 1,552, and time from 2.16 s to
  0.66 s.
- **Module preprocessing in front of FPT** (`theory/module_fpt_demo.py`): 2.8× faster on reducible 4-input
  targets, little change on generic ones.
- **Practical width:** a 5-input function (hypergraph-07, minimum 7) takes 10 s with FPT and 0.7 s with
  the reference SAT encoding. Use FPT for cores up to 4 inputs and SAT beyond
  (`experiments/module_fpt_bench.py`).

## First-gate elimination bounds (`theory/first_gate_bound.py`, `experiments/first_gate_compare.py`)

These are free-NOT binary bounds from restrictions and first-gate absorption, and they also bound the
NOT-enabled total: total ≥ max(binary bounds) + `not_lower`.

- **Status:** provisional. Independently tested: the supplied exact checks, a targeted differential run of
  `cube_search --firstgate` (1,950 jobs, 0 mismatches), and no violation of any verified upper bound.
- **Complete targets:**
  - beats the strongest production binary bound on **21 of 106**;
  - raises the NOT-enabled lower endpoint on **20** (threshold-7-4: 12 → 14; threshold-8-5: 14 → 16;
    parity-5: 11 → 14; exactly-3-of-6: 12 → 14; hypergraphs +1);
  - resolves hypergraph-07 to 7;
  - at most 0.94 s per target (n = 8).
- **Recursive combination with the regional bound** beats simply taking the maximum in only 1 case.
- **Affine identification** gave no gains and stays disabled. **XOR stripping** adds nothing beyond the
  bound on the corpus.
- **Partial targets** (`theory/partial_first_gate_bound.py`): partial-09 rises 7 → 8 (monotone) and 6 → 8
  (NOT-enabled), above the production endpoint.
- **Integration:** `cube_search --firstgate`, opt-in and adaptive (skipped above 9 essential inputs).

## XOR factors (`theory/xor_factor.py`)

For the exact factor f = x ⊕ h with h nonconstant and independent of x: C_free(f) = C_free(h) + 3.

- **Status:** independently tested, 284 identities against free-NOT enumeration
  (`verify/test_xor_factor.py`).
- The unrestricted XOR-input-module conjecture is not assumed.

## Partial counted-NOT bound (`theory/partial_counted_bound.py`, `experiments/partial_not_bound.py`)

Binary first-gate bound plus the exact NOT count from Markov inversion (`theory/partial_inversion.py`).
The two parts count disjoint gate types, so their sum bounds the counted total.

- **No violations** against counted gate-set enumeration.
- **Exact on 92% of all 3-input partial tables** (5,548 of 6,016), against 23% for the binary bound alone.
- **Exact on 76% of checked 4-input tables** (1,062 of 1,394), against 8%.
- The NOT term adds on 235 of 273 partial nonmonotone corpus labels.
- The inversion bound is 0 for monotone targets whenever the inputs are available, so it adds nothing
  inside `cube_search`.

## Exact NOT optimization on signed skeletons (`theory/skeleton_not_opt.py`, `experiments/skeleton_not_bench.py`)

Global NOT minimization on a fixed signed AND/OR skeleton: a three-state shared-wire dynamic program, or
polynomial minimum cut when the signed dependency graph is balanced.

- **Self-check:** matches exhaustive phase optimization on 600 skeletons and the OCT reduction on 300.
- **Competitiveness:** on all 192 three-input functions with a minimum free-NOT binary size of 4 or less,
  a minimum-binary signed skeleton plus exact NOT optimization reaches the true counted minimum every
  time.
- **Stored witnesses:** 294 recorded corpus witnesses were converted, re-optimized and verified, with no
  reduction, because none contains a NOT gate. All stored corpus witnesses are monotone.

### NOT-enabled intervals updated by cross-basis witnesses and today's bounds

A monotone witness is also a NOT-enabled circuit. Using the smallest verified monotone or module witness as
the NOT-enabled upper endpoint, together with the signed and first-gate lower bounds:

- **14 upper endpoints tighten.**
- **10 intervals close:**

  | Case | Exact minimum | Closed by |
  | --- | --- | --- |
  | hypergraph-18 | 8 | module core |
  | hypergraph-22 | 7 | monotone witness |
  | hypergraph-24 | 8 | module core |
  | graph-02 | 8 | monotone witness |
  | cycle-5 | 7 | monotone witness |
  | random-monotone-03 | 7 | module core |
  | random-monotone-09 | 8 | monotone witness |
  | generated-08 | 6 | module core |
  | generated-09 | 8 | module core |
  | comparator-10 | 9 | module core |

The lower bounds are provisional analytical bounds, apart from random-monotone-03, which is certified.

## Normalized signed-skeleton counted-NOT SAT (`theory/phase_budget_cnf.py`, `experiments/phase_budget_compare.py`)

Explicit NOT slots are replaced by per-source inverter variables and wire polarities, normalized against a
reference row, which leaves four binary operation types. Budgets can be fixed-binary, separate binary and
NOT, or joint total through activation variables.

- **Self-checks pass:** 1,186 CNF queries against an independent counted-gate oracle, 800 skeleton checks
  and 3,051 prefix checks.
- **Matched comparison** against the existing direct counted-NOT encoding: 42 cases with known NOT-enabled
  minima, n ≤ 6, budgets M − 1 and M, MapleChrono, 300 s limit, no open solves. Verdicts agree and every
  witness verifies.

  | | Existing direct encoding | Signed-skeleton (phase) |
  | --- | --- | --- |
  | Clauses | 428,876 | 2,678,274 (6.2×) |
  | Conflicts | 929,884 | 425,003 (−54%) |
  | Time | 61.6 s | 77.9 s (+26%) |
  | DRUP proof lines (UNSAT) | 82,663 | 79,096 (−4%) |

- **By group:**
  - monotone UNSAT: 2.7× slower (11.5 → 30.5 s);
  - monotone SAT: slightly faster (47.8 → 43.7 s; conflicts 3.4× fewer);
  - nonmonotone cases: too small to separate.
- **Decision:** no meaningful advantage, so the existing encoder stays. Lazy cycle cuts and conflict packing
  are not pursued.
- **Possible follow-up:** the conflict reduction points to the clause count (one selector per pair and
  type). A variant with phase normalization and the baseline's linear left/right selectors is untested.
- **Scope:** both encodings are at-most-G; neither is used for exact-size pinned-prefix claims.

## Adaptive analytical branch-and-bound (`bnb.py`, first version)

- **Nodes:** pinned prefixes at an exact budget.
- **Children:** every next gate allowed by the colex order (an exhaustive split).
- **Closing a node:** the forced-repeat bound and the ordered bound (cached on the multiset of feature
  columns) close nodes analytically; survivors are extended while probe rejection is at least 80%,
  otherwise handed to conflict-limited `run_cube` SAT.
- **Persistence:** the tree goes to JSONL and is resumable.
- **Smoke test on the 5-cycle:** all 20 root nodes close analytically at size 6; verified witnesses at
  size 7.
- **Depth probe** (`experiments/bnb_depth_probe.py`): one more pinned gate rejects 167 of 168 and 177 of 182
  children of the L-meta-1343 size-19 survivors.
- **Status:** prototype. Not yet run on the survivors and not yet differential-tested.

## Pair-irreducible cores (`theory/irreducible_region_fpt.py`, `cube_search --irreducible`)

After module contraction, a core has no raw AND/OR input module. Consequence: a gate whose two operands
are primary inputs cannot be the only reader of both. Otherwise f would depend on them only through that
gate, which would be a module. This is a semantic property of every circuit computing the core, so it also
holds with pinned prefixes.

- **FPT form** (every regional subtree with two or more leaves contains a port): 153 queries agree;
  recursive local calls fall 34% (37,883 → 25,095) and time from 0.85 s to 0.65 s (1.3×).
- **SAT form** (`--irreducible`: ¬sel(j, left = i) ∨ ¬sel(j, right = k) ∨ R_i ∨ R_k; needs `--readonce`;
  refuses targets that have a module):
  - differential check: 748 jobs, 0 mismatches;
  - ablation on pair-irreducible instances: conflicts −6% in the general basis, but time +5%; with
    `--fast`, slower.
  - **Decision:** a correct but redundant SAT constraint. Opt-in, not recommended, not allowlisted.

## Saturated monotone cuts (`theory/saturated_frontier.py`)

Deferred. Its own test needs `monotone_frontier_order.py` and `backward_column_synthesis.py`, which are not
in the repository. Its bounds apply to circuits that respect a chosen cut; they are not whole-function bounds
unless a cut must be respected.

## Branch-and-bound on the L-meta-1343 size-19 survivors (validation, in progress)

`experiments/l1343_bnb.py` runs `bnb.py` from each survivor's prefix. Survivors fully excluded so far, all
analytically with no SAT call (rule-dependent: partial ordered and forced-repeat bounds):

| Survivor | Result |
| --- | --- |
| b:1-1-4 | 323 analytical nodes; one child expanded one level deeper, all of its children closed |
| b:1-1-8 | 124 analytical nodes |
| b:1-2-9 | 106 analytical nodes |
| b:1-4-8, b:1-5-10, b:1-6-7, b:1-8-10 | analytical (no SAT call) |
| b:1-4-5 | all closed except one depth-5 node, open after an 1800 s SAT call |

Trees are in `results/bnb_l1343/`. A resume defect (resumed runs skipped every `expanded` node, so open
leaves below them were never revisited) was fixed on 2026-11-24; open nodes are now retried on resume.

## Low-excess exact ladder: modules -> one-sharing -> two-sharing (`experiments/sharing_ladder_corpus.py`)

Pipeline per complete target: module reduction (raw for monotone, signed for free-NOT), then
`theory/one_sharing_core.solve_core` (excess <= 1), then `theory/two_sharing_core.solve` (excess = 2), with
witnesses rebuilt by `two_sharing_core.reconstruct` (truth table and cost asserted on every row).
Free-NOT results are binary-gate minima with free NOTs, **not** counted-NOT totals.
Prototype self-checks pass (`two_sharing_core.py --signed-four`: 383 primary / 117 one / 500 none;
two-sharing is 10.6x faster than regional FPT on 28 matched cores).

Verified computational result (106 corpus targets, `results/sharing_ladder_corpus.jsonl`, 0 timeouts):

| Basis | excess 0 | 1 | 2 | > 2 (undecided) |
| --- | --- | --- | --- | --- |
| monotone (total) | 34 | 7 | 9 | 40 |
| free-NOT (binary) | 38 | 10 | 10 | 48 |

- 50 monotone and 58 free-NOT exact minima established without SAT; 0 conflicts with recorded intervals.
- Every ladder-decided monotone minimum was already closed in the recorded intervals: **0 new closures**.
- Production SAT (`cube_search.run_cube`, monotone, whole core) agrees on all 16 cores it was run on:
  ladder 0.095 s total versus SAT 37.4 s (e.g. random-monotone-09: 0.033 s vs 32.8 s).
  Regional FPT agrees on 13/13 small cores.
- Conclusion: the ladder is a fast exact front end for low-excess targets (a SAT replacement there), but
  the corpus's open targets all have excess > 2.

`theory/restriction_excess.py` (conditional filter, binary excess only): self-checks pass; the first-gate
stage gains often over unary restrictions, but on the samples it never beats max(regional, first-gate).
Kept as a filter for branch-and-bound candidates, not a whole-function bound.

## Second-chance screening (2026-11-24, stopped early for runtime)

- Normalized phase encoding vs direct counted-NOT encoding (`experiments/second_chance_encoding.py`,
  `results/second_chance_encoding.jsonl`, 66 of 98 matched pairs, challenger capped at max(10 s, 1.5x
  baseline)): phase faster on 9 (hypergraph-24 G=8 106 s -> 38 s; hypergraph-03 G=9 584 s -> 444 s;
  comparator-03 2.6 s -> 0.2 s), stopped-worse on 27, open 15; solved 1 of 16 baseline-open pairs. Not a
  default; a candidate for portfolio use on hard 6-8 input budgets. Peak-memory column is unreliable (0).
- Prefix restriction bound as a branch-and-bound filter (`experiments/prefix_restriction_probe.py`,
  partial): 196 children, 192 already rejected by production bounds, **0 new rejections**. Closed.

## Archived and closed directions

- `theory/archive/activity_port_bound.py`: local gains only, no whole-function strengthening.
- Purely structural regional compatibility under unrestricted control is closed:
  `theory/signed_control_completion.py` shows the signed compatibility test is exact for that relaxation.
