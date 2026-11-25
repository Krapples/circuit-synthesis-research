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

## Excess-three stage: ordered quotient reconstruction (`theory/ordered_quotient_core.py`, `experiments/excess3_ladder.py`)

Backends (experimental, not wired into `cube_search`): `theory/conditional_provider.py` (exact for circuits with at
most one shared internal wire plus repeated primaries) and `theory/ordered_quotient_core.py` (`solve3`: excess <= 3
on complete, fully reduced monotone / free-NOT cores; adds the two-shared-internal-wire class).
- **Fixed-layout feasibility vs unrestricted feasibility.** `fixed(...)` is exact for one specified layout only;
  `conditional_provider.solve` returning None excludes only its class. Only `solve3` claims an exhaustive decision,
  and only at excess <= 3 (the class enumeration is a prototype claim, checked on small oracles).
- Self-checks pass (`logs/ordered_quotient_check.log`, `logs/conditional_provider_check.log`): 1,203 + 1,800
  fixed-layout comparisons against independent formula-column enumeration, exhaustive gate-set oracle agreement
  (4-input monotone, 3-input free-NOT). `theory/quotient_bench.py` reproduces the six 7-input signed exact
  excess-three cores (9 gates each).

Corpus run (88 cores left undecided by two-sharing, 230 jobs, 120 s per job, `results/excess3_ladder.jsonl`):

| Basis | excess 3 (witness) | excess >= 4 (provisional) | timeout |
| --- | --- | --- | --- |
| monotone | 8 | 32 | 0 |
| free-NOT (binary) | 8 | 40 | 0 |

- Cross-checks: production SAT (monotone, G = m+1, m+2) agrees on 22/22 finished cores (10 timeouts); regional FPT
  agrees on 20/20 (2 timeouts). The two search orders always agree on the decision.
- **Closed intervals (verified witness meets the known lower bound):** hypergraph-14 monotone [9, 13] -> **9**,
  hypergraph-23 monotone [9, 13] -> **9**. Both are monotone targets whose NOT-enabled lower bound is 9, so the
  NOT-enabled minimum is also 9. SAT independently finds the 9-gate hypergraph-14 circuit and excludes 8.
- **New lower bound:** hypergraph-08 monotone >= 9 (was [8, 13]); confirmed by production SAT (G = 7, 8 UNSAT on
  the whole function, core = function), not proof-checked.
- Free-NOT exclusions imply counted-NOT lower bounds (binary min >= B and >= N NOTs give total >= B + N). Each implied
  bound L was checked with the direct counted-NOT encoding at L-1 (`experiments/excess3_not_confirm.py`,
  `results/excess3_not_confirm.jsonl`, maplechrono, 300 s, not proof-checked):

  | Target | NOT-enabled before | Implied | SAT at L-1 | Status |
  | --- | --- | --- | --- | --- |
  | complete-4 | [6, 7] | >= 7 | UNSAT 2.4 s | **closed = 7** |
  | threshold-4-3 | [6, 7] | >= 7 | UNSAT 2.6 s | **closed = 7** |
  | graph-01 | [7, 9] | >= 8 | UNSAT 11.7 s | [8, 9] |
  | hypergraph-08 | [8, 13] | >= 9 | UNSAT 73 s | [9, 13] |
  | mux-4-to-1 | >= 10 | >= 11 | open 300 s | provisional (solve3 exhaustiveness) |
  | random-monotone-10 | [10, 17] | >= 11 | open 300 s | provisional |

  hypergraph-12 (8), comparator-07 (8) and random-monotone-08 (9) were already exact; SAT agrees with each.

Search order (`solve3(internal_first=...)`):

| Task | Cores | default | internal_first | min of both |
| --- | --- | --- | --- | --- |
| construction, targeted (quotient_bench) | 6 | 117.6 s | 3.5 s | 3.5 s |
| construction, corpus | 16 | 21.7 s (wins 12) | 49.1 s | 17.7 s |
| exclusion, corpus | 71 | 148.9 s | 146.3 s | 143.2 s |

Neither order dominates construction; exclusion must exhaust both classes, so order is irrelevant there. Adaptive
policy: race both orders in parallel for construction (time = min), single order for exclusion. A cheaper
predictor than racing was not found.

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

## Provider-first layout projection

The code in [layout_projection.py](theory/layout_projection.py) generalizes the
ordered quotient layout enumerator. It chooses repeated primary inputs, the
number of internal providers, and their recipient multiplicities before it
places private primary groups. A partial placement is cut when the target
cofactors at one fixed readable primary pattern require more states than the
live internal wires can carry. A receiving region similarly needs at least
enough input patterns to realize its distinct observable selector slices.
For free NOTs the selector slices may be identified up to complement. The
ordinary first-gate and multi-restriction excess bounds run before the
fixed-layout solver. The stronger support-sensitive test stays optional.

The restriction debit uses the cycle-rank identity for excess. Deleting
fixed primary vertices of read counts $d_i$ leaves every remaining vertex
connected to the output through a directed reader path. Such a path never
passes through another primary. The deletion decreases cycle rank by
$\sum_i(d_i-1)$. Constant propagation, identity contraction, and dead-cone
removal cannot increase that rank. This justifies charging the repeated
primary reads before the private groups are placed.

For a reduced core, a portless binary region would have a private cherry,
which would give a raw pair module. Each normalized repeated internal region
has at least two leaf occurrences. The connectivity generator exhausts
ordered recipient multiplicities under those assumptions. An independent
recipient enumerator agreed on five degree classes at excess four and five.
All three projection checks passed on 161 concrete monotone and signed
layouts. Small reduced monotone minima also matched independent enumeration
of gate programs. Higher-excess layout exclusions are recorded as
provisional. These checks cover the connectivity combinatorics and the tested
filters within their scopes.

On the six supplied monotone excess-three targets, the combined run used 117
fixed-layout calls and took 4.34 seconds. The existing quotient solver took
6.74 seconds including one timeout at the three-second cap. Projection alone
used 203 calls and took 4.58 seconds. The unfiltered run made 6,561 calls on
its completed jobs. The combined run returned three verified witnesses and
three exhausted layout searches. [Matched replay](results/layout_projection_matched.jsonl)

Ten frozen higher-excess budgets used a four-second cap per method.
Projection found two witnesses and MapleChrono production SAT found four.
The methods found five distinct witnesses across their union. The two
newly closed intervals are:

| Target | Prior interval | Verified projected upper | Independent checked lower |
| --- | --- | --- | --- |
| `graph-01` | [8, 9] | **8** in 0.764 s | 7 gates excluded, 4 proofs and 50 RUP steps |
| `hypergraph-08` | [9, 13] | **9** in 1.418 s | 8 gates excluded, 4 proofs and 140 RUP steps |

Both checked bounds used the independent lazy terminal encoding and all
relevant reader shapes. The archived CNFs and traces were rechecked by both
RUP checkers. The prior production exclusions agree. MapleChrono found the
eight-gate `graph-01` witness in 2.083 s and timed out on `hypergraph-08`.
Changing to internal-first did not close any of three selected construction
timeouts. A separate support-sensitive replay on `graph-03`,
`comparator-09`, and `complete-5` reached the three-second cap with or
without the extra test. This suggests short conditional projection probes alongside SAT
instead of replacing it at higher excess. The harder higher-excess budgets
reached their caps, and this replay established no new higher-excess
exclusions. [Higher budgets](results/layout_projection_higher.jsonl) ·
[Proof index](results/layout_projection_checked_frontiers.jsonl) ·
[Search order replay](results/layout_projection_order.jsonl) ·
[Support-sensitive replay](results/layout_projection_support_probe.jsonl)

### Independent branch-and-bound work

Branch-and-bound JSONL files now bind evidence to the exact graph, budget,
seed, and colex scope. Legacy rows are retained and skipped when establishing
a fresh scoped segment. A file with a different scope is rejected. An actual
four-vertex path run resumed with its verified witness count and completed
without re-solving. Reusing that file for a four-cycle was rejected before
search. The worker also joins its stop timer before reusing the temporary
path. The change applies to all branch-and-bound runs.

Branch-and-bound now reuses analytical child probes after choosing to split a
node. The input to each reused bound is identical: target, budget, and full
prefix. The cache lives for the next frontier and has no effect on resumed
journals. At four gates for the four-vertex path, 162 duplicate bound calls
were skipped, 160 leaves were excluded analytically, and all four reported
witnesses passed independent truth-table evaluation. The regression checks
the same case with one worker.

```powershell
python sat-search/experiments/layout_projection_check.py -v
python sat-search/experiments/layout_projection_check.py --output fresh-higher.jsonl --seconds 4
python sat-search/experiments/layout_projection_check.py --output fresh-matched.jsonl --matched --seconds 3
python sat-search/verify/test_bnb.py -k resume_scope
python sat-search/verify/test_bnb.py -k probe
```

## Regional obligation caching and block completion

[ObligationCache](theory/regional_obligation_cache.py) and
[local_blocks](theory/regional_block_completion.py) are the default local
completion for the experimental ordered quotient and provider-first layout
searches. The reference remains selectable with `make_completion('reference')`
and the cache-only ablation with `make_completion('cached')`. Each search
creates one completion object and passes it to its subordinate recognizers.

For a fixed region, unconstrained slices can be omitted. The remaining port
columns determine all obligations. Equal columns are interchangeable, and in
the free-NOT basis complemented columns are interchangeable after flipping
literal phase. Each group still carries its full number of occurrences. The
cached tree is lifted using one original provider reference per occurrence,
with phase restored by XOR. This is valid on the observed slice patterns.
Separate LRUs for normalized and solved queries default to 4,096 entries each.
A bounded search over tied canonical orderings can miss equivalent cache keys
when it hits the cap. Both keys still encode exact problems.

A port assignment restricts a local formula to a read-once formula on its
surviving private variables. For any pair of surviving leaves its AND/OR
lowest common ancestor is unchanged by contraction. Thus an OR constraint
keeps its endpoints together across an AND split, and an AND constraint keeps
them together across an OR split. Connected components of the opposite
graph are the indivisible units of each candidate split. Every legal split
assigns each component to exactly one child. Ports with the same normalized
provider are indistinguishable up to their individual literal phases, which
remain free in the signed leaf checks. Enumerating the count given to each
child covers all occurrence assignments up to that symmetry. Recursive
completion still checks every slice of each candidate. Its per-query memo
tables are individually bounded and cleared at the end of the query.

The supplied prototype replay performed 2,000 oracle comparisons and
reconstructed the selected excess-four circuit in 0.436 s. The integrated
test checked 2,000 queries against independent formula-column enumeration,
including sparse provider IDs, row permutations, polarity flips, and exact
port occurrence counts. It had 1,348 cache hits. All three completion modes
agreed on nine matched jobs. This includes three exhausted excess-three
layout searches and six verified witnesses across the two drivers.

| Integrated metric | Reference | Cache only | Cache and blocks |
| --- | ---: | ---: | ---: |
| Six excess-three projection jobs | 4.184 s | 2.776 s | 1.220 s |
| Selected excess-four projection job | 2.490 s | 2.226 s | 0.471 s |
| All nine jobs, including two ordered quotient jobs | 7.648 s | 5.154 s | 1.698 s |
| Peak process working set | 56.6 MiB | 58.0 MiB | 38.5 MiB |
| Canonical cache hits / queries | — | 136 / 207 | 136 / 207 |
| Uncached completion recursion states | — | 196,827 | 78,092 |

The integrated eight-budget higher-excess replay used a strict four-second
worker cap per job. Both modes timed out on every case. Those runs established
zero new witnesses, exclusions, or minima. Block completion lowered measured
peak working set on every paired job. A one-second sampling profile on
`hypergraph-12`, `comparator-09`, and `random-monotone-10` located the main
cost in local completion. On `comparator-09`, both variants spent their first
second inside their first local query, with zero opportunities for a cache
hit. The sample is diagnostic and does not establish full-search coverage.

### Monotone row bounds and branch propagation

Three subsequent ablations target the local query accepting most of the work.
For a subtree, project each observed provider pattern to the providers present
in that subtree. At fixed primary values, subset order on those patterns
implies pointwise order on the output slices. Identical projected patterns
therefore require identical slices. A nonempty AND/OR tree is zero when all
its leaves are zero and one when all are one. These are additional endpoint
tests at the all-zero and all-one private assignments. The tests apply to
exact slices and ignore unspecified slices. Free-NOT mode bypasses them.

The endpoint test also eliminates inconsistent child-slice choices before
enumerating combinations across rows. An AND at an absorbing zero row can
require zero from either child. If a fixed row requires a nonzero slice from
one child at a smaller provider pattern, that child cannot be chosen to
supply the zero. The OR case uses the dual order and absorbing one. Choices
at two absorbing rows require the same constant, so those choices create
no pairwise incompatibility with each other. Bitsets identify the relevant
fixed obligations. Recursive completion still decides every surviving query.

Each ablation preserved the matched verdicts and reconstructed witnesses.
The final implementation also passed the 2,000-query independent test.
Timings below come from successive paired batches on the same nine jobs.

| Added check | Prior time | With check | Recursive states with check |
| --- | ---: | ---: | ---: |
| Subtree row order and endpoints | 1.748 s | 0.641 s | 45,274 |
| Prefilter child endpoints before branching | 0.657 s | 0.209 s | 7,083 |
| Propagate fixed-row dominance into absorbing branches | 0.205 s | 0.172 s | 2,228 |

The final dominance variant is the experimental default. On the selected
excess-four construction it took 0.041 s. Its profiled higher-excess round
used a four-second deadline. Interrupt delivery added at most 0.031 s.
Three budgets that had reached the prior layout cap yielded witnesses. The
independent reference evaluated all three witnesses. Their minima were
already established, so the replay changed zero certified intervals.

| Monotone target | Gates | Dominance variant | Earlier MapleChrono |
| --- | ---: | ---: | ---: |
| `hypergraph-12` | 8 | 0.068 s | 1.067 s |
| `hypergraph-21` | 8 | 0.255 s | 3.585 s |
| `hypergraph-03` | 9 | 0.422 s | 4 s timeout |

The SAT comparison uses the [earlier recorded run](results/layout_projection_higher.jsonl).
The remaining five dominance jobs timed out. Peak working sets for the eight
jobs were 35.5–40.1 MiB. On `comparator-09`, the first query still spent more
than four seconds checking 333,961 partitions. Absorbing-row propagation
rejected or simplified many candidates and left that query open. The next
test is whether many partitions have the same downstream slice constraints.
The comparator and random monotone timeouts offer probes for a proposed
quotient, with the original completion as a correctness reference.

[Row bound comparison](results/regional_completion_row_matched.jsonl) ·
[Endpoint comparison](results/regional_completion_endpoint_matched.jsonl) ·
[Dominance comparison](results/regional_completion_dominance_matched.jsonl) ·
[Row profiles](results/regional_completion_row_profile.jsonl) ·
[Endpoint profiles](results/regional_completion_endpoint_profile.jsonl) ·
[Dominance higher-excess records](results/regional_completion_dominance_higher.jsonl)

[Supplied prototype run](results/regional_block_prototype_bench.log) ·
[Integrated matched replay](results/regional_completion_matched.jsonl) ·
[Higher-excess jobs](results/regional_completion_higher.jsonl) ·
[Higher-excess profiles](results/regional_completion_profile.jsonl)

The supplied [fused quotient prototype](theory/archive/fused_quotient_search.py)
is archived outside the active solver. Its reported 148 oracle comparisons
are prior evidence. It expects the original companion prototype APIs. A
scaling replay would be useful if sampling shows global partial-layout
work dominating after local completion has been reduced.

```powershell
python sat-search/experiments/regional_completion_check.py -v
python sat-search/theory/regional_block_completion.py --bench --output fresh-regional-matched.jsonl
python sat-search/theory/regional_block_completion.py --bench --higher --seconds 4 --output fresh-regional-higher.jsonl
python sat-search/theory/regional_block_completion.py --bench --higher --profile --seconds 1 --output fresh-regional-profile.jsonl
python sat-search/theory/regional_block_completion.py --bench --row-bounds --output fresh-regional-row.jsonl
python sat-search/theory/regional_block_completion.py --bench --endpoint-branches --output fresh-regional-endpoint.jsonl
python sat-search/theory/regional_block_completion.py --bench --dominance-branches --output fresh-regional-dominance.jsonl
python sat-search/theory/regional_block_completion.py --bench --higher --mode dominance-branches --profile --seconds 4 --output fresh-regional-dominance-higher.jsonl
```

## Port-first partition propagation and witness-guided completion

Three opt-in completion modes share the integrated dominance implementation.
`port-first` changes partition generation. `witness-cover` changes absorbing-row
branching. `port-first-witness` enables both. The dominance solver remains the
default. The supplied `python regional_cover_completion.py --bench` replay used
the supplied companion files and the ordered quotient API from `30760d7`, which
the prototype expects. It reproduced 19,079 versus 354 partitions reaching the
prototype's cover routine, at 0.238 versus 0.094 s. The integrated ablations below
use the newer dominance solver as the reference. [Prototype replay](results/regional_cover_prototype.log)

### Soundness and local checks

At a fixed root operation, let a slice be nonabsorbing when its specified table
is neither arbitrary nor the root's absorbing constant. In a nonabsorbing AND
slice, both children can attain 1. Their private supports are disjoint, so each
child's essential variables remain essential in the product. The dual argument
uses children that can attain 0 at an OR root. The required support in a child
is therefore exactly its share of the target support. Equal projected provider
patterns require equal child functions and hence equal supports. Any variable
in the symmetric difference between two such slice supports must be assigned
to the other child. The implementation assigns whole opposite-operation
connected components and rejects an allocation if it forces a component to
both sides. For positive literals, a nonabsorbing child with all ports fixed
to the root's absorbing value must retain an essential primary. The same
necessity follows at that child's all-zero or all-one input endpoint.

On an absorbing row at least one child has to produce the absorbing constant
identically. This follows from independence of the private variables of the
two children. Given fixed child obligations, build a left witness for the
currently required rows and test the right child on every row the witness
leaves uncovered. If the right query is impossible, every valid alternative
must cover at least one more row from that failed query on the left. Branch
on these rows and memoize visited required subsets with a bounded set. Each
step adds a row. The recursion is exact even with an arbitrary choice of
left witness and uses the entire failed right demand as its branching set.
For free NOTs, the private leaves are read once, so their independently
attainable extrema combine exactly through each gate. Provider polarities
are evaluated on the actual observed patterns. The monotone-only endpoint
and dominance checks still apply only in the monotone basis.

All three variants matched independent formula-column enumeration on 2,000
queries each, including renamings, signed phases, repeated occurrences, and
unspecified rows. Returned local formulas were evaluated on every specified
slice and checked for exact occurrence counts. The stress runner uses a
Windows-compatible worker timer with a hard parent-process fallback.

### Matched measurements

Eight isolated queries were captured from the first, slowest completed, or
in-flight dominance call on the five stalled corpus jobs. Caps were 1.5 s
per isolated query and 0.35 s per generated query. Times include time spent
on timed-out jobs. Candidate counts on these capped jobs include only work
observed before interruption.

| Integrated mode | Isolated query outcomes | Isolated time | Candidate partitions | Partitions entering child obligations | Recursive states | Peak working set |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Dominance | 6 UNSAT, 2 timeouts | 8.915 s | 848,426 | 52,089 | 35,924 | 38.2 MiB |
| Port-first | 7 UNSAT, 1 timeout | 3.718 s | 8,554 | 4,943 | 22,095 | 38.1 MiB |
| Witness-guided | 8 UNSAT | 0.564 s | 43,541 | 6,429 | 3,287 | 36.0 MiB |
| Combined | 8 UNSAT | 0.140 s | 1,312 | 789 | 994 | 36.1 MiB |

The first `comparator-09` query had two private primaries and ten port reads.
Port-first propagation alone timed out after sending a single partition to
child completion. The combined variant decided that query in 0.017 s. On 20
generated signed queries with four to six private primaries, the integrated
dominance baseline completed 13 in 2.794 s including cap costs. The combined
variant completed all 20 in 0.069 s, with recursive states dropping from
254,157 to 1,599 and peak working set from 38.6 to 36.0 MiB. On the 20
generated monotone queries both completed all 20, at 0.045 and 0.047 s.

| Target | Core gate budget | Dominance | Combined |
| --- | ---: | --- | --- |
| `comparator-09` | 11 | Timeout | Timeout |
| `random-monotone-10` | 10 | Timeout | Layout exhausted in 3.720 s |
| `comparator-02` | 9 | Timeout | Verified witness in 0.138 s |
| `graph-03` | 10 | Timeout | Layout exhausted in 1.507 s |
| `comparator-04` | 9 | Timeout | Timeout |

This four-second end-to-end sample had five dominance timeouts. The combined
mode reached three layout decisions and timed out twice. Peak working set
increased from 39.6 to 49.6 MiB while the faster mode reached more layouts
and cached more queries. The signed and isolated workloads do not establish a
production default. [Captured queries](results/regional_cover_captured.jsonl) ·
[Isolated replay](results/regional_cover_isolated.jsonl) ·
[Generated stress](results/regional_cover_signed_stress.jsonl) ·
[Whole-layout ablation](results/regional_cover_layout.jsonl)

### Input symmetry after the local improvement

The combined local mode took `comparator-09` from one tested layout to 5,866
under the deadline. The next ablation used input transpositions that preserve
the complete target. Pairwise interchangeability gives a symmetric group on
each class: transpositions generate permutations, and conjugation makes the
interchangeability relation transitive. A representative can first choose a
prefix of each class for the repeated set, then order those repeated providers
by their recipient multiplicity vectors, then choose a prefix of each remaining
class for each private group. The later steps fix the previously chosen inputs.
Renaming a witness using these transpositions preserves its gate count and
target. The normal layout checks still run. Independent small-circuit minima
and a subset-enumeration oracle agreed with the representative generator.

Filtering after generating individual private subsets was too slow on
`comparator-09`. Generating class prefixes directly exhausted its 11-gate
layouts in 2.875 s and reduced the `graph-03` exclusion from 1.507 to 0.583 s
with 645 rather than 2,538 fixed-layout calls. `comparator-04` still reached
the cap inside its second local query. Both analysis variants remain opt-in.
[Filter-first run](results/regional_cover_symmetry.jsonl) ·
[Representative generation run](results/regional_cover_symmetry_direct.jsonl)

### Independently certified frontiers

The optional layout engine tests its allocated excess on reduced cores. The
separate lazy certificate backend was run on each original frozen function
with an at-most gate budget. It covered all applicable reader shapes by its
existing analytical prescreens and DRUP-checked SAT instances. This provides
the exclusion evidence independently of higher-excess layout coverage and of
the new local and symmetry rules. The witness evaluator checked every row
of each original truth table and the gate references and budgets.

| Original monotone target | Prior interval | New result | Evidence |
| --- | --- | --- | --- |
| `graph-03` | [10, 15] | **11 gates** | 10 excluded with 11 proof packets and 491 RUP steps. An 11-gate witness was found in 0.071 s. |
| `random-monotone-10` | [10, 17] | **12 gates** | The layout replay excluded the 10-gate reduced core. The original eight-input target has a one-gate contraction and was independently excluded at 11 gates with five packets and 2,060 RUP steps. A 12-gate witness was found in 0.079 s. |
| `comparator-09` | [11, 14] | **[13, 14]** | Separate runs excluded 11 and 12 gates. The 12-gate run used seven packets and 11,155 RUP steps. The 13-gate lazy and MapleChrono queries reached their caps. The archived 14-gate witness was reevaluated independently. |

The checks use the frozen target-manifest hashes in the job records and the
saved CNF and DRUP hashes. The proof counts cover the SAT subproblems that
survived the established prescreens. The [proof files](results/regional_cover_proofs)
are indexed by the [first exclusions](results/regional_cover_independent_checks.jsonl),
[original random-function exclusion](results/regional_cover_original_random11.jsonl),
[comparator 11-gate exclusion](results/regional_cover_comparator09_11.jsonl),
and [comparator 12-gate exclusion](results/regional_cover_comparator09_12.jsonl).
The [upper-bound runs](results/regional_cover_upper_checks.jsonl) save the
two new minimum circuits. The next MapleChrono budgets also reached four
seconds on both functions. [MapleChrono runs](results/regional_cover_next_witness.jsonl) ·
[Comparator lazy 13-gate run](results/regional_cover_comparator09_13.jsonl) ·
[Comparator MapleChrono 13-gate run](results/regional_cover_comparator09_sat13.jsonl) ·
[Comparator 14-gate witness](results/port_certificate_constructions.jsonl)

```powershell
python sat-search/experiments/regional_completion_check.py -v
python sat-search/experiments/layout_projection_check.py -v
python sat-search/experiments/regional_cover_stress.py capture --seconds 1.5 --output fresh-cover-capture.jsonl
python sat-search/experiments/regional_cover_stress.py isolated --seconds 1.5 --source fresh-cover-capture.jsonl --output fresh-cover-isolated.jsonl
python sat-search/experiments/regional_cover_stress.py stress --large --seconds .35 --output fresh-cover-stress.jsonl
python sat-search/experiments/regional_cover_stress.py layout --seconds 4 --output fresh-cover-layout.jsonl
python sat-search/experiments/regional_cover_stress.py layout --seconds 4 --modes port-first-witness --input-symmetry --case comparator-09 --case graph-03 --case comparator-04 --output fresh-cover-symmetry.jsonl
python sat-search/experiments/port_certificates_check.py --benchmark fresh-cover-proof.jsonl --seconds 8 --conflicts 2500 --proof --proof-dir fresh-cover-proofs --levels baseline --job graph-03 10 --job random-monotone-10 11 --job comparator-09 12
python sat-search/experiments/port_certificates_check.py --benchmark fresh-cover-upper.jsonl --seconds 6 --conflicts 2500 --levels baseline --job graph-03 11 --job random-monotone-10 12 --job comparator-09 13
Get-ChildItem sat-search/results/regional_cover_proofs -Filter '*.cnf.gz' | ForEach-Object {
    $trace = $_.FullName -replace '\.cnf\.gz$', '.drup.gz'
    python sat-search/experiments/certify_synthesis.py --verify $_.FullName $trace
}
```
