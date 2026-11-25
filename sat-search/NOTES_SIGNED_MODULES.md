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
| a:1-3-13 | 48 analytical nodes (no SAT call) |
| 14 other case-a survivors | 32-194 analytical nodes each; 1-10 nodes per survivor (42 total) open after 300 s SAT calls (`logs/l1343_bnb_2.log`) |

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

## Phase-first signed regional completion (`theory/regional_phase_first.py`, optional)

Free-NOT only. Enumerates the feasible literal-polarity availability classes (positive / negative / both, from
positive-negative row distinction clauses, unit propagation over finite domains), recodes each surviving class and
mixed-phase multiplicity as a monotone query, and calls an exact monotone completion. In the repo the monotone
solver is the production `regional_block_completion.local_blocks(port_first, witness_cover, row_quotient)`
through `theory/regional_production_adapter.py`; the original prototype dependencies are not in the repo.

- Oracle checks pass with the production solver underneath (600 phase-first, 600 axis-lift queries against
  independent formula-column enumeration).
- Supplied benches reproduced on Windows with the prototype solver (`experiments/win_deadline_run.py` maps
  SIGALRM/setitimer to a timer + `interrupt_main`): 30 signed stress queries 26 vs 22 decided, recursive states
  570 vs 8,904; extra 36-query workload complementary (phase 27 vs base 26 decided, 3 gained / 2 lost);
  lift-phase 27/30 vs lift alone 22/30 (`logs/phase_first_bench.log`, `phase_extra_bench.log`, `axis_lift_bench.log`).

**Production replay** (`experiments/phase_first_production.py`, `results/phase_first_replay.jsonl`, 0.5 s per query,
witnesses checked, all decisions agree). Captured queries are the distinct signed regional calls made by free-NOT
`solve3` (excess 3) and `layout_projection.search_exact` (excess 4) on 16 corpus cores, 60 s per search
(`results/phase_first_captured.jsonl`, at most 60 per search, port-heavy first).

| Workload | n | production base | phase | lift-phase | portfolio (25% phase) | adaptive |
| --- | --- | --- | --- | --- | --- | --- |
| captured from layout searches | 896 | 873 / 22.3 s | **896 / 8.5 s** | 896 / 7.7 s | 886 / 11.0 s | 896 / 8.3 s |
| phase-extra (heavy repetition) | 36 | 16 / 11.2 s | 33 / 4.4 s | **34 / 3.3 s** | 26 / 6.0 s | 33 / 4.2 s |
| generated stress, small (no repeats) | 20 | 18 / 2.5 s | 20 / 0.1 s | 20 / 0.1 s | 20 / 0.1 s | 18 / 2.4 s |
| generated stress, large (no repeats) | 20 | 20 / 0.05 s | 20 / 0.84 s | 20 / 0.78 s | 20 / 0.87 s | 20 / 0.04 s |

- Phase-first gained 42 queries over production and lost none. On the 927 queries both decided: 5.9 s vs 12.4 s.
- Only cost: wide queries without repeated providers (large stress, m 4-6), where it is ~17x slower but still decides.
- Adaptive rule tested: `repeats >= 1 and labels <= 512` -> 967/972, 15.4 s. A rule chosen after the fact on this
  same data, `not (repeats == 0 and m >= 4)`, gives 969/972, 13.0 s (always-phase 969/972, 13.8 s; never 927/972,
  36.1 s). In-sample only; needs a held-out workload before any default change.
- The sequential portfolio is dominated: splitting the cap loses decisions that phase-first reaches alone.
- Labelled table sizes stayed <= 1,024 here, so the quadratic distinction-clause build was never exercised; keep a
  label cap in any integration.
- Status: **opt-in completion mode `phase-first`** (`make_completion('phase-first')`, `regional_phase_first.
  adaptive_completion`): signed queries passing `phase_rule` (not (no repeated provider and m >= 4), labelled table
  <= 4,096) go to phase-first over the production monotone solver; everything else goes to production `local_blocks`.
  Added to the 2,000-query multislice oracle test in `experiments/regional_completion_check.py` (passes).
- **Held-out validation of the frozen rule** (`results/phase_first_captured_heldout.jsonl`, 547 signed queries from 26
  cores not used to choose the rule at excess 3-4, plus the original cores at excess 5; `results/phase_first_replay_heldout.jsonl`):
  production 528/547 in 14.3 s, `phase-first` rule 546/547 in 11.9 s (always-phase 546 / 12.5 s, portfolio 531 /
  16.0 s); 18 gained, 0 lost.
- **End to end** (`experiments/phase_first_layout.py`, every solve in a fresh process, baseline 120 s, phase-first
  early-stopped at max(10 s, 1.5x baseline); decisions agree on every pair, witnesses rebuilt and checked):

  | Free-NOT layout search, 48 corpus cores | production `row-quotient` | `phase-first` |
  | --- | --- | --- |
  | solve3 (excess <= 3) | 48 decided, 12.0 s | 48 decided, 13.1 s |
  | search_exact excess 4 | 41 decided (7 timeouts at 120 s), 70.3 s on the 41 | **48 decided**, 21.9 s on the 41 |

  At excess 4 the seven newly finished searches are comparator-02, -04, -08, complete-5, exactly-2-of-4, parity-4
  (all < 3 s) and random-monotone-10 (27 s). Witness searches also speed up (complete-4 4.65 s -> 0.19 s,
  hypergraph-21 4.41 s -> 0.17 s). Empty excess-4 results are provisional under `search_exact`'s contract, so no
  bound is claimed from them. At excess 3 the searches are dominated by cheap cached queries and phase-first adds ~9%.
- Recommendation: use `phase-first` for free-NOT searches at excess >= 4; keep `row-quotient` as the default until
  the regional owners decide.

Singleton-port promotion (`theory/regional_axis_lift.py`) is kept as an optional cheap reduction: it alone changed
no decision, and with phase-first it added one (phase-extra 34 vs 33).

### Bounded-multiplicity regional completion (opt-in, `theory/regional_bounded_multiplicity.py`)

Optional-leaf solver: each leaf may be used up to its allocated multiplicity (at least one leaf overall), with phase
feasibility as an early rejection, projected-row compatibility, forced absorbing-row ownership, witness-guided
branching and canonical row quotienting. Soundness contract of the exact wrapper (`exact` / `completion`):
optional UNSAT proves exact-occurrence UNSAT (exact formulas are optional formulas); a witness padded to the exact
allocation by `regional_padding.graft` proves SAT; a failed graft is never read as UNSAT and falls back to the exact
adaptive phase-first solver.

- Capacity-reduction theorem (mixed labels: a provider's optional capacity can be capped by the number of
  positive-negative row pairs it distinguishes; a reduced signed solution pads to the original allocation):
  `bounded_multiplicity_bench.capacity_checks` passes, 323 cases checked, 128 with a reduced capacity, 41 exact
  equivalences. Not yet used for pruning.
- Prototype benches reproduced on Windows (`experiments/win_deadline_run.py`): original 66 signed queries 64 vs 50
  decided for phase-first (`logs/bounded_mult_bench.log`); fresh 80 queries 75 vs 63, 62 matched 0.40 s vs 2.04 s
  (`logs/bounded_mult_fresh.log`). Note that these are mostly satisfiable queries.
- Repo adaptation: production `columns`/`combine`/`graft`/`evaluate`, production `check_tree`; bounded memo
  (`MEMO = 2**15` per query); `lazy_splits` generates the bipartitions lazily (same unordered pairs as the prototype's
  sorted list on 3,000 capacity vectors; orientation may differ). Exact fallback = `regional_phase_first.adaptive_completion`.
  Oracles pass in the repo version: `checks(600)`, `extra_checks(800)`, `capacity_checks(500)`. Mode
  `make_completion('bounded-multiplicity')`, added to the multislice oracle test in `regional_completion_check.py`.

Production comparison against the integrated `phase-first` mode (decisions agree everywhere; witnesses checked):

| Workload | phase-first | bounded-multiplicity |
| --- | --- | --- |
| held-out captured queries (547, 0.5 s) | 546 decided, 13.5 s | 527 decided, 36.9 s (lost 20, gained 1) |
| dev captured queries (896, 0.5 s) | 896 decided, 8.4 s | 879 decided, 26.5 s (lost 17) |
| free-NOT `search_exact` excess 4, 48 cores, 120 s | 48 finished; 23.8 s on the 45 shared | 45 finished (3 stopped-worse); 33.0 s |
| free-NOT `search_exact` excess 5, 48 cores, 120 s | 36 finished; 96.8 s on the 32 shared | 32 finished (3 stopped-worse, 1 timeout); 105.6 s |

(`results/bounded_multiplicity_replay.jsonl`, `results/phase_first_layout_e4_bounded-multiplicity.jsonl`,
`results/phase_first_layout_e5_bounded-multiplicity.jsonl`.)

Why it loses: captured layout queries are exclusion-dominated. On the 1,289 optional-UNSAT queries bounded takes
42.7 s against 10.3 s for phase-first; on the 51 padded-witness (SAT) queries it takes 1.3 s against 3.9 s. All 37
lost queries have 16-row tables with 3-5 repeated providers. No row-count activation threshold beats phase-first on
either the held-out or the dev set. In whole searches it is faster on some witness searches at excess 5
(graph-03 1.58 s -> 0.17 s, comparator-02 3.7 s -> 1.5 s) but loses exclusions (hypergraph-04 finishes only with
phase-first, 100 s).

Verdict: keep opt-in; not an adaptive default. It is a construction-side tool: worth trying for upper-bound
(witness) searches. Twelve excess-5 free-NOT searches time out at 120 s in both modes (comparator-04, -08,
complete-5, -6, hypergraph-05, -09, -10, -15, -20, petersen-10, random-monotone-05, threshold-5-3); those are the
remaining higher-excess targets. Empty excess-4/5 results are provisional under `search_exact`'s contract.

### Optional-occurrence lemma (repeated providers)

Proved: for a regional formula over leaf occurrences, if the query is completable with each repeated provider p used
d_p times (1 <= d_p <= c_p) and every singleton leaf used once, it is completable with c_p occurrences. Proof: take a
leaf l of p with parent P = l op S (one exists, since the formula has >= 2 leaves) and replace P by P op l; idempotence
gives the same function on every row and one more occurrence of p. Repeat. The argument uses no NOT, so it holds in the
monotone basis too (the free-NOT complementary-pair restoration is not needed). Checked against the exact reference
`two_sharing_core.local` on 1,365 free-NOT and 1,350 monotone random layouts: 0 counterexamples
(`experiments/optional_occurrence_check.py`).
Consequences: feasibility is monotone in occurrence counts. For construction, try minimal counts (d_p = 1) first and
pad. For exclusion, a child sub-query that is infeasible at the largest count it could receive excludes every smaller
allocation, so allocation branches can be pruned as a group (not yet implemented in `local_blocks`).

## Certificate-propagation prescreen for phase-first (`theory/regional_certificate_propagation.py`, opt-in)

After phase-first fixes literal polarities, each monotone query is screened by a necessary test: mandatory positive /
negative certificate memberships are propagated with the exact-one-intersection property, necessary AND/OR
lowest-common-ancestor relations are learned, and incompatible cotrees are rejected. Separate leaf occurrences
(duplicate provider columns) are kept; redundant monotone labels are reduced first. A rejection is sound UNSAT for that
phase class; passing is "unknown" and goes to the production solver.
- Mode: `make_completion('phase-certificate')` = `certificate_completion` (same routing as `phase-first`, prescreen
  skipped above 1,024 labelled entries). Added to the multislice oracle test (passes). Default unchanged.
- Checks: 1,200 random + 336 structured fixed-phase cases, 0 unsound rejections, 70 structured rejections beyond the
  basic distinction test. Supplied benches reproduced on Windows (`logs/cert_prop_bench.log`): original 66 queries
  55 -> 59 decided; fresh 80: 68 -> 71; exclusion-oriented 60: 45 -> 59 decided, local calls 132 -> 29, 5.85 s -> 1.34 s.

Production replay (`experiments/certificate_replay.py`, `results/certificate_replay.jsonl`, 0.5 s per query, witnesses
checked, decisions agree):

| Workload | phase-first | phase-certificate |
| --- | --- | --- |
| held-out SAT (33) | 32 decided, 2.66 s, 293 local calls | **33**, 0.67 s, 63 |
| held-out UNSAT (514) | 514, 9.26 s, 2,260 local calls | 514, **4.02 s**, **89** |
| dev SAT (18) | 18, 0.89 s, 184 | 18, 0.27 s, 31 |
| dev UNSAT (878) | 878, 6.76 s, 4,276 | 878, 2.72 s, 71 |

No losses; 2.3-2.5x less time and 17-60x fewer production local calls.

**Excess-5 timeouts unchanged.** The 12 free-NOT excess-5 searches that phase-first does not finish in 120 s
(comparator-04, -08, complete-5, -6, hypergraph-05, -09, -10, -15, -20, petersen-10, random-monotone-05,
threshold-5-3) still time out with `phase-certificate` (`results/phase_first_layout_e5_phase-certificate_subset.jsonl`).
Profile of 30 s of complete-5: 66,746 completion queries, 98.4% cache hits; 1,021 of 1,047 misses rejected by the
certificate; `local_blocks` 5 s of 25 s, while `ObligationCache._normalize`/`_pack` (canonical keys) take ~20 s.
The remaining bottleneck at excess 5 is cache canonicalization and layout count, not local completion; passing learned
AND/OR relations into the partition generator would not address it. Next: a cheaper cache key (e.g. hash before
canonicalizing, or memoize by raw query first) or fewer layouts.

**Cheaper cache keys (`phase-certificate-fastkey`, opt-in).** `ObligationCache(symmetry_limit=1, maxsize=2^17)`: the exact
compact key without the symmetric tie-break search (the cache documents that a capped key can only miss isomorphic hits,
never change a verdict) and a larger cache. Completion tests pass.
- 30 s throughput probe (`experiments/cache_key_probe.py`, `results/cache_key_probe.jsonl`): completion queries
  answered in 30 s rise 51% (comparator-04), 78% (complete-5), 27% (hypergraph-09); cache size alone barely matters
  over 30 s. Layout counts are enumerated up front, so they are not a progress measure.
- Matched excess-5 run on an idle machine (`experiments/fastkey_e5.py`, `results/fastkey_e5.jsonl`; each mode runs all
  12 searches at once, 300 s cap): both modes finish the same two searches, threshold-5-3 (plain 207 s, fast key
  98 s) and hypergraph-20 (112 s vs 102 s), both with no excess-5 layout (provisional). The other 10 time out in both.
  An earlier unmatched run that seemed to show two new completions overlapped another benchmark and compared a 300 s cap
  with 120 s; the completions came from the longer cap.
- Over 300 s the plain mode's 4,096-entry cache thrashes: it makes 2-20x more solver calls (complete-5 555k vs 93k).
- petersen-10 makes no completion calls at all: its time is layout enumeration.
- Conclusion: keys and cache size give up to ~2x; they do not close the excess-5 gap. The external baselines
  (bb018a6) point the same way: the remaining weakness is the decision stage at excess >= 4, where a stronger SAT stage
  is needed, not faster layout bookkeeping.

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

## Packed regional tables and ordered-block propagation

[PackedTables](theory/packed_regional_tables.py) now supplies support,
quantification, and exposed-cofactor checks to the existing regional block
solver. Tables retain their original coordinates. Swapping the two bit
halves of an axis and joining with OR or AND performs a single existential
or universal elimination. Support compares the same halves by XOR. The
scope is the exact private-variable slice representation used by monotone
and free-NOT regional completion. The existing per-query memo tables remain
bounded and the exact reconstruction checks still run.

To find the common nonconstant cofactor on a set of private variables, first
quantify those variables both ways. The difference marks precisely the
outside assignments whose cofactor is nonconstant. Existentially eliminating
the marked outside assignments gives a candidate cofactor. Comparing its
lifted table against the original on all marked rows detects every disagreement.
This handles zero, one, and multiple active outside slices without extracting
their individual tables.

The opt-in `ordered-block` mode extends port-first propagation. For a
nonabsorbing exact slice, quantifying the other child's private variables
recovers the owning child's table. For AND, existential quantification works
because the other child can attain 1. For OR, universal quantification works
because the other child can attain 0. Quantifying the rest of the owning
child then gives the required function for a connected block. Quantification
preserves pointwise order. If a required block table decreases between two
provider patterns in the monotone basis, its child must read a provider
that changes from one to zero. In the free-NOT basis, unequal tables require
at least one differing provider. Each such pair supplies a necessary mask
that must intersect the owning child's providers. These masks rule out a
block placement but leave the exact split and completion checks in place.

The supplied primitive script checked 3,520 function/subset pairs and measured
7.8× at four inputs and 202× at ten against its assignment reference. The
supplied regional `--bench` replay used the earlier prototype companion
API. Across its three eight-job batches, the baseline median was 0.0782 s,
the packed-only median was 0.0791 s, and ordered plus packed took 0.0832 s.
The ordered check reduced its partition count from 354 to 342. These very
short runs did not show a full-layout speedup. The integrated packed kernel
passed 3,522 primitive checks, including the zero-primary cases, and the
optional solver matched independent formula-column enumeration on 2,000
queries. [Primitive replay](results/regional_order_prototype_packed.log) ·
[Regional prototype replay](results/regional_order_prototype_completion.log)

### Integrated profiling and higher-excess ablation

The comparison kept the same integrated port-first and witness-guided search,
input-symmetry setting, and bounded caches. The old table implementation was
injected only as a benchmark reference. The new captures are the original
13-gate `comparator-09` endpoint and the nine-gate `comparator-04` reduced
core. They include a 13-occurrence, 64-row query and a 10-occurrence, 32-row
port-only query. The older captured queries contain up to four private
variables. The 24 generated queries exercise six, eight, and ten private
variables, both bases, sparse IDs, and repeated occurrences.

| Matched workload | Legacy tables | Packed tables | Packed with ordered-block |
| --- | ---: | ---: | ---: |
| 23 completed wide queries | 0.476 s | 0.206 s | 0.226 s |
| Eight ten-input queries within that set | 0.314 s | 0.088 s | 0.090 s |
| 12 completed captured queries, profiled | 1.454 s | 1.454 s | 1.647 s |
| Five higher-excess layout jobs including cap costs | 12.577 s | 12.392 s | 12.811 s |

Each method timed out on the same generated eight-input signed query and
the same captured port-only query. On the 23 completed wide queries, a
separate cProfile run attributed 0.608 s to exposed-cofactor calls and their
callees before packing, and 0.006 s after packing. The completed searches
visited the same 1,916 recursive states. On the narrow captured queries,
cofactor work was already about 0.0024 s in the profiled legacy run.
Partition generation and absorbing-row branching accounted for most of the
profiled work. Peak working set over the wide workers was 39.1 MiB with
legacy tables and 39.0 MiB with packed tables. Peak over the five layout
workers was 50.9 and 50.8 MiB, respectively.

Ordered-block filtering preserved all completed verdicts. It reduced
`comparator-02` partition checks from 1,793 to 1,732 but increased the
measured time from 0.134 to 0.139 s. On `random-monotone-10`, packed
completion exhausted the allocated layouts in 3.643 s and the ordered
variant timed out at four seconds. The rule stays optional. Packed tables
remain active in the regional block solver. Neither change altered a
certified interval. [New captures](results/regional_order_captured.jsonl) ·
[Captured profiles](results/regional_order_isolated.jsonl) ·
[Wide results](results/regional_order_wide.jsonl) ·
[Wide profiles](results/regional_order_wide_profile.jsonl) ·
[Layout replay](results/regional_order_layout.jsonl)

There is also a limitation specific to the integrated free-NOT checker.
Nonconstant child obligations are quantifier projections of learned
read-once slices. Quantifying a unate read-once tree fixes the eliminated
literals to their extrema, preserving polarity and the LCA operations of
surviving leaves. Two block projections on the same support therefore have
the same cotree under the already learned compatible LCA constraints.
Constant projections on nonabsorbing slices can only be neutral. Thus
signed equality on a block supplies the same placement restriction as
support equality in this solver. The monotone directional masks can still
add restrictions when projected patterns are comparable and distinct.

### Quotienting recursive row obligations

The profiles motivated an independent optional `row-quotient` mode. A
subtree's function sees only the providers whose occurrences it owns.
Equal projected patterns with conflicting exact tables are impossible.
Equal patterns with equal tables share one obligation, retaining an
original row index for slice-specific checks. In the monotone basis at
fixed primary assignments, a zero at a larger provider pattern implies
zero at a smaller pattern. A one at a smaller pattern implies one at a
larger pattern. Keep the maximal constant-zero and minimal constant-one
patterns. These are equivalent constraints for the candidate monotone
subtree. Free-NOT uses equality alone. Canonicalization runs before the
recursive memo lookup with bounded caches and keeps the same pool of
allocated leaves. The variant also matched the 2,000 independent queries.

| Focused replay | Packed | Packed with row quotient |
| --- | ---: | ---: |
| `comparator-04` port-only local query | 2 s timeout | UNSAT in 0.383 s |
| `comparator-04` nine-gate reduced core | 4 s timeout | Layout exhausted in 2.056 s |
| `comparator-02` nine-gate witness | 0.134 s | 0.075 s |
| `comparator-09` open 13-gate budget | 4 s timeout | 4 s timeout |

The port-only local query used 1,504 recursive states after quotienting,
versus 11,565 observed before the packed baseline reached its two-second
cap. The `comparator-04` exclusion is an additional completed layout job.
Its reduced core costs two fewer gates than the original, whose exact
12-gate monotone minimum was already certified. Whole-layout peak working
set rose to 53.6 MiB in the row-quotient replay, which completed more work.
The same generated signed outlier still reached its cap. The optional
row quotient gives the largest gain when a region has many provider rows
and few private variables. The 13-gate `comparator-09` budget remains open.
[Focused local replay](results/regional_order_row_quotient.jsonl) ·
[Layout replay](results/regional_order_row_layout.jsonl) ·
[Wide replay](results/regional_order_row_wide.jsonl)

```powershell
python sat-search/experiments/regional_order_check.py -v
python sat-search/experiments/regional_completion_check.py -v
python sat-search/experiments/layout_projection_check.py -v
python sat-search/experiments/regional_order_check.py --bench --dataset capture --seconds 2 --output fresh-order-capture.jsonl
python sat-search/experiments/regional_order_check.py --bench --dataset captured --source sat-search/results/regional_cover_captured.jsonl --source fresh-order-capture.jsonl --seconds 1 --profile --output fresh-order-isolated.jsonl
python sat-search/experiments/regional_order_check.py --bench --dataset wide --seconds 1 --output fresh-order-wide.jsonl
python sat-search/experiments/regional_order_check.py --bench --dataset wide --methods legacy packed --seconds 1 --profile --output fresh-order-wide-profile.jsonl
python sat-search/experiments/regional_order_check.py --bench --dataset layout --seconds 4 --output fresh-order-layout.jsonl
python sat-search/experiments/regional_order_check.py --bench --dataset captured --source fresh-order-capture.jsonl --methods packed quotient --seconds 2 --output fresh-row-local.jsonl
python sat-search/experiments/regional_order_check.py --bench --dataset layout --methods quotient --seconds 4 --output fresh-row-layout.jsonl
python sat-search/experiments/regional_order_check.py --bench --dataset wide --methods quotient --seconds 1 --output fresh-row-wide.jsonl
```

## Regional CDCL and root-split portfolios

The optional [regional certificate backend](experiments/regional_certificate_cnf.py)
uses the production `maplechrono` CDCL solver through PySAT. It reuses the
[cograph clause and cotree implementation](experiments/cograph_formulas.py).
Each allocated leaf occurrence has its own vertex. In free-NOT mode each
has an independent phase literal, even when two occurrences read one port.
All allocated occurrences survive reconstruction. The scope is exact regional
queries in the monotone and free-NOT bases, with unspecified slices allowed.

### Exact certificate constraints and separation

For a fixed phase assignment and labeled input row, a selected positive
certificate is an all-correct clique. Every incorrectly valued vertex must
have a selected nonneighbor, so it cannot extend the clique. Extending to a
maximal clique therefore adds only correctly valued vertices. The negative
case uses independent sets and selected neighbors. In a cograph, maximal
cliques and independent sets are the respective read-once certificates.
Conversely, a true structural certificate supplies all blockers and picks.
This establishes the incorrectly-valued-only maximality relaxation. It also
handles rows with all leaf values correct, where the empty selected set can
be extended.

`certificate-cnf` encodes all induced-path exclusions and rows initially.
`certificate-lazy` adds the induced P4s of each candidate graph and reuses
the CDCL instance. `certificate-rows` also defers rows and adds counterexamples
to the decoded cotree. Every added clause is necessary and each iteration
eliminates its invalid candidate. A reported witness matches every represented
label, including rows that were never added. `certificate-anchored` also
uses monotone boundary rows and learns phase and LCA units from exact slices
with at most one singly read provider left free. Fixing all other providers
removes leaves from the tree and preserves the surviving LCA operations.
The `certificate-fallback` experiment first gives the packed row-quotient
engine 256 search events on structurally eligible queries before using lazy
CDCL. The cutoff has no truth value. All these modes are optional.

Each of the five direct CDCL variants, including the absorption variant below,
matched independent formula enumeration on 360 local queries. All 64
four-vertex graphs agreed between lazy separation and eager P4 clauses. A
targeted regression requires opposite phases on the two occurrences of one
provider. Native solver cancellation uses the same `interrupt` and
`solve_limited(expect_interrupt=True)` interface as production search. The
initial timing pilot used Python-only interruption and overshot during native
search. The measured results below use cooperative native interruption plus
the hard worker-process fallback.

### Matched port-heavy and whole-layout runs

The one-second local replay uses 12 deduplicated frozen captures plus
`wide-8-1-1`, the unresolved known-satisfiable signed stress query. The
capture set includes 32–64 provider rows and up to 13 port occurrences.
Times are summed across jobs, including capped time. Encoding includes
initial and incremental Python clause construction. Native loading and
separation time are available separately in the records.

| Local mode | Decided / 13 | Total time | Encoding | CDCL search | Peak working set |
| --- | ---: | ---: | ---: | ---: | ---: |
| Packed row quotient | 12 | 1.994 s | — | — | 44.5 MiB |
| Eager certificate CNF | 0 | 13.144 s | 0.519 s | 12.221 s | 274.3 MiB |
| Lazy P4 only | 0 | 13.166 s | 0.423 s | 12.276 s | 272.7 MiB |
| Lazy P4 and rows | 0 | 13.121 s | 0.072 s | 12.680 s | 58.9 MiB |
| Anchored lazy P4 and rows | 1 | 12.368 s | 0.044 s | 12.049 s | 49.0 MiB |
| Bounded packed-to-CDCL fallback | 5 | 8.132 s | 0.054 s | 7.688 s | 54.5 MiB |

The single anchored exclusion was already decided by the packed baseline.
In the signed outlier, eager search encoded all 2,048 labeled assignments.
Lazy rows encoded 162 by the deadline and saved memory. Its solver time
still reached the cap. Encoding accounts for a small fraction of the
port-heavy failure cost. Increasing the CDCL share of the portfolio did
not help these queries. [Matched local records](results/regional_cnf_queries_matched.jsonl)

| Four-second whole-layout mode | Decided / 5 | Total time | Peak working set |
| --- | ---: | ---: | ---: |
| Packed row quotient | 3 | 10.903 s | 54.0 MiB |
| Eager certificate CNF | 0 | 20.045 s | 56.6 MiB |
| Bounded packed-to-CDCL fallback | 1 | 17.167 s | 52.0 MiB |
| Bounded packed-to-root portfolio | 4 | 10.410 s | 54.5 MiB |

The extra completion for the root portfolio was the previously established
`random-monotone-10` core layout exclusion, near the runtime cap. All four
modes reached the cap on the open 13-gate `comparator-09` budget. No original
function interval changed. [Whole-layout records](results/regional_cnf_layouts.jsonl)

### Root relaxation and supplied prototype replay

At an AND root both children must accept every positive row. For each
negative row at least one child must have a projected distinction from
every positive row. The OR case is dual. Monotone distinctions are directional.
Free-NOT distinctions use differing raw values. Connected private blocks are
indivisible, and a repeated provider is available to a child if it receives
at least one occurrence. The root CSP propagates these necessary hitting
conditions through the possible left, right, and both domains. A candidate
split still goes through exact regional completion. The split generator
agreed with exhaustive testing of 2,400 small allocation instances. Its
integration also passed the 2,000-query independent completion suite.

At 0.30 s per job in the supplied Windows-adapted reference replay,
port-first completed 22 of 30 signed queries, root-CSP completed 21, and
the time-sliced portfolio completed 23. Root-CSP completed signed trials
12 and 13 that port-first timed out on, one SAT and one UNSAT. The portfolio
gave port-first 80 ms and root-CSP the remainder, recovering trial 12. In
the integrated work-sliced replay, the packed baseline completed 12 and
the standalone and portfolio root variants each completed 10. Both root
variants found a verified SAT witness at signed trial 2, which the integrated
baseline missed. All three integrated modes completed all 30 monotone queries.
The variation between the supplied and integrated solvers makes root
propagation an optional second search order. [Supplied replay](results/regional_cnf_root_prototype.jsonl) ·
[Integrated replay](results/regional_cnf_root_portfolio.jsonl)

The [Pareto prototype](theory/archive/regional_pareto_completion.py) is archived.
The supplied stress results found no additional resolved queries from Pareto
completion. A replay would be justified by a workload with distinct useful
intermediate column frontiers and evidence that their pruning offsets the
cost of maintaining them.

### A smaller exact core for the signed outlier

`wide-8-1-1` uses only three of its eight private coordinates across all
specified slices. Only two providers are needed to retain the labels in
this query, and one has a spare allocated read. The optional
`certificate-absorption` mode identifies a consistent supported core,
solves it with CDCL, and restores all allocations. If the core contains
the literal `a` of a provider with a spare read, replacing that occurrence
with `a OR (a AND H)` preserves its function. `H` can be a read-once AND
of all the remaining unused leaves. The extra `a` uses the spare port
occurrence with the same phase. This gives an exact fixed-occurrence
construction in either basis. Failed core attempts leave the original
query to the exact backend.

For the signed outlier the core had five leaves instead of twelve and 32
labeled assignments instead of 2,048. MapleChrono solved the core in under
0.1 ms. The complete query took 4.2 ms at 36.6 MiB peak working set and
the independent evaluator checked all original slices and occurrences.
The packed, eager, lazy, and anchored full-query searches reached one second.
The construction is a witness prepass and the result is local to this
query. [Witness and measured phases](results/regional_cnf_absorption.jsonl)

```powershell
python sat-search/experiments/regional_certificate_check.py -v
python sat-search/experiments/regional_completion_check.py -v
python sat-search/experiments/cograph_formulas_check.py -v
python sat-search/experiments/regional_certificate_check.py --bench --dataset queries --seconds 1 --output fresh-cnf-queries.jsonl
python sat-search/experiments/regional_certificate_check.py --bench --dataset roots --seconds .30 --output fresh-root-portfolio.jsonl
python sat-search/experiments/regional_certificate_check.py --bench --dataset layouts --seconds 4 --modes row-quotient certificate-cnf certificate-fallback root-portfolio --output fresh-cnf-layouts.jsonl
python sat-search/experiments/regional_certificate_check.py --bench --dataset queries --case wide-8-1-1 --seconds 1 --modes certificate-absorption --output fresh-absorption.jsonl
```

## Constructive regional padding

The opt-in `padding-first` regional mode tries a smaller functional core, then
restores all spare leaves with one AND/OR graft. The prepass returns a witness
or unknown. The exact packed row-quotient solver decides the original query
on a miss. No CDCL activation is needed. Inputs are exact regional slices in
the monotone or free-NOT basis. The port multiplicities describe occurrences.

### Graft characterization

The root is sensitive on every specified row. A child's sensitivity mask is
the parent's mask intersected with rows where its sibling has the gate's
neutral value. At a subtree with value table `v`, an OR graft must supply zero
on sensitive zero rows of `v`. An AND graft must supply one on sensitive one
rows. The other rows permit either filler value.

For positive literals, AND of all spare leaves is the smallest possible
filler and OR the largest. These decide the zero and one requirements,
respectively. For free NOT, each choice of occurrence phases has an all-true
literal pattern and an all-false literal pattern. Every AND/OR tree evaluates
to one and zero there. If the critical rows contain every raw occurrence
pattern, the corresponding filler is impossible. If one pattern is absent,
a signed conjunction true only there supplies the required zero, or a signed
disjunction false only there supplies the required one. This counts raw
occurrence bits even if some combinations are unrealizable due to repeated
providers. At the root at most the smaller output side needs the corresponding
constant, so `2^q > min(positive rows, negative rows)` guarantees a graft for
`q` spare occurrences. The rows here include private assignments within slices.

The core prepass can omit unused private coordinates. Provider masks impose
necessary distinctions between observed slices, with raw difference in free
NOT and directional difference in monotone mode. Core searches use at most
six leaves, 24 solver trials, and 512 inspected allocations. Equal projected
provider rows share a core obligation. On complete projected tables with
distinct leaves, direct read-once recognition replaces recursive search.
Every leaf of a read-once tree on independent coordinates is essential,
since siblings can be set to their neutral values along its output path.
Partial or repeated-provider cores keep a finite search-work cap. The graft
test is exact for the given core and a single graft. The prepass can miss
other core witnesses or solutions needing several grafts.

The supplied `python regional_padding.py --bench --padded` replay replaced
only the Unix timer with the Windows worker deadline. It reproduced 34/60
versus 60/60 on deliberately surplus-heavy queries, with 7.984 versus 0.527 s.
On the broader supplied root stress sample the prepass solved no additional
queries in this replay. The integrated tests passed 1,400 exhaustive
single-graft comparisons and checked returned witnesses against 300 small
exact regional queries. Each returned construction is reevaluated on every
specified assignment and checked for all allocated occurrences.

### Matched integrated results

| Workload | Packed row quotient | Padding first |
| --- | --- | --- |
| 60 generated surplus-heavy queries at 0.20 s each | 37 SAT in 6.416 s | 58 SAT in 0.589 s |
| 12 captured queries plus signed `wide-8-1-1` at 1 s each | 12 UNSAT and one timeout in 1.982 s | 12 UNSAT and one SAT in 0.985 s |
| Five whole-layout jobs at 4 s each | Four decisions in 10.398 s | Four decisions in 11.158 s |

The generated cases explicitly have a padded witness and are favorable to
the prepass. The final replay obtained 57 of its 58 witnesses by grafting.
Peak working set for the generated workers fell from 61.2 to 40.3 MiB.
The initial integration completed 53/60. Quotienting duplicate projected
rows reduced setup cost and left the completion count at 53/60. Direct
recognition on complete distinct-leaf cores and increasing the signed
partial-core cap from 256 to 2,048 work events jointly brought it to 58/60.
The two remaining misses were signed. One exhausted all nine bounded core
trials. For the other, a diagnostic allocation cap of 4,096 reached nine
trials and still found no witness within the core work limits. Further
increasing caps has no demonstrated benefit on the frozen corpus.

`wide-8-1-1` used one core trial and a verified graft in 5.6 ms without SAT.
The 12 captured negative queries were decided by the exact fallback. The
whole-layout replay showed no new exclusion or witness and no interval
changed. The 13-gate `comparator-09` budget remains open. The costs of failed
prepasses on these layouts support keeping `padding-first` opt-in.

[Windows prototype replay](results/regional_padding_prototype.log) ·
[Initial surplus replay](results/regional_padding_surplus.jsonl) ·
[Projected row ablation](results/regional_padding_surplus_quotient.jsonl) ·
[Final surplus replay](results/regional_padding_surplus_final.jsonl) ·
[Captured queries](results/regional_padding_captures_final.jsonl) ·
[Whole layouts](results/regional_padding_layouts_final.jsonl)

```powershell
python sat-search/experiments/regional_padding_check.py -v
python sat-search/experiments/regional_padding_check.py --bench --output fresh-padding-surplus.jsonl
python sat-search/experiments/regional_certificate_check.py --bench --dataset queries --seconds 1 --modes row-quotient padding-first --output fresh-padding-captures.jsonl
python sat-search/experiments/regional_certificate_check.py --bench --dataset layouts --seconds 4 --modes row-quotient padding-first --output fresh-padding-layouts.jsonl
```
