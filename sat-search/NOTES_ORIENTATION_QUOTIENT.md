# Target-directed orientations, feature quotient and root partition (2026-11-26)

Integrates three externally supplied research bundles: `target_directed_encoder_research`,
`quotient_completion_research` and `slack_one_completion_research`. The bundles were audited first (stdlib only, no
writes outside their own directory) and run from copies. Everything here is an **upper-bound construction** or a
**fixed-interface conditional bound**. No new unrestricted minimum or lower bound is claimed.

Files:

* `native/src/orientation_witness.hpp`: the orientation constructor, its partial-oracle hook, the audit hook and the
  min-support / support-projection options.
* `native/src/feature_quotient.hpp`: the quotient test, walk certificate, minimum support and root-partition screen.
* `native/tools/orientation_synth.cpp` and `native/tools/fq_check.cpp`, built by `native/build_orientation.bat`.
* Drivers: `experiments/orientation_check.py` and `experiments/feature_quotient_check.py`.
* Records: `results/orientation/`, `results/feature_quotient/` and `logs/orientation/`.

## Reproduction of the bundles (Python, unchanged)

* **td.** `verify.py` checks 84 circuits / 8,064 rows, 196,608 orientation comparisons and 16,384 quotient
  comparisons. `orientation.py --max-n 6` reproduces replay6 at 261 gates.
* **quotient.** `verify.py` counts match its README. support / completion / archived_tight are identical except for
  timing (43 tight cases: 23 SAT, 20 UNSAT).
* **slack-one.** `verify.py` checks 782 decisions. `partition_replay` gives 20 UNSAT, identical apart from one new
  zero-valued stat key.

## Phase 1: orientation constructor (native port)

Faithful C++20 port of `orientation.py`:

* **Split and encoders.** X is 1–2 decoder inputs and Y the rest. The first encoder a comes from a bank: literals,
  cofactors, class indicators, affine cofactor pairs, signed literal ANDs, cone nodes and contextual partial
  completions. The bank keeps one cheapest representative per Y-column modulo complement.
* **Buckets.** Each (R, a) bucket is checked. A bucket with more than two distinct residual labels rejects a. The
  two-class buckets are oriented in every way, modulo global complement (2^(q-1) obligations). One-class buckets are
  left unspecified.
* **Second encoder.** b is built per obligation, optionally with a reused as an extra input. The decoder over
  (X, R, a, b) is completed on its reachable rows.
* **Cost and verification.** Cost is the live hash-consed AIG cone union. The result is the smaller of the fallback
  and the best orientation, so it never regresses. Every exported chain is evaluated row by row in C++, and again by
  the independent Python evaluator in `orientation_check.py`.

**Equivalence.** Sizes are identical to the Python replay on every bundle case (`--no-native`, bundle witness as
fallback):

| Set | Native | Python |
| --- | ---: | ---: |
| replay6 (15) | 1.7 s | 18.7 s |
| replay7 (11) | 1.2 s | 14.2 s |
| replay7held (4) | 0.7 s | 8.4 s |
| replay8 (2) | 0.4 s | 5.4 s |

**Fallback.** The fallback is the strongest current native constructor: `cofactor::synthesize` with root slack 2 for
n <= 6. For n = 7, 8 it is a memoized Shannon lift over native 6-input cofactor witnesses, measured by the shared cone
after import. The supplied bundle witness is used instead when it is smaller.

**New opt-in partial oracle** (`--native-partial S`). The native cofactor constructor (care sets, 3..6 inputs) is
called at the orientation sites in S:

* 1: first-encoder bank;
* 2: second encoder b;
* 4: decoder.

The cheaper of Shannon and the oracle is kept, and oracle results are memoized per (k, positive, care).

### Benchmarks against the native fallback

Matched runs. The totals are sums of gate counts over each set, and the table shows the final size (min of fallback
and orientation). Fallback time is reported separately from orientation time. Runs were concurrent (up to 12
processes), so times are indicative.

| Set | Fallback (time) | Orientation only | s4 (decoder oracle) | p7 (all sites) | p7 + min-support | p7 + support projection |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| n5 random 60 | 868 (3 s) | 856 / 9 wins, 6 s | 816 / 33, 66 s | **806 / 39**, 259 s | 806, 205 s | 806, 193 s |
| n6 random 40 | 1173 (4 s) | 1171 / 1, 10 s | 1168 / 3, 9 s | stopped (> 14 min) | | |
| n6 bundle 15 | 239 (4 s) | 239 / 0, 3 s | 235 / 1, 4 s | **226 / 6**, 789 s | | |
| n7 random 12 | 683 (7 s) | 683 / 0, 4 s | 683 / 0, 3 s | **655 / 10**, 335 s | | 655, 287 s |
| n7 bundle 15 | 381 (7 s) | 379 / 2, 3 s | 374 / 3, 4 s | **357 / 8**, 157 s | 357, 145 s | 357, 135 s |
| n8 random 6 | 679 (34 s) | 679 / 0, 10 s | 679 / 0, 10 s | 679 / 0, 11 s | | |
| n8 bundle 6 | 282 (21 s) | 282 / 0, 5 s | 282 / 0, 5 s | **280 / 2**, 36 s | | |

At n = 6 every orientation site has 4–5 Y-inputs, so all of them use the oracle, and the per-target oracle time is
largest there: about 53 s per target on the n6 bundle. The n6 random p7 run was stopped after about 14 minutes and
left open (no records).

Site ablation:

| Set | s1 | s2 | s4 | p7 |
| --- | ---: | ---: | ---: | ---: |
| n5 random | 850, 5 s | 849, 187 s | 816, 66 s | 806, 259 s |
| n7 bundle | 377, 72 s | 376, 89 s | 374, 4 s | 357, 157 s |

* **Decoder site.** It is the most cost-effective site. At n = 7 it gains 7 gates for about 1 s.
* **Superadditive sites.** At n = 7 the sites combine superadditively: 357 with all three, against 374–377 for each
  alone. Better bank and b chains enlarge the decoder's useful inputs.
* **n = 8.** The oracle only applies to 3..6-input instances, so at n = 8 most b and bank instances (7 Y-inputs) stay
  Shannon, and the gain there is small.

Conclusion: the plain orientation port is almost entirely dominated by the native constructor and the lift. With the
native partial oracle, the orientation constructor improves the strongest native upper bounds by 4–7% on 5- and
7-input targets, at 20–50× the orientation time. **Promotion:** this is an opt-in mode (`--native-partial 7
--support-project`) for upper-bound jobs, not the default. `--native-partial 4` is the cheap setting.

Witnesses: every record in `results/orientation/bench_*_{p0,s4,p7,p7m,p7sp}.jsonl` carries both chains (`spec`,
`orient_spec`), independently evaluated. No record exceeds its fallback (all records checked).

## Phase 2: feature-quotient bipartiteness and minimum support

`fq::certificate` implements the signed-graph balance test. Conflict edges have parity 1, and equality edges inside
each Z-class have parity 0. Self-loops are kept: a conflict self-loop is an odd walk by itself.

**Certificate.** An unbalanced graph yields an odd closed walk. Its mask (the union of w(i) XOR w(j) over the
parity-0 steps) must meet every feasible support. `fq::replay` re-checks a walk independently: it is closed, its
parity-1 steps are conflict edges, its parity is odd, and its mask equals the union.

**Search.** `fq::min_support` is conflict-directed. It runs an exact hitting set over the pairwise difference masks
plus the learned walk masks, then retests. It has explicit statuses:

* `constant` (empty conflict set; bound 0);
* `feasible`;
* `impossible` (some conflict joins identical signatures, or an empty mask);
* `unknown` (call or work limit; no bound).

**Conditional bound.** max(0, s* − 1) additional AND gates (`gate_bound`). This holds only for a trimmed completion
reading these available signals with free complements. It is a fixed-interface statement, never an unrestricted
lower bound.

**Fixed-target remark.** When the conflicts are all (positive, negative) pairs of a fixed target, the quotient is
bipartite iff Z covers every pairwise difference. So parity adds nothing at the Percy fixed-target residual boundaries.

### Checks

* **Brute force** (`fq_check --brute`, seeds 1–4, 63,000 instances). Random rows (1–5 features, 1–8 rows, duplicate
  rows), random edges (self-loops, empty sets). Every support was checked by enumerating all labellings of the
  Z-classes (777k support checks):
  * the quotient test and certificate agree with brute force;
  * s* equals the brute-force minimum;
  * every learned mask is hit by every brute-feasible support, and every walk replays;
  * constant and impossible are reported exactly.

  0 mismatches; parity raised s* above pair cover on 320 instances (about 3.2% of the 10,004 feasible ones).
* **Bundle.** `support.jsonl` (197 records): native s*, pair size and status are equal on all 197, and all 854
  learned walks replay natively. Parity exceeds pair cover on 121 of them. Record:
  `results/feature_quotient/support_native.jsonl`.

### Production audit (orientation second encoder, `--audit`)

The b obligations are where orientation is free. Rows are the Y assignments, and conflicts join the two classes of
each two-class bucket. Before an orientation is chosen this is not a fixed target, so parity matters.
Records: `results/orientation/audit_replay{6,7,8}.jsonl` (bundle targets, bundle fallback).

| n | Encoders | Feasible | Parity > pair | Sum s* / Sum pair | Sum bound / Sum best cost1(b) | cost1(b) < bound | Marginal < bound | Unknown |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 6 | 6599 | 6432 | 2356 (37%) | 19545 / 17080 | 13113 / 35701 | 0 | 31 | 0 |
| 7 | 5885 | 5753 | 2457 (43%) | 22291 / 19669 | 16538 / 59176 | 0 | 4 | 0 |
| 8 | 1856 | 1856 | 986 (53%) | 9310 / 8176 | 7454 / 26729 | 0 | 12 | 0 |

* **Soundness.** No standalone b chain was below its conditional bound, and every b's support was at least s*. The
  non-feasible encoders are `constant`: no two-class bucket.
* **Sharing.** The marginal cost (cost({a, b}) − cost1(a)) can fall below the standalone bound through sharing with
  a's cone. So the bound is **not** a sound pruning rule for shared cost, and it is not used for pruning.
* **Strength.** The bound is weak against actual b costs (about 37% of the best chain cost at n = 6).

**Constructive uses (opt-in).**

* `--min-support-orient` builds b only for orientations whose own fixed-target minimum support equals the
  orientation-free s*. This set is nonempty: the coloring of the s*-quotient gives one. If the search is not feasible,
  all orientations are kept.
* `--support-project` builds each kept b over its own s* support variables only. The obligation is projected, which is
  consistent by the quotient theorem.

Results:

* **Without the oracle.** The filter cuts b syntheses by 35–45% (replay6: 25,627 → 14,499) at equal size, but costs
  more time than it saves, because Shannon b is memoized and cheap (replay7: 1.8 → 2.9 s). Support projection is
  neutral to +1 gate. **Not promoted for Shannon-only runs.**
* **With the oracle.** Equal sizes and 21% / 8% less time for the filter. Projection gives 25% / 14% less time
  (n5 random / n7 bundle). Recommended together with `--native-partial`.

## Phase 3: root partition

**Already native.** The fixed-target rules already exist in the regional engine, opt-in through `--residual-filter
root|parity|direct` (NOTES_FIRST_LAYER.md, "Projected roots and provider parity"):

* mandatory provider distinctions and provider quotient bipartiteness (`residual_filter::provider_components`);
* root AND operand compatibility and the exact closure F ∩ L_A(T) ∩ L_B(T) = ∅ in both phases, under a work charge
  that returns unknown (`tight_residual.hpp:193`, `residual_filter::root_and_possible`).

They were not duplicated.

**New: multi-component screen.** `fq::root_partition` is the closure for **unoriented** conflicts. It enumerates all
2^c orientations of the c conflict components, which covers both global phases. It returns `unknown` above the
component cap (8), and `reject` when the conflict graph itself is not bipartite. Its only consumer so far is the
audit: b = op(Y_A) AND op(Y_B) over the disjoint Y-splits.

**Checks.**

* Brute force over every pair of operand functions on 240k random screens: 0 mismatches.
* Production audit (n = 6 / 7 / 8):
  * splits rejected: 63% / 70% / 72%;
  * encoders with some AND split: 79% / 76% / 86%;
  * unknown: 0, since there are at most 4 buckets.

A pass is only an unrestricted decomposition test and says nothing about a bounded-size realization. Optional early
provider-partition screening stays off by default, as before.

**Rule 5 (parity-aware support bounds for backend selection)** is implemented as `--support-project`, above. It routes
each b to an oracle/Shannon instance on s* inputs.

## Phase 4: cost-aware second encoders with full-cone reuse (essential-synthesis handoff, 2026-11-26)

Source: `cost_aware.py` from the essential-synthesis handoff. Its `orientation.py`, `quotient.py` and root-partition
modules are byte-identical to the bundles above, so priorities 2 and 3 (root partition and parity-aware support)
were already integrated.

The construction builds b with `Marginal`. Its features are the Y literals, a, and in mode 1 every node of a's cone.
Features are deduplicated by Y-column modulo complement and scored by marginal cost |cone(h) \ cone(a)|. The
construction runs an exact search over at most two new gates, then a feature-split recursion: complement normalized
by the lowest cared row, memoized, best of the top `branch` = 2 splits by marginal cost. First encoders with
cost(a) >= cost(fallback) are skipped.

**Native port.** `orient::Marginal` in `native/src/orientation_witness.hpp`. It is opt-in and off by default:

* `--cost-aware 1` is the reference construction. Mode 0 and mode 1 replace the native b and reuse.
* `--cost-aware 2` is the portfolio. The native modes are unchanged, and both Marginal candidates go into a third
  decoded pool that feeds the reuse result.
* `--ca-branch K` sets the branch width.

The fallback stays the floor in both modes. Every b is checked against its obligation, every decoded candidate
against the target, and every emitted chain is evaluated independently by `orientation_check.py`.

**Differential (checked, exact).** Setup: `replay --exe-args "--cost-aware 1 --first-cap 3 --pair-cap 5 --reuse"`,
bundle witness as fallback, native constructor off. Result: [fallback, mode 0, mode 1] sizes equal the Python
`cost_aware.py` output on all 36 bundle cases (34 distinct targets), with 0 mismatches. Totals are 1023 -> 1002
(orientations) -> 954 (full-cone reuse). The historical 875 -> 849 -> 812 in the handoff README is over a different
target list. Records: `results/orientation/replay_cost_aware_{native,python}.jsonl`.

**Benchmarks against the native fallback (verified upper bounds; matched sets and seeds, total gates).**

| Set | p0 (default) | ca2 | p7 (`--native-partial 7`) | ca2 + p7 |
| --- | --- | --- | --- | --- |
| n5 random (60) | 856, 5.9 s | 851, 7.0 s | 806, 259 s | **804**, 261 s |
| n6 random (40) | 1171, 10.3 s | **1168**, 14.6 s | (too slow) | not run |
| n7 random (12) | 683, 4.2 s | 683, 15.0 s | 655, 335 s | 655, 329 s |
| n8 random (6) | 679, 10.4 s | 679, 33.1 s | 679, 11.4 s | 679, 37.2 s |
| n6 bundle (15) | 239, 2.7 s | **237**, 3.9 s | 226, 789 s | not run |
| n7 bundle (15) | 379, 3.1 s | 376, 9.0 s | 357, 157 s | **355**, 162 s |
| n8 bundle (6) | 282, 4.9 s | 282, 14.2 s | 280, 36.2 s | 280, 46.1 s |

How to read the table:

* Times are orientation-stage (construction) seconds. Native fallback time is unchanged and reported separately in
  the records.
* There are no losses (the fallback floor).
* Against p7: the portfolio wins on 2/60 n5 targets and 1/15 n7-bundle targets.

Inside the portfolio, Marginal mode 1 beats mode 0 on most obligations. Over all five p7 sets it was better on 37k
and worse on 6k of 140k obligations. Even so, the decoded totals of Marginal alone (`mode1_size` with p7: n7 random
670, n7 bundle 369) stay above the oracle-backed native b. So the gain at the strongest configuration comes from the
portfolio, not from replacing b. Against the much stronger native fallback, the large standalone savings seen over
archived witnesses (-48 over 1023) shrink to -2..-5 per set.

Not applicable: this stage produces no residual exclusions and no proof steps, so there is no end-to-end proof time
to report. These are upper bounds only.

Records: `results/orientation/bench_*_{ca2,ca2p7}.jsonl` and `logs/orientation/bench_*_{ca2,ca2p7}.out`.

## Phase 5: exact partial reductions and a normalized core cache before the oracle (native follow-up handoff)

Source: the follow-up handoff `README(1).md`, items 1 and 2. Before the port, the partial-oracle path had no partial
or module preprocessing. The `module` code in `regional_kernel` / `restriction_certificate` concerns graph
modules, not this path.

**Rules** (`native/src/partial_reduce.hpp`). Each rule removes one input i, with an exact offset for *standalone*
minima K (independent primary inputs, free complements):

* **zero**, offset 0: the two cofactors agree on their overlap, and a constant or signed surviving literal covers the
  merged care. Consistency alone only gives an upper bound.
* **peel**, offset 1: i is mandatory, the neutral slice is nonconstant on care, and the opposite slice is constant
  on care.
* **module**, offset 1: i is mandatory, the neutral slice g is nonconstant, and the opposite slice, with its two x_j
  slices merged, is covered by the x_j = v slice of g with equal labels.

`greedy` repeats the least rule in the reference order. `construct` lifts any core chain: a module adds its gate
before the core and a peel after it; a zero rule only drops the input. `canonical` / `inverse` give the incomplete
signed-permutation and output-phase normalization: input statistics are sorted with ties kept and complete masks
compared, so normalization never merges inequivalent tables, though it can miss equivalences.

**Hook** (`orientation_synth`, all opt-in). In the partial oracle:

* `--reduce` reduces, then solves the core: native constructor for 3..6 inputs, Shannon for <= 2 inputs or
  constants.
* `--canon` caches cores by canonical key.
* `--reduce-wide` also passes 7..8-input queries; the oracle returns nothing when the core still has more than
  6 inputs.

The lifted chain is checked on the original care set before it is returned. The existing synth site still keeps the
cheaper of oracle and Shannon. The raw memo key now uses the full table, not `w[0]`. Per target, the JSON `oracle`
key records calls, constructor misses, reduced queries, removed inputs, offsets, wide rejections, reduction time,
and input and core width histograms.

**Checks.**

* *Proved here by exhaustive computation:* `preduce_check --exact3` computes exact standalone minima of all 256
  three-input functions by breadth-first search over column sets modulo complement (max K = 6). It then checks
  every partial table on 1..3 inputs (6,651 tables):
  * every applicable rule satisfies K(f) = K(g) + offset: 6,252 zero, 5,984 peel and 4,832 module rules, the
    handoff's counts exactly;
  * every completion of every reduced table lifts row by row to agree with f on care (148,952 rows);
  * the greedy core lifts to a valid chain;
  * canonical keys round-trip and preserve K.

  All checks pass with 0 failures.
* *Differential:* `experiments/partial_reduce_check.py` compares 4,000 random and planted queries on 4..8 inputs
  (seed 1) with the handoff's Python `greedy` / `canonical`. Core width, table, steps, offset and canonical key
  match with 0 mismatches, and every lifted Shannon chain is valid on care. Planted (random-AIG) queries reduce
  78-89% of the time; uniform random 7..8-input queries never reduce.

**Benchmarks.** Matched sets, same seeds, run concurrently in two waves. Baseline is the strongest native mode,
`--native-partial 7 --support-project`. Each cell gives total verified gates, oracle seconds, and constructor
misses:

| Set | baseline | `--reduce` | `--canon` | both |
| --- | --- | --- | --- | --- |
| n5 random (60) | 806, 201 s, 59,944 | 806, 191 s, 51,761 | 805 (2 wins, 1 loss), 173 s, 36,086 | 805, 155 s, 32,632 |
| n7 random (12) | 655, 292 s, 14,136 | 655, 185 s, 13,155 | 655 (3 wins, 3 losses), 229 s, 12,301 | 655, 170 s, 12,239 |
| n7 bundle (15) | 357, 131 s, 9,799 | 357, 69 s, 5,744 | **361** (1 win, 3 losses), 91 s, 5,632 | 361, 62 s, 4,813 |
| n8 bundle (6) | 280, 19 s, 2,824 | 280, 1.7 s, 408 | 280, 3.1 s, 711 | 280, 0.8 s, 236 |

* Reduction time is 0.04-0.37 s per set.
* `--reduce` left every witness size unchanged on all 93 targets. This is measured, not guaranteed: the core is
  solved by the same heuristic constructor. Core width histograms are in the records; for example, the n7 bundle's
  6,392 six-input queries leave 2,985 six-input cores.
* `--canon` changes heuristic quality in both directions, net +4 gates on the n7 bundle, as the handoff warned.
  Keep it off for quality runs.
* `--reduce-wide` on the n8 bundle passed 3,584 seven-input queries. 1,435 stayed wider than 6, the oracle time rose
  19 -> 32 s, and no size changed. It stays separate and off.
* Recommendation: use `--reduce` with `--native-partial` (37-91% less oracle time on the three non-n5 sets, and a
  lossless measurement). All three flags stay opt-in.

**Not implemented:** handoff items 3 (decoder-aware ranking) and 4 (deadline pruning). The handoff marks them
optional. The orientation path has no small-budget exact encoder enumerator for item 4 to prune, and item 3 would
need near-minimal encoder candidates that the current bank does not rank. The AND/XOR split was omitted, as advised.

Records: `results/orientation/bench_*_{p7spB,rd,cn,rdcn}.jsonl` and `bench_n8_bundle_rdw.jsonl`, with logs beside
them.

## Phase 6: exact <= 4-gate support-projection prepass (handoff section 1, opt-in `--exact4`)

`src/exact4.hpp` decides the standalone free-phase AIG minimum of a partial table exactly when it is at most 4,
and otherwise proves K >= 5.

*Theorem (paper; the handoff's argument, re-derived here):*
- A trimmed one-output AIG with g gates reads at most g + 1 inputs.
- At g = 4 with 5 inputs, the cone has 9 nodes and 8 arcs, so it is a tree, i.e. a signed read-once formula.
- So every solution with g <= 4 is either a complete 4-input function of cost <= 4 over some 4-subset of inputs,
  or a 5-input signed read-once formula, which agrees with the projection of the table onto that support.
- A support that misses a mandatory input is skipped, as is a projection where a positive and a negative row
  fall in the same fibre.

*Implementation:*
- Libraries: depth-first enumeration of gate sequences over distinct complement-normalized columns gives every
  function of 1..4 inputs with cost <= 4 and a minimum chain. Signed read-once formulas over 5 inputs are
  built by subset recursion.
- Each library has one bitset per row; the lowest surviving record is the cheapest match.
- Search order and early stop follow the Python reference.

**Checks.**
- `preduce_check --exact4`:
  - the libraries have 4 / 16 / 230 / 3,590 / 15,104 columns, the handoff's counts;
  - every chain simulates to its column at its cost;
  - the 3-input costs equal the exact3 BFS minima;
  - the exact <= 4 decision of all 6,651 partial tables on 1..3 inputs equals the exact minimum over
    completions (6,609 hits, 42 exclusions);
  - every hit's imported witness is valid on care, and the handoff regressions pass.
- `experiments/exact4_check.py` against the handoff's Python `exact4`: random, planted and small-planted
  queries on 4..8 inputs, 3,000 at seed 1 and 15,000 at seed 2. Cost, support and column match, with 0
  mismatches; the 15,000 include 327 cost-4 hits and 3,560 exclusions.

**Wiring.** In the partial oracle, after `--reduce`, each nontrivial core of 3..6 inputs is first given to
exact4:
- a hit is imported in place of the native constructor;
- an exclusion falls through to the constructor;
- with `--reduce-wide`, a 7..8-input core that hits is also served.

Results are cached per core. Only standalone witnesses are produced; the lower bound is never used to prune
the live, shared cost.

**Benchmark** (same sets as Phase 5, `--native-partial 7 --support-project --reduce` with and without
`--exact4`, run concurrently):

| Set | gates (both) | constructor calls | oracle s | exact4 queries / hits / s |
| --- | --- | --- | --- | --- |
| n5 random | 806 = 806 | 51,761 -> 48,323 | 188 -> 187 | 51,732 / 3,409 / 0.29 |
| n7 random | 655 = 655 | 13,155 -> 13,126 | 190 -> 190 | 13,155 / 29 / 0.12 |
| n7 bundle | 357 = 357 | 5,744 -> 5,636 | 70 -> 70 | 5,744 / 108 / 0.11 |
| n8 bundle | 280 = 280 | 408 -> 388 | 1.7 -> 1.8 | 408 / 20 / 0.15 |

No size changed and no target won or lost. The hits are small cores that the constructor already solves
cheaply, so oracle time does not move. This matches the handoff's expectation (0.64% of its pool was strictly
additional). `--exact4` stays opt-in and is not recommended for throughput. Its value is as a certified small
oracle (exact <= 4 or a proven K >= 5) for other callers.

Records: `results/orientation/bench_*_{rdB,rde4}.jsonl` (`rdB` is a concurrent rerun of `rd`; identical sizes and
counts).

**Not integrated** (handoff sections 0/0a): reusable exclusion cores, sparse lower-bound caches, and the
enhanced first-gate leaves. These are useful only for expensive exact exclusions, which this path does not
make. At four gates, the handoff's own replay shows the direct lookup is cheaper than the cache.

## Limits and open questions

* The partial oracle covers only 3..6 inputs, so the n = 8 b and bank stages (7 inputs) need a 7-input partial
  constructor, or a lift on care sets. Exact reductions bring 60% of the n8-bundle 7-input queries down to <= 6, with
  no size gain so far.
* A constructive AND-split backend for b is open: build the two operands over Y_A and Y_B from a passing root
  partition.
* The oracle time is still the bottleneck on random targets, where reductions rarely apply. A canonical cache that
  keeps the better of the canonical and raw witness would avoid the `--canon` quality losses, at the cost of extra
  misses.

## Reproduction

```
sat-search/native/build_orientation.bat         (via a wrapper .bat; the repo path contains '=')
sat-search/native/fq_check.exe --brute 1 3000
python -B sat-search/experiments/feature_quotient_check.py <bundle>/support.jsonl sat-search/results/feature_quotient/support_native.jsonl
python -B sat-search/experiments/orientation_check.py replay OUT --input <td>/input_pilot.jsonl <td>/input_heldout.jsonl --max-n 6 --reference <td>/replay6.jsonl
python -B sat-search/experiments/orientation_check.py bench OUT --random 5:60:5101 --exe-args="--native-partial 7 --support-project"
python -B sat-search/experiments/orientation_check.py bench OUT --input <td>/input_pilot.jsonl <td>/input_heldout.jsonl --min-n 7 --max-n 7 --with-spec --exe-args="--native-partial 7"
python -B sat-search/experiments/orientation_check.py replay OUT --input ... --exe-args="--audit"
python -B sat-search/experiments/orientation_check.py replay OUT --input <td>/input_pilot.jsonl <td>/input_heldout.jsonl <td>/eight_generated.jsonl --reference <ca outputs> --exe-args="--cost-aware 1 --first-cap 3 --pair-cap 5 --reuse"
python -B sat-search/experiments/orientation_check.py bench OUT --random 5:60:5101 --exe-args="--cost-aware 2 --native-partial 7"
sat-search/native/preduce_check.exe --exact3
python -B sat-search/experiments/partial_reduce_check.py --reference <dir with the handoff reduce.py> --count 400 --seed 1
python -B sat-search/experiments/orientation_check.py bench OUT --input <td>/input_pilot.jsonl <td>/input_heldout.jsonl --min-n 7 --max-n 7 --with-spec --exe-args="--native-partial 7 --support-project --reduce"
sat-search/native/preduce_check.exe --exact4
python -B sat-search/experiments/exact4_check.py --reference <dir with the handoff projection.py> --count 1000 --seed 2
python -B sat-search/experiments/orientation_check.py bench OUT --random 5:60:5101 --exe-args="--native-partial 7 --support-project --reduce --exact4"
```

Random seeds: 5101 / 6101 / 7101 / 8101 for n = 5 / 6 / 7 / 8.

## Coupled first-gate reader audit

The two absorbing restrictions and the joint reader profiles are sound for a
minimum AIG chosen to maximize its number of first-layer gates. The audit also
checks phase compatibility when two first-layer gates share an input pair.
`0x07e1` has exact free-complement AIG cost 7 by a small exhaustive cofactor
certificate and an independently replayed witness. The strongest compared
first-gate baseline already reaches 7 using recursive signed regional bounds.
The absorbing extension improves one of 300 seeded five-input tables and none of
the 89 frozen corpus targets with that baseline. The extensions remain experimental.
The proof uses complete truth tables and does not justify orientation or partial-label pruning.
[Audit, scope, and matched replay](results/coupled_reader/README.md)

## SAT on one Hamming layer

The independent SAT direction uses a signed projection into the actual paired grammar
at a fixed Hamming weight. Threshold guards and the monotone slice compiler give an
exponent-preserving equivalence to unrestricted SAT. This is a problem reduction,
with no circuit synthesis or orientation change. The ordinary monotone CLIQUE
projection is ruled out by averaging projected weights over vertex relabelings.
[Proof and replay](results/sat_weight_slice/README.md)

## Andreev projection and limits of path counting

The paired grammar embeds parity-addressed lookup by fixing all tokens except
the polarity of each input unit clause. Tautological padding extends the formula
bound to every sufficiently large even length. A linear-size realizing AIG can
concentrate the high multiplicities in selector-only gates, with exactly one
output path per gate having a data ancestor. This gives a barrier for a sharing
argument based on the Andreev restriction. [Proofs and replay](results/andreev_projection/README.md)
