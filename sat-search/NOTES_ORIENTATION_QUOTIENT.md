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

## Limits and open questions

* The partial oracle covers only 3..6 inputs, so the n = 8 b and bank stages (7 inputs) need a 7-input partial
  constructor, or a lift on care sets.
* A constructive AND-split backend for b is open: build the two operands over Y_A and Y_B from a passing root
  partition.
* The oracle time is the bottleneck. Its memo hit rate across targets is not yet tuned.

## Reproduction

```
sat-search/native/build_orientation.bat         (via a wrapper .bat; the repo path contains '=')
sat-search/native/fq_check.exe --brute 1 3000
python -B sat-search/experiments/feature_quotient_check.py <bundle>/support.jsonl sat-search/results/feature_quotient/support_native.jsonl
python -B sat-search/experiments/orientation_check.py replay OUT --input <td>/input_pilot.jsonl <td>/input_heldout.jsonl --max-n 6 --reference <td>/replay6.jsonl
python -B sat-search/experiments/orientation_check.py bench OUT --random 5:60:5101 --exe-args="--native-partial 7 --support-project"
python -B sat-search/experiments/orientation_check.py bench OUT --input <td>/input_pilot.jsonl <td>/input_heldout.jsonl --min-n 7 --max-n 7 --with-spec --exe-args="--native-partial 7"
python -B sat-search/experiments/orientation_check.py replay OUT --input ... --exe-args="--audit"
```

Random seeds: 5101 / 6101 / 7101 / 8101 for n = 5 / 6 / 7 / 8.
