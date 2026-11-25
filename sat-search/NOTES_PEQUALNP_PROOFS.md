# Reusable lower-bound mathematics from pequalnp-proofs

These notes review the Lean library at
[open-goat/pequalnp-proofs](https://github.com/open-goat/pequalnp-proofs) and the companion
note at <https://pequalnp.com/papers/note-1>. The review used upstream commit `d9f1ea23`
(2026-11-25), cloned into `external/pequalnp-proofs-open-goat`. `external/` is git-ignored.

The local `pequalnp-proofs/` fork is behind upstream. The helper files this review depends on
are byte-identical in the two copies: `Readers`, `ReadersExport`, `ReadersFunnel`,
`ReadersPat`, `PermInputs` and `Elim`. Both sources were treated as untrusted:
- No upstream scripts were executed.
- Lean files were read but not recompiled. Neither copy has built `PEqualNP` `.olean` files, and
  building the helper chain would have taken a long run.
- The statements and files cited below contain `sorry`, `axiom`, `admit` or `native_decide`
  only inside comments.

So "proved upstream" means a Lean proof term is present and the upstream checker accepts it. It
was not re-checked locally. A local `lean` build is the open follow-up.

Status labels used below:
- **Proved**: a Lean proof is present upstream.
- **Verified**: a computational result, checked here.
- **Experimental**: observed, not proved.
- **Conjecture** or **Open**: as stated.

## 1. Their circuit model and what transfers

The definitions are in `Defs/CircuitLowerBounds.lean` and `Defs/MetaComplexity.lean`.

- A circuit is a straight-line program over AND, OR and NOT gates (MOD and MAJ also exist but
  are excluded by `FanInTwo`). Each gate has at most two inputs.
- AND or OR with 0 inputs is a constant, and with 1 input is a buffer. **Every gate counts,
  NOT included.**
- The output may be an input wire, which gives size 0. A missing wire reads false, so
  constant-false has size 0.
- `HasCircuitSize n f s` means some such circuit with at most `s` gates computes `f`. Dead gates
  are allowed. Minima equal those of our exact-G model: drop dead gates, buffers and constants,
  and every wire is read.

How the bases relate:

| Our basis | Relation to theirs | What transfers |
| --- | --- | --- |
| Corpus `not` (`cube_search`/`synthesis_bench`: ops `and`/`or`/`not` occupy G slots, op 2 counted in `witness.gates`) | **Identical** | Their lower and upper bounds transfer both ways |
| Corpus `mono` (AND/OR) | counted-NOT min ≤ monotone min | Their lower bounds are valid monotone lower bounds. Their monotone constructions (L154) are valid upper bounds in both bases |
| Free-NOT AIG / Percy / XAIG minima | AIG min ≤ counted-NOT min | Their lower bounds do **not** transfer to AIG. Our AIG (and B2) minima **are** valid lower bounds in their model |
| Graph polarity bound in `NOTES_SYNTHESIS_BENCH.md` (binary gates, NOT free) | weaker than counted-NOT | Valid in their model. The converse fails |

**Proved (L112):** `|E|+τ−1` is not a general lower bound. For C4 (our `bipartite-2-2`),
`(x0∨x2)∧(x1∨x3)` uses 3 gates, while `|E|+τ−1 = 5`. Every exact edge-function lower bound
upstream excludes C4 (girth ≥ 7, or forests).

## 2. Priority lemmas

| Row | Statement (paraphrased exactly) | Model | Proof |
| --- | --- | --- | --- |
| **L-meta-107** | Let f depend on some input. Suppose every restriction `f|p=b` at a dependent `p` is nonconstant (`RestrNC`), and no two dependent `p≠q` form a *pair funnel* (∃a,b with `f|p=¬a,q=b = f|p=a,q=¬b = f|p=¬a,q=¬b`). Then any size-`s` circuit gives `f|y=0` with ≤ `s−3` gates or `f|y=1` with ≤ `s−4` gates, for some input y. | counted-NOT | `Helpers.Readers.fanout_step_3_4` |
| **L-meta-204** | Assume girth ≥ 7, distinct degree-≥3 vertices ≥ 7 apart, `A` a set of isolated vertices, (`A`≠∅ or E≠∅), and `k ≤` every vertex cover. Then `(OR A) ∨ f_G` has size ≥ `|A|+|E|+k−1`. | counted-NOT | `EdgeFn.stmtLB_final` |
| **L-clb-041** | For k ≥ 4, every fan-in-2 circuit deciding SAT (CNF-to-binary encoding of `Defs/Search.lean`) at length `4k+2` has ≥ `5k+1` gates. | counted-NOT | `Helpers.SatFive.main` |
| L102 / L106 | Path `P_n`: exactly `n+⌊n/2⌋−2`. Cycle `C_n`, n ≥ 5: exactly `n+⌈n/2⌉−1`. L106 uses L107. | counted-NOT | `PathSize*`, `cyc_exact_of_readers` |
| L104 / L105 / L154 | Forests: ≥ `|E|+τ−1`. Any graph: ≤ `|E|+|T|−1` for a cover T, by a monotone circuit (L154) | counted-NOT / monotone | `ForestElim`, cover circuit |
| L113 / L115 | Under girth ≥ 9 and hubs ≥ 9 apart, some minimum circuit has no NOT. A monotone lower bound holds under girth ≥ 9 and hubs ≥ 7 apart | both | `NotFreeCor`, `Loc*` |
| L100 / L012 / L153 | MAJ3 = 4. OR_n = n−1. `(x∧y)∨g` = `m(g)+2` for nonconstant g (rigid AND term) | counted-NOT | small |

## 3. Reusable infrastructure: their lemmas mapped to ours

| Upstream helper | Content | Our counterpart | Reuse |
| --- | --- | --- | --- |
| `PermInputs.dep_lower_set` | T essential inputs ⇒ `|T| ≤ s+1` | support bound (`support−1`) everywhere | Same statement. A Lean proof we could port into `sat-search/lean/CircuitLemmas` |
| `PermInputs.gate_elim_at` | For dependent `p` with `RestrNC` at `p`, some `b` has `f|p=b` of size ≤ `s−2` | `restriction_excess.py` (excess under restriction) | Lean-proved base case of our restriction step. Our excess identity is the quantitative refinement |
| `PermInputs.fix_many` | Fix a list L in order while T stays essential: `|T| + 2|L| ≤ s+1` | sequential restriction in `restriction_excess.py` | A proof template for any "fix k inputs, keep T essential" argument |
| `Readers.fanout_step` (L107) | An input has two readers, a NOT has two readers, or the first binary gate is a pair funnel. Pays (3,3), (4,2) or (2,4) | `first_gate_bound.py`, `primary_reader_caps.py` | The case split is the counted-NOT analogue of our primary-reader caps. `NoFunnel` is a checkable function property |
| `Readers.Least` normal form, `ReadersPat` | A least circuit has no constants, aliases or dead gates, and no gate reads both `a` and a reader of `a` | exact-G normal form; Lean `CircuitLemmas.Basic` | `ReadersPat` is a symmetry-breaking rule. It is sound for counted-NOT minimum circuits. As a SAT clause it would need a proof in our model before pruning |
| `Elim.gate_elim`, constant propagation | Substituting a constant removes the reading gates | Module contraction (`CircuitLemmas.Module`) | Complementary. Theirs removes gates, ours contracts modules |

**Not reusable as stated:** the AIG versions of L107 and `gate_elim_at`. A Schnorr-style
argument probably goes through with NOT free, but the savings differ and nothing here proves
them. Do not cite L107 for free-NOT sizes.

## 4. Prototype checks

### 4a. Graph-family minima vs. our corpus (`experiments/pequalnp_graph_check.py`)

The script recovers the graph from each complete corpus target that is exactly an edge function.
It then computes `|E|`, `τ`, girth and hub distances, and applies L102/L104/L106/L112/L204. It
also builds and evaluates the L154 star-cover circuit (asserted equal to the target, with gate
count `|E|+τ−1`). Output: [`logs/pequalnp_graph_check.out`](logs/pequalnp_graph_check.out).

- **Verified:** no conflicts. Every theorem lower bound is ≤ our recorded upper bound in both
  bases.
- **Exact rows reproduced:**
  - path-4 = 4 (L102/L104), `generated-06` = 4, `read-once-01` = 3 and `comparator-01` = 3 (forests).
  - C4 (`bipartite-2-2`) = 3 (L112).
  - cycle-5 = 7 (L106).
- **cycle-5 in the `not` basis:** the record says `[7,9]`. L106 proves exactly 7. Our own
  monotone 7-gate witness already gives the upper bound 7, so this independently confirms the
  value rather than adding a new one.
- **Verified upper bounds (L154 construction checked by evaluation):** the monotone and
  NOT-enabled recorded uppers improve as follows.

  | Case | Recorded upper | L154 upper |
  | --- | --- | --- |
  | `graph-03` | 15 | 11 |
  | `petersen-10` | 29 | 20 |
  | `comparator-08` | 22 | 14 |

  Current best lower bounds are 10, 15 and 9 (`first_gate_compare.jsonl`).
- **`graph-02` (verified):** monotone min 8 < `|E|+τ−1` = 9. The cover circuit is not optimal
  once triangles appear.
- The complete, bipartite, Petersen (girth 5) and triangle-containing random graphs are outside
  every upstream exact theorem.
- Upstream fleet work on Petersen-minus-a-vertex (L-meta-1007/1664/1940/2331, ≥ 13–16 gates) is
  in progress. It is not a theorem about `petersen-10`.

### 4b. L107 chained with exact small minima (`experiments/pequalnp_fanout_check.py`)

**Proved upstream (L107):** at `s = m(f)` the input `y` must be dependent. So, under
L107's hypotheses,

    m(f) ≥ min( min_p m(f|p=0) + 3 , min_p m(f|p=1) + 4 ),   p over dependent inputs,

and lower bounds may replace `m` on the right. The script computes the 3-input counted-NOT
minima by set-BFS. It finds 248 of 256 functions at ≤ 7 gates; the rest get bound 8. It then
recurses: `LB_n = max(support−1, L107 bound)`. Output:
[`logs/pequalnp_fanout_check.out`](logs/pequalnp_fanout_check.out), about 10 s.

Verified results:
- **Base-table cross-checks:** the BFS reproduces MAJ3 = 4 (L100), path-4 = 4 (L102), C4 = 3
  (L112) and OR4 = 3 (L012).
- **4-input soundness:** no violations. Of 2374 functions with exact minimum ≤ 5, none has
  `LB_4 > m`. L107's hypotheses hold for 58,838 of 65,536 functions, and the bound beats support
  on 57,026.
- **Corpus, n = 5 and 6:** the chain never exceeds a recorded upper bound. It raises the
  *recorded SAT-interval* lower ends:

  | Case | Recorded lower | Chain lower |
  | --- | --- | --- |
  | parity-5 | 6 | 14 |
  | exactly-2-of-5 | 6 | 11 |
  | exactly-3-of-6 | 6 | 11 |
  | threshold-5-3 | 5 | 8 |
  | threshold-6-4 | 5 | 9 |
  | hypergraph-03 | 5 | 6 |
  | hypergraph-21 | 5 | 6 |
  | comparator-02 | 5 | 6 |

  It does **not** beat our analytical bounds. `first_gate_compare.jsonl` totals are
  parity-5 14, exactly-2-of-5 11, exactly-3-of-6 14, threshold-5-3 9 and threshold-6-4 10. The
  independent agreement on parity-5 = 14 and exactly-2-of-5 = 11 is still a useful cross-check.
  The upstream half of it is a Lean-proved step; ours is the signed first-gate bound.

### 4c. Combining their elimination with our NPN4/Percy minima

**Sound direction (proved by composition):**
- Any minimum computed in a basis at least as strong as counted-NOT (AIG, XAIG, B2) is a valid
  lower bound in their model.
- So Percy-basis minima of the restrictions can feed the right-hand side of 4b, giving
  counted-NOT and monotone lower bounds for 5- and 6-input targets.

**Unsound direction:** Percy minima are not counted-NOT minima. The result is never an AIG lower
bound.

The prototype uses exact counted-NOT 3-input minima instead, because the NPN4 baseline files only
cover the hard and excess-4 classes (`hard_npn4.jsonl`, `npn4_excess4.jsonl`), not all 222
classes. **Open:** a full NPN4 counted-NOT table, either one SAT run per class or BFS with NPN
canonicalisation. It would make `LB_5` exact-based instead of recursive, and could lift the
hypergraph and comparator rows.

## 5. L-clb-041: encoding, proof, and where our tools could add gates

**Encoding** (`Defs/Search.lean`, `Helpers/SatFive.lean`):
- A literal `(i,b)` is encoded as `[1,b]`, then the bits of `i` as `[1,d]` pairs, then `[0,1]`.
- A clause is its literals followed by `[0,0]`.
- At length `4k+2` the standard string is `[1,α_r,0,1]` for r < k, followed by `[0,0]`. This is
  one clause of `k` copies of `x0` with polarities α.

This is a circuit lower bound for the *language* SAT. It is not a SAT-solver encoding, and it
has no connection to our CNF synthesis encodings.

**Proof** (`SatFiveMain.main`):
1. `fix_many` fixes the positions `4r+1` (r < k) in order. Each step saves 2 gates through
   `gate_elim_at`. The witnesses condA (r ≥ 1) and condA0 (r = 0) show that each position is
   still essential after the earlier ones are fixed.
2. The other `3k+2` positions remain essential (condC). `dep_lower_set` adds `3k+1`.
3. Total: `2k + 3k + 1 = 5k+1`. Asymptotically this is about `1.25·N` at `N = 4k+2`.

**Strengthening assessment:**
- **Reader caps / L107 (3 or 4 per step instead of 2): Open, and not direct.** L107 chooses the
  input y existentially, while `fix_many` needs a planned sequence whose survivors stay essential
  after every adversarial choice. It also needs `NoFunnel` on each intermediate slice.
  Adjacent block positions of the encoding (`[1,α,0,1]`) look funnel-prone. Bounded exhaustive
  slicing for k = 4 (N = 18) could test this, but it has not been done.
- **Excess identity / first-gate bounds on the residual: plausible +1, Conjecture.** Size
  exactly `|T|−1` with every gate counted forces a monotone read-once AND/OR formula of positive
  literals. If the residual slice is not positive-unate in some essential variable, an
  `excess ≥ 1` step adds one gate, giving `5k+2`. Proving a linear gain would need our excess or
  first-gate argument written for an unbounded family. Our current tools are computational, for
  n ≤ 10.
- **Regional decomposition (`NOTES_SIGNED_MODULES.md`): not applicable.** The SAT slice has no
  small read-once regions that would make module contraction bite. The regions span the whole
  string.

## 6. Proposals

1. **Port `dep_lower_set`, `gate_elim_at` and `fix_many`** into `sat-search/lean/CircuitLemmas`
   under our exact-G model. They give a Lean-checked base for `restriction_excess.py`. Small
   effort, since the helper chain is self-contained apart from `Defs`.
2. **Full counted-NOT NPN4 table**, then exact-based L107 chaining for all complete 5–6-input
   corpus targets. Compare against `first_gate_compare.jsonl`. Keep it only if it raises a best
   bound.
3. **`NoFunnel` as a pre-filter for first-gate enumeration.** For funnel-free targets, L107's case
   split certifies that the first binary gate is not a pair funnel. That is a sound restriction
   on first gates in counted-NOT. It is not valid for free-NOT search.
4. **L154 as a default upper-bound seed**: done 2026-11-25, see §7.

## 7. L154 seed integration (2026-11-25)

`cube_search.cover_circuit(n, edges)` builds the star-cover circuit from a minimum vertex cover.
Each star is processed greedily by remaining degree and the smallest result over all minimum
covers is kept. The circuit is checked on every row and gives at most `|E|+τ−1` gates. It is
monotone, so it is a valid upper bound in the mono, counted-NOT and free-NOT bases.

- **`synthesis_bench.run_case`** (default; `--no-cover-seed` reproduces earlier runs). For a
  complete graph edge function, the initial upper bound is the smaller of the corpus witness
  and the cover circuit, and a `kind='seed'` record carries the cover witness. The cover circuit
  is checked again against the case with `synthesis_cases.truth_table`. Over the 19 graph cases,
  the seed is below the corpus witness for 11: graph-01 11→8, graph-02 13→9, graph-03 15→11,
  path-4 5→4, cycle-5 9→7, petersen-10 29→20, random-monotone-06 7→5, generated-06 15→4,
  comparator-01 11→3, comparator-08 29→14. Complete and bipartite graphs keep their corpus
  witnesses, which are smaller. End-to-end, path-4 and cycle-5 start from 4 and 7 and finish
  as exactly 4 and 7 in both bases (1 s caps).
- **`cube_search` CLI.** It logs the verified cover bound U.
  - **Size = U:** prints the cover circuit as the WITNESS without searching.
  - **Size > U:** prints `RESULT: SKIPPED` with no search.
  - `--no-cover-skip` turns this off and is not a pruning rule (`NON_RULE_OPTIONS`).
  - Runs with `--manifest` always search.
  - `verify/cli_differential.py` and `verify/test_manifest.py` pass `--no-cover-skip`, so they
    still exercise the SAT side.
  - `test_manifest`, `test_rulesets` and `test_imports` pass.
- **Native C++ (`native/src`): no change, deliberately.**
  - Every native entry point is a fixed-budget decision procedure. `solve_blocks` and
    `solve_completion` take one region with given provider counts. `tight_residual`,
    `slack_one_extensions`, `directed_completion` and `slack_two_boundary` take one prefix
    with a given slack. None takes a starting upper bound.
  - A bound on the whole function cannot prune inside one fixed-budget decision. It only
    decides which budgets a driver asks about, and the drivers (ascending excess ladders,
    cube sizes) are Python.
  - Ascending ladders stop at the first SAT anyway, so the bound saves work only at sizes ≥ U
    (now skipped in `cube_search`), or by capping an open-ended ascent such as the hybrid
    driver's `run_ours_sat` loop up to `kmax`.

Reproduce:

```
python -I sat-search/experiments/pequalnp_graph_check.py
python -I sat-search/experiments/pequalnp_fanout_check.py --cap 7 --cap4 5
```
