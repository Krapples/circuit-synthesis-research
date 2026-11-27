# Explicit circuit lower bounds for the pequalnp SAT encoding: proof review (2026-11-25)

This note reviews ChatGPT's six-bit fragment and even-length notes, which were supplied as
`sat_six_bit_fragments_notes.md` and `sat_even_length_bound_notes.md` in Downloads and are not
committed. It is a paper review plus finite checks: **not Lean-checked as a whole, and no novelty claim.**
Lean status (2026-11-26): claims 4, 5 and 6 are formally checked; see "Lean formalization".
The external project was read at open-goat/pequalnp-proofs `d9f1ea2` (2026-11-25).

## Model and target

- **Language.** `PEqualNP.Search.SAT = {x | ∃φ, encodeCNF φ = x ∧ Satisfiable φ}` (`Defs/Search.lean`).
  - A literal `(v, b)` encodes as `[1,b] ++ flatMap (d ↦ [1,d]) (Nat.bits v) ++ [0,1]`.
  - A clause is its literals followed by `[0,0]`.
  - `Nat.bits` is least significant bit first, with no trailing zero, and `bits 0 = []`. `b = true` is
    positive.
- **Basis of the claims.** Fan-in-two AND/OR with free negations: the binary AIG gate count `B`, which
  is the Percy basis used throughout this repository.
- **Lean circuit model.** `Defs/CircuitLowerBounds.lean`, as restricted in L039/L041: AND/OR/NOT with
  fan-in at most 2, where size counts every gate, NOTs included.
  - Unary and nullary gates, repeated inputs and missing wires are all at most free in the AIG.
  - So a Lean circuit has at least `B` gates, and a lower bound on `B` transfers to the Lean `D.size`.
  - The converse transfer is not valid.
- **External results.** L041 is `D.size >= 5k+1` at `n = 4k+2`, about `5n/4` in the counted model. It is
  proved with repeated two-gate elimination (`PermInputs.fix_many`) and `dep_lower_set`.
- **Comparison.** If the review below holds, `B >= floor(4n/3) - 3` would also give
  `D.size >= floor(4n/3) - 3`. That beats L041's coefficient asymptotically on even `n`. This needs the
  external project's own review before it is stated anywhere as an improvement; L-clb-036 is open
  there.

## Claims and review verdicts

| # | Claim | Verdict |
| --- | --- | --- |
| 1 | `SAT(T(x1,y1)...T(xq,yq) 110100) = AND_i (xi XNOR yi)`, where `T(x,y) = 11x10y` | **Proved** (paper), and checked exhaustively through q=6 with an independently written decoder. |
| 2 | First-gate lemma: no pair funnel implies a repeated operand at the earliest gate | **Proved** (paper). The funnel test on F_q and the tails is checked finitely. |
| 3 | The absorbing restriction of a repeated earliest operand removes at least 3 gates | **Proved** (paper). The two-reader case is handled by the canalizing replacement; see below. |
| 4 | Independent literal extension: `C(g AND z) >= C(g) + 1` for nonconstant g | **Proved** (paper, standard). **Formally checked** in Lean for the repository's free-NOT model (`literal_extension`; see below). |
| 5 | `C(F_q) = 4q - 1` | **Proved** from 2-4. **Formally checked** in Lean (`xnorConj_lower`, 2026-11-26), with a direct proof that needs no canalizing replacement. Percy reports C(F_2) = 7 (UNSAT at 6, SAT at 7; solver-reported, not certified). |
| 6 | Excess monotonicity: `B >= n - m + C(f restricted)` for coordinate restrictions | **Proved** (paper). **Formally checked** in Lean (`excess_restriction`, 2026-11-26) by a counting proof in place of graph minors. The cycle rank `B - n + 1` of a trimmed connected circuit cannot increase under deletion or contraction. Not valid for identifications. |
| 7 | Full essential support of `SAT_n` | **Checked** for every even n from 12 to 60 except 14, using the witnesses in the notes (the n=16 certificate included). L037 proves the n=6q case in Lean. |
| 8 | Mux tail: `C(F_q AND mux) = 4q + 3` | **Proved** (paper). Percy reports C(F_1 AND mux) = 7. |
| 9 | Three-input tails, cases (a) and (b): `C(F_q AND g) >= 4q + 4` | **Proved** (paper). Percy reports C(F_1 AND g) = 8 for all four strong cofactors of H. |
| 10 | 14-bit tail H = 0xe8f2: `C(F_q AND H) >= 4q + 6` | **Proved** (paper); the premises are checked. Percy reports C(H) = 7, so the bound is not tight at q=0. |
| 11 | `B >= floor(4n/3) - 3` for every even n >= 16 (n=6k: `8k-3`; n=6k+2 and 6k+4: `n+2k-2`) | **Follows** from 5-10; the arithmetic is checked for even n from 16 to 2000. Conditional on this review. |

### Points checked in detail

- **Item 1, decoder states.**
  - Each valid fragment starts and ends with an empty digit run.
  - `T(0,1)` emits `01` with no digits, and `T(1,0)` closes a clause with digits pending. Both errors
    occur whatever the incoming clause is.
  - Every literal is positive, so all-true satisfies every legal instance.
- **Item 3, two readers g and h.**
  - With x set to g's absorbing value, g is constant. A third reader of g would degenerate, giving
    three gates.
  - g cannot be the output, since h is live and g's cone is `{x, b}`.
  - Otherwise `h = op(x, g(x, b))` is a function of `(x, b)` that is constant at the absorbing x. So it
    is canalizing, and one gate (or none) computes it, contradicting minimality.
  - Distinct fanins rule out h reading g twice.
- **Item 6, minors.** The restriction acts on the circuit graph through minor operations:
  - constant inputs are deleted;
  - alias gates contract one edge and delete the other;
  - dead cones are deleted;
  - remaining irrelevant inputs are fixed and the simplification repeated.

  Each step leaves `E - V + c` unchanged or lowers it. The final trimmed circuit reads exactly the m
  essential inputs and is connected.
- **Items 8-10, induction.**
  - A repeated XNOR operand gives `3 + 1 + C(F_{q-1} AND tail)`.
  - A repeated tail operand gives 3 gates (absorbing) or 2 gates (any constant, for H's strong
    cofactors). The rest follows from the excess inequality `C(F_q AND g) >= 4q - 1 + m_g`.
  - Every cofactor used is nonconstant, so the excess inequality applies.
  - Case (a) fixes the third input of g, which gives `F_{q+1}` up to an input complement.
- **Tail safety after an open positive clause.**
  - The mux tail `11zy1x0100` and the 14-bit tail `11u1zyx1110100` were checked after random legal
    prefixes that end in an open positive clause (300 per tail).
  - The notes' regression (`100100 110100` is unsatisfiable) was reproduced. The 12-bit gadget must not
    be used as an open-clause tail.

### Gaps and caveats

- **Model scope.** Every statement is for the free-NOT binary count. It is not a counted-NOT AIG
  statement and not a statement about other encodings.
- **Composition search.** `sat_gadget_composition.py --search` was not run; Addendum 2 deprioritized
  further exhaustive searches.
- **Additive weights.** The additive-weight theorem `C(AND f_j) >= sum w(f_j) - 1` was reviewed on paper on
  2026-11-26 (see "Additive weight theorem" below). It is not Lean-checked. The six-bit route does not need it.
- **Lean status.**
  - The external Lean library has string-witness infrastructure: `SatSlice`, `SatFive`, and L037 for
    full support at 6q.
  - It has two-gate elimination: `gate_elim_two` and `fix_many`, together with the connectivity bound
    `dep_lower_set`.
  - It has no three-gate absorbing elimination, no free-NOT binary-gate count and no cycle-rank excess
    lemma.
  - The repository's own Lean project now has a free-NOT binary model with gate deletion, restriction and
    literal extension (see the Lean formalization section below).
- **Formalizing would need:**
  1. a binary-gate count on `Circuit` and its comparison with `size`;
  2. constant folding and trimming with gate accounting;
  3. the first-gate funnel lemma and the canalizing replacement;
  4. the graph-minor cycle-rank argument, or a direct inductive replacement for it;
  5. the string identities, which are close to the existing `SatFive` witnesses.

  Items 1-4 are reusable for any gate-elimination bound.

### Lean formalization (started 2026-11-25)

`sat-search/lean/CircuitLemmas/GateElim.lean` is in the repository's own Lean project (Mathlib through
the existing junction, so nothing was downloaded). It defines its own free-NOT binary model:
- AND gates on literals, where a literal is a constant or a wire with a complement flag;
- size = number of binary gates, i.e. `B`;
- no well-formedness side condition, since a missing wire reads `false`.

It does not use the external project's `Circuit`. Comparing the two models (item 1 above) is still open.

**Formally checked** (`lake build`; `AxiomsCheck.lean` shows only `propext`, `Classical.choice` and
`Quot.sound`):

| Theorem | Statement |
| --- | --- |
| `bypass`, `deleteGate_eval` | A gate equal to a literal over earlier wires on every input can be deleted: one gate fewer, same function. |
| `delete_dead` | A gate that no later gate and not the output reads can be deleted. |
| `bypass_many` | All degenerate gates (`degCount`) can be deleted together. The latest is deleted first, so earlier prefixes stay unchanged. |
| `Circuit.eval_restrict`, `realizes_restrict` | Fixing an input to a constant gives a circuit of the same size, so restriction never increases complexity. |
| `restrict_eliminates` | Fixing input `z` deletes every gate that reads `z`: `size' + readers z ≤ size`. |
| `literal_extension` | If `g` is nonconstant and ignores `z`, a circuit for `g ∧ x_z` of size `s` gives one for `g` of size `s - 1`. This is claim 4 of the table. |
| `literal_extension_phase` (XnorConj.lean) | The same for `g ∧ (x_z == c)`, either phase. |
| `xnorConj_lower`, `xnorConj_std_lower` (XnorConj.lean) | Every circuit for the AND of `x_a == x_b` over `q` disjoint pairs has at least `4q - 1` gates. With pairs `(2j, 2j+1)` this is `C(F_q) >= 4q - 1` (claim 5). |
| `card_le_degCount`, `excess_restriction` (Excess.lean) | If every input of `F` is essential for `f` and `f` with `F` fixed is nonconstant, then `C(f restricted) <= C(f) - |F|`. This is claim 6 in the form the SAT argument uses (`|F| = n - m`). |
| `xnorConj_restriction_lower` (Composition.lean) | If fixing a set `F` of essential inputs leaves the XNOR conjunction of `q >= 1` disjoint pairs, then `C(f) >= |F| + 4q - 1`. With the six-bit fragments (`|F| = 4q + 6` at `n = 6q + 6`) this is the `8q + 5` step of claim 11, given the string identity and full support. |
| `three_step`, `potential_lower`, `potential_restriction_lower` (Robust.lean) | Strong pair sensitivity on a set `S` (for distinct `u, v` in `S` and either value of `x_u`, `x_v` still matters) gives `C(f) >= 3 + C(f|x_z=c)` for some `z` in `S`. A potential that drops by at most one per such restriction then gives `C >= 3*mu`, or `C(f) >= |F| + 3*mu` after an essential restriction. |
| `block_product_lower`, `block_restriction_lower` (BlockProduct.lean) | If `f` is the AND of `k` functions on disjoint blocks `V_j`, each `PS_d` (Strong on the free inputs under every partial assignment leaving at least `d >= 2` of them free) and each with `|V_j| >= d`, then `C(f) >= 3 * sum_j (|V_j| - d + 1)`, and `C(f) >= |F| + 3 * sum_j (|V_j| - d + 1)` when an essential restriction of `F` leaves that product. Non-vacuity check: parity on `r` inputs is `PS_2`, giving `3(r-1)`, which is tight. |
| `transfer` (SatBridge/Transfer.lean) | Model transfer. Any external `PEqualNP.CircuitLowerBounds.Circuit` whose gates are and/or/not with at most two inputs compiles into a GateElim circuit for the same function on `n` inputs, with at most `C.size` AND gates. NOTs become free negations, and `or` becomes a negated AND of negations. Lower bounds in the free-NOT model therefore bound the external counted size. |
| `word_mem_sat` (SatBridge/SixBit.lean) | String identity (claim 1) for the external `SAT` and `encodeCNF`: `T(x1,y1)...T(xq,yq) 110100 ∈ SAT ↔ ∀ j, xj = yj`. A bad block sends the external `wfD` acceptor to its dead state (`foldl_cnf`, `foldl_dead`). An all-good word is the encoding of an explicit positive CNF, which the all-true assignment satisfies. |
| `sat_six_lower`, `sat_six_lower'`, `sat_not_size_133` (SatBridge/SixQ.lean) | **End-to-end bound at `n = 6Q`, `Q >= 2`:** every external circuit with and/or/not gates of fan-in at most 2 that decides `SAT` on length `6Q` has `size >= 8Q - 3 = 4n/3 - 3`. Full support comes from the external L037, and the restriction step from `xnorConj_restriction_lower` with `|F| = 4Q + 2`. Corollary: no `SIZE s` with `100 s(n) <= 133 n + c` contains `SAT`. This is an internal check: the slope beats L041's 5/4, but only on lengths divisible by six. |

**XNOR proof (audited 2026-11-26).** Strong induction on circuit size, then on `q`. A degenerate first
gate, a first gate on an input outside the pairs, or a dead first gate gives a smaller circuit. Otherwise
the first gate `g0 = l_u ∧ l_v` reads two distinct pair inputs. Each of `u, v` has a second reader: if
not, fixing `x_u` to make `l_u` false would make the circuit ignore `x_v`. For the same reason `g0` is not
the output. One gate cannot read the three wires `u, v, g0`, so some `z ∈ {u, v}` has two distinct later
gates reading `z` or `g0`. Fixing `x_z` to make `l_z` false deletes `g0` and those two gates. The rest is
`F_{q-1} ∧ (x_z' == c)`, and the literal costs one more gate. The two-reader case of claim 3 never arises,
so the canalizing replacement is not needed.

**Excess proof (audited 2026-11-26).** Take a circuit of minimum size and call a wire constant if its
value does not depend on the free inputs once `F` is fixed. Every input of `F` is read by some gate:
it is essential, and the output reading it directly would make the restriction constant. Every constant
gate has a later reader: there are no dead gates, and the output is not constant. So at least
`|F| + #constant gates` distinct constant wires are read. A constant gate has at most two constant
operand slots, and a nonconstant gate at most one, since two would make it constant. So
`|F| <= #gates with a constant operand or value`. All of these are degenerate after the restriction, and
`bypass_many` deletes them. This is stronger than the per-input count: it needs no assumption about inputs
that become irrelevant. Both hypotheses are needed: `f = y ∧ z` with `y = 0` fixed has `C(f) = 1 < 2`,
and it is excluded only because the restriction is constant. **Finite check:**
`experiments/excess_restriction_check.py` takes every 4-input function and every restriction of essential
inputs with a nonconstant result, using the exact NPN sizes in `results/sat_gadget/npn4_exact_aig_all.json`:
2,920,992 cases, 0 violations, 0 undecided (`logs/excess_restriction_check.out`).

**Verification status.** `lake build` passes (18,268 jobs, with Robust.lean and BlockProduct.lean, 2026-11-26). `lake build SatBridge` passes (18,471 jobs) and `SatBridgeAxioms.lean` reports only the same three axioms for the five SatBridge theorems. `SatBridge` is not a default target: it requires the external pequalnp checkout at `external/pequalnp-proofs-open-goat/lean` (local path require, pinned commit d9f1ea23, same Mathlib revision). `AxiomsCheck.lean` reports only `propext`,
`Classical.choice` and `Quot.sound` for every theorem above. There is no `sorry` and no `native_decide`.
The new files have no string literals, no `#` commands and no `set_option`. They do define their own types
(the GateElim model), so external submission would need a model transfer and human review (below).

**Not formalized yet** (remaining gaps, 2026-11-26):
- done 2026-11-26 (SatBridge): the string identity, the model transfer, and claim 11 at `n = 6Q` (full
  support from external L037);
- full support of `SAT_n` for even `n` not divisible by six (claim 7). L037 covers only `n = 6q`;
- the tails for `n = 6k+2, 6k+4` (claims 8-10). Each is an induction like `xnorConj_lower`, with a tail
  factor in place of the last pair. These were deferred deliberately (README(8));
- 17n/12: the additive-weight theorem `C(AND f_j) >= sum w(f_j) - 1`, the four block weights (6/8/10/12),
  the 11-state mixed-block certificate and the padding lemma. README(8) clarifies that the recursive
  weights use only nonzero tables, trimming, literal factors, cofactors and signed-AND module quotients.
  They need no exact circuit minima and no Percy UNSAT certificates, so the finite weights can be checked
  by direct truth-table evaluation in the kernel.

- the 2n-o(n) route is now checked at lengths divisible by six. The other even residues still
  need a full-support theorem. See the robust identifier section for the checked finite loss.

The claim-2/3 route (funnel lemma, absorbing elimination, canalizing replacement) is no longer needed for
claim 5. The tails still need their own case analysis.

The additive-weight theorem stays separate until it has its own full review.

## Exact-size gadget study (2026-11-26)

Script: `experiments/sat_gadget_exact.py`. Record: `results/sat_gadget/blocks_l14.jsonl`. Exact minima per NPN class
are cached in `results/sat_gadget/npn4_exact_aig.json`.

**Accounting.** A coordinate restriction with m essential free bits gives `B(SAT_n) >= n - m + C(restriction)`
(cycle-rank excess, reviewed above; it needs full support of SAT_n). Suppose a block B(z) of length L with tail t satisfies

* `SAT(B(z_1) ... B(z_q) t) = AND_i f(z_i)`, and
* `C(AND_i f(z_i)) = q (C(f) + 1) - 1`.

Then the coefficient is `1 + e / L`, where `e = C(f) + 1 - m`. Check: T = `11x10y` gives f = XNOR, C = 3, e = 2, coefficient 4/3.

**Search.**

* Every block of length L <= 14 with 2..4 free coordinates (all other bits fixed), each with tails `''`, `00` and `110100`.
* f must depend on all m free bits. This gives 2,903 distinct (L, tail, f) blocks in 66 NPN classes.
* C(f) is exact for every class: a Percy cone+cond ladder below the cofactor library witness, extended tier, no open budget. The search takes 8 s.

**Composition proof for all q.** `induction_certificate` models the decoder as a finite automaton at token
boundaries. The state records the phase, whether the last index digit is 0, whether the clause is nonempty, whether it already has a positive literal, and the polarity of the current literal. The certificate requires, over all states R reachable at block boundaries:

* acceptance of each block value does not depend on the state, and equals f;
* every clause that closes has a positive literal (so the all-true assignment satisfies every valid word, and empty clauses are definite rejects);
* the tail reaches the accepting state from every state in R.

Induction on q then gives the identity for every q. The automaton agrees with the reviewed parser on all 21,845
words of at most 14 bits (`automaton_selftest`). The certificate is sound but incomplete: some blocks pass the
exhaustive q = 2, 3 checks but not the certificate.

**Result: block `11abcd` with tail `110100`.**

* f = `e8e4` (NPN class `036f`); 8 of 16 values accept. Exact C(f) = 7, so e = 4 and e/L = **2/3**.
* The composition identity is proved for every q by the certificate and also checked exhaustively for q = 2 and 3.
* T is its sub-restriction b = 1, c = 0. The earlier sparse searches fixed the final token, so they could not see it.
* If additivity held, i.e. C(AND of q copies) = 8q - 1, the bound would be `B(SAT_{6q+6}) >= 10q + 5`, about **5n/3**, compared with 4n/3 now and L041's 5n/4.

| Block | Tail | m | f | C | e/L | All-q certificate |
| --- | --- | ---: | --- | ---: | ---: | --- |
| `11abcd` | `110100` | 4 | e8e4 | 7 | 0.667 | yes |
| `10abc10d` | `110100` | 4 | e008 | 7 | 0.5 | no (all-negative clause); q=2,3 exhaustive yes |
| `11a1b0c10d` | `110100` | 4 | d004 | 7 | 0.4 | yes |
| `11a10b` (T) | `110100` | 2 | 9 (XNOR) | 3 | 0.333 | yes |

**Open obligation (the decisive one).** The lower bound `C(AND_q e8e4) >= 8q - 1`, or anything above 6q - 3,
is what beats 4n/3. Using the T sub-restriction only gives 4q - 1.

* A probe of mixed additivity, `C(e8e4(x0..x3) AND XNOR(x4,x5))`, would be 11 if additive. Percy in base mode (first-layer options support at most 5 inputs) proves k <= 8 UNSAT (k=8: 1.32M conflicts) and times out at k=9. So 9 <= C <= 11 is open (`logs/sat_gadget_probe_e8e4_xnor.out`).
* A proof would need a gate-elimination argument for e8e4 in the style of the F_q proof (absorbing elimination plus literal extension), or the additive-weight theorem with w(e8e4) = 8. That is theory work.
* Full support of SAT_n at lengths 6q + 6 is the existing 6k witness.

**Scope.** Free-NOT AIG count, which lower-bounds the Lean counted size. Every coefficient above is a candidate
until the additivity is proved. No novelty claim.

Reproduce: `python -B sat-search/experiments/sat_gadget_exact.py OUT.jsonl --max-len 14 --top 300`.

## Additive weight theorem and B(SAT_(12q+6)) >= 17q+5 (handoff 2026-11-26, reviewed)

**Status.**
- Paper proof: reviewed here, no gap found.
- Finite premises: reproduced independently.
- Not Lean-checked. Not a 5n/3 bound. No novelty claim.
- It does not claim `w(f) = C(f) + 1`, and it does not settle exact additivity for e8e4.

**Weight.** Define w on nonzero functions after removing inessential inputs (reference implementation:
`experiments/additive_sat_weight.py`, the handoff code verbatim):
- w(1) = 0, and w(literal) = 1.
- If some cofactor f|x_i=1-a is 0 (a literal factor), w(f) = 1 + w(f|x_i=a).
- Otherwise w(f) is the minimum of:
  - `max(3 + w(f|x_i=1-a), 2 + w(f|x_i=a))` over i and a, and
  - `1 + w(g)` over signed-AND modules f = g([x_i=a] AND [x_j=b], rest).

**Theorem.** For nonzero factors f_1..f_k on pairwise disjoint input sets (all inputs essential),
the free-NOT AIG count satisfies `C(AND_j f_j) >= sum_j w(f_j) - 1`.

**Proof review.** The proof is strong induction on the number of essential inputs, followed by a case
split on a first gate h = [x_i=a] AND [x_j=b] of a minimum circuit. Literal factors are peeled first,
which costs one gate each, using literal extension.

- **(A) i and j are read only by h, and lie in the same factor.**
  - h is a two-input function of the two inputs, with no other reader.
  - Replacing h by a fresh input y gives a circuit for the product with f_t replaced by its quotient g.
  - Such a quotient exists exactly when f_t factors through h. The fibre condition is that the three rows
    other than (a,b) of each slice agree.
  - It has one fewer gate. The induction gives `C >= 1 + (sum - w(f_t) + w(g)) - 1`, which matches the module term.
- **(B) i and j are read only by h, but lie in different factors.**
  - Fixing x_i to its absorbing value 1-a makes h = 0.
  - After that, x_j is read by nothing, yet x_j is essential in its own factor. Factor values on disjoint
    inputs are independent and every factor is nonzero, so x_j is essential in the product.
  - This is a contradiction, so the case cannot occur.
- **(C) one of i and j (say i) has a second reader.**
  - Neutral value x_i = a: h becomes the literal [x_j=b], and the second reader of x_i folds, which removes
    two gates. The remaining product has f_t replaced by f_t|x_i=a.
  - Absorbing value x_i = 1-a: h = 0 and the other reader folds. A third gate is removed through h's
    successor, which receives a constant.
  - If h's successor is the other reader itself, or the output, the canalizing replacement applies. Then
    f = [x_i=a] AND ..., which is a literal factor and was already peeled, or the circuit was not minimum.
  - I checked this replacement in the minimum-circuit setting: the successor of a constant-0 input is
    constant 0 or an alias, so a third distinct gate disappears unless the circuit had a removable gate.
  - This gives the R(f,i,a) term `max(3 + ..., 2 + ...)`: the bound must hold for both values, so the
    better of the two lower bounds cannot be used.
- **Restriction and accounting.** These follow the reviewed `restrict_eliminates` and `literal_extension`
  pattern from the three-gate absorbing elimination above. Cross-factor first gates need no gate separation,
  because case (C) restricts only the one factor containing x_i.

**Bound.**
- Block `11a1bcd1efg1` with tail `110100` gives f = `0xedc4ed00edc400c4edc4000000c40000` on 7 inputs (a is
  bit 0). Every input is essential, w(f) = 12, and there is no top-level signed-AND module.
- For q copies: n = 12q+6, m = 7q, and L037 gives full support because n = 6(2q+1).
- The excess inequality (reviewed above) and the theorem give

  `B(SAT_(12q+6)) >= (12q+6 - 7q) + (12q - 1) = 17q + 5`,

  compared with the previous `floor(4n/3) - 3 = 16q + 5` at the same n. The coefficient is 17/12, about
  1.417n. It transfers to the Lean counted size in the lower-bound direction only.
- Smaller block `11a1bcd1` with f = `edc4` and w = 7 has coefficient 11/8 on 8q+6. It needs full support, which
  L037 gives only when 8q+6 is a multiple of 6, i.e. q divisible by 3.
- Block `11abcd` (e8e4) has w = 6, not 8, so this method gives only 4n/3 for it. That does not show additivity
  fails, only that this method is weaker there.
- Consistency: w(e8e4) + w(XNOR) - 1 = 9 agrees with the open probe range 9 <= C(e8e4 AND XNOR) <= 11.
- The handoff's bounded template search (L = 6..12) reports best (w-m)/L of 1/3, 3/8, 3/10 and 5/12. That is
  the best in that search, not a universal optimum. It was not rerun here.

**Independent finite checks** (`experiments/additive_weight_check.py`, log `logs/additive_weight_check.out`):

- Recurrence agreement: the handoff `weight` matches an independent tuple recurrence on 1,177 functions. These are all nonzero tables on 1..3 inputs plus seeded 4..6-input samples and the gadgets.
- `w - 1 <= C` on all 65,535 nonzero 4-input functions (max gap 0, 6,422 tight). Each C or lower bound comes from one of two sources:
  - native exact <=4 projection (3,589 functions, exact or excluded with w-1 <= 5);
  - the per-NPN-class Percy exact-AIG ladder `results/sat_gadget/npn4_exact_aig_all.json` (61,946 functions). Classes 1681 and 1683 timed out at budgets 10 and 9. Every smaller budget is UNSAT, so those budgets serve only as lower bounds.
- Products of two disjoint factors: of 151,928 queries, 9,459 hit an exactly known C, all tight with the theorem. The other 142,469 were excluded as unknown, with no claim made.
- 20,784 composition-certificate transitions were rechecked, and both gadget certificates reproduce (7 states; 112 and 896 transitions).
- Solver verdicts above are maplechrono/Percy UNSAT, not checked proofs. They support the finite premises only. The structural induction is the paper argument.

**Lean.**
- Not formalized.
- Reusable pieces: `restrict_eliminates`, `literal_extension` and `bypass_many` in
  `sat-search/lean/CircuitLemmas/GateElim.lean`.
- New obligations:
  - first-gate accounting for cases A-C, including the canalizing replacement;
  - the module quotient;
  - induction over disjoint factors;
  - the excess inequality (cycle rank), which is still unformalized for the six-bit route too.

Reproduce:

```powershell
python -I sat-search/experiments/additive_sat_weight.py
python -I sat-search/experiments/additive_weight_check.py --exact4-exe sat-search/native/preduce_check.exe
```

## Every even length: B(SAT_n) >= floor(17n/12) - 4 for even n >= 16 (handoff README(3), reviewed 2026-11-26)

**Status:**
- This is a paper consequence of the additive-weight theorem and the cycle-rank excess inequality.
- Its finite premises were reproduced here. It is not Lean-checked.
- It is not a new leading coefficient and makes no novelty claim. 5/3 additivity stays open.
- It drops the restriction to lengths 12q+6. That residue keeps the sharper 17q+5.

**Mixed blocks.** All four templates share the tail `110100`:

| L | template | m | truth table | weight | w-m |
|---:|---|---:|---|---:|---:|
| 6 | `11a10b` | 2 | `9` | 4 | 2 |
| 8 | `11a1bcd1` | 4 | `edc4` | 7 | 3 |
| 10 | `11abcde1fg` | 7 | `e8e4e040...` | 10 | 3 |
| 12 | `11a1bcd1efg1` | 7 | `edc4ed00...` | 12 | 5 |

- Separate per-block certificates do not imply that mixed sequences compose. The joint certificate closes the reachable boundary states under all four types at once: 11 states, 3,036 transitions and 11 tail checks.
- Reviewed: each transition is either a definite rejection, exactly when the table entry is 0, or a move to a certified state. No transition is UNCERTIFIED, and the tail returns every state to START.
- By induction on the block sequence, any finite sequence of blocks with independent free bits plus the tail decides exactly the AND of the block functions.

**Full support at every even n >= 16.** Write U = `100100`, the clause (not x0).
- Base witnesses at lengths 12, 16 and 20 cover every position i with SAT(w) = SAT(wU) = 1 and SAT(flip(w,i)) = SAT(flip(w,i)U) = 0.
- Padding lemma, reviewed:
  - A complete prefix U resets the parser. It cannot repair a syntax error, and it only adds a clause.
  - A word ending in token `00` is either complete or already irreparably malformed. So when flip(w,i)U is rejected, appending more U's keeps it rejected.
  - Acceptance with x0 = 0 survives any padding.
- Choose b = 12, 20 or 16 for n mod 6 = 0, 2 or 4. Then the windows U^p w U^(k-p) cover all n positions, so every input is essential.
- Audit:
  - My first exhaustive check dropped the hypothesis SAT(w) = 1 and found 30 "violations". Each was an incomplete w whose open clause U completes, so the hypothesis is needed.
  - With the stated hypotheses, all 87,381 even words of length <= 16 satisfy three properties: prefix monotonicity, the 00-suffix property and acceptance padding.

**Arithmetic.** Let n = 12k+r. Use k-1 twelve-bit blocks (k when r = 6) plus the extras 6 / 8 / 10 / none / 6,8 / 8,8. This gives bounds 17k-4 / 17k-1 / 17k+1 / 17k+5 / 17k+7 / 17k+10, so B >= floor(17n/12)-4. That is at least floor(4n/3)-3 throughout, and strictly greater for n >= 18. I re-derived the table independently for n < 200, and the script checks it for n <= 10,000.

**Checks** (`experiments/mixed_sat_bound.py`, handoff reference): all PASS.
- 3,036 transitions;
- 212 base checks;
- 3,604 padded sensitivities (n = 16..120);
- 76,176 block pairs, checked against an independent token parser plus a SAT evaluator;
- 5,000 seeded mixed sequences.

**Lean obligations** beyond those of the 12q+6 route (none formalized as of 2026-11-26; the excess
inequality they rely on is now `excess_restriction`):
- a mixed-block automaton induction;
- the padding lemma over the `wfD` automaton or parser;
- an even-n full-support theorem replacing L037's 6q.

Reproduce: `python -I sat-search/experiments/mixed_sat_bound.py`.

## Robust identifier tests: B(SAT_n) >= 2n - O(n log log n / log n) (README(7), reviewed 2026-11-26)

**Construction (README(7) section "robust identifier tests").** Take `g` on `r` inputs with the
following robustness property: under every restriction that leaves `>= d` inputs free, the four cofactors
on any free pair are distinct. Fixed negative unit clauses `U(2^r + a, false)` for the `h <= 2^r` zeros of
`g` are followed by `q` positive unit clauses `U(2^r + x_j, true)` with `r` free identifier bits each. Each
word is `L = 2r + 8` bits. The SAT value is then `AND_j g(x_j)`, and padding uses unit clauses of length
6/8/10 on variables 0-2. Paper bound: `B(SAT_n) >= n - 1 + q(2r - 3d + 3)` with
`q = floor(n/L) - 2^r - 1`.

**Audit (paper, no gap found):**
- Helper identity: a positive unit clause is inconsistent exactly when its identifier is forced false.
  The words are legal for every free valuation.
- Essentiality of the `qr` free bits: `g` is nonconstant and every other copy can be satisfied.
- The union bound: it suffices to check exactly `d` free inputs.
- The weight recursion.

**Weight-free route (formally checked).** The README routes the per-copy cost through the additive-weight
theorem, which is not formalized. That theorem is not needed. Robustness implies `PS_d`: two distinct
cofactors on `x_v`, given `x_u = c`, mean `x_v` still matters. `block_restriction_lower` then gives
`B(SAT_n) >= (n - qr) + 3q(r - d + 1) = n + q(2r - 3d + 3)` directly, which is one gate better than the
README's form.

**Lean milestones for the robust route (2026-11-26).**

- [PairSensitiveCounting.lean](lean/CircuitLemmas/PairSensitiveCounting.lean) proves
  `exists_PS_logarithmic`. For every block of width `r ≥ 8`, there is a table that depends only on
  that block and is `PS_d` for `d = floor(log₂ r) + 5`. The proof overcounts the events by
  `3^r · r² · 2`, including all partial assignments. For each valid event it counts disjoint pairs
  of truth-table entries forced to agree by injecting the bad tables into tables with one endpoint
  of each pair removed. This supplies a convenient sufficient threshold and does not certify the
  optimized threshold reported below.
- [UnitClauses.lean](lean/SatBridge/UnitClauses.lean) proves the helper identity against external
  `encodeCNF` and `SAT`. The fixed-high-one identifiers are injective and their units have length
  `2r+8`. Positive units on identifiers 0, 1 and 2 fill every even remainder of at least six, and
  avoid the fixed-high-one identifiers for `r ≥ 2`.
- [RobustRestriction.lean](lean/SatBridge/RobustRestriction.lean) proves the conditional finite
  bound `n + q max(0, 2r-3d+3)` for the external counted AND/OR/NOT model at `n = 6Q`, `Q ≥ 2`.
  It uses the checked transfer, L037, and the disjoint-block elimination theorem. The coordinate
  identity relating the restricted input string to the block product is an explicit premise.
- [IdentifierLayout.lean](lean/SatBridge/IdentifierLayout.lean) supplies that identity at the bit
  level. It proves that the free positions in clause `j` are `p + jL + 3 + 2i`, where `p` is
  the length of the helper prefix and `0 ≤ i < r`. It checks disjointness and the cardinality
  of the complementary fixed set.
- [RobustIdentifier.lean](lean/SatBridge/RobustIdentifier.lean) reindexes one common table onto
  each query block, fits the helpers and padding, and proves the bound end to end. The numeric
  theorem takes `r ≥ 8`, `L = 2r+8`, `d = floor(log₂ r)+5`, and
  `q = floor(n/L) - 2^r - 1 ≥ 1`. The logarithmic-width theorem fixes
  `r = floor(log₂ n)/2` (integer division) for every `n ≥ 2^16` divisible by six and checks
  `2n ≤ D.size + floor(n/L)(3d+5) + (2^r+2)L`. The eventual theorem checks
  `2mn ≤ m D.size + n` for every integer `m ≥ 1` and all sufficiently large multiples of six.

For the explicit rate, the logarithmic-width choice has `L = Θ(log n)`, `d = O(log log n)`,
and `2^r ≤ sqrt(n)`. The two verified loss terms therefore have orders
`O(n log log n / log n)` and `O(sqrt(n) log n)`, respectively. This yields
`D.size ≥ 2n - O(n log log n / log n)` on multiples of six by elementary asymptotic estimates.
Lean checks the finite loss with this width and the eventual slope statement.

Replay with the pinned Lean 4.36.0 Lake workspace using `lake build SatBridge` and
`lake env lean SatBridgeAxioms.lean` from `sat-search/lean`.
From the repository root, run
`python -B sat-search/experiments/robust_identifier_layout_check.py` for the independent replay.
It checks 4,848 coordinate layouts and SAT values on two- and three-bit tables, and 41,702
feasible width and length combinations. As a numeric example, `n = 103,079,215,104` and `r = 24`
give a bound of `146,853,368,352` counted gates, versus `146,028,888,060` for `floor(17n/12)-4`.

**Weaker existence condition.** `PS_d` needs only `4 * C(d,2)` inequalities per `d`-dimensional
subcube, not robustness's 6 per pair. The exact union bound `C(r,d) 2^(r-d) * 2d(d-1) * 2^(-2^(d-2)) < 1`
gives a smaller `d`: for example `d = 7` at `r = 16` and `d = 8` at `r = 24`, against `d = 8, 9` from
`ceil(log2(4r)) + 2`.

**Finite threshold.** `experiments/ps_block_threshold.py` (`logs/ps_block_threshold.out`) maximizes the
explicit bound over `r` at powers of two. It first beats `floor(17n/12) - 4` at `n = 2^32` with the union-bound `d`, and at
`2^35` with the README `d`. Below that, 17n/12 remains the best proved bound. The coefficient tends to 2
only like `1 - O(log log n / log n)`.

**Obstacles toward L-clb-036 (superlinear, `n^1.01`).**
- README(7) gives a sorting-network circuit of size `O(n log^2 n)` for the whole unit-clause restriction,
  with arbitrary signs. The circuit size is `o(n^1.01)` on that restriction. The argument was checked
  on paper, and the bundle replay reports 9,624 evaluations.
- Bounded treewidth: with free disable bits and template treewidth `t`, SAT has circuits of size
  `(2m + v) 2^t`. Families with `t <= 0.01 log2 n` are `O(n^1.01)`.
- The joint residual cut `P_J <= 2^|C|` is sound, but superconcentrator topologies satisfy it, so it
  only excludes specific structures.
- The clique activation family embeds `CLIQUE_(V,k)` with length `Theta(V^2 log V)`. A lower bound
  through it would need an unrestricted `Omega(V^(2.02+eps))` circuit bound for clique, which is open.
- Golovnev et al. show that bounded-step gate elimination has linear barriers. The lower bound
  from the robust identifier argument approaches slope two.

No route to L-clb-036 was found. The family-independent statement remains open, and no superlinear
circuit lower bound is known for any explicit NP language.

## Encoder-cost and semantic-sharing theorems (README(7) sections 1-4 and later, reviewed 2026-11-26)

- **Exact common-encoder minimum (correct on paper).**
  - Setting: `q` five-cycle side-information copies, encoder width `k`, `3q <= k <= 5q`.
  - Slot count `g >= 2m - k - t`: an unexported independent source needs two readers.
  - Capacity: `2^(k-t) * alpha_T >= 2^(m-t)`.
  - The `C5` table `alpha_T^2 <= 2^(5-t)` was checked for every `t`, and the disjunctive-product
    independence number is multiplicative.
  - Together these give `t <= 2k - 5q` and `g >= 3(5q - k)`, with equality from adjacent-pair XORs plus a
    raw bit.
  - The bundle's 4,368 five-subset check is consistent with `alpha = 5`.
  - The result concerns a fixed encoder interface only. It is not a SAT or whole-circuit bound.
- **Joint residual cut:** sound (the cut values determine all terminals). In the bundle's sample it gives
  only 2 extra exclusions out of 1,200, so it is **not implemented**: no demonstrated benefit.
- **Boundary-sensitive sharing:**
  - `G >= max_i(L_i + Q_i)`, because unary and merge gates are charged disjointly.
  - `sum b_i + H <= K(G + m) - m`, counted over nonoutput wires.
  - `2L + Q <= K(G + m) - m`.
  - The paper derivations check, and the multiplexer `r = 3` row gives 11.
  - The topology counts (paths, covers, components, forests) are audit tools without an end-to-end
    benefit, so they are **not implemented**.
- **Global sharing (Nechiporuk-style):**
  - `M_i = r_i + e_i - 1` and `N_i <= 3^(2M_i + 1)` are standard.
  - For list-disjointness the bound forces `Omega(m)` wide gates, but sorting circuits meet every
    condition, so no superlinear bound follows.
  - The formula bound `Omega(n^2/log n)` holds only in the formula model.

## Sparse conflict templates and fork mode CNFs

The exact fork kernel reduces each deficient matching component to one clause, with at
most one positive and two negative occurrences per mode variable. The handoff gives the
additive circuit upper bound in terms of the maximum genuine fork count over input
assignments. A linear-size parsimonious reduction from width-at-most-three CNF shows that
feasibility remains NP-hard for supplied templates even when both matching contractions,
dominated-mode removal, pure-literal elimination and unit propagation leave the entire
linear width-two/three core intact. A residual core whose clauses all have at least three
distinct variables is satisfiable by Hall's theorem. [Proof, scope, and replay](results/fork_mode_core/README.md)

## Reproduction

```powershell
python -I sat-search/experiments/sat_encoding_bound_review.py
```

The script was written for this review and shares no code with the bundle scripts. It checks:

- the decoder (round trip of all legal strings up to 14 bits, plus 3,000 random CNFs);
- 5,460 six-bit identities;
- 15,384 tail composition checks;
- the structural premises of H and the mux;
- full support at 24 lengths;
- the bound arithmetic.

It also prints the truth tables used for the Percy exact checks:

```powershell
./external/percy-build/percy_run.exe --n 5 --tt 90909900 --start 1 --max 10 --method cegar
```

The other tables are `9009` (n=4), `e8f2` (n=4), `99909909`, `90009990`, `90000090` and `99909000`
(n=5).

The bundle scripts (`sat_six_bit_fragments.py`, `sat_even_length_bound.py`, `sat_gadget_composition.py`
and `sat_xnor_gadget.py`) also reproduced their printed counts when run with `python -I` from the
scratchpad.

## Quick-reference summary

Moved word for word from the root RESEARCH_NOTES.md on November 27, 2026.

| Topic | Result |
| --- | --- |
| SAT-encoding explicit bounds (review) | Paper review of ChatGPT's six-bit fragment `11x10y` plus `110100`, which restricts `SAT_n` (pequalnp `encodeCNF`) to q disjoint XNORs. With `C(F_q)=4q-1`, three-gate absorbing elimination and cycle-rank excess monotonicity, it gives free-NOT `B >= floor(4n/3)-3` for even n>=16, which transfers to the Lean counted size (L041 has `5k+1` at `4k+2`). Proofs reviewed with no gap found; finite premises checked with an independent decoder; Percy small minima match. Not Lean-checked as a whole. Formally checked in the repository's free-NOT Lean model (2026-11-26, no sorry, standard axioms only): gate deletion, restriction, literal extension, `C(F_q) >= 4q-1` (`xnorConj_lower`), restriction excess `C(f) >= C(f|rho) + |dom rho|` (`excess_restriction`, a counting proof in place of cycle rank), the template `C(f) >= |F| + 4q - 1` (`xnorConj_restriction_lower`), and the block product `C(f) >= |F| + 3 sum_j(|V_j|-d+1)` for ANDs of disjoint `PS_d` blocks (`block_restriction_lower`). README(7) robust identifier tests (reviewed, paper): `B(SAT_n) >= n + q(2r-3d+3) = 2n - O(n log log n/log n)` with no additive-weight theorem needed (via `block_restriction_lower`). The first tested power of two beating 17n/12 was `2^32`. The unit-clause restriction has `O(n log^2 n)` circuits. **End-to-end Lean bound at n = 6Q (2026-11-26, `SatBridge`, against the external pequalnp `SAT`, `encodeCNF` and `Circuit`, using external L037):** every and/or/not fan-in-2 circuit deciding SAT on length 6Q (Q >= 2) has size >= 8Q - 3 (`sat_six_lower'`). This rests on the string identity (`word_mem_sat`) and a model transfer (`transfer`). **End-to-end robust bound in Lean.** At multiples of six the external counted AND/OR/NOT model has a `2n-o(n)` lower bound (`sat_robust_identifier_eventually`), with a checked explicit loss at `r = floor(log₂ n)/2` using integer division. The loss gives the paper rate `O(n log log n / log n)`. Lean checks the table counting, helper-unit identity, coordinate positions, padding and length arithmetic. Full support and tails for even n outside multiples of six, and the 17n/12 chain, remain open in Lean. No route for contributions outside posted desk gaps was found. No novelty claim. Exact-size gadget study (2026-11-26): block `11abcd` + `110100` restricts SAT to q disjoint copies of a 4-bit function with C = 7 (composition proved for all q by a finite automaton certificate). This gives a candidate coefficient of 5n/3, conditional on the unproved additivity `C(AND_q) = 8q-1`. Additive-weight theorem (handoff, reviewed 2026-11-26, paper proof with no gap found, finite premises reproduced independently, not Lean-checked): `C(AND f_j) >= sum w(f_j) - 1` for disjoint factors. With block `11a1bcd1efg1` (7-input f, w = 12) it gives free-NOT **`B(SAT_(12q+6)) >= 17q+5`** (about 17n/12), compared with 16q+5 before. It is not 5n/3: w(e8e4) = 6, so 11abcd additivity remains open. All even lengths (README(3), reviewed 2026-11-26, paper argument with finite premises reproduced, not Lean-checked): a joint 11-state mixed-block certificate plus a padding lemma for full support at every even n >= 16 give **`B(SAT_n) >= floor(17n/12)-4`** for every even n >= 16. [Review](NOTES_SAT_ENCODING_BOUNDS.md) |
