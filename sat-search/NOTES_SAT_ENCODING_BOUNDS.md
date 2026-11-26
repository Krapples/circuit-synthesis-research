# Explicit circuit lower bounds for the pequalnp SAT encoding: proof review (2026-11-25)

This note reviews ChatGPT's six-bit fragment and even-length notes, which were supplied as
`sat_six_bit_fragments_notes.md` and `sat_even_length_bound_notes.md` in Downloads and are not
committed. It is a paper review plus finite checks: **not Lean-checked, and no novelty claim.**
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
| 5 | `C(F_q) = 4q - 1` | **Proved** from 2-4. Percy reports C(F_2) = 7 (UNSAT at 6, SAT at 7; solver-reported, not certified). |
| 6 | Excess monotonicity: `B >= n - m + C(f restricted)` for coordinate restrictions | **Proved** (paper). The cycle rank `B - n + 1` of a trimmed connected circuit cannot increase under deletion or contraction. Not valid for identifications. |
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
- **Additive weights.** The additive-weight theorem `C(AND f_j) >= sum w(f_j) - 1` (Addendum 1) was not
  reviewed in full here. The six-bit route does not need it.
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

**Not formalized yet:**
- the first-gate funnel lemma and the three-gate absorbing elimination (claims 2-3). `restrict_eliminates`
  and `bypass_many` are their accounting core: the remaining steps are a reader of the earliest gate and the
  canalizing replacement;
- excess monotonicity (claim 6);
- `C(F_q) = 4q - 1` and the tails (claims 5 and 8-10);
- the string identities (claim 1);
- the final bound (claim 11).

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
