# L-meta-16102 gap (A): B(f) ≥ 8 by a first-gate cascade recursion (2026-11-26)

Status: **paper proof plus computed recursion, not yet Lean checked.** This replaces the fork, read-once and DP
argument of [two_fork_handoff.md](two_fork_handoff.md) for the bound alone. It does not address gap (B), the one-NOT core.

Model: free-NOT AIG (`CircuitLemmas.GateElim`). Gates are `x^p ∧ y^q` over earlier wires, and negations and output phase are free.
`C(g)` is the least gate count. `SatBridge.Meta16102.posted_core` uses `C(F) ≥ 8` as its hypothesis `hA`.

## The recursion

Let `g` have at least 3 essential inputs and let `C` be a minimal AIG for `g`. Then:

- No gate is degenerate, that is, constant or equal to a literal of an earlier wire. Such a gate can be bypassed (`bypass_many`).
- Every gate except the output has a reader (`delete_dead`).
- The first gate `g1` reads two distinct inputs `i, j`. Both are essential: fixing an inessential input deletes its readers.
- `g1` is not the output, because `g` has at least 3 essential inputs.

Write `R(w)` for the readers of wire `w` and `C_b = C(g|x_v=b)`. Fixing an input deletes every gate with an operand that becomes constant, and
this cascades (`cascade_restriction`).

**Case 1: `|R(x_i)| = |R(x_j)| = 1`.** `g = Ψ(x_i^a ∧ x_j^c, rest)`, which can be checked on the truth table.
- Contracting `g1` to a new input gives `C(g) ≥ 1 + C(g')`.
- Fixing `x_i := ¬a` makes `g1` constant and deletes `g1` and `R(g1) ≠ ∅`, so `C(g) ≥ 2 + C(g|x_i=¬a)`. The same holds for `j`.

**Case 2: some `v ∈ {i, j}` has `|R(x_v)| ≥ 2`.**

1. **Fan-out bound.** Fixing `v` either way deletes `R(x_v)`, so `C(g) ≥ 2 + max_b C_b`.
2. **Minimality lemma: `R(g1) ⊄ R(x_v)`.** Suppose `g' ∈ R(g1) ∩ R(x_v)`. Then `g'` is a non-degenerate function of `(x_v, x_u)`. A short check shows it is `x_v^α ∧ x_u^β` for some phases, so it can read the inputs directly. If every reader of `g1` were of this kind, `g1` would become dead, giving a smaller circuit.
3. **Controlling value of `g1`.** Let `b0` be the value of `x_v` that makes `g1` constant. Fixing `x_v := b0` deletes `R(x_v) ∪ R(g1)`, which by the minimality lemma has at least 3 gates. So `C(g) ≥ 3 + C_{b0}`.
4. **At least 3 readers.** `C(g) ≥ 3 + max_b C_b`.
5. **Exactly 2 readers `{g1, g2}`.** Let `c` be the value of `x_v` that makes `g2` constant.
   - **If `c ≠ b0`:** `x_v := c` deletes `g1`, `g2` and `R(g2)`. `R(g2)` is nonempty unless `g|x_v=c` is constant, and `R(g2)` does not contain `g1` or `g2`. So `C(g) ≥ 3 + C_c`.
   - **If `c = b0`:** `x_v := b0` deletes `D = {g1, g2} ∪ R(g1) ∪ R(g2)`. Suppose `|D| = 3`. Then `R(g2) = {h}` and `R(g1) ⊆ {g2, h}`, and `h ∈ R(g1)` by the minimality lemma, so `h` reads `g1 = x_v^α ∧ A` and `g2 = x_v^α ∧ B`, with the same `α`.
     - For every pair of output phases, `h` is one of `x_v^α ∧ A ∧ B`, `¬x_v^α ∨ (¬A ∧ ¬B)` or `x_v^α ∧ A ∧ ¬B` (up to symmetry). Each takes 2 gates over `x_v, A, B`, replacing the 3 gates `g1, g2, h`.
     - If `B` is `g1` itself, `h` depends only on `(x_v, x_u)` and needs at most 1 gate.
     - Either way `C` is not minimal. Hence `|D| ≥ 4` and `C(g) ≥ 4 + C_{b0}`.
   - Since `b0` is unknown, the case is worth `min_{b0} max(3 + C_{b0}, min(3 + C_{1-b0}, 4 + C_{b0}))`.

`LB(g)` takes the minimum over pairs `{i, j}` of the best valid bound in each case. The floor is `#essential − 1`, and `LB = 1` for two essential inputs.
Output negation and dropping inessential inputs do not change `C`.

## Result

[first_gate_lb.py](first_gate_lb.py) (cascade level 2, 148 states) gives **LB(f16102) = 8**. Without cascades, and with only the first-level cascade, it gives 7.
The tight branches are the first gates that read `x0`, `x1` or `x2`. For `x1` and `x2`, `C_0 = 5` and `C_1 = 4`, and step 5 is needed.

Independent checks with exhaustive AIG search ([aig_exact_small.py](aig_exact_small.py)):
- `C(f|x0=0) ≥ 6`, because no 5-gate AIG exists. This agrees with the recursion's 6.
- `C(f|x1=0) = 5`, with witness `(x2∨x3) ∧ (x5 ∨ x4(x0∨x3))`.
- Soundness cross-check ([first_gate_lb_crosscheck.py](first_gate_lb_crosscheck.py), exhaustive `has_aig(n, tt, LB-1)` = NONE): all 43 ≤5-input recursion states reached from f, and 1517 states from ≤4-input states plus 1500 random 3/4-input functions (seed 1, 22 shards). 0 unsound. Logs: `sat-search/logs/first_gate_crosscheck/`.

## Lean plan

Formalizing gap (A) needs these pieces:
- **Minimal circuit, first-gate facts:** existing pieces are `bypass_many`, `delete_dead` and `XnorConj.first_gate_cases`.
- **Fan-out restriction and cascades:** `conditional_restriction` and `cascade_restriction` exist.
- **New lemmas:**
  - contraction of a fan-out-1 first gate;
  - the rewiring step of the minimality lemma;
  - the two-gate replacement in step 5.
- **The recursion over 148 states:** each state carries a certificate (pair, case, values) checked by `decide` on 32/64-bit truth tables.
