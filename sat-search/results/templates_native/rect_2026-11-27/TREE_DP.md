# Exact small-excess tree DP for desk rect units

Tool: `sat-search/native/tools/tree_dp.cpp` (build: `sat-search/native/build_tree_dp.bat`). It is opt-in and
does not change `template_synth`. Python reference: `tree_dp.py` (in this folder; covers s <= 1).

**Scope.** Monotone AND/OR, fan-in 2, partial label on the cared rows (the one-left-one-right promise
rows), output = some gate. It only decides units whose n inputs are all essential for the partial label;
it skips the others.

## Claim

Let every input be essential. For S <= 3, the DP decides whether a circuit with at most n-1+S gates
exists. If it finds no structure for any s <= S, the minimum size exceeds n-1+S. When it finds one, it
prints a witness circuit, which the tool checks by simulation on the cared rows.

## Proof

1. **Normal form of a minimum circuit.**
   - Every non-output gate is read; otherwise delete it.
   - No gate is constant on the cared rows. The basis has no constants, and a gate constant 0 (or 1)
     makes each AND (OR) reader constant too, and each OR (AND) reader equal to its other input. Rewiring
     such a reader's readers to that other input deletes at least one gate. The output is not constant,
     because the label is not.
   - Every essential input is read, since otherwise the circuit would compute a function independent of
     it that agrees with the label.

2. **Tree decomposition.**
   - Let H be the set of gates read at least twice, with fanout f_h, and p = |H|.
   - Every other non-output gate has exactly one reader. Following unique readers from any gate ends at
     the output or at a gate in H. So the gates split into p+1 binary trees rooted at H ∪ {output}.
   - A tree's leaves are reads of inputs or of gates in H. A tree with L leaves has L-1 gates.
   - Summing over the trees gives k = (input reads) + Σ f_h − p − 1. With all n inputs read,
     k = n − 1 + s, where s = e + Σ (f_h − 1) and e is the number of input reads beyond the first.

3. **Cases for s <= 2.**

   | s | structures |
   | --- | --- |
   | 0 | p = 0, e = 0 |
   | 1 | p = 0, e = 1; or p = 1, f = 2, e = 0 |
   | 2 | p = 0, e = 2 (one input three times or two inputs twice each); p = 1, f = 2, e = 1; p = 1, f = 3, e = 0; p = 2, f = (2, 2), e = 0 |

   For p = 2, take h1 to be a source of the DAG on H. Its tree's leaves are then inputs only. Gate h2
   reads h1 c times (c = 0, 1 or 2) and the output tree reads it the other 2−c times. Both reads of h2
   are in the output tree, because h1's tree has no gate leaves and h2 cannot read itself.

   **General shapes (s <= 3, the code since 2026-11-27).** Since every f_h >= 2, p <= s. Order H
   topologically as h_0, ..., h_{p-1}. A shape fixes the fanouts (each >= 2, Σ(f−1) <= s), the input
   multiset M with e = s − Σ(f−1) extra copies, and r[t][j], the number of reads of h_j by tree t. Here
   t < p is the tree of h_t, t = p is the output tree, r[t][j] = 0 unless j < t, and Σ_t r[t][j] = f_j.
   Every tree needs at least 2 leaves: an H gate is a gate, and the output is a gate that nothing reads.
   For s = 3 this gives p = 0 (e = 3); p = 1 with f = 2, 3 or 4; p = 2 with f = (2,2), (3,2) or (2,3);
   and p = 3 with f = (2,2,2). The s <= 2 cases above are the same enumeration.

4. **Placeholder tables.**
   - Gates act bitwise on cared-row vectors, and they are monotone. A tree containing placeholder leaves
     h1 and h2 is therefore exactly described by its 4 vectors, one for each value of (h1, h2), which
     the code calls `Tab.e`.
   - For one placeholder, the tree evaluates to lo | (hi & h), where lo ⊆ hi.
   - It equals T if and only if lo ⊆ T ⊆ hi and h agrees with T on D = hi & ~lo.
   - R(key) is the set of tables of trees with exactly that leaf multiset. AND/OR combine all splits
     into two nonempty sub-multisets, which makes the enumeration complete for trees.
   - Dropping tables that are constant in every entry is sound by step 1. A table that is constant in
     every entry is constant at the actual h value.

5. **Checks.** Each structure is checked exactly over every split of the input multiset, as in the
   code:
   - S_t is the input multiset of tree t. With p placeholders a table has 2^p entries and evaluates to
     OR_i (e[i] AND v_j for j in i).
   - The values v_0, ..., v_{p-2} are enumerated in order (distinct, nonconstant), each from its tree's
     tables at the earlier values. The output tree, evaluated at these values with v_{p-1} free, gives
     lo ⊆ hi, and the last value is matched as in step 4. If h_{p-1}'s tree reads no placeholder, its
     values are fixed and the D sets of all earlier value choices are pooled.
   - Witness: the chosen tables are expanded back into trees by searching for a production of each table
     (any production gives a tree with that leaf multiset). The trees are then assembled into one
     circuit, with the H trees in order and the output tree last.
   - D sets are reduced to the inclusion-minimal ones. If v agrees with T on D, it also agrees on any
     subset of D.
   - The tables R(key) depend only on the input wires, not on T. Units with the same n and cared-row wires
     therefore share each DP, and only the checks above use T.
   - The DP never assumes distinct gates or other normal forms beyond step 1. Every structure it accepts
     is a real circuit with exactly n−1+s gates, so a positive answer is an upper bound and a negative
     one is a lower bound.

## Verification

See `README.md` (section "Tree DP") for the differential checks against native SAT minima and the
results on the open units.
