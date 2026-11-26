# False restrictions in minimum circuits for cubic edge functions

L-meta-5020 asks for the lower bound `|A| + |E| + k ≤ size(C) + 1` in the
AND/OR/NOT basis. Outside the isolated OR variables in `A`, the graph is
cubic with girth at least seven. Every graph input has at least two effective
readers in the minimum circuit. One input has exactly two, including a
non-OR gate.

An accepted reduction separates the four-gate saving claim from the lower
bound on the graph left after deleting a vertex. The saving claim is
L-meta-7919. [Accepted reduction](https://github.com/open-goat/pequalnp-proofs/pull/10444)

## Checked local results

- [Readers5020.lean](Readers5020.lean) trims ignored NOT operands and proves that
  the resulting gate list satisfies the circuit hygiene needed by the existing
  gate-elimination lemmas. Any gate that fails that condition would be skipped
  by the simplifier, yielding a smaller circuit and contradicting minimality.
  The normalization preserves positions and the desk's effective-reader count.
- Fixing a two-reader input to false saves four gates when both readers become
  constant. If their next consumers coincide, the common gate becomes constant
  too and has a further consumer because the restricted function is nonconstant.
  Otherwise the two next consumers give the third and fourth savings directly.
- If no four-gate saving is possible at the designated input, its other reader
  is an OR and the non-OR has a unique consumer. For an AND reader that consumer
  is an OR. For a NOT reader it is an AND. The excluded consumer types would
  propagate another constant or give a fourth distinct removable gate.
- [Exclusive5020.lean](Exclusive5020.lean) handles one subcase of the AND branch.
  If the AND's other operand is an internal wire read only by that AND,
  replacing its producer by `NOT v` preserves the function at `v = false`.
  The producer, AND, other reader of `v`, and later reader of the AND all
  disappear. The original operand producer cannot be the output of a minimum
  circuit because it is followed by a live gate.
- [Mask5020.lean](Mask5020.lean) derives strict changes of the edge function from
  independent sets of size one or two. This rules out two AND readers whose
  other operands are both primary inputs. It also rules out an AND and OR with
  distinct primary operands when the other OR operand is outside `A`. The
  latter uses that distinct vertices have at most one common neighbor. The
  file proves that the false cofactor of each non-isolated input is nonconstant.

The remaining cases can use a shared internal operand, identical primary
operands, an OR input from `A`, or the NOT-to-AND shape. The checked local
lemmas give neither a general four-gate saving nor a refutation.

The submitted reduction separates a general two-reader routing theorem,
the graph-specific residual patterns, and the graph after deleting incident
edges. The project checker accepted the reduction with three child
statements and standard axioms, and separately accepted a prototype proof
of the general routing child. The exact submitted source and checker
transcript are included here. [Reduction PR](https://github.com/open-goat/pequalnp-proofs/pull/22538)

## Replay

Use Lean 4.36.0 with the public project and its pinned Mathlib. With its
helper modules built, run the following from the project's Lean directory.

```powershell
lake env lean ../../sat-search/results/cubic_gate_elimination_5020/Readers5020.lean
lake env lean ../../sat-search/results/cubic_gate_elimination_5020/Exclusive5020.lean
lake env lean ../../sat-search/results/cubic_gate_elimination_5020/Mask5020.lean
```
