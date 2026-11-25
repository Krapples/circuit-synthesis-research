# Seeded boundary synthesis for the order-three plane

L-meta-9063 asks for a 58-gate monotone AND/OR circuit for the order-three
projective-plane incidence function with line 1 removed. Point p is incident to
line l when p − l modulo 13 is 0, 1, 3, or 9. The circuit takes the 26 point and
line inputs and a supplied 27th input, `x₁ OR x₂`. Each gate reads two distinct
earlier wires. The posted specification checks minimal positives and maximal
negatives. Monotonicity of the circuit and the supplied OR makes these rows
sufficient for the full Boolean cube.

## Checked reduction

The two line sets are `{0,2,5,6,11,12}` and `{3,4,7,8,9,10}`. The first
contains every remaining line incident to point 1 or 2. Each child asks for
the exact incidence function of its six-line set on the same augmented
input. The budgets are 28 for the first set and 29 for the second.

The Lean proof keeps the input wires fixed, shifts each internal wire of the
second circuit by the size of the first, and adds a final OR. The arithmetic
shift is injective and preserves legality. The proof simulates the gate
evaluations before and after the shift and checks the partition by cases on
the line index. The final size is at most 28 + 29 + 1.

[R_meta_9063_1.lean](R_meta_9063_1.lean) passed the upstream project's file guard
and local kernel check in reduction mode on Lean 4.36.0. The checker accepted
two children and reported only the standard axioms. The submission adds only
that file. GitHub merged the reduction and the project posted L-meta-17641
for the 28-gate half and L-meta-17643 for the 29-gate half.
[Merged PR #22166](https://github.com/open-goat/pequalnp-proofs/pull/22166)

Lean also checked [Right29.lean](Right29.lean), a witness for the 29-gate side.
It uses three OR gates and one AND for each four-point line, then five OR
gates to join the six stars. The proof evaluates the circuit on symbolic inputs
and checks that the list of 24 expanded edges is exactly the modular incidence
relation. The supplied point-pair OR is unused in this witness.

## Search coverage

The 28-gate budget remains open. Twenty jobs pinned three line stars, one for
each such triple, and two pinned two. The solver used 22 processes, a 90-second
cap per active solve, and an exact AND/OR gate encoding with the fixed prefix
and an explicit final OR. The 24 minimal positives and 52 maximal negatives
were available for counterexample-guided row addition. Every tested window
timed out before finding a candidate. [Raw logs](L-meta-9063-half-search.jsonl)

With PySAT available, run this from the repository root and pass an unused
output path.

```powershell
python -B sat-search/results/pg3_seeded_boundary_9063/search-half.py new-half-search.jsonl
```

## Patterns from accepted PRs

- **Build the prescribed signal first.** The parent reduction installs
  `x₁ OR x₂` as wire 26 and leaves the 58-gate boundary synthesis problem.
  This makes the required internal signal explicit and lets the suffix search
  treat it as a free input. [PR #10654](https://github.com/open-goat/pequalnp-proofs/pull/10654)
- **Prove a small circuit extension.** The Fano counterpart appends five
  explicit gates to a 22-gate six-line core. This isolates the gate saving in
  the core and makes the output AND and the singleton obligations algebraic.
  [PR #10611](https://github.com/open-goat/pequalnp-proofs/pull/10611)
- **Use a set cover for a homogeneous final layer.** An OR collector uses
  existing wires that vanish on all negative rows and covers the positive
  rows with their true sets. An AND collector uses the dual obligations.
  For a fixed prefix, selecting k distinct wires costs k − 1 additional gates.
  [PR #13282](https://github.com/open-goat/pequalnp-proofs/pull/13282)

Points 1 and 2 share only line 1, which is absent here. The supplied OR therefore
cannot replace a two-point OR in an ordinary retained line star. Saving a gate
with that input would require a different circuit structure or another way
to exploit the boundary obligations.
