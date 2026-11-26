# SAT on a single Hamming layer

## Exponent-preserving reduction

For every even input length `n >= 2`, set `N = 3n + 12` and `t = 2n + 5`.
Define `G_n` on `N` bits by

```
G_n(y) = 0           if |y| < t
         SAT_N(y)    if |y| = t
         1           if |y| > t.
```

This is a total monotone Boolean function. Equal-weight comparable vectors are equal.
When comparable vectors have different weights, the two guards force the correct
ordering. For every fixed `alpha > 1`, the following statements are equivalent.

1. Exact-length SAT has unrestricted fan-in-two Boolean circuits of size `O(n^alpha)`.
2. `G_n` has monotone fan-in-two AND/OR circuits of size `O(N^alpha)` for every even `n`.

The equivalence also works if item 2 only promises correctness at weight `t`. The
complemented-edge AIG and counted AND/OR/NOT models differ by at most a constant
factor for these size exponents. Negation gates on inputs can be shared, and a
complemented edge model absorbs explicit NOTs and represents OR by De Morgan.
This targets the exponent in L-clb-036 without assuming that a hypothetical SAT
circuit has shallow depth or few reconvergent paths.
In particular, a lower bound at `alpha = 1.01` would have to rule out every
constant multiple of `N^1.01` on this monotone family.

### Balancing within the actual SAT grammar

Write the original word as `u q`, with `q` its last two bits. Every nonempty encoded
CNF ends in `00`, so SAT is false if `q` is anything else. Pin `q` to `00` in the
projection. Append a clause with the two literals `NOT x_0` and `x_0`, followed by one
negative literal with an identifier whose low bits are the complements of the bits
of `u` in order and whose high bit is fixed to one. The new word is

```
u  00  1001  1101  10  (1 NOT u_i) for all i in order  11  01  00
```

The projection duplicates each payload input in a signed pair: once directly in
`u` and once negated as a digit. These pairs contribute one 1 per payload bit, and
the fixed leading digit bits contribute one more. The fixed portions contribute
18 bits and nine 1s, so the length is `3(n-2)+18` and the weight is `2(n-2)+9`.
The high one makes the appended identifier canonical. Its value can collide with
an identifier from the prefix because the whole suffix clause is a tautology.

The pinned `00` is important for invalid inputs. In a successful parse of the
concatenation, every aligned `00` is a clause delimiter. It cannot be consumed as
an identifier digit or as the end of a literal. Thus the prefix up through the
pinned token must already be a complete CNF encoding, including any empty clauses.
The appended clause has no effect on satisfiability, so testing `q=00` and `G_n` on
the projection gives exactly `SAT_n`. Computing the signed coordinates and the
last-token test costs `O(n)` extra gates. Odd lengths are constant false, and the
empty input is a finite exception. This proves the implication from item 2 to item 1.
Omitting the last-token test would erroneously accept `100101`, whose pinned
prefix `100100` encodes a satisfiable negative unit clause.

### Compiling unrestricted circuits on the slice

The general compilation is the classical Berkowitz–Valiant slice principle.
Here is a constructive version tested by the replay. Run a Batcher bitonic sorting
network on the input bits, padded to a power of two with constant zeros. On the
weight-`t` layer, the sorted bits have known complements. At a comparator with
inputs `a,b`, outputs `hi=a OR b` and `lo=a AND b`, propagate the complements back
using

```
NOT a = (NOT hi) OR (b AND (NOT lo))
NOT b = (NOT hi) OR (a AND (NOT lo)).
```

Each identity holds for all four values of `a,b`. Treat the sorted output
complements as constants and traverse the network backwards. The resulting
monotone wires compute the required input complements on the whole promised layer.
The forward and backward passes together cost at most six gates per comparator,
so this step takes `O(N log^2 N)` gates. Then compute both polarities of every AIG
wire using two monotone gates per AND. The simulated output `h` agrees with SAT
on the layer. For the total function use
`[|y| >= t+1] OR ([|y| >= t] AND h)`, with the thresholds read off from the same
sorter. An `s`-gate unrestricted AIG thus needs at most `2s + O(N log^2 N)` monotone
gates. The additive overhead is `o(N^alpha)` for every fixed `alpha > 1`.
[Valiant's slice theorem](https://epubs.siam.org/doi/10.1137/0215037)
[Batcher's sorting networks](https://doi.org/10.1145/1468075.1468121)

## Why a direct monotone CLIQUE projection cannot close the proof

The following obstruction applies to every guarded layer target of this form,
regardless of its labels on the layer. Suppose a positive-coordinate projection
maps graph edges to target inputs by copying edge bits or using constants. On any
projected graph its Hamming weight is `b + sum_e w_e x_e`, with `b >= 0` and
integer multiplicities `w_e >= 0`. Every yes-instance must have projected weight
at least `t`, and every no-instance must have weight at most `t`.

For `CLIQUE(v,k)` with `3 <= k < v`, every edge variable is essential, so each
`w_e > 0`. A graph consisting of one `k`-clique and isolated vertices is positive.
A complete `(k-1)`-partite graph on `k+1` vertices with two parts of size two and
all other parts singletons, plus isolated vertices, is negative. It has
`binom(k+1,2)-2 > binom(k,2)` edges. Uniformly permuting the vertices of either
graph gives expected projected weight `b + edge_density * sum_e w_e`. The negative
orbit has strictly greater expected weight than the positive orbit, contradicting
the two necessary inequalities. This rules out importing a CLIQUE monotone lower
bound through ordinary monotone projections of any size. General monotone
preprocessing and lower bounds tailored to the equal-weight promise remain open.
The signed balancing projection exposes every payload bit in both polarities.
Hence a monotone circuit on its image can use either polarity, which prevents a
direct appeal to monotone lower bounds for an underlying unencoded problem. The
next lower-bound question is to find distributions of SAT and UNSAT words on the
same layer that support a monotone approximation argument on the original bits.

## Verification and scope

The independent replay uses the repository's separately written parser and brute-force
CNF semantics. It checks all 21,844 even-length words through length 14 and 2,000 seeded
encoded or mutated formulas. It tests the monotone compiler on 60 seeded AIGs with one
through ten inputs, including every assignment and every slice weight. This gives
122,880 guarded-output evaluations and 110,604 on-layer input-inversion checks.
The orbit arithmetic was replayed on 22,584 vertex relabelings with unequal edge
multiplicities. These are finite regressions for the proofs. The exponent equivalence
and the obstruction use the paper arguments above. They establish no superlinear
lower bound by themselves.

[`SatBridge.WeightSlice`](../../lean/SatBridge/WeightSlice.lean) formalizes the
paired-grammar projection. Its guard theorem treats arbitrary payloads of even
length and both values of each of the final two bits. The length and weight
theorems count all bits of the projected word. The locked `SatBridge` build and
axiom audit passed, with only standard Lean axioms. The monotone comparator compiler,
exponent equivalence, and CLIQUE projection obstruction are paper arguments.

The preceding handoff's affine-inequivalent cofactor construction was also inspected
and replayed at `26d92ea`. The fixed-point bound follows from a surviving quadratic
monomial, and the union bound is over the whole family at once. The reproducible
finite checks passed. No native search change was attempted.

```
python -B sat-search/workflow/research.py run sat-search/results/sat_weight_slice/manifest.json --workers 2 --memory-mib 256
python -B sat-search/workflow/research.py lean sat-search/lean --module SatBridge --timeout 120
python -B sat-search/workflow/research.py lean sat-search/lean --source sat-search/lean/SatBridgeAxioms.lean --timeout 90
```

[Independent stdout](replay.jsonl) · [Handoff stdout](handoff_replay.txt) · [Lean replay](lean_replay.txt)
