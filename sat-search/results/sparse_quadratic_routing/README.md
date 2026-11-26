# Sparse quadratic routing audit and cubic marginal covers

The deterministic quadratic promise-circuit upper bound survives the sparse
routing audit. The original records can be kept in fixed-capacity arrays,
including while selecting an instance-dependent rank certificate. This result
concerns the variable-incidence packed quadratic promise. The audit below
combines a mathematical cost argument with actual signed AIGs for the sparse
rank primitive, indexed gathers, and polar-constraint accumulation.

The cubic follow-up gives a separate sufficient condition for a quasi-linear
promise circuit. After a bounded-degree neighborhood kernel, the circuit can
find a set of variables meeting all cubic monomials of the marginal and use it
to solve the marginal. The search and the branching take place on the kernel,
so they do not multiply the cost of routing the full input or reading its table.

[Deterministic quadratic handoff](../../chatgpt_handoff/deterministic_quadratic_handoff.md) ·
[Cubic neighborhood handoff](../../chatgpt_handoff/cubic_neighborhood_handoff.md)

## Sparse rank with one sort per level

Let an `a` by `b` matrix over GF(2) be given by `S` records with dynamic row
ID, column ID, coefficient bit and active bit. Entries are the XOR of their
active occurrences. Let `T >= 1` be a fixed truncation threshold. On valid
IDs the output consists of `min(T, rank)` pairs of original row and column
IDs and a prefix of validity bits. The corresponding square minor is
nonsingular. Zero records produce the empty minor.

Pad the row intervals to a complete binary tree. Keep at most `T` original
independent rows at each node. If the full rank of a child is below `T`, the
kept rows span that child. If either child already supplied `T` rows, the
candidate matrix at the parent already has rank at least `T`. Otherwise its
rows span the full parent. Therefore taking up to `T` independent columns
of the candidate matrix, and then independent rows on those columns,
produces a nonsingular minor of the right size. The chosen rows themselves
are independent in the original matrix, because their restrictions to the
chosen columns are independent. This gives the induction from leaves to root.

The AIG carries only the original records belonging to retained rows. Each
of the `S` slots has a flag and an encoded row slot. No operation creates
more original records. At one level:

1. Sort active records by (parent interval, column). The child side and
   retained row slot give distinct candidate positions within each parent.
   At a leaf there is only one candidate position. An active record toggles
   its candidate bit in the current column. Thus duplicate records, including
   duplicates in a row that becomes zero, are handled by XOR.
2. Scan forward, resetting the small column basis on a parent change.
   At each column boundary, insert the aggregated vector if independent and
   capacity remains. Keep the original vector and column ID of each insertion.
   From these vectors select the row slots of a nonsingular minor. Enable
   this summary on the last active record of the parent.
3. Scan backward, replacing the carried summary at each parent boundary.
   The end record of a parent is encountered first, so every one of its
   records sees its own summary. Retain records whose row slot was chosen
   and update their slots for the next level. Empty parents have no active
   records and supply no rows. At the root the original row IDs and column
   IDs give the output certificate.

This schedule uses one sorting network per level. The handoff's second
sort to rebroadcast summaries is also valid, but consecutive group records
allow the backward scan. A compare-exchange on a record works with ordinary
bounded-fan-in Boolean comparison and multiplexing. Let `w` bound the index
and count widths, including `log(T+1)`. A column vector has `O(T)` bits and
the capped basis retains `O(T)` such vectors. Reducing and replacing its
state is `O(T^2+Tw)` gates per candidate column. Computing a row summary in
each potential slot costs `O(T^3+T^2 w)` gates, using the same small-basis
operation on `O(T)` rows. A bitonic sort on `S` records costs
`O(S w log^2(S+1))` gates. Thus the fixed circuit uses

```
O(S log(a+1) [w log^2(S+1) + T^3 + T^2 w])
```

AND gates up to a constant factor for signed AIG simulation. This count
includes the unrolled summaries even when they are disabled. It does not
allocate a dense matrix and it does not use a row-sized state.

## Audit of the complete quadratic promise upper bound

The orthogonal-block argument preserves the image through a low-dimensional
dual marginal. Each character outside the final annihilator has a witnessing
pair in every round. Pairs from different rounds are mutually orthogonal for
each scalar polar form. In that character, the `2k` chosen pairs give rank
at least `4k` on the compressed space as well as on the full space. Inside
the annihilator the projected map is affine on the final orthogonal
complement `V`, so retaining its linear signatures together with a complement
of `V` preserves the marginal image. A nonempty `t`-bit marginal fiber has
density at least `2^(-2t)`. Its contribution to Fourier inversion, after
multiplying by `2^k`, is at least `2^(-t)`. The omitted high characters
contribute in absolute value less than `2^(-k)`. This establishes the support
identity for both spaces without preserving histogram counts.

The augmented rank query is sound with redundant constraints: change bases
so the rank-`r` constraint matrix is `[I_r 0]` with zero rows for
redundant constraints. On a complement of `V`, each independent constraint
pairs with its corresponding pivot variable. Eliminating their couplings
leaves the polar form restricted to `V`, giving augmented rank
`2r + rank(B|V)`. A nonsingular minor above threshold `2r` still exists on
the union of its original variable indices and the pivot coordinates of
the constraints. This union is polynomial in `k`. It suffices to find an
actual pair in the kernel of the restricted constraint matrix. At most
`O(k^3)` padded queries suffice for the selection across all rounds.

The dimensions and record capacities in the remaining circuit are as follows.

- Gather `W` at the endpoints of the monomial list with a table-before-query
  sort, scan, and restore pass. For term `c x_i x_j`, emit `c W_i` for
  coordinate `j` and `c W_j` for coordinate `i`. Aggregate by indexed XOR into
  default-zero slots. Equal endpoints cancel in the polar form, and raw
  duplicate terms add by XOR. This builds the `q` columns of `L`, each of
  width `O(k^3)`, using `O(q+m)` records of width polynomial in `k` and the
  identifier width. The augmented matrix has `O(m+q k^3)` scalar entry
  records. The sparse rank circuit handles these at threshold `O(k^3)`.
- Find the pivot columns `I` of `L` and use elimination on their small
  submatrix to solve every nonpivot column in those pivot coordinates.
  The resulting kernel vector is represented by a tag `j` and the
  coefficients of `C_j` in `e_j+C_j`. To compute its signature, batch
  `B(e_j,e_i)` for `i` in `I`. For each endpoint `j` of a monomial, the
  vector payload sent to `j` has one slot per pivot, enabled when the
  other endpoint equals that pivot. This uses `O(q+m)` records of
  polynomial width, with XOR scatter and defaults. The terms involving
  only `C_j` use the small polynomial on the pivot coordinates. The
  quadratic identity for `F(e_j+C_j)` uses only these data and the
  linear coefficient at `j`. This avoids constructing a `q` by `q`
  kernel matrix. A small signature basis retains the original tags and
  pivot coefficients of the chosen kernel vectors.
- Use the selected generators as a padded list of `d=O(k^4)` variables
  for substitution. Duplicated or dependent generators preserve image
  by surjecting onto their span. Sorting joins route their coordinate
  forms to each monomial, after which degree-two expansion costs
  polynomial in `d,k` per record. The `2^k` remaining signed character
  sums operate on `d` coordinates. Pair selection can be unrolled by
  scanning the `d` by `d` coefficient array for the first nonzero pair,
  selecting its incident affine forms, and updating every coefficient.
  Each step is polynomial in `d` and there are at most `d` steps.
  An integer Walsh transform with `O(d+k+1)`-bit words recovers counts:
  intermediate magnitudes before normalization are at most `2^(d+k)`.

These operations give a deterministic gate bound
`(q+m+2^k+1) poly(k,log(q+m+2))`. The packed encoding has `2^k=Theta(n)`
and `q,m=O(n)`, giving `O(n log^C n)` for an absolute `C`. This is a
small-circuit control for both fixed and variable quadratic incidence. The
complete compressor bound is mathematical. The AIG experiments exercise the
rank and routing primitives, including the construction of `L`, with no
claim of building a full end-to-end compressor or checking it in Lean.

## Measured gates and correctness scope

The explicit AIG experiment checks original minor IDs, rank and
nonsingularity against an independent dense GF(2) rank computation on
8,201 inputs. These include every input record sequence in the four
smallest shapes, rectangular and non-power-of-two shapes, empty
groups, inactive records, duplicates and limits above matrix rank.
It also checks indexed gathers on 3,256 assignments and the routed
polar constraints against their direct definition on 1,336 assignments.

The matched baseline expands the same records to dense columns and uses
the same capped basis and original-minor output, so different certificates
are allowed. Counts are live AND gates after traversing the outputs, with
complement edges and constants free. Neither circuit count is a synthesis
minimum. The prior handoff benchmark used Python elimination on integers
and supplied no comparable Boolean circuit measurements.

| Rows and columns | Record capacity | Rank cap | Dense live ANDs | Sparse live ANDs |
| ---: | ---: | ---: | ---: | ---: |
| 8 | 9 | 2 | 4,437 | 17,895 |
| 16 | 17 | 2 | 26,209 | 72,000 |
| 32 | 33 | 2 | 170,461 | 265,912 |
| 64 | 65 | 2 | 1,205,657 | 917,255 |

Sparse routing saved 23.9% at the largest tested shape and cost more at
all three smaller matched shapes. The test makes no general crossover or
practical optimizer claim. The experiment code stays separate from Percy.

[AIG checker](../../experiments/sparse_rank_routing_check.py) ·
[Manifest](batch.json) · [AIG checks](aig_checks.jsonl) · [Gate counts](aig_bench.jsonl)

## Cubic residual marginal with an unsupplied cover

The cubic neighborhood proof uses centers at pairwise distance at least
four. Their closed one-neighborhoods are disjoint and there is no edge
between distinct neighborhoods. For a selected monomial containing a
center, conditioning outside the neighborhood cannot change its actual
coefficient: any original monomial that could contribute after
conditioning would also contain the center and hence be wholly inside the
neighborhood. This uses canonical coefficients after cancellation. Each
such cube is conditionally nonconstant and gives bias at most `3/4`.
For a high character there are `8k` such cubes, giving total bias at most
`(3/4)^(8k)`. The sum of high terms in the scaled inversion is strictly
below `2^(-2k)`, while an attained `t`-bit marginal supplies at least
`2^(-2t)`. The same witnesses survive after setting omitted variables to
zero. The component proof uses the same inequality with unconditional
independence across components. Local replays matched both handoff records.

Suppose maximum interaction degree is at most `poly(k)`, so the retained
kernel has `poly(k)` variables. Let `t` bound the residual marginal
dimension and let `h` bound the minimum number of its variables meeting
every nonzero cubic monomial. Both are fixed promise bounds per circuit.
The set of `h` variables need not be provided as input. Search by picking
the first uncovered triple and branching on its three variables. Any
successful cover extending the current selection must include one of the
three. Stop when all triples are covered, or reject the branch when its
budget is exhausted. The depth-`h` ternary tree has `O(3^h)` nodes. The
whole search costs `3^h poly(k)` gates on the compressed kernel: each
node uses equality tests against its chosen list, a first-valid scan and
masks. Enable padded slots only for choices actually made and select a
successful cover by a priority scan. If no cover is found, the input lies
outside this subpromise.

Enumerate the `2^h` assignments to the discovered cover. Each removes at
least one variable from every cubic monomial, so its marginal restriction
is quadratic. Compute its support by the exact quadratic Walsh algorithm
on the kernel, and OR the support vectors. This costs `2^(h+t) poly(k)`
gates. Marginal and cover dimensions smaller than their bounds use padding
with zero output rows or inactive variables. Finally lift the common
marginal support to all `2^k` original addresses with a single sorting
join, and test against the data table. The kernel is constructed once and
the original table is read once. At the packed scale the resulting bound is

```
O((n + 3^h + 2^(h+t)) poly(log n)).
```

In particular `h log2(3) <= k` and `h+t <= k` suffice for a quasi-linear
deterministic circuit. For example `h,t <= floor(k/2)` suffices, allowing
covers of logarithmic size in the original word length. This proof is a
sufficient upper bound. It leaves large genuinely cubic residuals outside
its range and makes no claim about their lower bounds.

Without a neighborhood kernel one can perform the same branching on the
original sparse polynomial records and run the deterministic sparse
quadratic algorithm per cover assignment. This gives the weaker general
bound `O(3^h (q+m+2^k+1) poly(k,h,log(q+m+2)))` when the original map
has a cover of size `h`. The advantage of the kernel is that it removes
the large input cost from all the branches.

## Cubic grammar and replay

The cubic slot uses two equality clauses, four clauses defining the triple
product, and four defining XOR with the slot parity. With common long
identifier width `w` and short pattern width `ell+1`, a slot has exactly
`24(4+2w)+2(4+2(ell+1))+20` bits. The final summand accounts for the
ten two-bit clause terminators. Pinning label zero false and using matching
IDs for repeated labels gives exactly the corresponding Boolean product.
For any fixed witnesses the product, row parities, guard tree and selected
table constraint give the same decision as evaluating the packed cubic
address and reading that table entry. A legal padding of length even
`p >= 48` exists as `10a+14b`: divide by two and use the Frobenius bound
for 5 and 7, or choose `b` in `0..4` to get the required residue. The two
tautologies use identifiers 0 and 1 with both polarities. The existing
balancing map keeps SAT and has length `3n+12` and weight `2n+5` on a padded
input of length `n`.

The independent grammar decoder matched 48 generated cubic packed cases.
There were 664 pinned decisions each on the original, padded and balanced
forms, and 96 source-coordinate flip probes under changed labels and
permutations. The cover regression compared the full output support of
213 abstract maps to exhaustive evaluation, including 130 genuine cubic
maps. The exact cover search and quadratic branch procedure passed 375
branch checks. These are finite references and separate from the asymptotic
circuit cost. The packed projection and cover result have no new Lean proof.

[Cover and grammar checker](../../experiments/cubic_witness_modulator_check.py) ·
[Cover and grammar output](cubic_cover.jsonl) ·
[Handoff replay manifest](cubic_handoff_batch.json) ·
[Component replay](cubic_component_replay.txt) · [Neighborhood replay](cubic_neighborhood_replay.txt)
