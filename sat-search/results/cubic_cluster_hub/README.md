# Cubic cluster audit and formula-hard cubic controls

The exact cluster series, common high-degree hub kernel, and batched
acceptance-table identity survived an independent mathematical audit.
An actual signed AIG verifies the table-query part of the construction.
Its gate counts indicate a practical penalty at small positive marginal
dimensions. A separate cubic control combines an exact Andreev projection
with full marginal dimension, irreducible coordinate restrictions, and a
linear-size AIG at fixed metadata. This addresses a limit of the parameter
approaches and supplies a test case for gate-role accounting.

[Cluster and hub handoff](../../chatgpt_handoff/cubic_cluster_hub_handoff.md)

## Cluster and hub audit

Center the map so the signed generating series `Z_U` has constant term one.
For a graph-disconnected `U`, each subset sign factors over its components.
This makes `Z_T` multiplicative and the logarithmic derivative `H_T`
additive for `T ⊆ U`. The alternating sum of an additive component term
cancels by summing over any other component. The low-degree cancellation
is independent of the graph. Work with separate formal markers for the
variables of `U`. Setting markers outside `T` to zero commutes with the
Euler derivative and inversion of the unit series. Alternating over `T`
selects terms involving every marker. Every such term has total degree
at least `|U|`. Specializing the markers to a single variable gives the
exact truncated connected-set formula. This uses the connected induced
subgraph technique with exact signed weight coefficients.
[Patel and Regts, partition function algorithms](https://arxiv.org/abs/1607.01167)
· [Connected induced subgraph counts](https://arxiv.org/abs/1707.05186)

For local or global sets of at most `Q` variables, the signed coefficients
obey `|Z_j| ≤ (Q+1)^j`. In the inverse geometric series, the coefficient of
degree `j` sums products indexed by compositions of `j`, and every product
is bounded by `(Q+1)^j`. Multiplication by the Euler derivative adds a
factor at most polynomial in `j`. The local `H_j` values, their alternating
sums, and the global sum therefore fit in `O(d log(Q+2)+d)` signed bits for
truncation `d`. One may bound the number of accumulated records by
`(Q+1)^(O(d))`, including failed or repeated walks. In reconstruction,
`j Z_j = H_j + sum_(i<j) H_i Z_(j-i)` is exact. Each pre-division product
of two such bounded integers still fits in a constant multiple of that
width. Exact integer division by the fixed positive `j` introduces no
oracle. The Walsh transform adds at most `t` bits for its `2^t` summands.

Under the residual degree bound, a length-`2(u-1)` depth-first spanning-tree
tour covers every connected set of size `u`. Fixed neighbor-slot arrays
therefore suffice. Sort the visited IDs within a tour, require exactly
`u` distinct vertices, and sort valid records by the resulting key. Mark
one copy of each key. Walks that repeatedly use one edge do not contribute
unless their actual vertex sets pass the same check. Invalid-neighbor flags
stay invalid for the whole walk. For `u=1` explicitly include all vertices,
including isolates. This gives the asserted `Q D^(2(u-1))` padded record
count with `D=max(1,Delta)`. The algebraic handoff replay instead enumerates
connected sets by growth.

For the hub kernel, subtract the hub-only polynomial and collect the
coefficient maps of the hub monomials of degree at most two. A residual
edge among two nonhubs can appear only if those original variables occurred
together. Thus the joint map's graph still meets the same residual degree
bound. Its common coordinate kernel preserves the **joint** image. Every
hub assignment then applies an affine map to that same image, so the one
kernel preserves every conditioned image. This implication would fail if
only the individual coefficient-map images were preserved. The padded
joint coefficient width is polynomial in `k`, and construction uses one
sparse routing and kernel pass before enumerating hub assignments.

Finally, for an arbitrary linear map `pi_u` with `t` rows, expanding
the inverse Walsh transform of `g_u` gives the scaled score

```
2^t sum_a table(a) g_u(pi_u(a)) = sum_w ghat_u(w) tablehat(pi_u^T(w)).
```

Using zero rows, repeated rows, or coincident frequency keys does not
affect the proof. Each column sum on the right still receives its own
contribution. A single table transform and the earlier table-before-query
sort, scan, and restore circuit suffice. With a signed word of `k+2t+2`
bits, every partial sum fits because the absolute contribution summed
over all `2^t` frequencies is at most `2^(k+2t)`. This verifies the
claimed separation between one near-linear table pass and the costs
per compressed branch. The full cluster solver remains a paper circuit
construction. The explicit AIG tests cover the batched score arithmetic
and routing with variable projection bits.

| Address bits `k` | Marginal bits `t` | Branches | Direct live ANDs | Walsh live ANDs |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 0 | 2 | 12 | 8 |
| 2 | 1 | 2 | 80 | 2,449 |
| 2 | 2 | 3 | 183 | 15,145 |
| 3 | 2 | 4 | 824 | 33,442 |
| 4 | 3 | 4 | 3,276 | 126,787 |

Both circuits produce the exact integer score for each branch. The dense
baseline selects a support bit by a mux for each address and sums its hit.
The Walsh comparator uses exact two's-complement arithmetic and the same
sorted join as the earlier routing audit. Both matched an independent
direct count on all 5,660 assignments. This is a comparison of explicit
construction costs with variable inputs. It gives no crossover claim or
practical reason to integrate Walsh scoring into the solver at this scale.

## Full address dimension and a linear-size AIG with a near-cubic formula bound

Let `k=7m` and choose any invertible binary mixing matrix `L` on `3m`
witness bits. Divide `Ly` into `m` blocks of three control bits. Seven
outputs in each address block are the degree-three indicator polynomials
of seven distinct control words. Omit the eighth word. The image is
exactly `S = {0,e_1,...,e_7}^m`, with one witness for each image point.
The seven indicators partition seven of the eight control assignments.
The ambient witness change of basis is a bijection. In particular every
proper coordinate restriction on these `3m` witnesses, with either fixed
phase, loses image points. Unused reserved witness labels in the SAT
word play no role in the statement.

`S` has no nonzero translation period. If some block of the shift has
weight at least two, its zero point leaves the block support. If all
nonzero blocks have weight one, choose a different unit vector in one
such block to leave it. Thus any exact description `S = pi^(-1)(T)`
through a linear projection has rank `k`, since every vector in the
kernel would otherwise be a nonzero period. The exceptional marginal
dimension must be full whenever a method represents the image in this
form. The same is true after translating `S` by any offset.

Any variable set hitting all nonzero cubic monomials has size at least
`m`. Fixing such a set to zero makes each triple-product indicator have
degree at most two. For a product of three linear parts, the coefficient
of a squarefree cubic on three distinct variable indices is the
determinant of the three corresponding columns over GF(2). The rank of
the three rows on the remaining variables is therefore at most two.
Over all `m` blocks the remaining stack has rank at most `2m`. Invertibility
forces rank exactly `3m-h` after deleting `h` columns, so `h>=m`.

Two explicit choices show different incidence regimes.

- Set the first `3m-1` output bits of `L` to the XOR of that input bit and
  the next input bit. Leave the last bit alone. `L` is triangular and
  invertible. Each block uses a window of at most four consecutive variables.
  Consecutive windows share an endpoint. In a full window the cubic part
  contains all four triples of its variables, so the graph is connected,
  with degree at most six.
- For even `m`, take `L=I+J` where `J` is the all-ones `3m` by `3m`
  matrix. Since `J^2=0`, `L^2=I`. If `s` denotes the XOR of all inputs,
  a block has linear forms `s+x_a`, `s+x_b`, `s+x_c`. The cubic part of
  their product includes every triple with two of `{a,b,c}` and one
  outside variable, each with coefficient one. Every pair of controls
  therefore co-occurs in an actual monomial, and the interaction graph
  is complete. To reduce its maximum degree to `Delta` one must delete at
  least `3m-Delta-1` variables. The same obstruction holds after any
  image-preserving coordinate restriction because none can remove a control.

Both choices fit the packed cubic grammar for sufficiently large `k`.
Each indicator uses polynomially many monomials in `k`, and each address
row provides `J=Theta(2^k/k^2)` slots. Use zero-label monomials for
unused slots and repeated labels for degree-one or degree-two terms.
Encode the constant from each indicator in the selector parity offset.
If `b` is the remaining selector offset, SAT accepts exactly when the
input data table has a one on `b+S`.

**Linear-size AIG at fixed metadata.** Compute the `k` selector parities
in `O(2^k)` gates by reading one copy of each source bit. For each 7-bit
address block and each concrete local key, calculate whether the XOR with
the corresponding block of `b` has weight at most one. Each such guard
costs a constant number of gates. Fold the table one block at a time in a
tree with 128 children per internal node. Each node ORs its children with
the shared guards for that level. The geometric sum of child incidences
is `O(2^k)`, and the guard budget is `O(k)`. Hence the whole promise at
fixed metadata has a signed AIG of size `O(n)` at word length
`n=Theta(2^k)`. The same semantic rule also applies to all invertible
choices of `L`. If the slots are permuted and tagged, the earlier sort
recovers the parity offsets in `O(n log^2 n)` gates.

**Exact Andreev projection.** Let `C` be the subspace of even parity
in each 7-bit block. It has dimension `6m` and `S ∩ C={0}`. Put the
data bits on `C` and fix the table to zero outside `C`. Program the
selector offset in `C`; then `(b+S) ∩ C={b}`, and the promise predicate
returns exactly the addressed bit. In each address block, use six
independent parity rows of length `r'=floor((r-1)/6)` where `r` is the
packed row length. Copy their physical selector variables into six
disjoint segments of the seventh row. This makes its parity the sum
of the six independent row parities. Spare bits implement the fixed
indicator constants. The construction uses literal copies and constants
at actual grammar digit positions. Each independent selector bit has
four occurrences. Since `r'=Theta(2^k/k)`, fixing the data table to a
maximal-size function on `6m` bits and applying Tal's Lemma 7.1 gives

```
Omega(2^(6m) (r')^2 / log(6m))
  = Omega(n^(20/7) / ((log n)^2 log log n))
```

signed De Morgan formula leaves on the same fixed-metadata promise.
Counting labeled binary formula trees supplies the `2^(6m)/log(6m)`
factor. The even-length padding uses the existing 10- and 14-bit
tautologies. Consecutive allowed scales, using a step of 7 in `k` or
14 for the dense example, have a bounded ratio. A formula for a
padded length restricts to the projection above. Tal is an external
theorem premise. [Tal, revised TR14-048, Lemma 7.1](https://eccc.weizmann.ac.il/report/2014/048/revision/1/download/)

The data dimension for this isolation method is exact. If two data
addresses agree on the first six positions in each block, their difference
has at most one nonzero bit per block and belongs to `S`. They cannot both
be isolated in the same translated-image lookup scheme. Partitioning
addresses by those first six bits bounds the isolated set by `2^(6m)`.
The even-parity code attains the bound.

The control separates connectivity, coordinate incompressibility, cubic
cover size, and full linear marginal dimension from high distinct-gate
complexity, even with a large formula lower bound on the same promise.
For the fixed-metadata linear AIG, unfolding alone requires some internal
gate to have `Omega(n^(13/7)/((log n)^2 log log n))` output paths. This
derivation uses the total unfolded gate count. It supplies no claim about
the number of gates attaining that threshold.

## Verification and scope

- The independent Node replays matched the handoff outputs for exact
  cubic clusters, the common hub kernel, and the later Andreev–Tseitin
  charge control. The latter remains a separate example of joint
  compatibility with easy parity semantics.
- The seven-output regression checked 648 witness evaluations, 960 period
  probes, 49 insufficient covers and 960 isolated code addresses. The
  actual packed `k=7` projection passed all 256 pinned decisions across
  32 contexts, checking every witness assignment for each context.
- A separate two-output control uses pairs
  `(a_i b_i (Lc)_i, a_i b_i (1+(Lc)_i))`. The product image forbids
  `11` in each pair. A table address with every pair active forces all
  `a_i,b_i` to one and specifies the entire phase vector. Thus invertible
  `L` makes all witnesses necessary for an image-preserving zero
  restriction. Yet fixing every `a_i` to one preserves the image and
  makes the map quadratic. The checker exhaustively tested all 13,512
  zero kernels across nine small maps. It also ran 473 pinned SAT
  comparisons on two concrete packed maps. The latter inspect sampled
  negatives and a programmed witness for each sampled positive address.
- The locked Lean build and axiom audit passed for the two-output support
  identity, the converse surjectivity condition, and the trivial-period
  lemma. The seven-output, circuit-cost and Tal-dependent formula arguments
  are mathematical proofs with separate finite checks.

The next lower-bound target is an inequality across stable original gate
IDs in multiple legal SAT contexts. The paired cubic controls and the
Andreev–Tseitin charge control give falsification cases for such an
inequality. None of the circuit bounds here decides unrestricted SAT.
L-clb-036 remains open.

[Checker](../../experiments/cubic_cluster_hub_check.py) · [Batch](batch.json) ·
[Negative controls](controls.jsonl) · [AIG scores](table_aig.jsonl) ·
[Cluster replay](cluster_replay.txt) · [Hub replay](hub_replay.txt) ·
[Joint witness replay](joint_replay.txt) · [Lean verification](lean_replay.txt)
