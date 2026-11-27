# Theory and asymptotic results

Paper proofs, reductions, and asymptotic bounds. Moved word for word from the root RESEARCH_NOTES.md on November 27, 2026.

For L-clb-036, the protected elimination procedure has rank-one and rank-zero
fallbacks with a stable unit ledger. The fixed-metadata hard incidence core on
`g >= 2` clauses has exact algebraic degree `(3g-1)ell` for `ell`-bit literal
IDs. A surjective affine core projection therefore forces at least
`(3g-1)ell-1` surviving nonlinear binary gates in the full binary basis,
regardless of the affine reconstruction cost. This is a paper proof with
independent finite checks. The unrestricted SAT bound remains open.
[Proof, scope, and replays](results/protected_hard_incidence_degree/README.md)

For quadratic witness lookups, signed Fourier elimination has an exact
support cutoff at polar rank `4k+2` for `k` address bits, using the
minimum size of a nonempty Boolean fiber. Polar ranks and absolute biases
alone fail to determine the image. Two equal-length paired SAT words show
that shared witness IDs can change joint satisfiability while both
individual lookups stay satisfiable. Coupled one-bit quadratic checks
express 3-CNF with unique witness extension per satisfying assignment.
Lean checks the local packed layout and its source-position invariance.
[Proofs, controls, and matched experiments](results/quadratic_witness/README.md)

The deterministic quasi-linear circuit bound for the variable-incidence
quadratic promise passed the independent sparse routing audit. A signed
AIG checks the rank-minor primitive, indexed joins, and polar constraint
routing. The sparse implementation used 917,255 live AND gates versus
1,205,657 for matched dense decoding at the tested `64 x 64` shape with
rank cap two. Dense decoding was smaller at the three smaller sizes.
For a cubic neighborhood kernel of polynomial dimension in `k`, a
residual marginal of `t` bits with an unsupplied cubic monomial cover
of size `h` has a circuit of size `O((n+3^h+2^(h+t)) poly(log n))`.
The exact packed cubic grammar passed finite checks including padding,
balancing and invariant source positions. Unrestricted SAT distinct-gate
accounting remains open.
[Routing proof, gate counts, cubic bound and grammar replay](results/sparse_quadratic_routing/README.md)

The cubic cluster and simultaneous hub arguments passed independent audit.
An explicit signed AIG verified exact batched Walsh scores, with direct
decoding smaller at every tested positive marginal dimension. A separate
packed cubic control needs the full linear marginal and every essential
witness under coordinate restrictions, yet has a linear-size AIG at fixed
metadata. Its exact Andreev projection gives a signed De Morgan formula
lower bound `Omega(n^(20/7)/((log n)^2 log log n))` using Tal's theorem.
This complements the joint Andreev–Tseitin charge control. The remaining
lower-bound target concerns gate roles across multiple legal contexts.
[Audit, proofs, AIG counts and replays](results/cubic_cluster_hub/README.md)

The audited Andreev projection gives a near-cubic De Morgan formula lower
bound for paired SAT at all sufficiently large even lengths, using Tal's
published shrinkage theorem. A linear-size AIG for that exact restriction
concentrates all path multiplicity above one in selector-only gates. This
obstructs a charge to distinct gates based on the restriction and path counts
alone. [Proofs, Lean scope, and replay](results/andreev_projection/README.md)

An exact paired-grammar projection sends each SAT length `n` to one Hamming layer
of length `3n+12` and weight `2n+5`. With monotone threshold guards and the
Berkowitz–Valiant slice compiler, an `O(n^alpha)` monotone size bound on this family
is equivalent to unrestricted SAT in `O(n^alpha)` for every fixed `alpha > 1`.
An orbit-averaging obstruction rules out positive-coordinate projections from
ordinary CLIQUE to any guarded single layer. The equivalent lower bound remains
open. [Reduction, obstruction, and replay](results/sat_weight_slice/README.md)

The coupled first-gate reader audit gives a separate lower-bound proof of the known
seven-gate AIG minimum for `0x07e1`. The inexpensive absorbing extension raises
the exact-leaf identification bound from 6 to 7, and the stronger recursive regional
baseline already reaches 7. Against that baseline the extension improves one of 300
seeded five-input tables and none of the 89 frozen corpus targets. Extra reader and
phase compatibility tests stay experimental. [Proof, finite replay, and comparison](results/coupled_reader/README.md)

For sparse SAT conflict templates, the exact fork kernel has at most three occurrences
per mode variable. A linear-size parsimonious reduction gives fully genuine, linear
width-two/three mode cores that survive matching contraction and pure-literal or unit
reduction. All residual clauses of width at least three instead admit a satisfying
assignment by Hall's theorem. [Proofs and independent replay](results/fork_mode_core/README.md)
