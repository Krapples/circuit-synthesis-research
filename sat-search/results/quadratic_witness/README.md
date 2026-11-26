# Quadratic address images and shared-witness SAT contexts

Audited against [handoff 575f7be](https://github.com/Krapples/circuit-synthesis-research/commit/575f7be).
Two workflows were tested on the same degree-at-most-two maps over GF(2):
exact signed Fourier inversion for fiber counts and enumeration modulo the
common subspace of neutral witness translations. A third workflow certifies
image support with rank-truncated signed Fourier inversion. The support test
below has an unconditional cutoff and a lower, optionally inconclusive cap.

## A rank cutoff that decides exact image support

Let F map q witness bits to k address bits, with degree at most two in every
coordinate. For each k-bit mask lambda, write N_lambda for the signed integer
sum of (-1)^(lambda dot F(x)) over all 2^q witness assignments. Character
orthogonality gives 2^k times the fiber cardinality at address a as the sum of
(-1)^(lambda dot a) N_lambda over all masks. Retain signs in the inversion.

An interacting pair x,y in the scalar quadratic has the form
xy + xA + yB + C, with A and B affine in the remaining variables. Its signed
sum over x,y is 2(-1)^(C+AB). Eliminate pairs this way. If the remaining
polynomial is affine, its sum is zero when nonconstant, and otherwise its
sign times the number of remaining assignments. Stopping after T pairs gives
the rigorous bound |N_lambda| <= 2^(q-T); each eliminated pair lowers the
maximum magnitude by a factor of two. Translating x by B and y by A is an
invertible affine change of coordinates, after which the eliminated pair
contributes an isolated rank-two polar block. The retained signs are
computed exactly.

The fiber indicator is the Boolean polynomial product of the k equality
indicators, one for each output bit. After multilinear reduction it has
degree at most 2k. A nonzero Boolean polynomial on q bits of degree at most d
has at least 2^max(0,q-d) ones. To see this, split on the last variable as
g0 + x g1. If g1 is nonzero, each nonzero value of g1 contributes exactly one
one across the two extensions of that input. Apply induction using degree
d-1. If g1 is zero, the smaller truth table is duplicated, giving the same
bound. For d >= q the nonzero premise suffices.

Consequently, the fiber cardinality is either zero or at least
2^max(0,q-2k). Take **T = 2k+1** and skip exact signed sums for characters
reaching that many pivots. The constant character is never skipped. The
absolute error in each estimated fiber cardinality is less than 2^(q-T)
when any term is skipped, because fewer than 2^k characters are missing.
This is less than half the minimum positive cardinality. Thus, for image
membership, all scalar quadratics of polar rank at least **4k+2** can be
discarded simultaneously, without computing their signs or exact ranks.
For smaller q, an unattainable cutoff simply computes every signed count.

The implementation also certifies answers at a smaller cutoff. Let H be the
span of character masks whose computed signed sums are nonzero. Compute the
exact signs and sums for all of H and form the inverse Walsh sum using only
H. It equals |H| times the number of witnesses matching the projection of
the address observed by H. A zero marginal certifies absence. All remaining
unknown characters lie outside H, and their total contribution can be bounded
by the number of unknown characters times 2^(q-T). For a nonzero marginal,
use that error interval and the minimum positive cardinality to certify
presence or absence. An interval allowing either outcome is unresolved.
The prototype still considers all 2^k characters. Neither the paper
argument nor the measurements give a quasi-linear size bound for this
promise or a lower bound on distinct gates.

## The neutral quotient and a sign counterexample

The neutral translations form the subspace K of directions z with
F(x+z)=F(x) for all x. For each output polynomial f, first impose that z
lies in its polar radical. On the common radical, f(z)+f(0) is linear.
Intersect the kernels of those linear restrictions to obtain K exactly.
A representative from each coset suffices, and each observed fiber count is
then multiplied by |K|. The checker constructs a complement by using the
coordinate units at the pivot columns of the equations defining K. This
method can save all dependence on redundant directions during enumeration.
Its enumeration is still exponential in the quotient dimension.

On four bits a,b,c,d, take the same first two outputs ab+bd+a and ac+ad+b.
For the third let w=ab+ac+ad+bd+cd+a. Compare w+c with w+d. All arithmetic is
over GF(2) and the first output is the least significant address bit.
The polar ranks of the eight characters are [0,2,2,4,2,2,4,2] in both cases.
The signed sums are [16,0,0,4,0,8,4,0] and [16,0,0,4,0,8,-4,0].
The first map reaches all eight addresses, while the second misses 1 and 6.
Polar rank and the full profile of absolute signed sums cannot decide
surjectivity.

There is also an infinite sparse family where the common neutral quotient
does nothing. Take the first two outputs x0*x1 and x0*(1+x1).
Use a third output that sums disjoint pair products over the remaining
witnesses and couples x0 to the first variable in each pair. Extra outputs
can be affine. The polar radical of the first output forces z0=z1=0, and
the third then forces every remaining coordinate to zero. The interaction
graph is connected. The first two outputs exclude the address prefix 11,
so mere connectedness and a trivial common radical do not imply a full
image.

## Simultaneous constraints and clause incidence

For the 300-bit paired-grammar example, the first check forces ab=1.
In one context the next check forces a(1+b)=1. In the other it forces
a(1+c)=1. The auxiliary output variables are distinct. Each standalone
check is satisfiable. The joint instances are respectively unsatisfiable
and satisfiable. Equal-width ID renaming changes eight digit bits and
keeps every clause position and word length fixed. The independent
paired-grammar parser and enumerator reproduce all five outcomes.

A family made only of required products of signed literals inherits an
easy test. Each accepted product pins both underlying literals to one.
Collect these requirements, sort by variable identifier, and look for
opposite signs within a run. The existing sorting-network control applies
even with arbitrarily many shared identifiers in this family. The
300-bit example makes the joint-witness effect visible for a test, while
its repeated product-only form has an efficient common evaluation.

Even one-bit quadratic lookup checks can express 3-CNF when their number
grows and they share variables. For each clause let f1,f2,f3 be the
falsity bits of its literals. Introduce one witness t and require the
two zero-lookups t+f1*f2=0 and t*f3=0. The first forces t, so the second
accepts exactly when the clause holds. Each satisfying original assignment
has one extension to all new witnesses. This is a linear number of bounded
arity equations from 3-CNF. It also yields a paired SAT encoding of
O((variables+clauses) log(variables+clauses)) bits by replacing each gate
with constant-width clauses and choosing consecutive identifiers.
Checking each image separately loses the required joint witness.
Applying the exponential-in-k support algorithm to all output bits at once
does not yield a quasi-linear bound when the number of checks grows.

The small equal-length pair isolates a semantic effect any proposed
cross-context accounting rule must capture. It supplies no bound on how
often a gate can serve several such contexts. L-clb-036 remains open.

## Reproduction and measured scope

Run from the repository root.

```powershell
python -B sat-search/workflow/research.py run sat-search/results/quadratic_witness/batch.json --workers 2 --memory-mib 512
```

The four jobs finished in 14.42 seconds wall time, with one worker and a
256 MiB reservation per job. Peak memory was not measured. Across 216
seeded small maps, exact Fourier and quotient histograms agreed with brute
force. The check covers 2,370 signed character counts, 1,488 neutral
directions, and 2,432 address decisions at the guaranteed cutoff, including
cases where elimination actually stopped. There were 2,920 unknowns in
7,782 address checks across deliberately shorter caps. Every classified
answer agreed with brute force. The 3-CNF reduction was exercised on 72
formulas, checking unique extension for every original assignment.

The benchmark uses identical maps for all methods. Times are elapsed
Python seconds per operation from one run. Full inversion and the quotient
compute counts. The support test only classifies addresses and uses the
aggressive cap k+2 in this table.

| Family at 192 witnesses and 8 address bits | Quotient dimension | Full inversion | Support test | Unresolved addresses |
| --- | ---: | ---: | ---: | ---: |
| Random sparse | 192 | 0.452 s | 0.041 s | 0 |
| Lift of a 12-dimensional map by disjoint parities | 12 | 0.047 s | 0.048 s | 0 |
| Connected with omitted addresses | 192 | 0.102 s | 0.022 s | 0 |
| Connected with small positive fibers | 192 | 0.017 s | 0.009 s | 58 |

The quotient histogram finished only on the parity-lifted family under
the dimension-14 cap. Its 192-witness run took 0.058 s. The guaranteed
support cutoff matched exact inversion on all 20 benchmark maps. The
finite timings identify surviving algorithmic structure. They do not
certify a circuit-size result.

## Affine compression replay

The [affine compression handoff](../../chatgpt_handoff/quadratic_compression_handoff.md)
at `afe3753` uses the same minimum fiber size to bound the probability
that a random affine sketch misses a reachable address. For distinct
sketch inputs `u,v`, the augmented coefficient vectors `(1,u)` and
`(1,v)` are linearly independent over GF(2). The sampled images are
therefore pairwise independent, which suffices for the variance bound.
The fixed-list obstruction applies when the sketches are chosen before
the quadratic map. It leaves open sketches computed from the map.

The replay passed 2,192 pinned SAT checks, 180 exact histogram comparisons,
4,880 compressed evaluations, and 128 fixed-sketch counterexamples.
Full images survived in all 84 small sampled instances. The separate
rare-fiber control had 22 misses in 256 sketches. The deterministic rank
cutoff above still operates on the full witness space and visits every
character. Its runtime measurements do not test the handoff's proposed
randomized circuit or resolve deterministic compression for varying
incidence.

[Replay manifest](compression_replay_batch.json) · [Replay output](compression_replay.txt)

The subsequent deterministic checker at `a3fb7b7` used simultaneous
orthogonal blocks to find an input-dependent subspace. It passed 1,000
truncated rank-certificate checks, 3,300 image-bit checks on 232 maps,
and 57 high-rank checks on compressed maps. The subspace was strictly
smaller on 128 maps. The benchmark above tests rank-truncated inversion
independently of this construction. Evaluating deterministic compression
as a circuit requires accounting for how it finds the subspace from
variable-incidence input data.

[Deterministic checker](../../chatgpt_handoff/deterministic_quadratic_check.py) · [Replay output](deterministic_replay.txt)

## Checked coordinate layout

`SatBridge.PackedAndreevLemmas` checks the programmed literal evaluation,
chunk evaluation, ordered source IDs, and invariance of source positions
under equal-width auxiliary and tag changes. The position invariant also
holds for concatenated chunks. This verifies the local packing interface
used to compare contexts with different identifier assignments. The
quadratic image and shared-constraint proofs above are mathematical proofs
with separate finite checks.

[Lean source](../../lean/SatBridge/PackedAndreevLemmas.lean) · [Lean verification](lean_replay.txt)

[Checker](../../experiments/quadratic_witness_check.py) ·
[Batch manifest](batch.json) · [Finite checks](checks.jsonl) ·
[Matched measurements](bench.jsonl) ·
[Permutable replay](permutable_replay.txt) · [Affine replay](affine_replay.txt)
