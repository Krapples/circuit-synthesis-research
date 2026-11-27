# Exact hard-incidence degree and the surviving nonlinear gate count

This follows the [protected elimination and hard-core reserve](../../chatgpt_handoff/protected_amortized_core_handoff.md)
for L-clb-036. The model is the full binary basis (`B2`) with free constants and
wire complements, and the hard target is a complete function. The proof below
gives a bound on surviving nonlinear gates at an affine elimination snapshot.
It is a paper proof with independent finite enumeration, with Lean verification open.

## Exact degree of the fixed-metadata incidence function

Let `H(g, ell)` be satisfiability of `g` clauses, each with three independently
programmed `ell`-bit literal IDs. The low bit selects polarity, and the upper
bits select one of `2^(ell-1)` witness variables. For `ell >= 1` and `g >= 2`,
the algebraic degree over the Boolean ring is exactly `(3g - 1)ell`. With one
clause the function is constant true, of degree zero.

For the upper bound, an ANF coefficient indexed by a set of coordinates is the
parity on the coordinate subcube that frees that set and fixes its complement to
zero. If fewer than `ell` coordinates are fixed, choose an ID bit position
that is free in all slots. Flipping it in every ID is a fixed-point-free
involution on the subcube. For a high bit it renames the witness variables.
For the low bit it complements every witness value. Both preserve SAT, so the
parity vanishes.

For the lower bound, fix a single entire slot to the positive literal `v0` and
free all other bits. Within the first clause, swapping the two free slots
pairs equal-verdict inputs except where their IDs coincide. For each of the
other clauses, first swap two slots and keep only the equal-ID cases. This
leaves two independently chosen literals in that clause, since one is
duplicated. Swapping the two remaining choices preserves the reduced clause, so
only the equal cases survive again. These parity cancellations can be applied
one clause at a time. The resulting parity is over `g-1` unit clauses and one
clause `(v0 OR a)` with a free literal ID `a`.

Inconsistent unit tuples contribute zero. A consistent unit tuple with `q`
assigned variables contributes an even number of choices of `a` if `v0` can
be true. If the tuple forces `v0` false, precisely `q` IDs for `a` are
impossible, one for each assigned variable. The contribution modulo two is
then `q mod 2`. For each fixed ordered tuple of variable names of support size
`q` containing `v0`, there are `2^(q-1)` consistent polarity choices forcing
`v0` false. They cancel for `q >= 2`. The unique ordered tuple with support
`{v0}` and all polarities negative contributes one because `g-1 >= 1`.
The original subcube therefore has odd SAT parity and dimension `(3g-1)ell`.
Taking the fixed slot to have any other literal ID gives the same parity by
witness renaming and complementing. Only an all-zero pin is needed for the
ANF coefficient.

## Transfer through the affine elimination ledger

Take a protected fair-system state with effective dimension `a` and choose one
blocking branch per pair. Select the fixed hard-mode query with all `g` core
groups active and the other groups inactive, as in the preceding handoff.
If the raw core projection from this affine branch is surjective, write it as
`L(u)` for the surviving branch parameters. The circuit restricted to this
query and branch computes `H(g, ell) ∘ L`.

A surjective affine map has an affine right inverse. Affine substitutions cost
zero multiplications in the AND/XOR/NOT model with only AND gates charged. Thus
the multiplicative complexity of `H(g, ell) ∘ L` equals that of `H(g, ell)`:
compose with `L` for one inequality and with a right inverse for the other.
The equality also holds for algebraic degree by the same two substitutions.
The right inverse can be dense. This transfer applies to multiplicative
complexity and degree, while a transfer charging XORs needs an independent cost
argument.

At the fixed query all frozen query functions are constants. Fair-system
auxiliaries are affine functions of the parameters because the affine system
is invertible and reads no active nonlinear gates. Each active nonlinear
binary gate can be written as a product of two signed operands plus a phase,
so it costs at most one multiplication. With `k` such products, write all
affine computations inline as affine forms in the input and earlier product
symbols. Expand the affine output by substituting each product in reverse
topological order in the Boolean ring. The degree increases by at most one per
substitution because each square-free monomial contains the product symbol at
most once. This gives the standard degree bound `degree <= k+1`.
[Reference for multiplicative complexity and the degree bound](https://tsapps.nist.gov/publication/get_pdf.cfm?pub_id=926913)

Consequently at least **`(3g-1)ell-1` still-active nonlinear original gate
IDs** are required whenever `g >= 2`. The initial grammar equations and gates
converted to affine equations contribute no nonlinear IDs. If `Z` counts all
distinct previously deleted or frozen units, then the original circuit size
`B` and the paid grammar embedding overhead `E` obey

```text
B + E >= Z + (3g-1)ell - 1.
```

The counted units in the two terms are disjoint. A valid snapshot with the
claimed core projection and fewer active nonlinear IDs is impossible. The
existing group-cover test supplies the projection certificate. For a positive
effective dimension `a`, the selector-based continuation in the preceding
handoff already requires at least `2a-1` remaining units of all types. The hard
core has `3g ell <= a`, so the hard-mode degree alone gives a smaller total-unit
floor. Adding the two floors would double count. Its new information is the
type of gate that must survive. There is no improvement to the checked
unrestricted SAT lower bound. L-clb-036 remains open.

## Reproduction and finite coverage

```powershell
python -B sat-search/workflow/research.py run sat-search/results/protected_hard_incidence_degree/batch.json --workers 3 --memory-mib 384
```

The independent Python checker enumerates satisfying witnesses and computes the
full ANF by a Möbius transform. It checks every single-slot pin value in eight
profiles, totaling 791,624 raw entries through 18 bits. The 24 surjective affine
lifts use two nuisance coordinates and seeded affine offsets, totaling 149,504
entries through 14 parameter bits. The Node grammar replay checks 270 SAT
verdicts with DPLL and parses 12 additional legal words. The Node selector-only
elimination replay checks stable IDs and 41,680 semantic evaluations. See the [manifest](batch.json),
[ANF and affine-lift output](degree-replay.json), [grammar output](grammar-replay.json),
and [elimination output](elimination-replay.json). All three commands passed in
2.918 s batch wall time with a shared admission estimate of 384 MiB. Peak RSS
was not measured. There were no exact-size solver queries.

The next test is to classify actual nonlinear IDs consumed by rank-one fixing
and pair retirement, then check whether any argument forces a loss of those
IDs faster than this hard-mode reserve drops. The existing selector-only
chain remains the control for any claim based only on selector contrast.
