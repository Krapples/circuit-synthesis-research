# Order-four projective-plane OR lower bound

This ledger records work on L-meta-4653, the OR-critical case of L-meta-2377. The target is the
edge function of the 105 incidences of PG(2,4), in cyclic coordinates with differences
`0,5,7,17,20`. The target theorem says every fan-in-at-most-two AND/OR circuit computing that
function and meeting the posted per-operand bypass condition has at least 104 OR gates. The
standard edge-term disjunction uses 104 OR gates and 105 AND gates. Stars give the same OR count
with 21 AND gates. The unrestricted lower bound remains open in this work.

## Upstream proof map

| Source | Checked content and remaining obligation |
| --- | --- |
| `R_meta_2377_631` | Reduces L-meta-2377 to monotonicity and cost decrease of OR bypass, and the OR-critical 104 lower bound. `L_meta_4651` gives the bypass result. L-meta-4653 is the outstanding critical case. |
| `R_meta_2377_2` and `L_meta_4053` | The reduction's conjunction-list normalization is already checked in L-meta-4053. Exactly one list entry per OR gate is retained. Each operand and the output become finite sets of earlier references, with a designated false input. The remaining conjunctive-program inequality asks for length at least 104 given all minimal positive pairs and maximal independent zero assignments. |
| `R_meta_4653_37` and `L_meta_8265` | The checked simulation gives the same list of at most one edge-set union instruction per OR to every vertex cover. L-meta-8267 asks whether a common list reaching all 105 edges from every cover's stars must have at least 104 entries. |
| `R_meta_4653_271` and `L_meta_7581` | The checked Gram identity has diagonal five and off-diagonal one. The merged reduction derives area at most 36 for incidence-free rectangles and expresses the target as two families of clauses for subsets of size at most six. The other hypothesis still asks for the OR lower bound from those clauses. |
| `R_meta_4653_731` | Splits backward distinct binary OR normalization from the remaining OR-critical counting argument. The proof of the implication alone does not settle either hypothesis. |
| `R_meta_4653_73` | Splits the same critical bound by AND counts at most 20, 21–45, and at least 46. The merged file dispatches those cases assuming the three bounds. |
| `PEqualNP.MetaComplexity.L663`, `L_meta_696`, `L_meta_697` | L663 counts at least four low merges per line here. Its sum counts at least 84 **gate-line incidences**. L-meta-697 gives uniqueness only for a gate independent of the line inputs. |
| `R_meta_3491_1`, `_436`, `_2` | These reductions concern the total gate count. The first two require a side-pure normalization hypothesis, then a count for the normalized form. The third splits total edge count from vertex-cover cost. None of the reduction files by itself establishes normalization or a type-specific count. |

The leased L-meta-4653 lists `PEqualNP.Defs` as its sole project dependency. Mathlib modules are
also permitted. The other proofs above guide the argument and supply already-checked branches of
their own reductions. Their modules cannot be imported directly into an L-meta-4653 submission.
Check the lease-specific allowlist of any child before moving a proof there. A public desk result
of `not_open` can also mean the step was stood down. Use a checked file or authoritative result
to establish a dependency. At the audit, L-meta-8267 was desk-open, whereas L-meta-6642,
L-meta-6644, and L-meta-7583 were `not_open` and had no corresponding file on the checked tree.

[OR bypass reduction](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/R_meta_2377_631.lean)
· [AND compression proof](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/L_meta_4053.lean)
· [Gram and rectangle reduction](https://github.com/open-goat/pequalnp-proofs/pull/10434)
· [Cover-union reduction](https://github.com/open-goat/pequalnp-proofs/pull/10847)
· [Low merges](https://github.com/open-goat/pequalnp-proofs/pull/910)
· [Two-level normalization and counting cut](https://github.com/open-goat/pequalnp-proofs/pull/7030)
· [AND-count cases](https://github.com/open-goat/pequalnp-proofs/pull/22623)

## Boundary and symmetries

Every minimal positive row is the two endpoints of an incidence. Every maximal negative row is
the complement of an inclusion-minimal vertex cover. For a monotone circuit those two boundaries
imply correctness on all inputs by domination. `check_geometry.py` enumerates the maximal
independent sets by closure of unions of neighborhoods, verifies the transposed calculation, and
independently checks the result by enumerating subsets of size at most six on either side.

There are 25,237 maximal negative rows. The largest minimal covers have 34 vertices, with 105
such covers. The incidence-free rectangle area of 36 occurs at size 6 by 6. The 6 selected points
meet each of the 15 lines outside the rectangle in exactly two points. Indeed their total
incidence is 30 and the Gram identity gives sum of squared degrees 60, so the sum of squared
deviations from two is zero. The dual conclusion holds for the 6 selected lines. `geometry.json`
records all maximal shapes, the exact Pareto frontier, and the cover-size distribution.

Translations and the six affine difference-set symmetries, with point-line duality, act on the
boundary via a subgroup of size 252 and give 125 orbits. `projective_symmetry.py` uses the trace
pairing on the three-dimensional extension of GF(4) to give coordinates for the cyclic graph.
Elementary projective linear maps, field conjugation, and point-line duality give 10 orbits,
one for each unordered maximal independent-set shape. Every permutation used in that calculation
was checked against the incidence graph. A fixed arbitrary circuit need not respect these
symmetries. Orbit representatives may classify invariant geometry or normalize a search after
simultaneously relabeling the circuit. Boundary evaluation of an arbitrary fixed circuit still
requires all rows or a separate implication proof.

## Counting approaches and an obstruction

**Private-edge bound.** Fix a minimal vertex cover and choose one private edge per vertex. The
chosen edges have at most one in any starting star. Label the private edges distinctly and track
the invariant that every available set contains private edges with at most one label. An active
union requires identifying at most two labels. The final full set forces all labels equal and
therefore uses at least one fewer instruction than the number of private edges. This gives a
33-instruction lower bound with a 34-vertex cover. `CoverUnion4653.lean` uses the explicit cover
omitting `0,2,7,8,31,32,37,39`, verifies its incidences in the kernel, and proves the relabeling
argument. This is a scoped bound for the L-meta-8267 model. Combined mathematically with the
checked simulation, it also lower-bounds the number of OR gates in the original model.

**Symmetry strengthens the bound to 34.** For any first instruction, one can choose a cyclic
translate of that 34-vertex cover on which its first operand cannot contribute a label merger.
If that operand contains two distinct incidence edges, it either has no common center or has
one unique common center. Some translate omits that center, so the operand is unavailable.
If it contains just one incidence edge, another translate keeps both endpoints in the cover.
That edge is then absent from the private-edge set. An operand containing no incidence edges
is disjoint from the private set on every cover. The first instruction preserves all 34
distinct labels on the chosen cover, and the remaining list still needs at least 33 merges.
Lean checks the translated covers and the proof. This addresses the first instruction only.

**Exact scope with independent operand centers.** Mark a center if one of the program's
operands lies in its star and contains at least two incidences. If the marked centers form an
independent set, choose their complement as the vertex cover. The only initial sets queried
by the program contain at most one incidence. Initial availability of all other sets can be
discarded because each instruction consults exactly its two named operands. Lean checks this
equivalence along the fold and obtains 104 using the full set of 105 incidences as distinct labels.
Thus every sub-104 program must use star operands on two adjacent centers.

The mathematical extension replaces each endpoint outside the marked centers by a fresh leaf
for its incidence. The resulting graph has 105 edges, and its non-leaf subgraph lies inside the
marked center subgraph. Any cover of the new graph induces a cover of the old graph by taking
the same marked centers and all unmarked original vertices. Project each operand to the new
edges corresponding to its original incidences. A queried set that was initially available and
contained two or more incidences had a marked center, and that center remains available in the
new graph. A singleton incidence is always available. Subset and union implications are
preserved throughout the fold. Lean checks `split_cover_transport` for every cover of the
surrogate and `splitEndpoint_fresh`, which ensures each split endpoint belongs to only its
original incidence. The transport preserves the number of instructions.

If the marked center subgraph is a forest, so is the new graph. The converse cover simulation
would turn its projected program into a monotone circuit using at most one OR per instruction.
For a nontrivial forest, delete a leaf while some edge remains. Along a path from that leaf input
to the output, the first OR can be removed under the zero restriction, since the preceding ANDs
hold the operand at false. Such a path must contain an OR, or the restricted function would be
identically false. Induction on edges gives at least `|E|−1` ORs for the forest. This proves on
paper that a sub-104 program must have a cycle of marked centers. Each leaf deletion that
leaves an edge saves one OR, including in graphs with a cyclic core. Thus any saving over
`|E|−1` must survive leaf deletion all the way to the remaining core. `LeafOrElimination.lean`
checks the elimination and the induction for any finite certificate of leaf deletions.
Applying the induction to every acyclic surrogate still requires a graph theorem producing
the leaf certificate and the corresponding split-incidence edge presentation.

**Uniform bound of 40 in the straight-line circuit model.** The same elimination applies to
any vertex incident to an edge if deletion leaves some edge. An edge using the vertex
witnesses essentiality and another edge witnesses that the restricted function can still be
true. The earliest wire with both properties must be an OR with an operand whose zero
cofactor is identically false. Replace it by an AND with the other operand repeated. The
replacement preserves wire numbering and the restricted function. For PG(2,4), a reverse
spanning-tree traversal rooted at the incidence `(0,21)` gives 40 such deletions. Lean checks
the explicit deletion order and `LeafOrElimination.PG4.lower_bound_40` for straight-line
AND/OR circuits with variable and constant sources. `CompilerBridge.PG4.lower_bound_common_union`
uses the compiler and the evaluator equivalence to transfer 40 to the common-union model.
The earlier direct label argument gives 34 uniformly and gives 104 for independent operand
centers. The exact unrestricted 104-OR statement remains open. The transport and elimination
proofs checked with Lean 4.36.0 under the locked `sat-search/lean`
environment, in 58.862 s for the transport and 34.893 s for the elimination and order.

**Low merges can be shared even when every OR operand is critical.** Choose two different points
on each of the 21 lines. Build one OR tree from the first chosen edge on each line and another
from the second. Merge the two outputs with one OR. At each one-hot line restriction this gate
merges two distinct singleton alive sets. It is a *new* low merge on all 21 lines since each
earlier OR has at most one live edge at that line. Complete the circuit by OR-ing the remaining
63 edge terms into the result. Each OR splits disjoint nonempty sets of edge-minterm witnesses,
so its two bypasses fail on respective positive pairs. This is a 104-OR circuit. A proof based on
L663 therefore needs an amortized count charging the OR gates that build such shared operands.

**Two-level case.** Suppose every AND gate in the output cone combines point and line sums, and
all remaining output logic consists of OR gates. Each contributing rectangle is a star by the
Gram identity. Assign each incidence to one contributing AND gate. Group the gates by star
center, choosing either endpoint for singleton stars. An internal sum with at least two leaves
cannot serve two different centers since their neighbor sets intersect in at most one vertex.
At a center with `t` participating AND gates and `m` assigned edges, at least `m−t` inner ORs
are needed. Otherwise merging the initial singleton labels could not make the `m` leaves lie in
the at most `t` output components. Top OR gates need at least the number of participating AND
outputs minus one. Summing proves 104 for this form and allows arbitrary sharing inside a center.
`output_cover_lower_bound` in Lean proves the shared multi-output `m−t` count. The missing step
for the two-level route is an OR-cost-preserving normalization of arbitrary circuits.

**Converse to the cover simulation.** For a fixed instruction list, write `A_i(S,Z)` for the
availability of `S` after `i` instructions on `Z`. Then
`A_i(S,Z) = A_(i−1)(S,Z) ∨ (S ⊆ X_i ∪ Y_i ∧ A_(i−1)(X_i,Z) ∧ A_(i−1)(Y_i,Z))`.
Put `Z` equal to the complement of the input support. Under complementation, initial failure
of availability is a conjunction of all possible star centers. For the empty set it is false.
Each instruction yields one shared OR of the two prior failure predicates. Each later failure
predicate is a conjunction of its initial failure and all applicable instruction outputs. This
realizes `¬A_final(E,Z)` with one OR per instruction. On a cover the final availability assumption
makes failure false. On a noncover each available set contains only covered edges, so failure is
true. `ConjunctionCompiler.lean` checks this converse for all finite vertex sets. Each rule
emits exactly one OR and otherwise only ANDs, the initial failure of a star is a conjunction
of its possible centers, and the compiled output agrees with the edge signal on all Boolean
assignments. The compiler uses a forward gate list and explicit constant sources. Its Lean
4.36.0 check finished in 32.721 s under the locked workspace. `CompilerBridge.lean` checks
that reversing the gate list preserves both wire values and the OR count. It reused the
two locally compiled modules and checked in 30.439 s.

## Bounded diagnostics and proof transfer

The diagnostic SAT model implements the L-meta-4053 normal form with one bit for each potential
reference to an input or earlier OR. Each sample's conjunction value is constrained to be true
exactly when no selected reference is false. The SAT test omits the false constant because forward
propagation of constant false simplifies AND to false and OR with false to its other input without
increasing OR count. Empty conjunction is true. Unused OR entries pad smaller circuits. The test
uses complete monotone boundaries on small inputs, and independently evaluates each witness on
all rows. This normalization preserves OR count while losing information about the count of AND
gates. It cannot test the AND-capped branches without additional cost constraints.

`profiles.jsonl` is the original 22-worker run at a 105-second cap. The square control has a
verified 2-OR witness. The path control, C6 at four ORs, and four seven-edge incidence subgraphs
at five ORs returned solver UNSAT without proof traces. Fifteen larger subgraphs reached the
cap. No PG(2,4) budget was tested or settled. `cnf-profiles.jsonl` measures construction only.
All 22 encodings together took approximately 0.03 seconds. The timeouts were dominated by solving.
The script caches boundary construction by graph and appends each result to a JSONL checkpoint
when `--output` is supplied. Reopening the frozen checkpoint skipped all 22 prior queries.

The current route is to prove a counting invariant on the compressed or cover-union model.
Small diagnostics can falsify candidate invariants before any full-size search. A future SAT
counterexample must be decoded and checked on the full monotone boundary, then proved as a
concrete circuit in Lean. A future UNSAT result must have a mechanically linked encoding and a
certificate reconstructed or checked inside Lean's kernel, or be replaced by an analytic proof.
The existing solver verdicts alone cannot supply the exact theorem. Run the exact statement and
allowlist through the project's gate before any public submission.

```powershell
python -B sat-search/results/pg4_or_4653/check_geometry.py
python -B sat-search/results/pg4_or_4653/search_or_budget.py --profile-cnf
python -B sat-search/results/pg4_or_4653/search_or_budget.py --output sat-search/results/pg4_or_4653/profiles.jsonl
python -B sat-search/workflow/research.py lean sat-search/lean --source sat-search/results/pg4_or_4653/CoverUnion4653.lean --timeout 100
python -B sat-search/workflow/research.py lean sat-search/lean --source sat-search/results/pg4_or_4653/LeafOrElimination.lean --timeout 100
python -B sat-search/workflow/research.py lean sat-search/lean --source sat-search/results/pg4_or_4653/ConjunctionCompiler.lean --timeout 90
```

To reproduce the bridge check, compile the two source modules to a private cache with the
locked toolchain. Rebuild a cached module when its source or Lean environment changes.

```powershell
$proofs = (Resolve-Path sat-search/results/pg4_or_4653).Path
$cache = Join-Path $PWD.Path '.research/pg4-bridge'
$lake = Join-Path $env:USERPROFILE '.elan/toolchains/leanprover--lean4---v4.36.0/bin/lake.exe'
New-Item -ItemType Directory -Force $cache | Out-Null
Push-Location sat-search/lean
try {
  foreach ($module in 'ConjunctionCompiler', 'LeafOrElimination') {
    & $lake env lean "--root=$proofs" -o (Join-Path $cache "$module.olean") (Join-Path $proofs "$module.lean")
    if ($LASTEXITCODE -ne 0) { throw "Lean module build failed for $module" }
  }
} finally { Pop-Location }
$priorLeanPath = $env:LEAN_PATH
try {
  $env:LEAN_PATH = $cache
  python -B sat-search/workflow/research.py lean sat-search/lean --source sat-search/results/pg4_or_4653/CompilerBridge.lean --lake $lake --timeout 90
} finally { $env:LEAN_PATH = $priorLeanPath }
```
