# Petersen guard substitution for L-meta-7893

The posted claim excludes an exactly binary AND/OR circuit (B) of size 16–18
that computes the Petersen edge function after input (x_0) is replaced by
(x_0 ∨ h). The guard (h) is a wire evaluated with (x_0=0), and gates through
that wire cannot read input 0. The claim posts 15 edge rows, 15 maximal independent
rows, and ten rows on which the guard must be false.
[Parent reduction spelling out the rows](https://github.com/open-goat/pequalnp-proofs/blob/501dda8586110abcaebe0ea32060309d020bb2ee/lean/PEqualNP/Outside/R_meta_2590_491.lean)

[Guard7893.lean](Guard7893.lean) checks that the guard must be internal. It also
proves that if the guard fires on an assignment with no edge in the graph
minus vertex 0, its input with bit 0 erased is exactly mask 200 or 772. These
two masks are the alternating triples of the distance-two six-cycle. Neither
contains a neighbor of vertex 0. Consequently the guard's contribution to the
target is just its conjunction with the edge function minus vertex 0. A one-gate
guard must be an AND of an edge of that graph. A separate permutation enumeration
verifies that these edges fall into two orbits under the graph automorphisms
fixing vertex 0, represented by ((1,2)) and ((2,3)).

[Expand7893.lean](Expand7893.lean) verifies the physical circuit underlying the
search. Insert (mathrm{OR}(x_0,h)) immediately after the guard, then reindex the
remaining gates and redirect their reads of input 0 to the inserted gate.
The proof checks evaluation, legality, the cost of one extra gate, and that
the inserted OR is the unique gate that reads raw input 0.

[Upper7893.lean](Upper7893.lean) gives a base with 19 gates, hence a 20-gate
expanded circuit. Delete the two edges ((1,2)) and ((1,6)), compute the
remaining 13-edge graph with a 17-gate star cover centered at (0,3,7,8,9),
and use two gates for (h=x_1∧(x_2∨x_6)). The guard forces (x_0) high on
the two deleted edges so they are accepted by the retained edge ((0,1)).
Python independently checked all 1,024 assignments. Lean also checked a
vertex-cover lower bound of six. For the construction class in which the
retained and deleted edge sets use separate star covers and the deleted-edge
output feeds one OR with (x_0), the union of both covers covers the full graph.
Their total cost, including that OR, is therefore at least (15+6-1=20).
The 19-gate expanded question remains open beyond this construction class.

## SAT coverage

Each run used 22 workers, the repository's gate encoding and MapleChrono. Graph
monotonicity makes the posted 30 rows sufficient for a witness, and the decoder
checks all 1,024 assignments after contracting the guard OR back to the
original representation. The no-dead-gate and no-duplicate-operand constraints
apply after reducing a candidate. The special OR survives that simplification
because the output depends on raw input 0. The canonical variants place all
guard ancestors first, then the guard and the special OR. They partition by
prefix length and order operands within the two gate blocks. The distinct
variant merges ordinary wires equivalent on the tested rows, keeping the special
OR and prohibiting a replacement that would create another raw input-0 reader.
The guard cannot merge with a primary because every nonzero input is true on
some guard-off row.

| Run | Bound per search | Completed scope |
| --- | --- | --- |
| [Baseline](L-meta-7893-search.jsonl) | 150 s | Both first-operator shards UNSAT at sizes 9–12. Both open at every size 13–19. |
| [Canonical prefix](L-meta-7893-canonical.jsonl) | 180 s | All 22 shards open at sizes 13–19. |
| [Distinct labellings and short-guard orbits](L-meta-7893-distinct.jsonl) | 180 s | All 22 shards open at sizes 13–19. |
| [Repair of the 20-gate witness](L-meta-7893-repair.jsonl) | 95 s | One pinned 19-gate slice UNSAT, 21 open. The slices pin the guard and selected suffix gates after removing a gate from the 20-gate template. |

The gate count refers to the expanded circuit in the search logs. An output
depending on ten inputs needs at least nine binary gates in its cone. UNSAT
figures are solver verdicts without proof certificates. The logs record solver
work and wall-time caps, with no peak-memory measurements.

```powershell
python construct-20.py
python search-7893.py
python search-7893.py --canonical
python search-7893.py --distinct
python search-7893.py --repair
```

Run the scripts in a directory without the same log names, or move the existing
logs aside. The Lean files use v4.36.0 and the public project definitions.
`Upper7893.lean` imports the locally built `Expand7893.lean` module.
`Guard7893.lean` uses the generic wire monotonicity proof from the accepted L-meta-8029 module.
[Accepted wire monotonicity proof](https://github.com/open-goat/pequalnp-proofs/blob/cf3e0737b74e5103a45bfdf5d2bbab705f2dab91/lean/PEqualNP/Outside/L_meta_8029.lean)
