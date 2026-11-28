# Cofactor bounds on direct readers in AO2

Sol developed the bounds and ran the screens. Luna checked prior work and found
a related restriction-deletion argument for a different basis in
[the first-layer notes](../../NOTES_FIRST_LAYER.md#L1783). The bounds below use
AND and OR with two inputs, no counted constants or unary operations, and a
complete monotone truth table. The SAT probes use live circuits with distinct
operands and the last gate as output.

## Bounds

Fix a set of primary inputs `S`. For every assignment to `S`, each original
gate with a direct operand in `S` becomes a constant or a wire. Propagate
constants and aliases in topological order. If those gates number `d`, a
size-`k` circuit gives a realization of each cofactor with at most `k − d`
gates. This includes cofactors whose outputs are constants or inputs, which
take zero gates for the bound. Thus any lower bound `L` on one cofactor gives
`d ≤ k − L`, and the largest lower bound over the assignments gives the
tightest cap for `S`. Count a gate once even when both operands belong to `S`.

1. **Support.** A cofactor with `r` essential inputs needs at least `r − 1`
   gates for `r ≥ 1`. In the output cone, connectivity requires at least
   `g + r − 1` edges, while the `g` binary gates have at most `2g` incoming
   edges. For constant cofactors use zero.
2. **Read-once obstruction.** For `r ≥ 2`, equality at `g = r − 1` forces
   the cone to be a tree with exactly one occurrence of each essential input.
   In a read-once monotone tree, every minimal true set meets every minimal set
   of inputs forced to zero exactly once. At an AND the true set takes both
   children and the zero set takes one. At an OR the true set takes one child
   and the zero set takes both. The child supports are disjoint, so induction
   gives the claim. A minimal true row and the complement of a maximal false
   row that intersect in at least two inputs give the stronger lower bound `r`.

The [shared helper](../../experiments/ao2_restriction_bounds.py) adds an
auxiliary bit per eligible gate and fixed set. Every selected pair touching
that set implies the bit. A sequential at-most constraint bounds the number
of these bits. For an allowed circuit, set exactly the bits for touching
gates to true to see that the one-way implications suffice. The helper can
also take another valid complete-cofactor lower bound. Transferring the
deletion argument to another gate basis requires proving that its restricted
gates can be eliminated at zero cost.

## Short-interval experiments

Each entry uses one CaDiCaL 1.9.5 worker, complete frontier rows, and a
12-second wall cap for a fixed plain budget. Times are solver seconds from one
run per entry.

| Cofactor bound | Fixed-set widths | Case 6, 7 gates | Case 8, 8 gates |
| --- | --- | --- | --- |
| None | None | UNSAT, 48,197 conflicts, 2.149 s | Wall limit |
| Support | 1 | UNSAT, 59,224 conflicts, 3.300 s | Wall limit |
| Support | 1–2 | UNSAT, 52,571 conflicts, 2.462 s | Wall limit |
| Read-once | 1 | UNSAT, 229 conflicts, 0.005 s | Wall limit |
| Read-once | 1–2 | UNSAT, 351 conflicts, 0.008 s | Wall limit |
| Read-once | 1–3 | UNSAT, 351 conflicts, 0.010 s | Wall limit |

The read-once obstruction tightened four singleton caps in each case relative
to support alone. The singleton read-once encoding took 0.027 seconds to
build in case 6, with 0.032 seconds total inside the worker for the budget.
Extending to triples left the conflict count unchanged from pairs in case 6
and did not finish case 8 within the cap. The width-three screen overlapped
briefly with the small exhaustive checker. The results support keeping the
flags opt-in and using singleton read-once as the first candidate in a broader
screen. Timed-out variants leave their replay scopes open. The archived
case-8 solver verdict is discussed in the [sweep record](README.md).

The [finite checker](verify_restrictions.py) independently enumerated 44,718
three-input circuits through four gates and 7,452 four-input circuits through
three gates. It checked the caps through width three, including outputs
outside the bipartite graph family. It also checked the strict majority
obstruction. With width two and the read-once bound, the sweep verified owned
witnesses at sizes five and six for cases 0 and 1 and reproduced the
plain one-smaller UNSAT verdicts. Both mathematical arguments are recorded
here and computationally tested. There was no Lean run, axiom audit, or
independent check of an UNSAT certificate for this experiment.

The manifests are [support](restriction-screen.json),
[read-once](restriction-read-once-screen.json), and
[width three](restriction-width3-screen.json). The
[result rows](restriction-results.jsonl) identify the batches under
local `.research/batches/`. Each batch's `jobs.jsonl` points to the complete
stdout and stderr. Replay from the repository root with
`python -B sat-search/workflow/research.py run <manifest> --workers 1 --memory-mib 1024`.
