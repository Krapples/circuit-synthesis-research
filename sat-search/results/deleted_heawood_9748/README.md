# Deleted-line Heawood incidence, L-meta-9748

The posted lower-bound step asks whether every AND/OR/NOT circuit for the
listed 13-vertex, 18-edge graph needs at least 23 gates. Its positive
twin is L-meta-9747. The unrestricted 22-gate question remains open.

## Exact monotone minimum

The missing Heawood vertex is line 13 with neighbors 1, 2, and 4.
Starting with a circuit for the deleted-line graph, insert the new
input while preserving the value of every old wire. Append two ORs
on its three neighbors, an AND with the new input, and an OR with
the old circuit output. A 22-gate monotone circuit would give a
26-gate monotone Heawood circuit, contradicting the checked 27-gate lower
bound. Lean 4.36.0 accepted `DeletedHeawood9748.lean` against the actual
merged theorem L-meta-971. The file also proves that any circuit in the
posted basis reaching 22 gates must use a NOT. A 23-gate right-star
circuit was checked independently on all 8,192 assignments.
[Merged Heawood theorem](https://github.com/open-goat/pequalnp-proofs/pull/13091)

## Pinned families

Fix right-hand stars and collect them in a shared OR prefix.
Join the suffix to this prefix with one reserved final OR. With four
pinned stars, two remain and six gates are available in the suffix.
With three pinned stars, three remain and ten gates are available.

Set the frozen center inputs to zero and inactive left inputs to
one. The suffix still computes the residual edge function. Constant
propagation removes the frozen star products, their OR collectors, and
every prefix disjunction containing an inactive input. The surviving
prefix sources are disjunctions of two or three active left inputs
from one frozen neighborhood. Each intersects each residual
neighborhood in at most one point. Any projected circuit using the
actual surviving providers lifts by reconnecting those exact wires.

Every raw residual input must have a path with even NOT parity to the
output. For a left input `a`, choose an incident residual right input
`b`. Keep only `b` true on the right and set all left inputs outside
`N(b)` true. Toggling `a` changes the target from zero to one, with all
other raw inputs and every free provider fixed. The right raw inputs
have the same positive dependence, since providers are purely left.
A circuit with only odd paths from a given source is antitone in that
source when the other sources are held fixed. The left-input toggle
argument is kernel-checked in
`../c4free_9791/Providers9791.lean`.

For a live suffix with `k` gates, `p` required raw sources, `q`
additional providers, and `t` NOT gates, the number of operand
occurrences beyond one reader per nonoutput wire is
`k + 1 − p − q − t`. This is nonnegative. The normalized suffix
has only unary NOTs and binary AND/ORs after constant, alias, and
dead-gate removal. A zero count gives a read-once tree.

- Every two-star residual has seven raw inputs and an induced
  four-vertex path. Six gates therefore force a read-once AND/OR
  formula. A four-vertex path edge function has no such formula.
  An OR root would disconnect its accepted pairs. An AND root
  would make those pairs complete bipartite.
- Four three-star residuals have ten raw inputs. A ten-gate suffix
  with a NOT must be a read-once tree with one NOT and zero providers.
  Some raw input then has only an odd path, which is impossible.
- Sixteen three-star residuals have nine raw inputs. With two NOTs,
  ten gates force a read-once tree with no providers. Each leaf has
  even parity, so pushing NOTs to the leaves produces a monotone
  read-once formula, excluded by the path. With one NOT and one
  provider the unique NOT can only read that provider in a read-once
  tree, since any raw source below it would have odd parity. Fixing
  the support of the provider to zero leaves an induced path and a
  read-once monotone circuit for its edge function.
- The remaining nine-source case uses one NOT and no provider, with
  at most one repeated wire. If there is no repeated wire, a raw
  source has only an odd path. Otherwise call the repeated wire
  `w`. A raw source reaching the NOT must also have a path avoiding
  it. The first split of those paths is necessarily at `w`. Thus
  every raw source in the NOT cone enters it via `w`. At any binary
  gate between `w` and the NOT, an other operand would supply a raw
  source with no avoiding path, or would use the only other branch
  out of `w` and make that branch go through the NOT as well. The
  normalized NOT therefore reads `w` directly.

For the last case, the raw source set of `w` has no other route into
the output. If it is a proper subset, it has a member with an external
neighbor because the graph is connected. That member's singleton must
set `w` to one, since the all-zero internal input and the external
singleton fail, while the edge succeeds. An internal edge would also
set `w` to one, making the output at that singleton accept. This would
contradict the target. The subset is thus independent, and all its
members must have external neighbors and identical neighborhoods.
The nine-source residual graph is twin-free, so `w` reads only one
raw source. Fixing that source to zero leaves an induced path and removes
the only repetition and NOT. If the set is the whole source set, the
output is a Boolean function of `w` alone. A nonconstant target that
rejects the all-zero input must equal `w`, whose cone is read-once.
That again contradicts the induced path.

The exact monotone lower bound excludes a NOT-free suffix grounded in
the actual prefix providers. The direct argument therefore excludes
all 15 two-star and 20 three-star projected scopes at their posted
suffix budgets. The path and twin checks are independently reproduced
by `verify-9748.py`. The argument does not exhaust the unrestricted
topology or allow arbitrary sharing before the pinned prefix.

## SAT records

Each batch used 22 workers and the repository's topology and truth
clauses. The first-gate screen used 24 graph automorphisms, nine
unordered pair orbits, and three vertex orbits. Its 21 first-gate
queries and extra one-NOT query all reached the 125-second cap.
The residual screens allowed all potential providers even when some
could not occur together in one prefix. Both independently
excluded the same sixteen nine-gate and two six-gate queries. All
twenty ten-gate queries reached the 65-second cap in each batch.
With even-path clauses the observed nine-gate UNSAT times were
17.8–29.5 seconds, versus 41.9–58.8 seconds without them.
The exclusions from these SAT runs have no retained proof traces.
Peak memory was unmeasured.

Run from the research repository root with a fresh path for each
record. To replay Lean, build the public L-meta-971 module and
`PermInputs`, then run `lake env lean` from the public Lean directory.

```powershell
$dir = 'sat-search/results/deleted_heawood_9748'
python -B "$dir/verify-9748.py"
python -B "$dir/search-9748.py" "$dir/replay-first-gate.jsonl"
python -B "$dir/residual-9748.py" "$dir/replay-residual.jsonl"
python -B "$dir/residual-9748.py" "$dir/replay-parity.jsonl" --parity
```
