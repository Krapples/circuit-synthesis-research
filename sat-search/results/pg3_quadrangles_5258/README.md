# Two-output quadrangle separation, L-meta-5258

The Singer incidence graph has 26 inputs, 52 incident pairs, and 234
quadrangle rows. A quadrangle row sets its four points and its three
disjoint lines to one. Both designated outputs must accept all incident
pairs. Their conjunction must reject all quadrangle rows, and each output
must individually accept a quadrangle that the other one rejects.
The posted step asks for a smaller realization below 63 gates if the
given circuit has one AND in the cone of another. The unrestricted step
remains open.

## Pinned prefix bounds

Fix stars on one side of the graph and compute their OR in a shared
prefix. Each designated output is an OR of that prefix and its own
suffix result. With two unfrozen stars there are 54 prefix gates and two
reserved output gates, leaving a six-gate suffix. With three unfrozen
stars the prefix uses 49 gates, leaving an eleven-gate suffix.

Only the incident rows not accepted by the prefix and all quadrangle
rows constrain the suffix. On these rows the fixed star products and
all their OR collectors are identically zero. The possibly useful
prefix sources are raw inputs and disjunctions whose supports are
subsets of a frozen neighborhood. Allowing all such subsets covers
every grouping of the prefix ORs.

For each uncovered incident row and each quadrangle, some selected
source must be true on the first and false on the second. Otherwise the
negative row dominates the positive row at every selected source, and
the monotone conjunction of the two outputs cannot separate the pair.
An exact hitting-set enumeration in `support-5258.py` finds a minimum
of nine sources in all 156 two-star scopes, covering all 78 active pairs
in each orientation. A six-gate circuit feeding two outputs accesses
at most eight distinct sources. Its union of backward cones has at
most two components and at most twelve gate-operand edges.

### Three-star exclusion

For the conjunction of the two suffix outputs, allow one additional
AND for a total of at most twelve gates. Fix every raw input outside
the residual graph to zero and intersect every free prefix
disjunction with the remaining raw set. This leaves the uncovered
positive rows unchanged and can only decrease the value on the negative
rows. Forget the private positive obligations for the individual
outputs in this argument.

An exact support search and a separate SAT cardinality check agree
in all 572 scopes. In the 104 common-intersection scopes, a separating
support needs all 13 raw inputs and no provider can be used within
the budget of 13 sources. In the 468 scopes with distinct pair
intersections, a separating support needs at least 12 sources. A
12-source solution uses all raw inputs. A 13-source solution uses all
raw inputs and at most one provider.

A 13-source realization with 12 gates must be a read-once tree.
For the lone-provider case, choose an induced four-vertex path
disjoint from the provider's support and fix all other raw inputs
to zero. The provider becomes zero and the read-once restriction
has exactly the path's accepted pairs. The no-provider case uses
any induced four-vertex path. These facts are checked in
`check-triple-paths-5258.py`. Every nonincident pair of vertices
is contained in a quadrangle row, so monotonicity rules out every
nonedge pair and every singleton of the path. A read-once OR root
would disconnect the path, since no branch could accept a singleton.
A read-once AND root would make its accepted pairs a biclique.
Neither can produce a four-vertex path, even when larger minterms
are unrestricted.

For 12 raw sources and 12 gates, the only additional possibility
is a wire with two readers and every other nonoutput wire with a
single reader. The source set entering through the repeated wire
forms a module of the accepted-pair graph. To see this, a vertex with
an external neighbor must turn the wire on at its singleton.
An internal edge would also turn it on, and then the circuit would
accept that singleton. Thus the set is independent. Every member
has an external neighbor because the graph is connected, so all
members have the same external neighborhood. If the set is the
entire source set, the output after that wire evaluates to the wire
itself by AND/OR idempotence and its cone is read-once. Otherwise
set the module to zero. This removes the only repeated wire and
leaves an induced four-vertex path. The script independently
checks the path assertion after every nonempty subset of a twin
class is removed, including singleton modules.

These bounds apply to the shared pinned-star prefix and two reserved
final ORs. The step has additional open cases outside that family.

## Checked reductions and gate deletion

Three live reductions already occupy the project's slots for this step.
The latest merged cut uses restrictions at an incident point-line
pair outside both designated quadrangles and asks for seven gate
erasures plus a punctured lower bound. The previous merged gate-removal
cut has checked constant-false and AND-input replacement children.
[Restriction cut](https://github.com/open-goat/pequalnp-proofs/pull/22324)
[Gate-removal cut](https://github.com/open-goat/pequalnp-proofs/pull/10585)

`Critical5258.lean` uses checked L-meta-7854. In a minimum-size
realization, fixing any gate to false must destroy an acceptance
on a required positive row or on one of two chosen private rows.
All negative obligations persist under the deletion because each
output can only decrease. This theorem applies to arbitrary positive
and negative sets of one fixed input length.

`QuadrangleCounting5258.lean` checks the counting implication used
to choose an incident pair outside both quadrangles. Among the
points outside the first quadrangle, at least five each have at
least three incident lines meeting it. One of these points lies
outside the second quadrangle too, since that quadrangle has four
points. At least two lines through this point meet the second
quadrangle, and there are only four incident lines, so some line
meets both. The Python finite check verifies the cardinal hypotheses
on all 234 quadrangles and independently finds at least six suitable
pairs for each of the 54,756 ordered quadrangle pairs. This does not
establish the seven erasures.

## Records and replay

Each topology screen ran 22 workers with a 115-second solver cap.
The first 22 pinned runs, with three to six unfrozen stars and
internal suffix outputs, all reached the cap. The compact screen
merges sources agreeing on the cared rows and permits an existing
source as a suffix output. Its 16 two-star scopes were UNSAT in
12.5 to 23.3 seconds, and its six three-star scopes reached the cap.
The recorded topology queries found zero SAT models. An index
correction to the compact witness decoder was made afterward.
The lower bounds above use witnessed finite conditions and
independent enumeration. SAT proof traces and peak memory were
unrecorded. A MiniSat worker access violation prevented the initial
cardinality cross-check from finishing. The retained MapleChrono
cross-check completed all 2,288 cardinality queries with 22 workers.

Run these commands from the research repository root with fresh
output paths. Run `lake env lean` on the two Lean files from the
public project's Lean directory after building the checked dependency.

```powershell
$dir = 'sat-search/results/pg3_quadrangles_5258'
python -B "$dir/search-5258.py" "$dir/replay-topology.jsonl"
python -B "$dir/search-5258.py" "$dir/replay-compact.jsonl" --compact
python -B "$dir/support-5258.py" "$dir/replay-all-pairs.jsonl" --maximal-providers
python -B "$dir/triple-support-5258.py" "$dir/replay-triples.jsonl" --sat
python -B "$dir/check-triple-paths-5258.py"
python -B "$dir/check-quadrangle-incidence.py"
```
