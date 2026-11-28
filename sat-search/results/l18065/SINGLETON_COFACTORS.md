# Cofactor cuts for singleton regions

Sol developed the restriction argument and ran the screens. Luna checked the
archived comparator interval and prior provider-layout work. The target is
the full eight-input truth table of `comparator-05` in the frozen synthesis
corpus. Gates are two-input ANDs or ORs. The previously established interval
is 14–21 gates. This work tests budget 14.

## Restricting a closed set of regions

Eight pairwise incompatible primaries force eight read-once regions. At
budget 14 there are at most seven extra reads. Thus each region owns just
one primary, and each non-output region has a provider wire with exactly
two reads. This is the only reader-count pattern that survives the
coexistence bound.

Take a subset of non-output regions that contains every provider of each
of its members. For example, a prefix of any order from inputs to output
is such a subset. Fix those regions' primaries. Their outputs become
constant because they have no outside providers. Each eliminated region
with `l` provider ports had `l+1` leaves and `l` gates. Each remaining
region keeps its own free primary, and after fixing `t` port leaves its
tree needs at most its original gate count minus `t`. Count the ports
sourced in the removed regions, including those consumed inside the set.
Each region in the set supplies two ports, so fixing `p` primaries saves
at least `2p` gates. Extra simplification or aliases can only increase
the savings.

If one cofactor needs more than `k−2p` gates, those primaries cannot
form a prefix. More generally, at least one provider port must enter the
set from outside. The opt-in encoder applies these cuts only when every
primary pair is incompatible, there are as many primaries as regions,
and every provider has two reads. In the compact crossing encoding, a
witness selects a port. Its source must be outside the set, and its
unique owning region must be inside.

## Iterations at budget 14

1. The fixed threshold screen found 25 excluded prefix sets, leaving
   27,072 of the 40,320 input orders. The small bounds come from the
   checked 2-of-4 six-gate exclusion, the prior 2-of-5 nine-gate
   exclusion, and AND/OR duality.
2. The [cofactor checker](check_prefix_cofactors.py) tried additional
   four- and five-input saturated cofactors. It also recursively checked
   whether every possible first region is excluded by at least one
   assignment to its primary. The verified evidence gives **39 excluded
   sets**, 16 of size three and 23 of size four. It leaves **20,448**
   orders. The checked table lists 12 direct small-cofactor queries,
   including six exclusions verified with 766 reverse-unit-propagation
   steps. Three additional five-input exclusions follow by the recursive
   restriction argument. This recursive screen gave no exclusions of
   shorter parent prefixes. [Checked cofactor records](singleton-prefix-cofactors.json)
3. The crossing cuts strengthened these restrictions to cover any closed
   subset, regardless of the chosen order. Representing a crossing by
   its port reduced the extra crossing clauses from 8,023 to **4,201**.
   On the comparator, the baseline local encoding has 230,752 clauses.
   Adding the 39 prefix clauses alone gives 230,791, and the compact
   combined encoding has 234,992.

All six comparator runs hit the six-second worker cap. This includes
the matched controls, the threshold and checked-prefix variants, and
both crossing encodings. The 14-gate budget remains open. The compact
variant preserved an independently evaluated eight-gate witness on
`hypergraph-21`, including one nonvacuous closed-set cut. It also
reproduced the eight-gate exclusion for `threshold-5-3` with a checked
trace. A finite encoding check agreed with the direct crossing test on
all 12,096 four-region layout, port-placement, and subset combinations.

The reduction is a paper argument. The proof checks cover the small
encoded cofactor exclusions and the stated control. There was no Lean
or axiom audit.

## Replay

The [result rows](singleton-cofactor-results.jsonl) identify the runner
batches for the [threshold-prefix](singleton-prefix-screen.json),
[checked-prefix and crossing](closed-cofactor-screen.json), and
[compact crossing](compact-cofactor-screen.json) screens. The older
crossing rows used one witness per possible source-port/target pair.
The current encoder uses the compact variant.

```powershell
python -B sat-search/results/l18065/check_prefix_cofactors.py comparator-05
python -B sat-search/results/l18065/check_prefix_cofactors.py --check-encoding
python -B sat-search/workflow/research.py run sat-search/results/l18065/compact-cofactor-screen.json --workers 1 --memory-mib 1024
```
