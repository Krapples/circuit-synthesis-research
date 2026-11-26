# Coupled first-gate reader bounds

## Proof audit

The bounds hold for complete functions in the single-output, fan-in-two AND basis with
free constants and complemented edges. Project away inessential inputs. For three or
more remaining inputs, take a minimum AIG and maximize the number of gates whose two
operands are distinct primaries. Every gate is live and none computes a constant or a
duplicate of an available signal up to phase.

Write a first-layer gate as `g = u AND v`, where `u` and `v` are signed primary literals.
The four signed ANDs on `g` and `u` produce `g`, `0`, `u AND NOT v`, and `NOT u`.
The analogous identities hold for `v`. Bypassing a consumer that reduces to an
available wire would decrease size. Replacing it by `u AND NOT v` preserves topological
order and increases the number of first-layer gates. If that replacement makes a gate
dead, deleting the dead gate contradicts minimum size. Thus no consumer of any
first-layer gate also reads either of its primary operands. The same extremal choice
works for all first-layer gates. This normal form need not hold for forced prefixes,
exact-size padded circuits, or arbitrary unnormalized topologies. For example, the
legal circuit `(x AND NOT(x AND y)) AND z` has a consumer that also reads `x`.

For `g` on `i,j` with absorbing values `a,b`, the zeroing of `g` by `i=a` removes `g`
and at least one consumer. If `i` survives `j=b`, there is another reader of `i`,
which is distinct from those gates by the normal form. Swap `i,j` to get the other
absorbing inequality. Fixing a primary to its neutral value removes its direct readers
alone. The live-gate requirement ensures that `g` has a consumer, because a first-layer
gate cannot be the output of a full-support function on three or more inputs.

For the coupled test, `A`, `B`, and `D` indicate the existence of other direct
`i`-only, `j`-only, and joint readers, respectively. These are disjoint classes.
Fixing both inputs eliminates all these readers, `g`, and a consumer of `g`. An
identification eliminates every joint reader and `g`. The parity that makes `g`
constant also eliminates a consumer. This gives all seven inequalities in the
handoff. A gate counted in each such argument is a distinct alias or constant under
that restriction. Counts from different restrictions constrain the same original size.
They are never added across restrictions. The indicators only increase the lower
bounds, so for each value of `D` it suffices to keep the coordinatewise smallest
allowed `A,B`. With `D=0` these are the two survival indicators, and with `D=1` they
are both zero. This reduces the eight profiles to two.

### Additional phase compatibility

If a pair has any `D=1` first gate, it has at least two first gates on the same pair.
They have different absorbing phases, since duplicate gates are removable, and each
has `D=1` because of the other. Sort the four conditional lower bounds for the `D=1`
profile. The second-smallest is a lower bound whenever that pair has at least two
first gates. Take its minimum with the best `D=0` bound for the pair, and then minimize
across pairs. This uses the same cofactors and identifications as the two-profile
screen. It applies to a normalized minimum and gives a local gate-elimination bound.
In fact, the numerical recurrence without the separate regional bound is at most
`3n - 3` for `n >= 1`. Induct from the exact small-input leaves. A single-coordinate
or identification step adds at most three, a double-constant step adds at most five,
and the support-excess term charges at most one per removed input. Taking maxima,
minima, or the second-smallest phase bound cannot raise this ceiling.

## Exact size of `0x07e1`

The independent checker enumerates the exact small AIG minima through three inputs by
sets of available truth tables, quotienting available literals by complementation.
A minimum circuit can omit constants and repeated functions up to phase, so these
sets retain all possible extensions. All three-input tables are reached by depth six.
Of the 24 first-gate orientations on four inputs, 23 give a lower bound of seven from
one of the two absorbing restrictions alone. The remaining orientation is `(i,j,a,b)
= (2,3,1,1)`. Identifying `x3 = NOT x2` makes the proposed first gate constant, removes
its consumer, and leaves the three-input table `0xe7` of exact cost five. This proves
`C(0x07e1) >= 7` using only the small exhaustive table and the local rewrite argument.
An archived seven-gate witness is reevaluated on every assignment. This gives exact
size 7, in agreement with the earlier Percy and ABC solver records in
[`screen_npn4.jsonl`](../baselines/screen_npn4.jsonl). No new solver verdict is needed.
The handoff's timed-out SMT query supplies no exclusion.

## Matched analytical screen

The plain baseline is the repository's mode-2 first-gate recurrence with exact
three-input leaves. The checker agrees with the installed mode-2 implementation on
all 208 essential NPN4 representatives when both use the original leaves. The main
comparison uses a stronger baseline, adding the repository's recursive signed regional
bound while retaining mode-2 identification and the exact leaves. This combines the
features of the existing modes 2 and 3. It already gives 7 for `0x07e1` and reaches the
verified witness size on 96 of 208 essential NPN4 classes. No extension increases
that count. The independently replayed 222-class witness library has full NPN coverage
and provides upper bounds, including for cases where the numerical lower bound is weaker.

The gain columns are cumulative relative to the corresponding baseline. The regional
comparison uses a separate bounded subset of the seeded six-input sample.

| Sample | Regional bound | Targets | Two-sided absorbing | Joint readers | Phase compatibility |
| --- | --- | ---: | ---: | ---: | ---: |
| Essential NPN4 classes | Off | 208 | 1 | 1 | 4 |
| Seeded five-input | Off | 300 | 6 | 6 | 11 |
| Seeded six-input | Off | 80 | 3 | 3 | 5 |
| Complete frozen corpus through seven essential inputs | Off | 89 | 1 | 2 | 2 |
| Essential NPN4 classes | On | 208 | 0 | 0 | 0 |
| Seeded five-input | On | 300 | 1 | 2 | 4 |
| Seeded six-input | On | 16 | 0 | 0 | 0 |
| Complete frozen corpus through seven essential inputs | On | 89 | 0 | 0 | 0 |

With regional bounds on, the five-input batch took 4.05 s for the baseline and
4.14 s for the two-sided extension. The corpus batch took 8.87 s and 10.03 s with no
gain. These are single matched runs and serve as screening evidence only. The
four-input classes `0x0182`, `0x0662`, and `0x17ac` gain from phase compatibility
with the regional bound off. The stronger baseline already covers all three.

The four-input sweep covers every essential NPN class, and the unquotiented handoff
replay checks all 64,594 full-support four-input tables. It reproduces the 384
improvements in the orbit of `0x07e1` with exact leaves and without regional bounds,
plus six improvements in 300 seeded five-input targets. Those 384 tables are one
class. The matched screen reports per-batch analytical timings with cleared memo
caches. It does not measure native fixed-budget search or peak memory. A diagnostic
run with a larger recursive regional sample completed all 80 six-input targets
without a gain, then reached the 120 s wall cap during the corpus batch. The final
bounded manifest completed both jobs, in 15.88 s and 101.46 s, respectively. The
diagnostic timeout carries no solver verdict.

No native, Percy, or Lean change is justified by the measured gains. The normal-form
proof above supplies a paper lower bound and executable finite evidence for the target.
L-clb-036 remains open. Reader profiles could merit another look if a future proof can
charge the same resource consistently across many restrictions or if a held-out
fixed-budget workload shows enough analytical exclusions to pay for this prepass.

## Replay

The archived [`handoff_reference.py`](handoff_reference.py) is the first Python block
of the handoff at `ecb7fcd`. From the repository root, run the bounded workflow job.

```powershell
python -B sat-search/workflow/research.py run sat-search/results/coupled_reader/manifest.json --workers 1 --memory-mib 768
```

The [handoff stdout](handoff_replay.txt) and [matched stdout](matched_screen.jsonl)
record the counts, examples, orientation certificate, witness, and timings.
