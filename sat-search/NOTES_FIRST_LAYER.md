# First-layer constraints in Percy SSV

## Implemented scope

The C++20 driver supports `--first-layer edges`, `--first-layer all`, and the independent
`--first-layer-budget`. Codes 2, 4, 8 and 14 are Percy's four normalized AIG operators. Typed
primary-primary and mixed-primary presence variables are equivalent to the selected fanins and operator
bits. A shared native C++ routine computes target-side clauses once per specification, then deduplicates and
removes supersets by subset testing on packed boundary masks. The driver installs the result before CEGAR
adds simulation rows. All options are opt-in. This is free-NOT binary cost.

For any chosen fanins, the remaining circuit receives information from the primary-primary gate outputs
and the primary coordinates it reads directly. If every selected feature agrees on two cared assignments,
topological induction gives equal outputs. A pair with different labels must therefore distinguish on
one of the selected features. At Hamming distance one this also enforces the first-layer projection of the
derivative reader rule. A masking first-layer gate cannot itself supply the required distinction.

For the budget bound, let `h` be the number of first-layer gate **occurrences**, `m` the number of distinct
mixed primaries, and `r=B-h` the number of remaining gates. In a trimmed circuit with `r>0`, each of the
`h+m` boundary signals and each non-output remaining gate needs one reader among the remaining gates.
There are `2r` fanin slots, so `2r >= h+m+r-1`, or `B >= 2h+m-1`. The degenerate trimmed `r=0` case has
one first-layer gate and no mixed primaries. The counter charges twice for each selected first-layer step,
including duplicate typed gates. This bound needs trimming and works at fixed budgets under that assumption.
It neither requires no-reapplication nor makes the existing minimum-preserving reader caps exact-size rules.

The driver bounds the packed prototype to two through five inputs. Partial tables use only cared pairs
and are supported in standard SSV when row zero is labeled. Percy's CEGAR simulator compares the full
table and its normalized basis fixes row zero, so the new options reject unsupported partial driver
combinations explicitly. The complete-table cycle cutoff and signed automorphism symmetry remain
disabled. The two named Python prototype scripts were absent from the available checkout. Existing
symmetry clauses stay on for this experiment because these first-layer conditions hold for every
circuit represented by the trimmed encoding. The budget option rejects `--nosym`, which disables trimming.

## Verification and screening

An independent AIG enumerator checked 130 exact fixed-budget jobs on three inputs at two and three gates,
including output-complemented functions and one partial care set. 60 were feasible and 70 infeasible.
All five configurations matched the expected verdict, and each returned chain was simulated independently.
[Raw correctness replay](results/baselines/first_layer_oracle.jsonl)

The initial hard-set screen used the first eight complete four-input cases from the frozen hard-NPN file,
four workers, Satoko CEGAR, an 8 s wall cutoff per job and a 20,000-conflict cutoff per solver call. Clauses
are added to the same SSV encoder. All 40 jobs returned unknown before proving a minimum. Across the 34
budgets finished as UNSAT by every configuration, the recorded search work was:

| Configuration | Conflicts | Decisions | Propagations | CEGAR rows | Added clauses |
| --- | ---: | ---: | ---: | ---: | ---: |
| Percy | 133,308 | 203,932 | 3,618,836 | 223 | 0 |
| Edges | 95,451 | 165,573 | 3,965,246 | 125 | 20,492 |
| All pairs | 93,666 | 163,431 | 3,786,811 | 113 | 21,723 |
| Budget | 139,683 | 212,652 | 4,761,383 | 224 | 7,652 |
| All pairs + budget | 80,488 | 141,576 | 3,875,724 | 116 | 27,983 |

At budget seven, Percy finished 2 exclusions, edges finished 3, and each other mode finished 4. Joint verdicts
agreed. These are solver verdicts without independent UNSAT proof packets. An earlier Percy process remained
active on another job, so the search-work screen supports no conclusions about elapsed speed or PAR-2.
Each record includes encoding time, CNF counts, peak working set, and the per-budget Satoko counters.
The observed increase in propagations motivates reducing the cost of presence clauses before a wider run.
[Raw hard-set screen](results/baselines/first_layer_hard_screen.jsonl)

## Reproduction

```powershell
$env:PERCY_BUILD_DIR = 'percy-first-layer-release'
& 'sat-search/baselines/build/build_percy.bat'
$percy = 'external/percy-first-layer-release/percy_run.exe'
python sat-search/baselines/first_layer_check.py check sat-search/logs/first_layer_oracle_replay.jsonl --exe $percy --workers 4
python sat-search/baselines/first_layer_check.py screen sat-search/logs/first_layer_hard_replay.jsonl --exe $percy --workers 4 --limit 8 --seconds 8 --conflicts 20000
```

## Exact residual completion at the boundary bound

When the bound is tight, every first-layer occurrence, directly read primary, and non-output
residual gate has exactly one reader in the residual circuit. The residual DAG is a binary
read-once tree on that fixed boundary. Its only extra structural condition is that two mixed
primary leaves cannot be siblings. Such a pair would create another first-layer gate.
Equivalently, each nontrivial subtree must have a first-layer occurrence among its leaves.
Conversely, attach each fixed first-layer occurrence to its leaf in any tree with this property.
The result has exactly the prescribed first layer, mixed inputs, and gate count. De Morgan's
laws make the signed-leaf AND/OR tree and free-NOT AIG descriptions equivalent in binary cost.

Plain phase-first completion can be too permissive. For `H=(ab)`, `M=(c,d)`, and
`f=ab(c|d)`, the three boundary columns can take all eight combinations. The unrestricted
completion `H & (c | d)` has a forbidden cherry. Each allowable three-leaf tree must first
combine `H` with `c` or `d`. For either choice, the target has three distinct cofactors on
the remaining primary (`0`, `1`, and that primary). A single intermediate bit can distinguish
at most two. Thus this fixed boundary is infeasible. A different first layer realizes the
target with three gates.

The shared C++20 kernel `tight_residual.hpp` decides the constrained completion directly.
Its state is the leaf-occurrence subset and the truth vector projected onto the cared rows.
It tries the two leaf phases, deletes nontrivial primary-only subsets, and joins complementary
subsets by AND and OR. By structural induction this generates exactly the legal truth vectors.
Equal vectors in the same subset have identical behavior in every parent context. The Python
binding exposes the query separately. It supports partial labels for fixed boundaries, caps
the width at six leaves and returns unknown if the pair-combination allowance runs out.

The Percy flag `--tight-residual` queries this kernel after a SAT model and before CEGAR
simulation. It applies to trimmed, complete, two- through five-input AIG problems. Every checked
model has `2h+m=B+1`. It allows up to 128 queries per budget and 4,096 candidate joins per query.
Only a proved infeasible query yields a clause. The clause fixes the typed first-layer
occurrences at their current step positions and one selected reader per mixed primary. Any
model retaining those facts has at least the same occurrences and primaries. Trimming and
equality forbid adding any others, so the excluded residual problem is unchanged. Feasible,
unknown, and out-of-scope queries fall through to Percy. The driver still extracts and verifies
its own chains under its own constraints.

`--tight-residual-set-cuts` uses the existing presence literals for distinct first-layer types
and mixed primaries. A model with those `h` types has at least `h` occurrences, so the same
equality argument applies regardless of their positions. When a type repeats, Boolean presence
cannot express its multiplicity and the driver uses the original step-position clause.

### Verification and bounded search

- The independent bottom-up AIG merge oracle matched all **19,939** direct queries. Coverage
  includes every partial labeling of an independent three-wire boundary for each possible
  positive first-layer count, and 256 seeded four-wire queries. The replay separately checks
  the phase-first counterexample, a feasible alternate boundary, and width and work limits.
  [Direct record](results/baselines/tight_residual_direct.jsonl)
- **113** fixed-budget Percy jobs matched direct circuit enumeration. Set clauses were exercised on
  feasible and infeasible jobs, and every SAT chain was evaluated independently.
  [Oracle replay](results/baselines/tight_residual_oracle.jsonl)
- In the first hard-set screen, step-position clauses with all-pair and budget constraints
  added 956 exclusions and completed the same budgets as those constraints alone. With
  no distinction or budget constraints, step-position clauses increased both conflicts and
  decisions on the 34 shared completed budgets.
  [Initial screen](results/baselines/tight_residual_hard_screen.jsonl)

The set-cut ablation used the same first eight hard four-input cases, one worker, Satoko,
an 8 s per-job wall limit, and 20,000 conflicts per solve. All 24 jobs hit the solver limit
before establishing a minimum. On the 35 budgets excluded by all three configurations:

| Configuration | Conflicts | Decisions | Propagations | CEGAR rows | Residual cuts |
| --- | ---: | ---: | ---: | ---: | ---: |
| All pairs + budget | 108,505 | 182,105 | 5,301,307 | 125 | 0 |
| All pairs + budget + step-position cuts | 105,497 | 260,004 | 5,580,065 | 124 | 956 |
| All pairs + budget + set cuts | 99,668 | 178,336 | 4,949,233 | 97 | 98 |

Set cuts reduced the number of learned boundary clauses by 89.7% relative to step-position
cuts and simulation rows by 22.4% relative to the control on those budgets. They completed
three size-seven exclusions, versus four for the other two modes. Joint solver verdicts
agreed. The screen did not produce independent proof packets or establish a runtime or
minimum gain. All residual options remain opt-in.
[Set-cut ablation](results/baselines/tight_residual_set_screen.jsonl)

### Positive slack

For `r>0`, let `s=B-(2h+m-1)`. Summing `d_v-1` over the boundary and non-output residual
wires, with readers counted only in the residual, gives exactly `s`. Thus at most `s`
such wires are repeated. Split the residual DAG into regions at the `q<=s` shared residual
outputs. There are `q+1` read-once regions over `h+m+q+s` leaf occurrences in total. Indeed,
the sum of reader counts over the boundary and those `q` providers equals that total, and
the other residual wires are internal to their regions. The no-primary-cherry condition still
applies. At slack one, the decomposition below exhausts the possible multiplicities.

```powershell
& 'sat-search/native/build_native.bat'
python sat-search/experiments/tight_residual_check.py
python sat-search/baselines/first_layer_check.py check sat-search/logs/tight_residual_oracle_replay.jsonl --exe $percy --workers 4 --modes base residual all+budget+residual all+set-cuts all+budget+set-cuts
python sat-search/baselines/first_layer_check.py screen sat-search/logs/tight_residual_screen_replay.jsonl --exe $percy --workers 1 --limit 8 --seconds 8 --conflicts 20000 --modes base residual all+budget all+budget+residual
python sat-search/baselines/first_layer_check.py screen sat-search/logs/tight_residual_set_replay.jsonl --exe $percy --workers 1 --limit 8 --seconds 8 --conflicts 20000 --modes all+budget all+budget+residual all+budget+set-cuts
```

## Slack-one completion and boundary extension

Exactly one residual wire has two readers at slack one. If the wire is on the boundary, the
residual unfolds to one tree with the single repeated pair of boundary occurrences. If it
is internal, its fanin cone is a read-once provider on a proper boundary subset. The remaining
tree reads the other boundary wires and two occurrences of the provider. The subset is proper
because a decoder with only the two provider occurrences would have identical fanins.
The converse follows by identifying the repeated leaves or connecting the decoder leaves to
the provider output. In both cases the native tables reject a two-leaf subtree made from the
same wire, and any nontrivial subtree with only raw-primary leaves. Equal truth columns of
distinct wires retain their distinct occurrence bits.

Packed signed truth vectors are deduplicated per subset. Decoder root joins try both output
phases and test an AND pair only if both oriented columns contain the desired one-set.
For each provider subset the kernel first partitions the cared rows by the remaining
boundary columns. In any fiber with both labels the decoder is a nonconstant function of
one bit, so the provider must equal the target or its complement throughout that fiber.
Different fibers may choose different orientations. This is a necessary test before decoder
synthesis. Provider truth vectors are tested once per complement class.

For a proved infeasible slack-one boundary, an antecedent retaining its first-layer
occurrences and mixed primaries can admit at most one extra mixed primary. A new first-layer
occurrence would cost two units. Each possible extra primary is queried with tight completion.
If every extension is infeasible the clause negates the antecedent alone. Otherwise it
requires at least one extra primary with a feasible or unknown extension. An unknown exact
boundary produces no clause. When typed first-layer gates repeat, the antecedent fixes their
positions and operators to preserve multiplicity. Positive extension literals still use
mixed-primary presence.

`--slack-one-residual` works with trimmed CEGAR, full tables with two through five inputs,
and first-layer presence variables. It can be enabled independently of the tight completion
flags. The native API supports arbitrary care masks in a 64-bit table. Its boundary width is
at most six, with at most seven leaf occurrences. In the driver each budget gets up to 128
slack-one queries with an independent tight-query allowance. Each slack-one query has a shared
100,000-unit work limit, a 25 ms deadline polled periodically, and up to 4,096 joins per
tight extension. The deadline is also checked before each extension. Memoized entries are
bounded by the work limit and are released after each query. Trace output is opt-in via
`--trace-slack-one`.

### Verification

The attached `slack_one_residual.py` was run directly. It reproduced the 2,000 direct DAG
oracle cases, 20,841 rejections out of 20,953 generated provider candidates, and 65 pure
cuts on 120 extension queries. Its three 80-query Python runs took 4.197 s, 2.104 s, and
0.861 s on this replay with both ablations enabled cumulatively. The attachment SHA-256
is `445178193244A1D71F41A726E78D52E7663328D1878E63B256053022EF5578C8`.

The C++ binding matched all 1,000 slack-one queries from that oracle with care holes
inserted between rows. It found 569 boundary-repeat completions and 13 internal-provider
completions, and excluded 418 queries. It matched all 120 generated extension decisions.
Additional cases exercised both allowed and excluded extra primaries in the same
conditional cut, repeated-wire operands, equal columns of distinct wires, width, work and
deadline exits, and retention of unknown extensions. Percy matched the fixed-budget DAG
oracle on 38 runs across its control and slack-one modes, with every SAT witness checked
independently. The previous tight-residual implementation is retained for the control.
[Native verification](results/baselines/slack_one_native_oracle.jsonl) and
[Percy oracle replay](results/baselines/slack_one_percy_oracle.jsonl)

### Matched Percy screen

The 43 hard four-input NPN targets ran on one worker with Satoko CEGAR, an 8 s safety cap
per process and 20,000 conflicts per solve. Both configurations use all-pair distinctions,
the boundary bound, and tight-residual set cuts. Neither configuration reached a
verified witness or established a minimum under these limits. All 86 jobs ended at
the solver limit. No independent proof packets were emitted.

| Metric | Control | With slack-one cuts |
| --- | ---: | ---: |
| Size-seven exclusions | 13 | 17 |
| Conflicts on 185 jointly excluded budgets | 535,445 | 530,860 |
| Decisions on jointly excluded budgets | 960,375 | 954,772 |
| Propagations on jointly excluded budgets | 26,978,668 | 26,874,237 |
| CEGAR rows on jointly excluded budgets | 566 | 561 |
| Solver wall seconds on jointly excluded budgets | 6.525 | 7.326 |
| End-to-end process wall seconds, summed over 43 targets | 32.025 | 34.810 |

Across all 43 targets, 98 of 246 slack-one queries were excluded and 148 hit an
allowance. Exclusions yielded 70 pure cuts and 28 conditional cuts. Of the 65
extensions evaluated, 4 were excluded and 61 remained unknown. The queries
spent 0.748 s in completion including extensions. The size-seven improvement
comes with higher elapsed time in this bounded comparison. The mode remains opt-in.
[Untraced benchmark](results/baselines/slack_one_percy_screen.jsonl)

A separate trace on the first eight targets captured 42 queries representing 34 distinct
boundaries. There were 18 exclusions, 24 work-limit returns and no feasible completions
across those 42 observations. The provider test rejected 7,717 of 7,761 candidate columns.
The queries cost 0.132 s in total. The attached Python oracle independently checked 30
distinct captured boundaries of width at most five. A bounded offline C++ replay at
2,000,000 units excluded 12 of 16 distinct boundaries previously recorded as unknown.
The remaining four stayed open. This identifies incomplete coverage under the current
work cap. The next algorithmic target is to cut repeated-boundary root search on dense
five- and six-wire obligations before considering higher limits.
[Captured boundaries](results/baselines/slack_one_percy_captured.jsonl)

```powershell
$ref = 'C:\Users\Carson\Downloads\slack_one_residual.py'
$percy = 'external/percy-first-layer-release/percy_run.exe'
python $ref
python sat-search/experiments/slack_one_native_check.py $ref
python sat-search/baselines/first_layer_check.py check sat-search/logs/slack_one_oracle_replay.jsonl --exe $percy --workers 4 --modes all+budget+set-cuts slack-one-trace
python sat-search/baselines/first_layer_check.py screen sat-search/logs/slack_one_screen_replay.jsonl --exe $percy --workers 1 --limit 43 --seconds 8 --conflicts 20000 --modes all+budget+set-cuts slack-one
python sat-search/baselines/first_layer_check.py screen sat-search/logs/slack_one_trace_replay.jsonl --exe $percy --workers 1 --limit 8 --seconds 8 --conflicts 20000 --modes slack-one-trace
python sat-search/experiments/slack_one_native_check.py $ref --captured sat-search/logs/slack_one_trace_replay.jsonl
```

## Projected roots and provider parity

For one target phase let `P` be its positive cared rows. Each child of an AND root
must be constant on the fibers of its projected inputs. To contain `P`, it must
contain every fiber touching `P`. The intersection of these two minimal forced
sets must equal `P`. The native kernel checks both output phases before building
either child table. A passing phase still needs an exact structural completion.

For a proposed provider allocation, each projected provider-input fiber represents
one unknown bit. Within a mixed-label fiber of the remaining inputs, every
positive-label provider fiber must have opposite parity to every negative-label
provider fiber. The resulting bipartite constraint system describes arbitrary
Boolean provider columns on the observed rows. A contradiction excludes the
allocation before provider formula generation. In direct mode, when there are
one to three components, the kernel fixes one component phase to quotient by
global complement and tries the at most four remaining columns. Each column
must pass exact provider recognition and exact decoder completion. Other allocations
fall back to the provider table and the existing per-column distinction test.

The opt-in `--residual-filter root|parity|direct` selects cumulative ablations.
All three activate projected roots in slack-zero queries, including boundary
extensions. The slack-one paths use the same structural subset rules for repeated
boundary wires, provider recognition, and decoder search. The original mode is
`off`. Projection work and provider allocation tests are charged against the
existing counters. The production limits still allow 4,096 units per slack-zero
query and 100,000 units and a 25 ms deadline per slack-one query. Unknown exact
results yield no clause, and unknown extensions retain their positive literals.

### Verification

The supplied native check built under MSVC C++20 with assertions enabled. It matched
3,000 independent provider systems and 6,000 root phases. The supplied Python
reference matched 1,810 full DAG cases. Its root-plus-parity times on the three
synthetic workloads were 0.346 s, 0.530 s, and 4.400 s, against 0.845 s, 1.246 s,
and 13.783 s for its optimized baseline. The production integration matched all
1,810 DAG cases in all four modes, including 905 at slack zero and 905 at slack
one. The native checks scattered cared labels across a 64-bit mask. Percy matched
76 fixed-budget oracle runs and every SAT chain was independently simulated.
[Native oracle record](results/baselines/residual_filter_native_oracle.jsonl) and
[Percy oracle replay](results/baselines/residual_filter_percy_oracle.jsonl)

### Frozen Percy boundary replay

All 34 distinct boundaries from the previous capture were replayed with the
production 100,000-unit work cap and an offline 2,000,000-unit cap. Replay used no
wall deadline, the same per-extension 4,096-unit limit, and the same boundaries
and order in every mode. A recorded status of infeasible refers to the exact
boundary. Its extensions are assessed separately. All decisive results agreed
with the attached Python filter implementation, including the four six-wire
boundaries.

| Mode | Excluded at 100,000 | Seconds | Candidate joins | Provider allocations examined | Allocations rejected by parity | Provider candidates | Pure cuts justified |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Off | 18 | 0.093 | 2,055,162 | 244 | 0 | 7,732 | 14 |
| Root | 22 | 0.079 | 1,547,258 | 298 | 0 | 10,022 | 21 |
| Parity | 22 | 0.078 | 1,527,054 | 298 | 218 | 531 | 21 |
| Direct | 22 | 0.076 | 1,526,342 | 298 | 218 | 44 | 21 |

At 2,000,000 units the baseline excluded 30 boundaries and left four six-wire
boundaries unresolved. Each projected-root mode excluded all 34, including those
four and all 12 five-wire boundaries that had required the higher baseline
cap. The parity mode used 5,343,576 joins in 0.251 s versus 8,624,969 joins in
0.346 s for the baseline. Direct enumeration made 393 exact provider queries and
reduced the provider candidates passed on by the enumerator from 9,937 to 1,294,
with comparable elapsed time. Eleven of the twelve remaining production-cap
failures were exhausted in repeated-boundary completion before a provider allocation
was tested.
[Boundary-by-boundary replay](results/baselines/residual_filter_captured_replay.jsonl)

### End-to-end Percy ablation

All four modes used slack-one cuts, tight set cuts, all-pair distinctions, and
the boundary bound on the 43 hard four-input targets. Runs used Satoko CEGAR,
one worker, an 8 s process limit, and 20,000 conflicts per solve. Each of the
172 jobs hit the solver limit, so no mode established a minimum. The 183
jointly excluded budgets had agreeing verdicts. These are solver results
without independent proof packets.

| Mode | Size-seven exclusions | Conflicts on jointly excluded budgets | Tight cuts | Slack-one pure / conditional cuts | Slack-one joins across all jobs | Provider allocations / parity rejections | End-to-end seconds |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Off | 17 | 473,093 | 661 | 70 / 28 | 14,389,589 | 1,445 / 0 | 35.072 |
| Root | 18 | 293,888 | 2,541 | 643 / 22 | 30,367,024 | 9,488 / 0 | 41.122 |
| Parity | 18 | 294,728 | 2,553 | 644 / 39 | 30,208,757 | 9,603 / 6,817 | 41.005 |
| Direct | 18 | 294,728 | 2,553 | 644 / 39 | 30,137,834 | 9,609 / 6,822 | 40.858 |

The filters changed the CEGAR path and the sample of boundaries examined. Root
alone reduced conflicts by 37.9% and simulation rows from 540 to 288 on the joint
exclusions. It increased the number of slack-one queries from 246 to 836 over
the full workload. The gap between fixed-boundary joins and total joins reflects
this change in search work. Parity and direct gave comparable end-to-end
results. All filter modes remain opt-in.
[Matched Percy runs](results/baselines/residual_filter_percy_screen.jsonl)

### Follow-up root condition

For any phase that passes the projection test, let `A` and `B` be the forced
positive row sets of the left and right children. Every realizable left child
must contain `A` and be zero on `B \ P`, because the right child is forced
one there. The symmetric condition holds on `A \ P` for the right child.
Closing these required zeros over the corresponding child fibers gives
partial child obligations that could be propagated before generating full
child tables. Matching the obligations alone does not finish the root,
because the two children can still introduce a shared positive row outside
`P`. This refinement was derived here and has not been implemented or benchmarked.

### Replay commands

```powershell
$ref = 'C:\Users\Carson\Downloads'
$percy = 'external/percy-first-layer-release/percy_run.exe'
New-Item -ItemType Directory -Path external/residual-parity-check -Force | Out-Null
cmd /d /c 'call "C:\Program Files\Microsoft Visual Studio\18\Community\VC\Auxiliary\Build\vcvars64.bat" >nul && cl /nologo /std:c++20 /O2 /EHsc "C:\Users\Carson\Downloads\residual_parity_native_check.cpp" /Foexternal\residual-parity-check\parity_check.obj /Feexternal\residual-parity-check\parity_check.exe && external\residual-parity-check\parity_check.exe'
python "$ref/residual_parity_filter.py"
& 'sat-search/native/build_native.bat'
$env:PERCY_BUILD_DIR = 'percy-first-layer-release'
& 'sat-search/baselines/build/build_percy.bat'
python sat-search/experiments/residual_filter_check.py $ref
python sat-search/experiments/residual_filter_check.py $ref --capture sat-search/results/baselines/slack_one_percy_captured.jsonl --output sat-search/logs/residual_filter_captured_replay.jsonl
python sat-search/baselines/first_layer_check.py check sat-search/logs/residual_filter_oracle_replay.jsonl --exe $percy --workers 4 --modes slack-one slack-one-root slack-one-parity slack-one-direct
python sat-search/baselines/first_layer_check.py screen sat-search/logs/residual_filter_screen_replay.jsonl --exe $percy --workers 1 --limit 43 --seconds 8 --conflicts 20000 --modes slack-one slack-one-root slack-one-parity slack-one-direct
```

## Target-directed partial obligations

The optional native `directed` backend replaces the full-column witness decision
for a fixed occurrence tree. An AND root with obligations `(P,N)` needs both
children to contain `P`. It enumerates attainable columns `a` for the child
with fewer occurrences. A column `a` that contains `P` reduces the other
child's obligations to `(P,N & a)`. This equivalence is exact for a fixed
split and output orientation. Both output orientations are tried.

Projection closes each obligation over the fibers of the child's input columns.
A fiber receiving both labels is impossible. If the larger child is forced to
one on a negative row, the enumerated child must be zero on that row. After
this test, columns that induce the same closed negative obligations on the
larger child are interchangeable. The memo key consists of the occurrence
subset and closed positive and negative masks, canonically ordered up to output
complementation. Since each call uses a strictly smaller subset, recursive
failure establishes infeasibility. Caps and deadlines yield unknown without
installing a failure in the memo. Optional dominance skips a negative obligation
set containing one already found infeasible in the same split and phase.

The Percy flag `--residual-backend directed` selects this tree solver and
`--residual-backend dominance` adds obligation dominance. The default
`columns` backend remains executable. The existing provider allocation
search and provider parity filter still apply. In direct-filter mode, parity
candidates get exact target-directed provider checks. Other allocations still
enumerate attainable provider columns, then use target-directed decoders.
Slack-zero boundaries and extensions share the same backend. A slack-one
call gives each subquery the remaining work and the original absolute
deadline. Slack-zero calls retain the 4,096-unit allowance. Slack-one calls
retain the 100,000-unit allowance and 25 ms deadline in Percy. The two
backends charge different operations.

The adapter gives each occurrence its own leaf index and aliases only the
two occurrences of the repeated underlying wire. A raw-primary pair or two
occurrences of the same wire cannot be siblings. Witnesses carry the phases
and occurrence indices, plus the provider subset and column when present.
A Python caller can use `directed_completion` to reconstruct these witnesses.
If a fallback provider column was enumerated without a witness, a requested
witness is reconstructed within the remaining limits. A blocked reconstruction
reports unknown. Percy still extracts its own SAT witnesses, which the
benchmark harness evaluates independently.

### Verification

The supplied Python check passed 1,980 independent DAG queries. The supplied
MSVC C++20 check passed 2,400 merge-oracle comparisons and all 995 generated
fixtures in stream mode, with 318 feasible and zero unknown fixtures. The
integrated directed backend matched 990 slack-zero and 990 slack-one DAG
queries with dominance disabled and enabled. All **2,452** native witnesses
were independently evaluated, including 14 internal-provider witnesses.
Checks exercised deadlines, exhausted work, empty care, and conservative
extension masks. All 57 fixed-budget Percy runs matched the independent
circuit enumerator.
[Native oracle summary](results/baselines/residual_directed_native_oracle.jsonl) and
[Percy fixed-budget replay](results/baselines/residual_directed_percy_oracle.jsonl)

The supplied Python benchmark repeated the speedup on each synthetic workload.
Full-column direct-filter times were 0.366 s, 0.539 s and 4.597 s. Directed
times without dominance were 0.078 s, 0.153 s and 0.181 s. On the 30 wide
queries, directed pair joins fell from 3,027,192 to 8,560. Those are Python
reference figures.

### Fixed Percy boundary replay

All modes used the current direct provider filters, the same 25 ms query
deadline, the same 512 MiB Windows Job Object commit cap, and the same 4,096-unit
extension allowance. Five interleaved samples per mode and boundary gave
stable statuses. Time is the sum of the 34 per-boundary medians and includes
extension checks. Work counts describe different charged operations. The
full-column path counts signed pairs, while the directed child tables count
pairs of complement classes before trying their phases.

| Backend | Exclusions at 100,000 units | Pure cuts justified | Sum of median times | Work | Joins |
| --- | ---: | ---: | ---: | ---: | ---: |
| Full columns | 22 | 21 | 73.4 ms | 2,192,851 | 1,526,342 |
| Directed | 34 | 34 | 14.5 ms | 459,328 | 6,466 |
| Directed + dominance | 34 | 34 | 14.1 ms | 455,508 | 6,466 |

At 2,000,000 units and the same deadline, full columns still left four
boundaries open and took 173.0 ms. Both directed modes again excluded all
34 in about 14 ms. This includes the 12 queries unresolved in the prior
production replay, eleven of which previously exhausted the allowance
before reaching provider synthesis.
[Captured boundary replay](results/baselines/residual_directed_captured.jsonl)

### End-to-end Percy comparison

All three modes used all-pair distinctions, the boundary budget, tight set cuts,
slack-one cuts, and direct provider filtering. The 43-target screen used Satoko,
one worker, the same 512 MiB Windows process-family commit cap, an 8 s process
deadline and 20,000 conflicts per solve. Every job hit a solver limit without
establishing a minimum. The 187 jointly excluded budgets agreed, and there were
no independent proof packets for these hard-set exclusions.

| Metric | Full columns | Directed | Directed + dominance |
| --- | ---: | ---: | ---: |
| Size-seven budgets excluded | 18 | 19 | 19 |
| Conflicts on 187 jointly excluded budgets | 461,807 | 454,425 | 454,425 |
| Elapsed seconds on jointly excluded budgets | 8.832 | 7.078 | 7.087 |
| Tight cuts | 2,553 | 3,208 | 3,208 |
| Slack-one pure / conditional cuts | 644 / 39 | 1,075 / 0 | 1,075 / 0 |
| Slack-one queries / unknown | 845 / 162 | 1,075 / 0 | 1,075 / 0 |
| Slack-one joins across all jobs | 30,137,834 | 56,495 | 56,495 |
| All residual check seconds | 2.302 | 0.412 | 0.408 |
| Largest solver peak working set | 22.9 MiB | 26.6 MiB | 25.5 MiB |
| Total end-to-end seconds | 41.144 | 40.181 | 39.723 |

Directed visited more slack-one boundaries and excluded every visited one.
Dominance reduced directed states from 28,642 to 28,425 and produced the same
cut totals and CDCL counters in this screen. One sequential run is insufficient
to establish a reliable elapsed-time difference between the two directed modes.
Dominance and the directed backend remain opt-in.
[Matched Percy records](results/baselines/residual_directed_percy_screen.jsonl)

### Follow-up on repeated occurrences

When a tree state of width `w >= 3` contains both occurrences of a repeated
wire, swapping them preserves truth columns, raw status, and all node rules.
An unordered split that keeps them together is fixed by the swap. The
`2^(w-2)` splits separating the occurrences form pairs, since there is at
least one other leaf. Keeping one representative of each pair removes
`2^(w-3)` root splits before structural filtering. A witness at the kept
split still uses both occurrence indices. Subset memoization could also
identify states that differ only by one of the two occurrence indices, with
the stored witness relabeled on lookup. The split counts and preservation of
the raw-leaf root rule were checked exhaustively for widths three through
seven, including all compatible raw-leaf masks. This reduction has not been
implemented in the benchmarked backend.

### Replay commands

```powershell
$directedRef = 'C:\Users\Carson\Downloads'
$percy = 'external/percy-first-layer-release/percy_run.exe'
python 'C:\Users\Carson\Downloads\residual_target_recursion.py' --check --bench
New-Item -ItemType Directory -Path external/residual-directed-check -Force | Out-Null
cmd /d /c 'call "C:\Program Files\Microsoft Visual Studio\18\Community\VC\Auxiliary\Build\vcvars64.bat" >nul && cl /nologo /std:c++20 /O2 /EHsc "C:\Users\Carson\Downloads\residual_directed_check.cpp" /Foexternal\residual-directed-check\directed_check.obj /Feexternal\residual-directed-check\directed_check.exe && external\residual-directed-check\directed_check.exe'
python 'C:\Users\Carson\Downloads\residual_directed_fixtures.py' | & 'external/residual-directed-check/directed_check.exe' fixtures
& 'sat-search/native/build_native.bat'
$env:PERCY_BUILD_DIR = 'percy-first-layer-release'
& 'sat-search/baselines/build/build_percy.bat'
python sat-search/experiments/residual_directed_check.py $directedRef
python sat-search/experiments/residual_directed_check.py $directedRef --capture sat-search/results/baselines/slack_one_percy_captured.jsonl --output sat-search/logs/residual_directed_captured_replay.jsonl
python sat-search/baselines/first_layer_check.py check sat-search/logs/residual_directed_oracle_replay.jsonl --exe $percy --workers 1 --memory-mib 512 --modes slack-one-direct slack-one-directed slack-one-dominance
python sat-search/baselines/first_layer_check.py screen sat-search/logs/residual_directed_screen_replay.jsonl --exe $percy --workers 1 --memory-mib 512 --limit 43 --seconds 8 --conflicts 20000 --modes slack-one-direct slack-one-directed slack-one-dominance
```

## Exact slack-two completion

For a trimmed size-`B` free-NOT circuit whose output is after the first
layer, let `h` count typed first-layer **occurrences** and let `m` count
distinct mixed primaries. The residual has `h+m` boundary wires and
`B-h` binary gates. Its excess is `s = B+1-(2h+m)`. At `s=2`, every
extra read is either on the boundary or an internal output. With no shared
internal output, the extra reads are distributed among boundary wires. One
shared output can have three readers, or two readers with one repeated
boundary wire. Two shared outputs have two readers each and may feed
independent regions or be nested.

Cut each shared internal output at its outgoing edges. Its region is a tree
on available occurrences, and the regions can be processed in provider
topological order. Reader-count distributions and allocations enumerate
every such decomposition. At each provider, opposed labels in a fiber of the
other available signals must be separated by the provider output. This
imposes equality and inequality relations on its input fibers. Consistent
component orientations give candidate columns for exact tree recognition.
The alternative path enumerates provider trees and tests their columns.
The final region uses target-directed completion. Every tree preserves
distinct fanins, exact occurrence use, and the ban on cherries with two
raw primaries.

A failed frontier stores one entry per still-available distinct wire, keyed
by normalized cared truth column, raw status, and remaining reader count.
The sorted multiset preserves separate equal-column wires. Together with the
ordered suffix of pending provider multiplicities it gives a bijection
between the remaining choices of equivalent frontiers. Previous regions
constrain the rest only through the live wires and their counts. Free phases
allow column normalization. Only proved failures enter this per-query cache.
The optional singleton filter uses the fixed polarity of a wire appearing
once in a provider tree. A forced output difference along that coordinate
links component orientations to the same phase variable across all such
pairs. Contradictions exclude an allocation. Consistent parity and phase
systems still require exact tree recognition.

### Extensions and cut scope

After proving the exact boundary infeasible, retaining its first-layer
occurrences and mixed-primary presences leaves two units for extension.
One additional mixed primary leaves slack one, two leave slack zero, and
one extra first-layer occurrence leaves slack zero. The latter includes
types already present. The adapter checks those extensions with the
existing directed slack-zero and slack-one kernels. Its clause negates the
old occurrences by their SAT positions and the old mixed presences. It
adds a positive literal for every feature in a feasible or unknown extension.
The added-gate literals range over positions outside the old first layer.
This preserves multiplicity even when an added type matches an old one.
A union of extensions in one clause may admit combinations already shown
infeasible, which weakens the cut while keeping it valid.

The adapter uses 100,000 work units for the exact search and each slack-one
extension, 4,096 for each tight extension, and a single 25 ms deadline
shared across all of them. The per-budget Percy query cap is 128. An
unknown exact boundary produces no clause. Unknown extensions are retained.
Percy integration is opt-in for complete, trimmed AIG CEGAR and two to five
primary inputs. The standalone native engine also accepts partial cared
columns, which the Python differential check exercises.

### Stronger clause for a proved-infeasible singleton

Suppose an extension containing just a new mixed input `x` is proved
infeasible. Under the original boundary and presence of `x`, only one
unit remains. Every completing extension must therefore add a second mixed
input `y` whose tight pair `{x,y}` remains feasible or unknown. This gives
a clause with the original negative antecedent, a negative literal for
`x`, and positive literals for those `y`. The rule is valid even if the
unextended slack-two boundary was feasible, since the antecedent includes
`x`. An infeasible tight extension can similarly exclude its entire
presence antecedent. This is a derivation for future ablation. The current
adapter emits only the union clause.

### Native checks and captured boundaries

The three supplied programs built and ran with MSVC in C++20 mode. The DAG
oracle checked 4,470 complete and partial queries, including three feasible
witnesses with two internal providers. The separate unateness oracle checked
2,500 cases. In the generated benchmark rerun with 2,000,000 work units and
25 ms per query, mode 0 completed 139 of 200 queries, including seven
exclusions. Mode 3 completed 164, including 26 exclusions. The archive's
published completion totals were 138 and 191 under its GCC run. The checks
agree on the qualitative gain and the absolute deadline-sensitive counts
differ between runs. The in-repo Python harness independently enumerates
small exact DAGs with complete and partial care, reconstructs and checks
native witnesses, and tests duplicate wires, extensions and exhausted limits.
It passed 4,224 mode-by-query oracle comparisons plus the focused tests.
The 96 fixed-budget Percy checks agreed with forward DAG enumeration at
small sizes and with plain all-row Percy on three hard size-seven budgets.
They exercised 102 slack-two queries, including 14 feasible residuals
and 48 pure clauses.
[MSVC archive test and benchmark output](results/baselines/slack_two_archive_msvc.txt)

The directed slack-one control emitted 90 observations of actual slack-two
boundaries on the first eight hard Percy targets. After deduplicating by
target, sorted first-layer multiset and mixed mask, 44 remained. They came
from size-seven and size-eight searches and had no repeated first-layer type.
Every decisive replay result was an exclusion, and every excluded boundary
justified a pure position-based cut. At the 100,000 work limit every unknown
exhausted its work allowance. Elapsed time includes extension checks and
the Python call. These are single sequential passes.

| Native replay mode | Excluded / 44 at 100k | Total at 100k | Excluded / 44 at 2M | Total at 2M |
| --- | ---: | ---: | ---: | ---: |
| No parity pruning or cache | 8 | 152.5 ms | 38 | 635.6 ms |
| Parity plus direct provider columns | 30 | 111.5 ms | 44 | 161.7 ms |
| Plus failed-frontier memo | 34 | 111.4 ms | 44 | 155.3 ms |
| Plus singleton unateness | 35 | 107.5 ms | 44 | 143.7 ms |

All four modes used the same 25 ms limit. Memo recorded 377 frontier hits
at 100k. With unateness enabled, 809 provider allocations failed the phase
test, and directed tree calls fell from 7,763 to 4,884 while more boundaries
completed. At 2M the nine boundaries still open in unate mode at the
production allowance were all excluded.
[Raw traces](results/baselines/slack_two_percy_captured.jsonl)
· [100k replay](results/baselines/slack_two_captured_replay.jsonl)
· [2M replay](results/baselines/slack_two_captured_replay_2m.jsonl)

### Matched Percy screen

The three modes shared all-pair distinction, the boundary budget, tight set
cuts, and directed slack-one. The 43-target hard screen used one Windows
worker, a 512 MiB process-family commit cap, an 8 s per-target deadline and
20,000 Satoko conflicts per solve. Every run closed sizes three through six.
All jobs stopped at a solver limit with no verified upper bound or minimum
from this screen. Percy reported the exclusions below; independent proof
packets were unavailable for the hard budgets.

| Metric | Directed slack-one | Plus slack-two memo | Plus memo and unateness |
| --- | ---: | ---: | ---: |
| Size-seven exclusions / 43 | 19 | 38 | 41 |
| Size-eight exclusions | 0 | 0 | 0 |
| Conflicts on 188 jointly excluded budgets | 476,965 | 205,103 | 186,807 |
| Solver seconds on jointly excluded budgets | 7.436 | 3.120 | 2.907 |
| Slack-two queries / unknown | — | 813 / 222 | 827 / 157 |
| Slack-two pure / conditional clauses | — | 591 / 0 | 670 / 0 |
| Slack-two completion and extension seconds | — | 2.173 | 2.185 |
| Largest Percy peak working set | 25.5 MiB | 33.5 MiB | 22.2 MiB |
| Sum of job wall seconds | 39.632 | 43.351 | 42.148 |

All attempted extensions of excluded boundaries were excluded in this hard
screen. The independent synthetic extension test exercises a conditional cut
with one mixed pair and one extra first-layer occurrence retained. The
additional size-seven exclusions put more jobs into size eight. Measured
whole-screen time increased in both experimental modes. Both remain opt-in.
[Raw matched Percy records](results/baselines/slack_two_percy_screen.jsonl)
· [Fixed-budget oracle records](results/baselines/slack_two_percy_oracle.jsonl)

The 90 observations versus 44 unique boundaries suggest a separate
cross-query reuse opportunity. At one fixed budget and target, a cache
keyed by the typed first-layer multiset and mixed mask could reuse exact
exclusions and extension masks as SAT positions change. The SAT clause
would still be rebuilt using the positions in the current model. This
cache is independent of the existing within-query failed-frontier cache.
The measured duplication comes from the trace-only control, so reuse in
the active cut path still needs a screen.

When every extension is excluded and the old first-layer types are distinct,
the same proof gives a position-independent pure presence clause. Any model
with all the old types present contains an injection of the old boundary
wires into its first layer. The slack-two extension list therefore still
covers the model, including any extra occurrence of one of those types.
Each of the 35 exclusions in the 100k unate replay qualifies. This is a
candidate for the next cut-quality ablation. The repeated-type case still
requires positions or a multiplicity threshold.

### Replay commands

```powershell
Expand-Archive 'C:\Users\Carson\Downloads\residual_slack_two_native.zip' external/residual-slack-two
cmd /d /c 'call "C:\Program Files\Microsoft Visual Studio\18\Community\VC\Auxiliary\Build\vcvars64.bat" >nul && cd /d external\residual-slack-two && cl /nologo /std:c++20 /O2 /EHsc residual_slack_two_check.cpp /Feslack_two_check.exe && slack_two_check.exe && cl /nologo /std:c++20 /O2 /EHsc residual_provider_unate_check.cpp /Feunate_check.exe && unate_check.exe && cl /nologo /std:c++20 /O2 /EHsc residual_slack_two_bench.cpp /Feslack_two_bench.exe && slack_two_bench.exe'
& 'sat-search/native/build_native.bat'
$env:PERCY_BUILD_DIR = 'percy-first-layer-release'
& 'sat-search/baselines/build/build_percy.bat'
$percy = 'external/percy-first-layer-release/percy_run.exe'
$trace = 'sat-search/logs/slack_two_trace.jsonl'
python sat-search/experiments/slack_two_native_check.py
python sat-search/baselines/first_layer_check.py check sat-search/logs/slack_two_oracle.jsonl --exe $percy --workers 1 --memory-mib 512 --modes slack-one-directed slack-two-memo slack-two-unate
python sat-search/baselines/first_layer_check.py screen $trace --exe $percy --workers 1 --memory-mib 512 --limit 8 --seconds 8 --conflicts 20000 --modes slack-two-trace
python sat-search/experiments/slack_two_native_check.py --capture $trace --output sat-search/logs/slack_two_replay.jsonl
python sat-search/experiments/slack_two_native_check.py --capture $trace --output sat-search/logs/slack_two_replay_2m.jsonl --work-limit 2000000
python sat-search/baselines/first_layer_check.py screen sat-search/logs/slack_two_screen.jsonl --exe $percy --workers 1 --memory-mib 512 --limit 43 --seconds 8 --conflicts 20000 --modes slack-one-directed slack-two-memo slack-two-unate
```

## Singleton phase screening and slack-two presence cuts

In an exact signed tree, a wire used once has a fixed polarity. Fix any two
oppositely labeled cared rows that agree on repeated coordinates. For the
positive row to avoid lying below the negative row in the phase-adjusted
singleton order, at least one differing singleton must become 1 on the
positive row and 0 on the negative row. Thus the pair forbids exactly the
phase subcube whose differing bits equal those of the positive row.
Singleton differences force phase bits. The integrated screen intersects
the remaining allowed phases with packed 64-bit word masks. The conjunction
is exact for unrestricted functions unate in the singletons and arbitrary
in the repeated coordinates, since the upward closure of the positives
gives a completion in each repeated fiber. A passing result goes to the
existing exact tree solver. The code charges row, pair and word-mask work
and polls the shared deadline at batches of at most 64 charged steps.
An interrupted screen yields unknown through the engine's existing limit
path, which emits no clause.

The check runs just before an exact tree lookup, both for directed provider
columns and for the decoder. It cannot screen the whole shared DAG as if it
were one tree. For example the circuit `(x AND z) XOR y` can have `x` and
`z` each read once by the shared AND, with the AND and `y` each read twice
in the decoder. In the whole DAG there is no common phase for `x` at
`z = 1` across the two `y` fibers. The independent dynamic allocation
reference from the archive stays standalone.

### Repeated-wire masks

At fixed care, target column and distinct wire universe, turning a singleton
into a repeated wire only removes constraints. Row pairs newly distinguished
by that wire drop out. Pairs that remain agree on it, so it was absent from
their phase clause. Hence feasible masks are upward closed and infeasible
masks are downward closed. Mode `phase-cache` keeps minimal feasible and
maximal infeasible masks within each of at most 128 signatures. Signatures
use the target modulo output complement and the sorted distinct-wire column
multiset. Equal-valued separate wires retain separate entries and IDs supply
the tie break within the query. This reuse applies before direction-based
exact completion for a concrete tree, including tree-only reader allocations.
The repeated count above one does not enter the phase relaxation. Reversing
the target phase reverses every singleton phase, so the status is invariant
under output complement.

For a fixed whole-tree orientation, the repeated sets can also be described
as a hitting problem. Each opposing pair whose positive row would be below
its negative row supplies the set of their differing coordinates. Repeating
one coordinate in that set discards the pair. Therefore the minimal repeated
sets for that orientation are the inclusion-minimal hitting sets of its
violated pairs. This gives a possible joint phase-and-multiplicity
formulation under a repetition cap. The per-query cache above is the tested
reduction. Enumerating phases and minimal hitting sets up front remains an
unmeasured alternative for a single tree.

### Independent cut ablation

`--slack-two-set-cuts` replaces a pure positional clause by negative type
and mixed-primary presences when the old first-layer types are distinct.
Any model containing those types has an injection of the corresponding
old wire occurrences into its first layer. Its additional boundary is
one of the previously checked extensions, including an extra copy of an
old type. This implication is independent of SAT position. A repeated old
type or any feasible or unknown extension uses the existing position-based
clause path. The fixed-budget harness exercises the optional clauses without
changing the default driver or the slack-zero and slack-one kernels.

### Checks and captured costs

The supplied phase check and benchmark built and ran under MSVC in C++20
mode. The standalone oracle passed 5,000 polarity cases and 4,470 full
DAG comparisons. On this MSVC run the archive benchmark completed 170
of 200 queries in 1.604 s with the screen off, and all 200 in 0.402 s
with the screen on. The phase test rejected 41,015 tree requests. The
archive's recorded GCC run completed 190 and 200 in 1.134 s and 0.288 s.
The packed production screen and its cache variant also passed the
adapted standalone oracles, with polarity widths up to 12 and up to 64
cared rows. The in-repo binding passed 7,040 exact-DAG comparisons,
including complete and partial targets, plus focused duplicate-wire,
shared-provider, extension and interruption checks.
[MSVC check and benchmark output](results/baselines/slack_two_phase_msvc.txt)

The captured cases used 100,000 work units, a 25 ms total query deadline
and a 512 MiB process-family cap. Status and counters were stable across
five interleaved passes. Times sum per-boundary medians, including
extension checks and Python binding overhead. Every decided case was
excluded, and each justified a pure cut.

| 44 captured queries | Memo + unateness | Plus phase screen | Plus phase-mask cache |
| --- | ---: | ---: | ---: |
| Proved exclusions | 35 | 44 | 44 |
| Proved exclusions in the nine previously open | 0 | 9 | 9 |
| Median time sum, all 44 | 113.4 ms | 80.3 ms | 80.1 ms |
| Median time sum, nine previously open | 19.1 ms | 28.5 ms | 28.5 ms |
| Exact tree calls | 4,884 | 3,209 | 3,209 |
| Phase rejections before a tree call | — | 2,694 | 2,694 |
| Phase-cache hits, including strict repeated-set implications | — | — | 1,712 / 697 |
| Charged work | 3,081,318 | 716,421 | 569,885 |

The nine previously open queries cost more in aggregate when taken to an
exclusion. The full replay was faster overall. The cache reduced charged
work without a measurable local elapsed-time gain and stayed outside
the end-to-end screen. At 2 million work units and the same 25 ms deadline,
all three modes excluded all 44. Median time sums were 156.9, 84.1, and
83.7 ms. On this equally completed comparison the phase screen prevented
2,694 of 5,903 exact tree calls.
[Captured replay](results/baselines/slack_two_phase_captured.jsonl)
· [Equal-completion replay](results/baselines/slack_two_phase_captured_2m.jsonl)

### Matched Percy screen

All modes used the same 43 hard four-input targets, Satoko, one worker,
20,000 conflicts per SAT call, an 8 s process deadline per target and a
512 MiB process-family commit cap. The phase and set-cut flags form two
independent factors. All modes excluded sizes three through six. The
runtime is the sum of target wall times, including encoding and process
startup. Memory is the largest recorded Percy peak working set.

| Metric | Memo + unateness | Phase | Set cuts | Phase and set cuts |
| --- | ---: | ---: | ---: | ---: |
| Size-seven exclusions | 41 | 43 | 36 | 40 |
| Size-eight attempts | 41 | 43 | 36 | 40 |
| Size-eight SAT / UNSAT | 0 / 0 | 0 / 0 | 0 / 0 | 1 / 0 |
| SAT conflicts on 207 jointly excluded budgets | 426,810 | 291,324 | 322,988 | 222,864 |
| Solver seconds on those budgets | 8.086 | 5.109 | 5.940 | 3.900 |
| Slack-two queries / unknown | 827 / 157 | 801 / 0 | 812 / 163 | 812 / 0 |
| Slack-two pure clauses / set clauses | 670 / 0 | 801 / 0 | 649 / 649 | 812 / 812 |
| Slack-two exact tree calls | 113,253 | 62,249 | 110,500 | 62,521 |
| Phase rejections before tree calls | — | 48,963 | — | 49,140 |
| Slack-two completion and extension seconds | 2.273 | 1.425 | 2.156 | 1.439 |
| Peak Percy working set | 22.1 MiB | 26.5 MiB | 36.6 MiB | 18.2 MiB |
| Total wall seconds | 44.367 | 46.785 | 45.755 | 36.806 |

The changes alter which boundaries Satoko visits, so total tree-call
counts and phase rejection counts describe different comparisons. Phase
alone reached size eight for every target. Phase with set cuts recovered
the known eight-gate optimum for `npn4-016a`, with a witness independently
verified by the harness. The other size-eight jobs reached a solver limit.
The set clauses can change CDCL behavior in either direction. The combined
mode solved one additional target and ran faster overall, while phase
alone excluded three more size-seven budgets. All modes remain opt-in.
All 127 fixed-budget jobs matched the independent small DAG enumeration
or the plain full-row encoding at size seven. The two set-cut variants
learned 57 set clauses in that check.
[Matched records](results/baselines/slack_two_phase_percy_screen.jsonl)
· [Fixed-budget checks](results/baselines/slack_two_phase_percy_oracle.jsonl)
· [Previously verified optima](results/baselines/caps_hard_npn4.jsonl)

### Replay commands

```powershell
$archive = 'external/residual-phase-screen'
$zip = 'C:\Users\Carson\Downloads\residual_phase_screen_native.zip'
Expand-Archive -LiteralPath $zip -DestinationPath $archive
cmd /d /c 'call "C:\Program Files\Microsoft Visual Studio\18\Community\VC\Auxiliary\Build\vcvars64.bat" >nul && cd /d external\residual-phase-screen && cl /nologo /std:c++20 /O2 /EHsc residual_phase_screen_check.cpp /Fephasecheck.exe && phasecheck.exe && cl /nologo /std:c++20 /O2 /EHsc residual_phase_screen_bench.cpp /Fephasebench.exe && phasebench.exe'
& 'sat-search/native/build_native.bat'
$env:PERCY_BUILD_DIR = 'percy-first-layer-release'
& 'sat-search/baselines/build/build_percy.bat'
$percy = 'external/percy-first-layer-release/percy_run.exe'
$modes = 'slack-two-unate', 'slack-two-phase', 'slack-two-unate-set', 'slack-two-phase-set'
python sat-search/experiments/slack_two_native_check.py
python sat-search/experiments/slack_two_native_check.py --capture sat-search/results/baselines/slack_two_percy_captured.jsonl --output sat-search/logs/phase_captured_replay.jsonl --modes 3 4 5 --repetitions 5
python sat-search/experiments/slack_two_native_check.py --capture sat-search/results/baselines/slack_two_percy_captured.jsonl --output sat-search/logs/phase_captured_equal_replay.jsonl --modes 3 4 5 --repetitions 5 --work-limit 2000000
python sat-search/baselines/first_layer_check.py check sat-search/logs/phase_oracle_replay.jsonl --exe $percy --workers 1 --memory-mib 512 --modes $modes
python sat-search/baselines/first_layer_check.py screen sat-search/logs/phase_screen_replay.jsonl --exe $percy --workers 1 --memory-mib 512 --limit 43 --seconds 8 --conflicts 20000 --modes $modes
```

For the production standalone differential, copy the archive's
`residual_slack_two_check.cpp` to `production_dag_oracle.inc` and change its
engine include to `../../sat-search/native/src/residual_slack_two.hpp`.
In a copy of `residual_phase_screen_check.cpp`, include the adapted oracle
instead and remove the `residual_phase_slack.hpp` include. Replace the
standalone phase call with
`residual_phase_screen::feasible(residual_phase_screen::collect(a),p,n,[](unsigned){})`.
Construct `residual_slack_two::Engine` with parity, direct, memo, unateness
and phase enabled, testing both settings for the final cache flag. Draw
widths 1–12 and row counts 2–64 in the polarity oracle, avoiding shifts by 64
and limiting duplicate insertion to leave room for the remaining distinct
coordinates. The archived dynamic reference is `residual_dynamic.hpp` in
the same archive, SHA-256
`8b541aa2a08a9946300d95364d3831400da007ede6358772fc2482dbc41712fe`.

## Slack-three boundary extensions and occurrence-symmetric trees

Source: `residual_occurrence_symmetry_native.zip` (SHA-256
`e3edcc7ffe726ea57befa4674c62feb2ee8239179126b887abef244211f0255b`). Its
directed occurrence-symmetric tree solver is vendored, with only a
four-line provenance comment added, as
[residual_symmetric_directed.hpp](native/src/residual_symmetric_directed.hpp)
(bundle file SHA-256
`d22f3e5e23009275a0dc3a665c37c0bd90006482f25842494f163e0425799f48`).
The bundle has no slack-three Percy cuts. This repository adds them in
[slack_three_boundary.hpp](native/src/slack_three_boundary.hpp).

### Rule and soundness

For a first-layer boundary with h typed occurrences and m distinct mixed
primaries at budget k, slack is s = k+1-(2h+m). At s = 3 the exact
residual question is `Engine.run(.,3)`; `run()` now accepts s = 0..3.

When that query is UNSAT, the boundary itself cannot be completed. A
sibling boundary that adds structure still can, at lower slack. A new mixed
primary costs one unit of slack and a new first-layer occurrence costs two.
Every addition of cost at most three is tested with the exact recognizer for
the remaining slack:

| Addition | Remaining slack | Recognizer |
| --- | ---: | --- |
| One new mixed primary | 2 | `Engine.run(.,2)` |
| Two new mixed primaries | 1 | `slack_one_residual` |
| One first-layer occurrence | 1 | `slack_one_residual` |
| Three new mixed primaries | 0 | tight `residual_zero` |
| One occurrence and one new mixed primary | 0 | tight `residual_zero` |

Antecedents stay multiplicity-aware. A new occurrence may repeat an
existing type, and the extended boundary then keeps both copies.

An extension is excluded only by a decided UNSAT. A SAT or unknown
extension is retained. A larger extension whose elements are all retained
is subsumed rather than tested.

The Percy clause has the slack-two clause shape:

- The antecedent is the position-based first-layer selection and operation
  variables plus the negated mixed-primary features.
- The consequent lists the retained mixed features and the gate
  `typed_steps` for steps outside the current first layer.
- With nothing retained the clause is pure.
- A set clause over type features is emitted only for a pure result whose
  observed types are distinct. Only then do the type features name separate
  old occurrences.

An unknown exact query emits no clause. Retained extensions only weaken
the clause. Neither can exclude a completable boundary.

The vendored solver makes these changes:

- It partitions a region's leaves into classes by wire identity. Distinct
  wires with equal columns are not merged.
- It enumerates per-class count vectors instead of occurrence subsets.
- It memoizes on canonical multiplicity subsets and relabels leaves to fresh
  occurrences once, at the end.
- It installs no failure memo on interrupted searches.

It is selected per `Engine` by a final `use_symmetric` constructor flag that
defaults off.

### Checks

- Bundle, built with MSVC (VS 18):
  - Merge oracle: 1,200 x 2 queries, 461 SAT, no disagreements.
  - DAG oracle: 5,520 queries, 3,831 SAT.
  - 5,000 phase systems.
  - The README's 1,572 multiplicity counting checks are not in any bundled
    source and were not reproduced.
- [slack_three_native_check.py](experiments/slack_three_native_check.py):
  - 14,080 independent DAG-oracle comparisons of the native slack-three
    extension decisions, over both residual modes and both tree solvers.
  - 60 duplicate-wire, 20 extension/limit and 3 argument checks.
  - The slack-two control check still passes 7,040 comparisons.
- Percy fixed-budget check: 104 jobs, 0 verdict mismatches against the small
  DAG enumeration, the plain encoding, or known optima. This includes, for
  every slack-three mode:
  - size-eight `npn4-0116`: UNSAT at 8;
  - size-eight `npn4-016a`: SAT at 8, with the witness verified by the
    harness.

### Captured boundaries

`--trace-slack-three` captured 382 events from 40 of 43 hard four-input
targets, giving 168 distinct boundaries. Their (h,m) shapes:

- (1,4): 128 times. Here all four primaries are already mixed, so only
  occurrence extensions remain.
- (2,2): 36 times.
- (1,3): twice.

The replay used 2 million work units per query:

| 168 captured | 25 ms deadline (median of 3) | Unlimited deadline |
| --- | ---: | ---: |
| Exact UNSAT / SAT | 166 / 2 | 166 / 2 |
| Pure cuts | 37-38 | 166 |
| Excluded / unknown extensions | about 4,600 / 1,250-1,325 | 5,870 / 0 |
| Time sum | about 3.81 s | 5.35-5.44 s |

The exact query always completes. The 25 ms deadline is spent on the
extension recognizers. Time is unchanged across mode 4/5 and across
directed/symmetric trees.

At the unlimited deadline all four settings retained identical masks;
`replay()` now asserts this. Work was:

| Mode | Directed | Symmetric |
| --- | ---: | ---: |
| 4 | 32.0M | 31.6M |
| 5 | 24.3M | 24.0M |

Symmetric trees give no measurable gain on these production boundaries.
They did help on the bundle's generated benchmark:

- MSVC rerun: 175 vs 178 of 200 decided, in 1,199 vs 862 ms.
- The bundle's GCC claim: 175 vs 180-181.

[Captured boundaries](results/baselines/slack_three_percy_captured.jsonl)
· [25 ms replay](results/baselines/slack_three_captured_replay.jsonl)
· [Unlimited replay](results/baselines/slack_three_captured_unlimited.jsonl)
· [Bundle and native check output](results/baselines/slack_three_symmetric_msvc.txt)

### Matched Percy screen

Settings:

- 43 hard four-input targets, Satoko, one worker;
- 20,000 conflicts per SAT call, 8 s per target, a 512 MiB cap;
- an increasing search from n-1.

Every slack-three mode includes slack-two phase and set cuts. Joint
conflicts and solver seconds are summed over the 212 budgets that every
mode excluded. Wall time is the sum of target wall times.

| Mode | Size-7 excl | Size-8 SAT / UNSAT | Joint conflicts | Joint solver s | Size-8 conflicts | Wall s | Peak MiB |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| slack-two phase | 43 | 0 / 0 | 312,515 | 5.368 | 1,936,350 | 44.0 | 26.5 |
| slack-two phase + set | 40 | 1 / 0 | 233,182 | 4.118 | 1,628,679 | 34.7 | 17.9 |
| slack-three, 25 ms | 40 | 1 / 4 | 208,335 | 3.878 | 1,896,633 | 67.0 | 32.8 |
| slack-three symmetric, 25 ms | 40 | 1 / 6 | 208,335 | 3.875 | 1,950,160 | 68.0 | 33.0 |
| slack-three, 100 ms | 40 | 0 / 8 | 208,335 | 3.865 | 2,167,126 | 85.8 | 49.7 |
| slack-three symmetric, 100 ms | 40 | 0 / 8 | 208,335 | 3.878 | 2,167,126 | 86.3 | 49.5 |

Slack-three cut statistics:

| Mode | Boundaries | Pure | Conditional | Extensions excluded / unknown | Slack-three s |
| --- | ---: | ---: | ---: | ---: | ---: |
| 25 ms | 499 | 47 | 440 | 9,401 / 4,631 | 11.7 |
| 25 ms, symmetric | 518 | 43 | 463 | 9,288 / 4,996 | 12.1 |
| 100 ms, either solver | 529 | 501 | 16 | 14,362 / 361 | 18.1 |

Size-8 exclusions by mode:

- 25 ms directed: `1668`, `1669`, `177e`, `6996`.
- 25 ms symmetric: the same four plus `166b` and `1697`.
- 100 ms, either solver: `0116`, `1668`, `1669`, `1681`, `16a9`, `177e`,
  `19e1`, `6996`.
- No slack-two mode proved any size-8 exclusion.

All 10 distinct size-8 UNSAT targets agree with plain Percy's size-8 UNSAT
budgets in [caps_hard_npn4.jsonl](results/baselines/caps_hard_npn4.jsonl),
so no new lower bound is claimed. For `1669`, `166b` and `1681` the plain
run proved size 8 UNSAT and then timed out at size 9.

The cuts are valid only in an increasing search from a proved lower bound,
which is how these exclusions were obtained.

Observations:

- Joint conflicts match across the slack-three modes because the rule rarely
  fires below size 8.
- The extra wall time is spent in the extension recognizers.
- The 100 ms modes lost the `016a` optimum to the conflict limit, a CDCL
  trajectory change.
- Directed and symmetric trees made identical decisions at 100 ms.

All modes stay opt-in. The captured replay shows that the extension
decisions, not the trees, are deadline-bound, so cheaper extension
decisions are the useful next direction.

[Matched records](results/baselines/slack_three_percy_screen.jsonl)
· [Fixed-budget checks](results/baselines/slack_three_percy_oracle.jsonl)

Not verified:

- UNSAT proof certificates for the size-8 exclusions;
- the bundle's 1,572 counting checks and its GCC timings;
- any target beyond four inputs.

The bundle's pair-screen and guided-slack alternatives stay unintegrated.

### Flags and binding

Percy flags:

- `--slack-three-residual memo|unate|phase|phase-cache` (Engine modes 2-5);
- `--slack-three-set-cuts`;
- `--slack-three-symmetric`;
- `--slack-three-ms N` (default 25);
- `--slack-three-work N` (default 2,000,000);
- `--trace-slack-three`.

Harness modes:

- `slack-three-{memo,unate,phase,phase-cache}[-sym]`;
- `slack-three-{phase,phase-sym}-set[-100ms]`;
- `slack-three-trace`.

Python binding:

- Call:
  `_native.slack_three_boundary(columns, first_layer, primaries, mixed_mask, gate_columns, target, care, work_limit=2000000, deadline_seconds=0.025, mode=5, symmetric=False)`.
- It returns `(metrics, regions)`.
- A deadline of 0 or less means unlimited.

The captured file is a copy of the trace screen's records.

```powershell
$archive = 'external/residual-occurrence-symmetry'
Expand-Archive -LiteralPath 'C:\Users\Carson\Downloads\residual_occurrence_symmetry_native.zip' -DestinationPath $archive
cmd /d /c 'call "C:\Program Files\Microsoft Visual Studio\18\Community\VC\Auxiliary\Build\vcvars64.bat" >nul && cd /d external\residual-occurrence-symmetry && cl /nologo /std:c++20 /O2 /EHsc residual_symmetric_merge_check.cpp /Fesymmerge.exe && symmerge.exe && cl /nologo /std:c++20 /O2 /EHsc residual_symmetric_check.cpp /Fesymcheck.exe && symcheck.exe && cl /nologo /std:c++20 /O2 /EHsc residual_symmetric_bench.cpp /Fesymbench.exe && symbench.exe 2 && symbench.exe 3'
& 'sat-search/native/build_native.bat'
& 'sat-search/baselines/build/build_percy.bat'
python sat-search/experiments/slack_three_native_check.py
python sat-search/baselines/first_layer_check.py screen sat-search/logs/slack_three_trace_capture.jsonl --workers 6 --limit 43 --seconds 8 --conflicts 20000 --modes slack-three-trace
python sat-search/experiments/slack_three_native_check.py --capture sat-search/results/baselines/slack_three_percy_captured.jsonl --output sat-search/logs/slack_three_captured_replay.jsonl --limit 400 --modes 4 5 --repetitions 3
python sat-search/experiments/slack_three_native_check.py --capture sat-search/results/baselines/slack_three_percy_captured.jsonl --output sat-search/logs/slack_three_captured_unlimited.jsonl --limit 400 --modes 4 5 --deadline 0
python sat-search/baselines/first_layer_check.py check sat-search/logs/slack_three_percy_check2.jsonl --workers 6 --modes slack-three-phase-set slack-three-phase-sym-set slack-three-phase-sym-set-100ms
python sat-search/baselines/first_layer_check.py screen sat-search/logs/slack_three_screen.jsonl --workers 1 --memory-mib 512 --limit 43 --seconds 8 --conflicts 20000 --modes slack-two-phase slack-two-phase-set slack-three-phase-set slack-three-phase-sym-set slack-three-phase-set-100ms slack-three-phase-sym-set-100ms
```

## Lazy weighted slack-three cuts

Source: `residual_lazy_cuts_native.zip` (SHA-256
`ff8b3f1d8679aef592de91fee7a6d299cedf9f103e52a165bd5869e4b8ee096c`). It is a
standalone C++20 prototype with its own boundary model. It is not linked into
the production build; the rule was re-implemented in the native kernel and
the Percy adapter.

### Rule

Let `W = 2h + m` be the actual boundary weight: first-layer occurrences
counted twice plus distinct mixed primaries. Slack is `s = k + 1 - W`. A
slack-three boundary has original weight `w = k - 2`.

Let `A` be the antecedent "the actual boundary contains the original one":
every original first-layer gate type occurs at least as often as in the
original, and every original mixed primary is present. Under `A`, the actual
boundary is the original plus an extension `E` with
`W = w + cost(E)`, where an added occurrence costs 2 and an added mixed
primary costs 1.

**Claim (proved).** Suppose the exact boundary and every extension of cost
`c < d` have been proved infeasible at their own slack `3 - c`, except
extensions that add an element of a retained set `R`. Then every feasible
circuit satisfies `NOT A OR (W >= w + d) OR R`.

**Proof.** Take a feasible circuit with `A` true and `W < w + d`. Its boundary
is the original plus some extension `E` of cost `c = W - w < d`, and the
circuit realizes `E` at slack `3 - c >= 0`. Either `E` adds an element of `R`
(so `R` holds) or `E` was proved infeasible, a contradiction. ∎

Consequences:

- `d = 1` needs no extension checks: under `A`, equality `W = w` forces the
  excluded boundary itself.
- `d = 4` gives `W >= k + 2`, which is impossible, so the clause is the
  existing pure exclusion `NOT A OR R` and needs no threshold literal.
- Cost levels: 1 = one free mixed primary (slack 2); 2 = two primaries or one
  extra occurrence (slack 1); 3 = three primaries, or one occurrence plus one
  primary (slack 0). Empty levels are skipped, so a boundary whose primaries
  are all mixed already reaches `d = 2` with exact-only.

The same restriction as before applies: the cut preserves the minimum only in
the increasing search from a proved lower bound. It is not valid for
exact-size or pinned-prefix claims.

### Encoding

- `native/src/reified_counter.hpp` adds `reified_at_most`, a Sinz sequential
  counter with both directions, so `T_t <-> (count >= t)`.
  `native/tests/reified_counter_check.cpp` checks every assignment of 27
  counter shapes (574 assignments).
- The first-layer weight counter uses the reified form only under a lazy
  policy, and the clause reuses its threshold literal `T_{w+d}`. The full
  policy keeps the original one-way counter as the control.
- Antecedents: the set antecedent (gate-type features) when set cuts are on,
  the observed types are distinct and no retained gate is among them.
  Otherwise the positional antecedent over `typed_steps` is used, which covers
  repeated first-layer types by position.
- The cut aborts (assertion) if the threshold literal is missing or
  `w != k - 2`.

### Policies

Percy flag `--slack-three-policy full|exact|lift1|adaptive` (requires
`--slack-three-residual` and `--first-layer-budget`):

- `full`: the existing behaviour (all extensions of cost <= 3; `d = 4`).
- `exact`: no extension checks; `d = 1`, or 2 when no primary is free.
- `lift1`: checks only the single free mixed primaries; `d = 2`.
- `adaptive`: tests extensions level by level and skips one whose element is
  already retained. A per-target `ResidualMemo` (keyed by target, care, the
  leaf columns, `h` and slack; independent of `k`) is seeded from decided
  slack-two answers and reused across boundaries. At the deadline, the first
  incomplete level sets `d` and its partly retained elements are dropped.
  Unknown answers returned before the deadline are retained, as in `full`.

Unknown exact answers stay unknown under every policy (no clause).

### Checks

- [slack_three_native_check.py](experiments/slack_three_native_check.py)
  `policy_checks`: four 5-input targets × four policies against an
  independent DAG enumeration of all extensions; the clause's soundness
  (every feasible extension cheaper than `d` meets `R`); exact-only makes no
  calls; lift1 retains exactly the feasible singles; a repeated adaptive query
  is fully answered from the memo; the deadline-revert path for seeded memos
  (`d` = 1 and 2); unknown handling; non-adaptive policies ignore the memo;
  all-mixed 4-input boundaries reach `d = 2`; out-of-range policy rejected.
  [Log](logs/slack_three_policy_check.out).
- Percy fixed budgets: 137 jobs, every policy plus `phase-sym-set-adaptive-100ms`,
  including size-8 `0116` (UNSAT) and `016a` (SAT), agree with the expected
  verdicts. [Records](results/baselines/slack_three_policy_percy_check.jsonl).
- Bundle: `boundary_weight_check` passed (1,000 base cases, 425,701 checks,
  451 multiplicity distributions). MSVC `extension_lift_bench 50 2`: exact
  119.2 ms, lift1 254.7 ms, full 391.1 ms; `30 3`: 13.4 / 65.7 / 122.8 ms.
  These are local recognizer costs only.

### Captured boundaries

The 168 distinct captured production boundaries
([records](results/baselines/slack_three_percy_captured.jsonl)) were replayed
under each policy. The replay used the same solver as `slack-three-phase-set`
(Engine mode 4, directed trees). Adaptive shares one memo per target, in
capture order, and the replay does no slack-two seeding.

| Deadline | Policy | Wall s | Extension calls | `d` (boundaries) | Retained gates |
| --- | --- | ---: | ---: | --- | ---: |
| 25 ms | full | 3.83 | 4,643 | 4: 166 | 1,354 |
| 25 ms | exact | 1.08 | 0 | 1: 38, 2: 128 | 0 |
| 25 ms | lift1 | 1.12 | 74 | 2: 166 | 0 |
| 25 ms | adaptive | 3.79 | 4,631 | 2: 128, 4: 38 | 0 |
| 100 ms | full | 5.47 | 5,870 | 4: 166 | 0 |
| 100 ms | exact | 1.07 | 0 | 1: 38, 2: 128 | 0 |
| 100 ms | lift1 | 1.13 | 74 | 2: 166 | 0 |
| 100 ms | adaptive | 5.23 | 5,676 | 4: 166 | 0 |

- Every policy agrees on every exact decision: 166 UNSAT and 2 SAT. The
  replay asserts that the lazy retained sets are subsets of full's.
- At 25 ms, full keeps 1,354 unknown gate extensions in conditional clauses.
  Adaptive instead reverts the 128 boundaries that hit the deadline to a pure
  `d = 2` clause. At 100 ms, adaptive matches full's 166 pure exclusions.
- 128 of the 168 boundaries are (1,4) shapes whose primaries are all already
  mixed, so exact-only reaches `d = 2` on them without any checks. The other
  38 reach `d = 2` with 74 single-primary checks, all infeasible.
- Exact-only takes 28% of full's time at 25 ms and 20% at 100 ms. This is
  close to the bundle's 82.5 / 330 ms ratio.

[25 ms](results/baselines/slack_three_policy_captured_25ms.jsonl)
· [100 ms](results/baselines/slack_three_policy_captured_100ms.jsonl)
· [Totals](results/baselines/slack_three_policy_captured_summary.txt)

### Matched 43-target screen

Setup:

- Satoko CEGAR on the 43 hard four-input targets.
- Per budget: 8 s and 20,000 conflicts. Memory: 512 MiB. One worker per mode.
- The eight modes ran as eight concurrent single-worker processes. Wall times
  therefore include about 10-15% contention: full at 25 ms took 67.0 s alone
  and 76.3 s here.

| Mode | Size-7 excl | Size-8 SAT / UNSAT | Conflicts | Size-8 conflicts | Minima | Wall s | Peak MiB |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| slack-two phase + set | 40 | 1 / 0 | 1,930,363 | 1,628,679 | 1 | 38.9 | 18.3 |
| full, 25 ms | 40 | 1 / 4 | 2,419,072 | 1,991,585 | 2 | 76.3 | 33.1 |
| exact | 42 | 1 / 1 | 2,446,460 | 2,154,379 | 2 | 72.1 | 26.6 |
| lift1 | 42 | 0 / 4 | 2,401,835 | 1,976,612 | 0 | 68.3 | 32.7 |
| adaptive, 25 ms | 42 | 0 / 1 | 2,685,100 | 2,332,837 | 0 | 87.7 | 33.9 |
| full, 100 ms | 40 | 0 / 8 | 2,610,766 | 1,985,287 | 0 | 94.7 | 49.8 |
| exact, 100 ms | 42 | 1 / 1 | 2,446,460 | 2,154,379 | 2 | 71.7 | 26.5 |
| adaptive, 100 ms | 42 | 0 / 8 | 2,826,850 | 2,170,969 | 0 | 93.8 | 33.3 |

Slack-three cut statistics, summed over all budgets:

| Mode | Cuts | Repeat visits | `d` = 1/2/3/4 | Literals per lazy cut | Extension calls | Avoided | Memo hits | Slack-three s |
| --- | ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| full, 25 ms | 485 | 15 | — | — | 8,720 | 5,161 | — | 11.8 |
| exact | 561 | 4 | 46/515/0/0 | 5.9 | 0 | 15,680 | — | 4.6 |
| lift1 | 566 | 6 | 0/566/0/0 | 5.9 | 95 | 15,905 | — | 4.7 |
| adaptive, 25 ms | 572 | 7 | 0/470/0/102 | 5.7 | 9,447 | 6,522 | 2,354 | 13.6 |
| full, 100 ms | 493 | 9 | — | — | 14,147 | 381 | — | 19.3 |
| exact, 100 ms | 561 | 4 | 46/515/0/0 | 5.9 | 0 | 15,680 | — | 4.6 |
| adaptive, 100 ms | 583 | 6 | 0/0/0/583 | 5.4 | 12,529 | 4,156 | 3,787 | 18.4 |

- "Avoided" is the number of extensions of cost at most 3 minus the number
  actually decided. Full avoids some only by hitting the deadline, and it
  retains those.
- Literal counts cover the whole lazy clause: antecedent, threshold and
  retained literals.

Size-8 exclusions:

- full, 25 ms and lift1: `1668`, `1669`, `177e`, `6996`.
- exact (either deadline): `0196`.
- adaptive, 25 ms: `177e`.
- full, 100 ms: `0116`, `1668`, `1669`, `1681`, `16a9`, `177e`, `19e1`,
  `6996`.
- adaptive, 100 ms: `0116`, `0661`, `1668`, `1669`, `166b`, `1681`, `177e`,
  `6996`.

Verified minima:

| Mode | Minima found |
| --- | --- |
| exact | `0196` = 9 (after its size-8 exclusion), `1699` = 8; no other mode reached either |
| full, 25 ms | `016a` = 8, `177e` = 9 |
| slack-two | `016a` = 8 |

Every verdict and minimum agrees with
[caps_hard_npn4.jsonl](results/baselines/caps_hard_npn4.jsonl): no
disagreements, and no UNSAT beyond its known lower bounds. No new bound is
claimed.

Assessment:

- **lift1 is the useful policy.** Compared with full at 25 ms:
  - It keeps all four size-8 exclusions with 95 extension calls instead of
    8,720.
  - It cuts slack-three time from 11.8 s to 4.7 s and wall time from 76.3 s
    to 68.3 s.
  - It adds two size-7 exclusions and has fewer repeated boundary visits
    (6 vs 15).
- **exact-only** is the cheapest mode (4.6 s, peak 26.6 MiB). Its clauses
  have `d <= 2`, and it proved only one size-8 exclusion. It reached two
  minima that no other mode found; this is a trajectory effect, not a
  stronger rule.
- **adaptive** at 100 ms matches full's count of eight size-8 exclusions, at
  the same wall time, with a different set: it adds `0661` and `166b` and
  loses `16a9` and `19e1`. At 25 ms it is the slowest mode, because its pure
  `d = 2` reverts are weaker than full's conditional clauses there.
- Exact-only's deadline does not matter. The exact query always finished
  within 25 ms, and the 25 ms and 100 ms runs have identical conflicts.
- No slack-three policy beats slack-two phase + set on wall time, so all stay
  opt-in. The lazy clauses remove the recognizer cost. What remains of the
  slack-three cost is the exact query (`three_tree_calls` and phase checks)
  and the CDCL time at size 8.

[Matched records](results/baselines/slack_three_policy_screen.jsonl)
· [Summary](results/baselines/slack_three_policy_screen_summary.txt)
(from [slack_three_policy_summary.py](baselines/slack_three_policy_summary.py))

Not verified:

- UNSAT certificates for the size-8 exclusions.
- Targets with more than four inputs.
- The bundle's earlier 1,572-case counting test, which is missing from its
  archive.

The bundle's shared cross-query caches and grouped raw-primary relaxations
remain unintegrated; both were slower in its generated comparison.

### Flags, binding and commands

- Percy: `--slack-three-policy full|exact|lift1|adaptive`.
- Harness modes: `slack-three-{phase,phase-sym}-set-{exact,lift1,adaptive}[-100ms]`.
- Binding: `_native.slack_three_boundary(..., symmetric=False, policy=0, memo=None)`,
  where `policy` 0-3 means full, exact, lift1, adaptive, and `memo` takes a
  `_native.ResidualMemo()`. New metrics: `lift`, `extension_total`,
  `covered`, `memo_hits`, `memo_inserts`, `exact_cached`.
- Percy JSON fields: `three_policy`, `three_cuts`, `three_lift`,
  `three_threshold_cuts`, `three_clause_literals`, `three_covered`,
  `three_extension_total`, `three_memo_hits`, `three_memo_inserts`,
  `three_seed_inserts`, `three_exact_cached`, `three_repeats`,
  `three_memo_size`.

```powershell
Expand-Archive -LiteralPath "$env:USERPROFILE\Downloads\residual_lazy_cuts_native.zip" -DestinationPath external/residual-lazy-cuts
python -I external/residual-lazy-cuts/boundary_weight_check.py
cmd /d /c 'call "C:\Program Files\Microsoft Visual Studio\18\Community\VC\Auxiliary\Build\vcvars64.bat" >nul && cd /d external\residual-lazy-cuts && cl /nologo /std:c++20 /O2 /EHsc extension_lift_bench.cpp && extension_lift_bench 50 2 && extension_lift_bench 30 3'
cmd /d /c 'call "C:\Program Files\Microsoft Visual Studio\18\Community\VC\Auxiliary\Build\vcvars64.bat" >nul && cl /nologo /std:c++20 /O2 /EHsc /Isat-search\native\src sat-search\native\tests\reified_counter_check.cpp && reified_counter_check'
& sat-search/native/build_native.bat
& sat-search/baselines/build/build_percy.bat
python sat-search/experiments/slack_three_native_check.py
python sat-search/baselines/first_layer_check.py check sat-search/logs/slack_three_policy_percy_check.jsonl --workers 8 --modes slack-three-phase-set-exact slack-three-phase-set-lift1 slack-three-phase-set-adaptive slack-three-phase-sym-set-adaptive-100ms
python sat-search/experiments/slack_three_native_check.py --capture sat-search/results/baselines/slack_three_percy_captured.jsonl --output sat-search/logs/slack_three_policy_captured_25ms.jsonl --limit 200 --modes 4 --directed --policies --deadline 0.025
python sat-search/experiments/slack_three_native_check.py --capture sat-search/results/baselines/slack_three_percy_captured.jsonl --output sat-search/logs/slack_three_policy_captured_100ms.jsonl --limit 200 --modes 4 --directed --policies --deadline 0.1
foreach ($m in 'slack-two-phase-set','slack-three-phase-set','slack-three-phase-set-exact','slack-three-phase-set-lift1','slack-three-phase-set-adaptive','slack-three-phase-set-100ms','slack-three-phase-set-exact-100ms','slack-three-phase-set-adaptive-100ms') { Start-Process python -NoNewWindow -ArgumentList "sat-search/baselines/first_layer_check.py screen sat-search/logs/lazy_screen/$m.jsonl --workers 1 --memory-mib 512 --limit 43 --seconds 8 --conflicts 20000 --modes $m" }
python sat-search/baselines/slack_three_policy_summary.py sat-search/results/baselines/slack_three_policy_screen.jsonl
```

## Termination reasons and benchmark tiers

### Audit

The table below lists every limit that can end a Percy run or an inner residual query without a
verdict, as found in `percy_run.cpp`, `first_layer_check.py` and `native/src`.

| Limit | Where | Scope before this change | Reported now |
| --- | --- | --- | --- |
| SAT conflicts (`--conflicts`) | `satoko_solve_assumptions_limit` | **Each CEGAR SAT call**, counted from that call's start. A budget with r CEGAR rows may use about r times the limit. | Budget `reason` `conflict_limit`; `conflict_limit`, `conflict_scope`, `sat_calls` and `conflicts` per budget. `--conflict-scope budget` makes the limit cover the whole budget. |
| Wall clock (`--seconds`) | harness `communicate(timeout)` | **Whole run** (every budget from `n - 1` up), enforced only by killing the process. The open budget printed no record, so its conflicts, elapsed time and number were lost. | `percy_run --seconds`: a watcher thread raises Satoko's stop flag. The open budget prints `reason` `wall_deadline` with `elapsed` (since run start) and its conflicts. The harness kill stays as a backstop at `seconds + 10` (`reason` `harness_kill`, `open_budget` = last record + 1). |
| Memory (`--memory-mib`) | Windows commit cap | An allocation failure crashed the driver and aborted the whole screen with `RuntimeError`. | `std::bad_alloc` gives exit 3 with `final` `UNKNOWN` and `reason` `memory`. Any other crash under a cap is `MEMORY` with `crash_<code>`. Neither is ever a verdict. |
| Slack-two boundary recognizer | `slack_two_cut` | Hard-coded 25 ms and 100,000 work units per boundary. | `two_unknown_cause` = [deadline, work, capacity] per budget. New flags `--slack-two-ms` and `--slack-two-work` (defaults unchanged). |
| Slack-three boundary recognizer | `slack_three_cut` | `--slack-three-ms` (25) and `--slack-three-work` (2M) per boundary. The exact query and all its extension checks share the one deadline; each recognizer call gets its own work allowance. | `three_unknown_cause` per budget. |
| Tight and slack-one recognizers | `residual_zero` (4,096), `slack_one_residual` (100,000, 25 ms) | Per call. | Counted as unknown, as before (no cause split). |

An inner recognizer's unknown only withholds a clause; it never becomes a verdict. The budget
status is decided by the SAT solver alone, and `TIMEOUT` (with its `reason`) is never read as
UNSAT. The harness's cross-mode verdict check still ignores `TIMEOUT` budgets.

Classification of an inner unknown: `deadline` if the clock has passed the query's deadline
when it returns. Otherwise `capacity` if no work was done (the boundary shape is outside the
recognizer's range: more than eight wires, more than six primaries), and `work` otherwise. The
Engine throws before a tick would exceed its allowance, so a work exit can report slightly less
than the allowance.

Premature-unknown findings:

- **The 20,000-conflict limit is per CEGAR call, and it, not the 8 s wall, ends the rapid
  screen.** At the rapid tier, 37 of 40 runs ended with `conflict_limit`, after a median of 1.3 s
  (maximum 3.7 s), well inside 8 s. Plain Percy proves size 8 for `0116` in 1.9 s and 111,207 conflicts
  when unlimited. With 20,000 per call it stops after 10 calls at about 1 s.
- The wall limit is shared by every budget from `n - 1` up, so the time left for the open budget
  depends on the earlier ones. Records now carry `elapsed` from the run start.
- The slack-two recognizer limits do not bind in the slack-two configuration: the rapid tier had
  0 slack-two unknowns, and 10x work with a 4x deadline gave identical conflicts (`slack-two-phase-set-wide` in `results/baselines/tier_rapid_wide.jsonl`). Inside the
  slack-three configurations, 7-8 slack-two queries per tier hit the work limit.
- The rapid-tier timings overlapped the 122-job check suite on the same machine, so its run
  times are not reported; its verdicts and reasons are unaffected.
- Memory never binds: peak 16-50 MiB under a 512-1,024 MiB cap.
- Fixed-budget checks: `first_layer_check.py check` (122 jobs: base, slack-two-phase-set,
  slack-three lift1) all match their expected verdicts with the driver deadline on.

### Matched tiers

Setup:
- Ten hard four-input targets: `016a`, `1699`, `0116`, `6996`, `0196`, `16a9`, `1668`, `1686`, `1669`, `166b`.
- Each run searches upward from budget `n - 1` until the first SAT or the first budget left open.
- One process per (mode, target), 11 at once, with a 1 GiB commit cap.
- Per-call conflict scope unless stated.
- Columns: "Size-8 excl" counts targets whose size 8 was proved UNSAT. "Excl k>=7" counts excluded budgets of size 7 or more, summed over the targets.
- Every record agrees with the 36 known optima in `caps_hard_npn4.jsonl` (`tier_summary.py`).

| Tier | Mode | Minima | Size-8 excl | Excl k>=7 | Max / median run s | Reasons |
| --- | --- | ---: | ---: | ---: | --- | --- |
| rapid 8 s / 20k | base | 0 | 0 | 6 | - | conflict_limit 10 |
| | slack-two-phase-set | 1 | 0 | 10 | - | conflict_limit 9, sat 1 |
| | slack-three-phase-set | 1 | 3 | 13 | - | conflict_limit 8, sat 1, wall_deadline 1 |
| | slack-three-phase-set-lift1 | 0 | 3 | 13 | - | conflict_limit 10 |
| long 60 s / 200k | base | 4 | 4 | 14 | 47.2 / 17.5 | conflict_limit 6, sat 4 |
| | slack-two-phase-set | 6 | 7 | 17 | 55.3 / 19.7 | conflict_limit 4, sat 6 |
| | slack-three-phase-set | 6 | 8 | 18 | 47.2 / 14.5 | conflict_limit 4, sat 6 |
| | slack-three-phase-set-lift1 | 6 | 8 | 18 | 51.7 / 19.6 | conflict_limit 4, sat 6 |
| extended 300 s / 2M | base | 8 | 8 | 19 | 173.3 / 37.5 | conflict_limit 2, sat 8 |
| | slack-two-phase-set | 9 | 8 | 19 | 162.8 / 21.2 | conflict_limit 1, sat 9 |
| | slack-three-phase-set | 9 | 8 | 19 | 279.8 / 62.1 | conflict_limit 1, sat 9 |
| | slack-three-phase-set-lift1 | **10** | 8 | **20** | 252.0 / 60.1 | sat 10 |

Observations:
- Only slack-three lift1 established all ten minima at the extended tier, including `166b` = 10, where every other mode ended with `conflict_limit` at budget 9.
- No run ended on the wall deadline at the long or extended tier.
- Peak commit stayed at or below 225 MiB.
- Inner unknowns at the extended tier: slack-two work exits 17, 26 and 24 across the three residual modes, and four slack-three deadline exits under lift1.

### Which limit binds (60 s)

| Limits | Mode | Minima | Size-8 excl | Excl k>=7 | Reasons |
| --- | --- | ---: | ---: | ---: | --- |
| 60 s, 200k per call | base / two / three / lift1 | 4 / 6 / 6 / 6 | 4 / 7 / 8 / 8 | 14 / 17 / 18 / 18 | all incomplete: conflict_limit |
| 60 s, no conflict limit | base / two / three / lift1 | 6 / 7 / 7 / 6 | 8 / 8 / 8 / 8 | 18 / 18 / 19 / 19 | all incomplete: wall_deadline |
| 60 s, 200k per budget | base / two / three / lift1 | 3 / 2 / 3 / 2 | 3 / 6 / 6 / 7 | 13 / 16 / 16 / 17 | all incomplete: conflict_limit |

Findings:
- With 200k conflicts per call, the conflict limit ends every incomplete long-tier run. The wall limit never binds, and removing the conflict limit gains 1-2 minima per mode within the same 60 s. For example, slack-three finds `1669` = 10.
- Scoping the same 200k conflicts to the whole budget is about 5-20x tighter, because Percy's CEGAR makes many calls per budget.
- Comparisons between modes at a fixed limit are therefore comparisons at matched conflicts per call, not at matched time.
- The wall-only rows are the time-matched comparison. There slack-two and slack-three each reach 7 minima, and slack-three and lift1 exclude the most budgets (19).
- `unknown` is never read as UNSAT: every incomplete budget carries its `reason` and stays open.

Commands (from `sat-search`):

```
python baselines/tier_bench.py results/baselines/tier_rapid.jsonl --logs logs/tiers/rapid --tier rapid
python baselines/tier_bench.py results/baselines/tier_long.jsonl --logs logs/tiers/long --tier long
python baselines/tier_bench.py results/baselines/tier_extended.jsonl --logs logs/tiers/extended --tier extended
python baselines/tier_bench.py results/baselines/tier_wall_only_60.jsonl --logs logs/tiers/wall_only_60 --seconds 60 --conflicts 0
python baselines/tier_bench.py results/baselines/tier_budget_scope_60.jsonl --logs logs/tiers/budget_scope_60 --seconds 60 --conflicts 200000 --conflict-scope budget
python baselines/tier_summary.py results/baselines/tier_long.jsonl results/baselines/tier_wall_only_60.jsonl results/baselines/tier_budget_scope_60.jsonl
```

## Last-provider decoder phase screen (opt-in)

Source: the supplied `residual_decoder_phase_native` reference (an ablation of the standalone
occurrence-symmetric engine). It was ported as a small screen inside the production
`residual_slack_two::Engine` ([residual_decoder_phase.hpp](native/src/residual_decoder_phase.hpp)).
The standalone engine was not copied.

### Statement and proof

Take the last shared-provider allocation (`next + 1 == ds.size()`). Its remaining region is the
final decoder: a free-NOT AND tree over the remaining wire occurrences `rest` plus at least two
occurrences of the new provider `p`. Let S be the wires that `rest` reads once and R those it
reads more than once.

1. A tree reads each wire of S exactly once, so the decoder is unate in each wire of S. Fix its
   phase vector t (t_i = 1: x_i appears complemented).
2. Take a positive cared row a and a negative cared row b that agree on every wire of R. If they
   also agree on p, then some literal of S must be 1 at a and 0 at b. That is, some i in
   D = {i in S : a_i != b_i} has a_i != t_i. Otherwise a cannot reach 1 while b stays 0.
3. The provider is a function of its inside wires, so it is constant on inside fibers. The base
   distinction test, together with the singleton unate merges, writes every surviving provider as
   p(row) = o(component(row)) XOR side(row). A pair with t|_D = a|_D therefore forces:
   - same component, same side: impossible, so that phase subcube is removed;
   - same component, opposite sides: always satisfied;
   - different components: o(c_a) XOR o(c_b) = 1 XOR side(a) XOR side(b).
4. A candidate provider column fixes every o. It survives iff some remaining t satisfies every
   active edge.

The screen is a relaxation, because the decoder is only required to be unate in S. Exact tree
recognition still runs on every candidate that survives. A complemented decoder output swaps
the roles of a and b and complements t, so the condition is unchanged. The theorem is applied
only at the last provider: an earlier singleton may feed a later shared provider and need not
have a consistent polarity in the final target. The `(x & z) XOR y` shared-provider regression
covers this. The screen is skipped, with no rejection, when |S| > 6.

Modes:
- **Mode 1** removes phases using same-component equalities, then screens each candidate column
  (both the direct-orientation and ProviderDP branches) before exact provider recognition.
- **Mode 2** also checks each surviving phase's edge system for parity consistency (DSU) before
  any candidate.

Production adaptation:
- Work is charged while the screen is built, through the Engine's `tick`, which also polls the
  deadline. The reference charged after building.
- Each candidate check charges `edges + 1`.
- Counters per Engine answer: `decoder_screens`, `decoder_rejects` (allocation rejected before
  any candidate), `decoder_column_rejects`, `decoder_skipped` and `decoder_work`.
- `slack_three_boundary` now reports `exact_seconds`, the time in the exact `Engine(., 3)` query,
  so extension cost is the remainder.
- Interfaces: `Engine(..., use_decoder)`, `slack_two_boundary(..., decoder)`,
  `slack_three_boundary(..., memo, decoder)`, the Python `decoder=` argument, and Percy
  `--decoder-phase 0|1|2`. Percy applies it to both the slack-two and slack-three Engines and
  records `two_decoder` / `three_decoder` = [screens, rejects, column rejects, skipped, work] and
  `three_exact_seconds`.
- Harness modes: `<mode>-dec1` and `<mode>-dec2` for slack-two-phase-set,
  slack-three-phase-set and its exact and lift1 variants.
- Default 0 (off).

### Verification

- Bundle reference (MSVC `cl /std:c++20 /O2 /EHsc`, built outside the extracted directory):
  `decoder systems=2651 columns=32078 impossible=66`, `phase systems=5000 rejected=3084`,
  `DAG queries=5520 sat=3831`. The README states 3,838 SAT; every query matched its own oracle
  and verified its witnesses.
- `slack_three_native_check.py`: 28,160 decoder-mode oracle comparisons (k = 2, 3, all cares and
  first-layer counts, Engine modes 0/2/3/4/5, directed and symmetric, decoder 1 and 2). It also
  covers duplicated-wire and extension checks with the decoder on, and rejects `decoder=3`.
- `slack_two_native_check.py`: decoder modes added to its 18,304 oracle comparisons, plus the
  shared-provider regression with decoder 0/1/2.
- The 168 captured boundaries with no deadline: identical verdicts (166 UNSAT, 2 SAT) and
  identical fully decided retained sets under full, lift1 and exact. SAT witnesses verified.

### Captured slack-three boundaries (168, directed Engine mode 4)

No deadline, 2M work units, exact policy:

| Decoder | Exact tree calls | Exact work | Allocation rejects | Column rejects | Decoder work |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0 | 143,680 | 32.0M | - | - | - |
| 1 | 13,104 | 12.6M | 73,693 | 2,144 | 7.7M |
| 2 | 13,104 | 12.6M | 73,858 | 1,017 | 7.7M |

25 ms deadline, idle machine, median of 3 rotated repetitions; all 168 boundaries decided in every
configuration (`results/baselines/decoder_captured_25ms_{exact,lift1,full}.{jsonl,out}`):

| Policy | Decoder 0 | Decoder 1 | Decoder 2 | Exact part (0 -> 1) |
| --- | ---: | ---: | ---: | --- |
| exact | 1,087.8 ms | 519.1 ms | 520.9 ms | ~ whole call |
| lift1 | 1,132.5 ms | 549.5 ms | 547.2 ms | 1,073 -> 514 ms |
| full | 3,811.7 ms | 3,755.5 ms | 3,756.4 ms | 1,060 -> 515 ms |

The exact query cost halves; extension cost is unchanged per call. Under `full` the saved time
lets more slack-two extensions finish before the deadline (extension calls 4,683 -> 5,088), so
total wall time barely moves. Mode 2 does no better than mode 1, which matches the bundle's
recommendation; mode 1 is the one to use.

### Long matched tier (60 s / 200,000 conflicts per call, 10 hard targets)

`results/baselines/tier_long_decoder.jsonl` against the controls `tier_long.jsonl` and
`tier_long_exact.jsonl` (same targets, caps and harness; see the termination audit above).

| Mode | Minima | Size-8 excl | Excl k>=7 | Wall s | Reasons | Residual s (slack-three / slack-two) |
| --- | ---: | ---: | ---: | ---: | --- | --- |
| slack-two-phase-set | 6 | 7 | 17 | 214.9 | conflict_limit 4, sat 6 | - / 0.6 |
| slack-two-phase-set-dec1 | 6 | 7 | 17 | 201.1 | conflict_limit 3, sat 6, wall_deadline 1 | - / 0.5 |
| slack-three-phase-set | 6 | 8 | 18 | 153.3 | conflict_limit 4, sat 6 | 2.5 / 1.3 |
| slack-three-phase-set-dec1 | 5 | 8 | 18 | 267.4 | conflict_limit 5, sat 5 | 2.5 / 1.2 |
| slack-three-phase-set-lift1 | 6 | 8 | 18 | 226.9 | conflict_limit 4, sat 6 | 1.2 / 1.3 |
| slack-three-phase-set-lift1-dec1 | 7 | 8 | 18 | 144.9 | conflict_limit 3, sat 7 | 0.5 / 1.2 |
| slack-three-phase-set-exact | 7 | 8 | 18 | 162.2 | conflict_limit 3, sat 7 | 1.1 / 1.3 |
| slack-three-phase-set-exact-dec1 | 6 | 8 | 18 | 177.6 | conflict_limit 4, sat 6 | 0.5 / 1.2 |

- Every reported minimum agrees with the 36 known optima; no unknown was read as UNSAT.
- Inside Percy the screen halves slack-three exact time (1.1-1.2 s -> 0.5 s over the whole tier)
  and cuts inner work-limit unknowns (slack-two 11 -> 5 in slack-two mode, 16 -> 1 in lift1).
  Decoder totals for lift1-dec1: 58,321 slack-three screens, 58,141 allocations rejected,
  667 column rejects, no skips.
- The residual engines spend 1-4 s of 300-530 s SAT time per mode. The outer per-call conflict
  limit binds, and minima move by +-1 between runs because different cuts change the SAT
  trajectory. That variation is not a decoder effect. An extended (300 s / 2M) tier cannot
  measure the screen either, so it was not rerun for the decoder modes.
- Verdict: keep `--decoder-phase` opt-in (default 0). It is a clean exact-query speedup
  (about 2x on captured boundaries) with no soundness cost. End-to-end gains need the outer
  SAT search to stop dominating.

### Decoder commands

```powershell
Expand-Archive -LiteralPath "$env:USERPROFILE\Downloads\residual_decoder_phase_native.zip" -DestinationPath external/residual-decoder-phase
# Build the bundle's check and benches from a separate directory (see the bundle README), then:
& sat-search/native/build_native.bat
& sat-search/baselines/build/build_percy.bat
python sat-search/experiments/slack_three_native_check.py
python sat-search/experiments/slack_two_native_check.py
foreach ($p in 'exact','lift1','full') { python sat-search/experiments/slack_three_native_check.py --capture sat-search/results/baselines/slack_three_percy_captured.jsonl --output sat-search/results/baselines/decoder_captured_25ms_$p.jsonl --limit 200 --modes 4 --directed --decoder $p --deadline 0.025 --repetitions 3 }
python sat-search/baselines/first_layer_check.py check sat-search/results/baselines/decoder_percy_check.jsonl --workers 8 --modes slack-two-phase-set-dec1 slack-three-phase-set-lift1-dec1 slack-three-phase-set-dec2 slack-three-phase-set-exact-dec1
python sat-search/baselines/tier_bench.py sat-search/results/baselines/tier_long_decoder.jsonl --logs sat-search/logs/tiers/long_decoder --tier long --modes slack-two-phase-set-dec1 slack-three-phase-set-dec1 slack-three-phase-set-lift1-dec1 slack-three-phase-set-exact-dec1
python sat-search/baselines/tier_summary.py sat-search/results/baselines/tier_long.jsonl sat-search/results/baselines/tier_long_exact.jsonl sat-search/results/baselines/tier_long_decoder.jsonl
```

## Restriction (gate-elimination) certificates on CEGAR models (opt-in, negative end to end)

Source: `restriction_certificate_native.zip` (extracted to `external/restriction-certificate`).
Port: [restriction_certificate.hpp](native/src/restriction_certificate.hpp), wired into
`percy_run --restriction-cuts trace|cut|all|rows` with `--restriction-burst M` and
`--capture-models PATH`.

### Rule and scope (proven, complete four-input targets; partial labels use min over completions)

- For a primary substitution pi (8 constants `x_i := b` and 12 identifications `x_j := x_i ^ b`), every
  gate that becomes a constant or an alias (up to complement) of an earlier wire can be deleted.
  So a `B`-gate circuit for f has `B >= L(f o pi) + D`, where `D` counts the deleted gates.
- `L` is the exact free-NOT AIG cost of the restricted three-input function. The table `kCost3` was
  recomputed with Percy over all 256 functions and matches the bundle's brute force exactly
  (`results/restriction_certificates/aig_costs3.json`). With don't cares, `L` is the minimum over
  completions. Above three variables, the header falls back to essential variables - 1, an
  independently valid but weak bound.
- Deletions are found by constant, alias, equal/complementary-operand and structural-hash propagation.
  Each deletion carries a proof: step masks `pairs` (fanin selector fixed) and `typed` (selector plus
  operator fixed).
- A deletion caused by a constant operand, or by equal or complementary operands, needs only its own
  pair, because `g(c, y)` and `g(y, +-y)` lie in {0, 1, y, ~y} for every operator. Propagated values
  keep typed proofs.
- If the deletion count exceeds `B - L`, the cheapest set of proofs covering `B - L + 1` deletions
  gives the clause: one `-sel` literal per core step, plus the two operator bits for each typed step.
  Percy's primitive clauses forbid ops 0/6/10/12, so op bits 1 and 2 identify the AIG op.
- Output phases are read from the normalized op itself: 8 `a&b`, 2 `a&!b`, 4 `!a&b`, 14 `!(!a&!b)`.
  Nothing is pushed into neighbouring gates.
- `L > B` gives an empty core, which refutes the budget outright. The first port passed that empty
  clause to satoko, which crashed on n=3 budget 2. The fixed-budget check caught it, and the code now
  returns UNSAT directly.

### Verification

- Bundle checks (MSVC build of `restriction_certificate_check.cpp`): 80,000 restriction cases;
  161,235 mutated cores; Python oracle 50,000 restrictions / 55,448 mutated cores. All passed.
- Tripwires in Percy:
  - `deletions_hold` semantically re-checks every certificate; a failure exits with code 4.
  - In trace, rows and burst modes, a certified model that then simulates as correct also exits with code 4.
  - Neither tripwire fired in any run.
- Independent replay ([restriction_replay.py](experiments/restriction_replay.py)): it re-implements
  restrictions, propagation, cores and a semantic deletion check from scratch. Over all 145,978
  captured models, models, rejects and literal counts equal Percy's exactly. Structural deletions are a
  subset of semantic ones on every model. 1,418,260 mutations kept the deletion count; each mutation
  resampled every step outside the core and the phases of pair-only steps.
- `first_layer_check.py check` with `base-restrict`, `base-restrict-rows` and
  `slack-three-phase-set-lift1-restrict`: 122/122 expected verdicts, including the new size-8/9 jobs
  (0116 8 U, 016a 8 S, 6996 8 U, 1668 8 U, 0116 9 S, 1699 8 S).
- All tier minima pass the caps cross-check against the 36 known optima. No unknown was read as UNSAT.

### Captured CEGAR models (10 hard targets, budgets 8 and 9, 60 s / 200k per call)

`trace` follows plain Percy's trajectory exactly and only measures. `cut` learns the cheapest core
and skips simulation of rejected models.

| Mode, k | Models | Rejected | Literals/clause | Pair-only / typed steps | Repeats | Rows | us/model | Conflicts | Propagations | Decided |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| trace 8 | 107 | 104 (97.2%) | 4.58 | 275 / 67 | 10 | 116 | 35 | 2.50M | 93.7M | 4/10 |
| trace 9 | 119 | 106 (89.1%) | 7.11 | 328 / 142 | 9 | 125 | 35 | 2.84M | 115.1M | 4/10 |
| cut 8 | 40,011 | 39,961 | 5.84 | 94,394 / 46,286 | 0 | 58 | 54 | 1.74M | 71.7M | 9/10 |
| cut 9 | 105,741 | 105,647 | 6.16 | 316,668 / 111,440 | 0 | 98 | 72 | 2.74M | 127.1M | 6/10 |

- Nearly every non-final CEGAR model is certifiably redundant under some restriction. Pair-only
  (operator-independent) steps are 69-80% of core steps.
- In trace mode, 210 of 241 rows went to certified models, so each could have been replaced by a
  clause of about 5 literals. Repeats (10 and 9) show plain Percy revisiting the same core.
- Subsumption is negligible: 32 new clauses subsumed older ones across 145,608 cuts, and no clause
  was subsumed. Certificate time is 35-72 us per model, at most 2.7 s of a 60 s run.
- The catch is that cut clauses are narrow and position-specific. The solver finds the next nearly
  identical model at once: cut mode needs 400-1,100 models per CEGAR row.
- Cut mode decides 9/10 size-8 budgets against trace's 4/10, with 0.2 s refutations for 1668, 1669,
  166b and 6996. But size-9 SAT budgets slow down: 6996 k=9 takes 50.9 s against 5.6 s.

### Variants

- `rows` keeps simulating and adds the CEGAR row as well as the clause. It is no better than plain
  (016a k=8 reached the conflict limit).
- `--restriction-burst M` makes the next model after M consecutive cuts get a row too
  (`results/restriction_certificates/restriction_burst_sweep.jsonl`, 8 budgets × M ∈ {0, 1, 4, 16, 64}).
  Results were dominated by SAT variance with no consistent winner: cut decided 6/8, burst16 5/8,
  plain 1/8 under the 200k-per-call limit.

### End-to-end tiers (10 hard targets; controls from `tier_long`, `tier_wall_only_60`, `tier_extended`)

| Limits | Mode | Minima | Size-8 excl | Excl k>=7 | Wall s total |
| --- | --- | ---: | ---: | ---: | ---: |
| 60 s / 200k | base | 4 | 4 | 14 | 192 |
| 60 s / 200k | base-restrict | 3 | 7 | 17 | 455 |
| 60 s / 200k | lift1 | 6 | 8 | 18 | 227 |
| 60 s / 200k | lift1-restrict | 3 | 8 | 18 | 405 |
| 60 s wall only | base | 6 | 8 | 18 | 357 |
| 60 s wall only | base-restrict | 3 | 7 | 17 | 456 |
| 60 s wall only | lift1 | 6 | 8 | 19 | 362 |
| 60 s wall only | lift1-restrict | 4 | 7 | 17 | 402 |
| 300 s / 2M | base | 8 | 8 | 19 | 632 |
| 300 s / 2M | base-restrict | 6 | 7 | 17 | 1,497 |
| 300 s / 2M | lift1 | 10 | 8 | 20 | 765 |
| 300 s / 2M | lift1-restrict | 7 | 8 | 18 | 1,257 |

- Under 200k per call, restriction cuts raise base's size-8 exclusions from 4 to 7. That gain is
  mostly the per-call limit: cut mode makes thousands of short calls, and with the wall-only control
  base already excludes 8/10.
- Time-matched (wall only, and 300 s), restriction cuts lose minima and exclusions in both base and
  lift1. 1686 k=8 is never refuted by base-restrict at 300 s, while lift1 needs 10 s.
- Verdict: keep `--restriction-cuts` off by default (opt-in). It is sound and cheap per model, but as
  local blocking clauses the cores exclude too few assignments to pay for the extra SAT calls.

### What would justify reopening

- Position-independent certificates: a core is a small pattern (pairs of fanins with constant or
  aliased operands). Encoding "no restriction makes more than `B - L` gates redundant" as auxiliary
  propagation over all positions (eager, like the first-layer counters) would exclude whole families
  instead of one model.
- A reified per-restriction deletion counter in the encoding (constant and alias propagation
  variables per restriction) is the eager analogue. Measure clause and variable cost on the hard
  budgets first.
- For n > 4, replace `kCost3` with certified lower bounds for the restricted functions (exact
  four-input costs from the frozen corpus, or the existing analytical bounds). The current
  essential-variable fallback is valid but weak.

### Restriction commands

```powershell
Expand-Archive -LiteralPath "$env:USERPROFILE\Downloads\restriction_certificate_native.zip" -DestinationPath external/restriction-certificate
# From vcvars64, in a separate directory: cl /std:c++20 /O2 /EHsc <bundle>\restriction_certificate_check.cpp; then run the bundle's restriction_certificate_cuts.py with python -I
& sat-search/baselines/build/build_percy.bat
python sat-search/experiments/restriction_capture.py sat-search/logs/restriction_capture --modes trace cut
python -I sat-search/experiments/restriction_replay.py sat-search/logs/restriction_capture sat-search/results/restriction_certificates/aig_costs3.json
python sat-search/baselines/first_layer_check.py check sat-search/results/baselines/restriction_percy_check.jsonl --workers 8 --modes base-restrict slack-three-phase-set-lift1-restrict base-restrict-rows
python sat-search/experiments/restriction_burst_sweep.py external/percy-build/percy_run.exe
python sat-search/baselines/tier_bench.py sat-search/results/baselines/tier_long_restrict.jsonl --logs sat-search/logs/tiers/long_restrict --tier long --modes base-restrict slack-three-phase-set-lift1-restrict
python sat-search/baselines/tier_bench.py sat-search/results/baselines/tier_wall_only_60_restrict.jsonl --logs sat-search/logs/tiers/wall_only_60_restrict --seconds 60 --conflicts 0 --modes base-restrict slack-three-phase-set-lift1-restrict
python sat-search/baselines/tier_bench.py sat-search/results/baselines/tier_extended_restrict.jsonl --logs sat-search/logs/tiers/extended_restrict --tier extended --modes base-restrict slack-three-phase-set-lift1-restrict
python sat-search/baselines/tier_summary.py sat-search/results/baselines/tier_extended.jsonl sat-search/results/baselines/tier_extended_restrict.jsonl
```

## Eager constant-only restriction counters in the Percy encoding (opt-in, positive end to end)

The eager follow-up to the certificates above, from the `restriction_counter_native.zip` bundle
(extracted to `external/restriction-counter`, not committed). Instead of learning cores from models,
every budget's CNF caps the deletions of each constant restriction directly:
`sum_g D_g(pi) <= K - L(f o pi)`. The default stays off.
- `--restriction-counters zero|const|anchor` enables the counters.
- `--complement-inputs auto` enables complement normalization.

### Rule and encoding (proven for single-selection models; one-way flags)

- **Restrictions.** pi is `x_i := c`, and L is the exact `kCost3` cost of the restricted
  three-input function (min over completions). The configurations are:
  - zero: `x_i := 0` for every i;
  - const: both constants;
  - anchor: per input, the constant with the larger L (ties to 0).
- **Deletions.** A gate with a selected operand that is provably constant under pi becomes a
  constant or a possibly complemented copy of its other operand. All such gates are deleted
  together, so a K-step chain of f leaves a `K - D` step chain of `f o pi`.
- **Gate semantics.** The normalized AIG gate is `AND(a ^ na, b ^ nb) ^ (na & nb)`, with
  `na = op bit 2` and `nb = op bit 1` (Percy ops 2, 4, 8, 14; op bit j is the output at fanin0 =
  j & 1, fanin1 = j >> 1).
- **x_i := 0 (one flag per wire).** The restriction contains row zero and every wire is 0 there,
  so a provably constant wire is 0. The rules are `D = A | B` and
  `Z = (A & !na) | (B & !nb) | (A & B)`.
- **x_i := 1 (two flags per wire).** Each wire gets "provably 0" and "provably 1" flags. Each
  operand flag is pushed through its negation, the AND is provably 0 if either input is and provably
  1 if both are, and `na & nb` swaps the two output flags.
- **Shared literals and one-way flags.** Shared operand-selection literals `use[t][pos][w]` are
  implied by every selected pair with that operand, and all restrictions reuse them. Every flag is
  a one-way implication.
  - On a model with one selected pair per step, the least flag assignment is exactly the
    propagation above.
  - Percy has no at-most-one constraint on selections. Models with several selected pairs get
    over-approximated flags, which are excluded more often but never wrongly admitted.
  - Soundness therefore assumes that every feasible budget keeps a single-selection model of a
    valid chain under Percy's symmetry breaking. The checks below test this; it is not proven
    separately.
- **Cap.** The cap uses the existing Sinz `at_most`. A negative cap (`L > K`) returns UNSAT before
  any clause is added, so Satoko never receives an empty clause. Caps of K or more are skipped.
- **Input-complement normalization.** `--complement-inputs auto` complements every input whose
  `x_i := 1` cofactor costs more than its `x_i := 0` cofactor, so the stronger bound sits at zero.
  It then synthesizes the complemented target and maps the chain back by permuting each reading
  gate's operator table. The mapped chain is verified against the given table and may contain
  non-normal AND-type ops; the harness accepts any AND-type op.
- **Implementation.** `percy_run.cpp` (`encode_counters`, called from `add_extra`). The
  combination with `--restriction-cuts` is rejected.

### Verification

- **Bundle checks** (MSVC build in the scratchpad) reproduce the bundle's outputs exactly:
  4,800 representative-counter checks, 30,000 alias/deletion checks and 4,800 constant-only checks.
  The bundle bench gives:

  | Budget | const8 | zero4 | all-hash certificates |
  | --- | ---: | ---: | ---: |
  | B=8 | 1,240 | 1,133 | 1,254 |
  | B=9 | 2,284 | 2,061 | 2,333 |

- **Fixed-budget oracle** (`results/baselines/restriction_counter_check.jsonl`): 368/368 verdicts
  as expected. Modes: zero, const, anchor, renorm and renorm+zero, plus lift1+const and
  lift1+renorm+zero. Coverage spans all three-input checks (std and CEGAR, with a partial table)
  and the hard four-input budgets 0116 8 U, 016a 8 S, 6996 8 U, 1668 8 U, 0116 9 S and 1699 8 S.
  For 1699, renorm complements x3, so the mapped-back witness is checked.
- **Tier caps.** Every tier below passes the caps cross-check against the 36 known optima: no
  UNSAT at or above an optimum, and no SAT below one.

### Coverage on the 145,978 captured CEGAR models

Computed by `experiments/restriction_counter_replay.py`, which propagates constants independently
in Python. Output: `results/restriction_certificates/counter_replay.jsonl`.

| Rule | Models excluded | Share |
| --- | ---: | ---: |
| cert20 (earlier certificates, alias + hashing, 20 restrictions) | 145,818 | 99.89% |
| ids20 (representative IDs, no hashing) | 145,805 | 99.88% |
| const8 | 145,353 | 99.57% |
| ids_zero10 (IDs on the 10 restrictions containing row zero) | 124,419 | 85.2% |
| anchor4 | 120,634 | 82.6% |
| zero4 | 116,087 | 79.5% |

- Every model const8 excludes is also excluded by cert20.
- IDs add only about 450 models over const8, so representative-ID counters (option 3) were not
  implemented.

### CNF overhead (four inputs)

| Mode | k=8 vars | k=8 clauses | k=9 vars | k=9 clauses |
| --- | ---: | ---: | ---: | ---: |
| zero | 288-337 | 975-1,066 | 366 | 1,274 |
| const | 704-837 | 2,154-2,401 | 995 | 2,975 |

Encoding takes at most 8 ms summed over a whole tier.

### Bounded comparisons (CEGAR, single budget, conflicts to verdict)

| Budget | base | zero | const | lift1+const |
| --- | ---: | ---: | ---: | ---: |
| 6996 k=8 U | 160,734 | 73,163 | 274 | 453 |
| 1668 k=8 U | 519,505 | 59,783 | 401 | 479 |
| 0116 k=8 U | 111,207 | 53,256 | 45,449 | 2,886 |
| 016a k=8 S | 72,947 | 109,421 | 159,873 | 142,170 |
| 1699 k=8 S | 607,063 | 481,384 | 134,731 | 28,217 |

- The base column is base-renorm, which for these targets has an empty complement mask and so is
  identical to base. 1699 is the exception: its base value comes from the separate base run.
- The signed `x_i := 1` counters are what refute 6996 and 1668. zero alone needs about 150 times
  more conflicts on those budgets.

### End-to-end tiers (10 hard targets)

60 s jobs ran matched in one batch with fresh controls; 300 s const jobs are compared with the
archived idle-machine `tier_extended` controls.

| Limits | Mode | Minima | Size-8 excl | Wall s total | Conflicts |
| --- | --- | ---: | ---: | ---: | ---: |
| 60 s / 200k | base | 4 | 4 | 231 | 4.40M |
| 60 s / 200k | base-count-zero | 5 | 7 | 205 | 3.48M |
| 60 s / 200k | base-count-const | 6 | 7 | 159 | 2.80M |
| 60 s / 200k | base-count-anchor | 7 | 8 | 178 | 3.30M |
| 60 s / 200k | base-renorm | 3 | 4 | 252 | 4.68M |
| 60 s / 200k | base-renorm-count-zero | 5 | 7 | 175 | 3.40M |
| 60 s / 200k | lift1 | 6 | 8 | 225 | 3.35M |
| 60 s / 200k | lift1-count-zero | 5 | 8 | 236 | 3.30M |
| 60 s / 200k | lift1-count-const | 8 | 8 | 116 | 2.05M |
| 60 s / 200k | lift1-renorm | 3 | 7 | 323 | 4.24M |
| 60 s / 200k | lift1-renorm-count-zero | 4 | 7 | 272 | 3.26M |
| 60 s wall only | base | 6 | 8 | 405 | 6.40M |
| 60 s wall only | base-count-zero | 5 | 8 | 344 | 4.97M |
| 60 s wall only | base-count-const | 9 | 8 | 264 | 3.53M |
| 60 s wall only | base-count-anchor | 7 | 8 | 294 | 3.98M |
| 60 s wall only | base-renorm | 4 | 6 | 421 | 6.33M |
| 60 s wall only | base-renorm-count-zero | 6 | 7 | 349 | 4.42M |
| 60 s wall only | lift1 | 4 | 8 | 398 | 4.09M |
| 60 s wall only | lift1-count-zero | 6 | 8 | 374 | 3.91M |
| 60 s wall only | lift1-count-const | 8 | 8 | 219 | 2.86M |
| 60 s wall only | lift1-renorm | 4 | 7 | 421 | 4.78M |
| 60 s wall only | lift1-renorm-count-zero | 5 | 7 | 359 | 3.60M |
| 300 s / 2M | base (archived) | 8 | 8 | 632 | 11.81M |
| 300 s / 2M | base-count-const | 9 | 8 | 570 | 5.31M |
| 300 s / 2M | lift1 (archived) | 10 | 8 | 765 | 11.29M |
| 300 s / 2M | lift1-count-const | 10 | 8 | 372 | 2.69M |

- **Const counters win time-matched in every tier.**
  - Base: 4 -> 6 minima (200k), 6 -> 9 (wall only), 8 -> 9 (300 s).
  - lift1: 6 -> 8, 4 -> 8, and 10/10 at 300 s in 49% of the wall time with 24% of the conflicts.
  - At 60 s, lift1+const finds 166b = 10 and base+const finds 1669 = 10; neither control reached
    these in either 60 s tier.
  - base+const at 300 s leaves 166b open at k=10, with k=9 excluded.
- **Zero and anchor counters** help base under the 200k limit but are weaker than const. Zero gives
  nothing for lift1.
- **Input-complement normalization alone is negative** (base 4 -> 3 and 6 -> 4; lift1 6 -> 3).
  renorm+zero is no better than zero, so the anchor effect is not a normalization effect. The
  stronger cofactor bound helps when it is encoded (anchor beats zero for base) but loses to
  encoding both constants.
- **Scope of the 300 s rows.**
  - Only const modes were run at 300 s. Archived controls were reused instead of re-run.
  - Targets already solved by const at 60 s were re-run as part of the batch, which was
    unnecessary: a SAT budget found under the 60 s limits is a prefix of the 300 s search.
  - The batch overlapped another session's 22-process search, so its wall times are pessimistic.

### Status and next questions

- **Status.** `--restriction-counters const` is the first restriction rule with a demonstrated
  end-to-end gain. `percy_run` keeps it opt-in. Since 2026-11-25, `tier_bench.py` runs lift1 as
  `slack-three-phase-set-lift1-count-const` by default; pass `--modes slack-three-phase-set-lift1`
  for the plain control.
- **Identification counters.** Alias flags for `x_j := x_i ^ b` would cover the last 0.3% of
  models. That is low value given the replay.
- **More inputs.** For n > 4 the `kCost3` bound must be replaced by certified restricted costs;
  the four-input exact table is the natural source. Re-measure on five-input targets.
- **Combinations.** Combine `const` with first-layer budgets in the other residual modes (slack-two)
  and re-run the oracle for each combination before using it.

### Counter commands

```powershell
Expand-Archive -LiteralPath "$env:USERPROFILE\Downloads\restriction_counter_native.zip" -DestinationPath external/restriction-counter
# From vcvars64, in a separate directory: cl /std:c++20 /O2 /EHsc <bundle>\restriction_counter_check.cpp; run it; run the bundle's restriction_counter_bench.py with python -I
python sat-search/experiments/restriction_counter_replay.py sat-search/logs/restriction_capture sat-search/results/restriction_certificates/aig_costs3.json
& sat-search/baselines/build/build_percy.bat
python sat-search/baselines/first_layer_check.py check sat-search/results/baselines/restriction_counter_check.jsonl --workers 8 --modes base-count-zero base-count-const base-count-anchor base-renorm base-renorm-count-zero slack-three-phase-set-lift1-count-const slack-three-phase-set-lift1-renorm-count-zero
python sat-search/baselines/tier_bench.py sat-search/results/baselines/tier_long_counters.jsonl --logs sat-search/logs/tiers_counters_long --tier long --modes base base-count-zero base-count-const base-count-anchor base-renorm base-renorm-count-zero slack-three-phase-set-lift1 slack-three-phase-set-lift1-count-zero slack-three-phase-set-lift1-count-const slack-three-phase-set-lift1-renorm slack-three-phase-set-lift1-renorm-count-zero
python sat-search/baselines/tier_bench.py sat-search/results/baselines/tier_wall_only_60_counters.jsonl --logs sat-search/logs/tiers_counters_wall60 --seconds 60 --conflicts 0 --modes <same modes>
python sat-search/baselines/tier_bench.py <out> --logs <dir> --tier extended --modes base-count-const slack-three-phase-set-lift1-count-const
python sat-search/baselines/tier_summary.py sat-search/results/baselines/tier_extended.jsonl sat-search/results/baselines/tier_extended_counters_const.jsonl
python sat-search/experiments/restriction_counter_summary.py sat-search/results/baselines/tier_long_counters.jsonl
```
