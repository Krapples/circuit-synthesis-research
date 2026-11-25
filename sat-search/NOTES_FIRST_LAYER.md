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
