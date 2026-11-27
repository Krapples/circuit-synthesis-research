# Synthesis Audit and Endpoint Followup

## One-hot bipartite representation

The desk step L-meta-11869 asks whether the 8-by-8 table with row-major word
`7583035862004050432` requires at least 21 fan-in-two AND/OR gates. Its domain has
64 labels, each with one row input and one column input active. The smallest circuit
found has **30 gates**. Lean 4.36.0 checked its gate basis, budget, and representation
on the whole declared domain, using only `propext`.
[Lean upper bound](results/represents_8x8_11869/audit-L-meta-11869-upper.lean)

The elimination prototype establishes a **computational lower bound of 17**.
The exact budget of 20 remains open. First set the isolated row input to zero.
Its positive coordinate occurs only on zero-labeled samples, and monotonicity preserves
those labels when the coordinate decreases. Allow both constants for free and normalize a
minimum circuit by discarding unused gates and simplifying constant operands, copies, and
sample-equivalent wires. Each remaining input whose removal causes an ordered positive
and negative pair to collide must occur in the output cone. There are 15 such inputs initially.

The prototype branches on the first gate and which of its two operands have an additional
reader. If the gate loses a positive versus negative distinction after projecting away its
operands, some raw operand on which the ordered pair differs must have another reader.
Fixing a raw input eliminates its direct reader gates. A controlling value also removes a
successor of the first gate. This successor cannot also read the raw input, because either
AND or OR with the raw input and the first gate simplifies by absorption. When neither
operand has another reader, contracting the first gate leaves one new feature on the labeled
rows. These transformations only use valid labels on the selected restriction.

At the support-tight budget, equality in the operand-slot count forces a read-once formula.
For an OR root and a fixed positive sample, any child accepting it must distinguish it from
every negative sample. If a comparison differs in one coordinate in the positive-to-negative
direction, that coordinate must be in the accepting child's support. The dual argument
applies to an AND root and a fixed negative sample. If the resulting co-location constraints
connect all essential coordinates for both root operations, a read-once formula is impossible.
The bounded elimination replay excludes budgets 14 through 16 and leaves 17 open. It was
cross-checked at the exact minima of 1,920 satisfiable three-input partial labelings. A
separate two-child projection test also excludes the read-once and single-extra-fanout cases.
[Reproduction and raw records](results/represents_8x8_11869/README.md)

## Frozen baseline and harder budgets

The audit joined the 2,386 records to the complete target-label manifest and independently
evaluated all 583 SAT witnesses. Every witness matched its declared labels and gate budget.
Recorded intervals agreed with the SAT, UNSAT, and timeout outcomes. The frozen source archive
contains the implementation, Python and PySAT versions, and SHA-256 hashes of the source files,
raw results, and target manifest. [Frozen baseline sources](results/synthesis_baseline_sources.zip) ·
[Baseline results](results/synthesis_ablation.jsonl) · [Target labels](results/synthesis_cases.json)

There were 92 matched monotone budgets strictly above the elementary input-support bound.

| Configuration | SAT | UNSAT | Timeout | Summed job seconds |
| --- | ---: | ---: | ---: | ---: |
| Direct SAT | 24 | 14 | 54 | 30.11 |
| A, antichains | 46 | 7 | 39 | 22.22 |
| B, hitting sets | 58 | 19 | 15 | 9.77 |
| D, subtree cuts | 58 | 19 | 15 | 7.90 |
| E, one-sharing | 58 | 21 | 13 | 7.19 |

E completed 79 of 92 harder jobs, versus 38 for direct SAT. Summed durations including
timeouts were 4.19× lower on those jobs. Across all 258 shared budgets, E used 7.30 s versus
57.13 s for SAT, a ratio of 7.82×. These are sums of job durations from the concurrent run.

## Lower-endpoint sweep

The follow-up selected all 45 open monotone intervals and prioritized the 39 with untested
lower endpoints. SAT, B, D, and E each received the same current lower budget, with a one-second
cap and six concurrent cases. An UNSAT certificate advanced the lower endpoint. The runner
tested the new endpoint up to two rounds per case, stopping when the interval closed or a
round added no evidence. All 80 selected budgets were strictly above the support bound.
[Endpoint results](results/synthesis_endpoints.jsonl)

| Configuration | SAT | UNSAT | Timeout | Summed job seconds |
| --- | ---: | ---: | ---: | ---: |
| Direct SAT | 3 | 13 | 64 | 67.77 |
| B | 10 | 44 | 26 | 33.86 |
| D | 10 | 60 | 10 | 14.02 |
| E | 10 | 61 | 9 | 13.33 |

The sweep narrowed 39 intervals and raised 35 lower endpoints. Ten newly exact minima bring
the corpus total to **65 of 100**.

| Case | Certified monotone minimum |
| --- | ---: |
| `generated-08` | 6 |
| `cycle-5`, `hypergraph-22`, `random-monotone-03` | 7 |
| `generated-09`, `graph-01`, `graph-02`, `hypergraph-24`, `random-monotone-09` | 8 |
| `comparator-10` | 9 |

At the end of this sweep, the complete five-vertex graph was at [8, 10] and threshold
3-of-5 was at [8, 12]. The later certificate encoding below closes both at ten gates.
`hypergraph-12` narrowed from [5, 11] to [7, 11].

## Independent UNSAT checks

The certificate runner uses a separate pair-selection encoding. A real gate chooses an AND or
OR and an unordered pair of distinct operands. A minimum witness can be trimmed and padded with
identity gates at the end, so requiring the output in the last slot still represents all
at-most circuits. The real gates can be assigned in a topological order with nondecreasing
largest-operand index by taking the smallest available largest-operand index at each step.
Every newly available gate reads the latest output, so the order is safe. The encoding commits
to boundary labels in the monotone basis.

Glucose emits a DRUP trace. A separate checker verifies every addition by reverse unit
propagation, finishing at the empty clause. Retaining deleted clauses is sound because every
retained clause has already been derived. The certificates prove unsatisfiability of the
archived CNFs. The correspondence between each CNF and its named budget follows from the encoding
above and can be checked by rebuilding it from the target manifest. [Certificate files](results/synthesis_proofs/)

| Case | Excluded budget | Checked proof additions |
| --- | ---: | ---: |
| [`hypergraph-07`](results/synthesis_proofs/hypergraph-07-b6.json) | 6 | 7,459 |
| [`cycle-5`](results/synthesis_proofs/cycle-5-b6.json) | 6 | 7,681 |
| [`complete-5`](results/synthesis_proofs/complete-5-b7.json) | 7 | 74,100 |
| [`threshold-5-3`](results/synthesis_proofs/threshold-5-3-b7.json) | 7 | 64,608 |

The first two exclusions pair with verified seven-gate witnesses. The complete-graph and
threshold certificates validate the seven-gate exclusions that one-sharing found in the original
sweep. Checking those larger proofs took several minutes in the Python verifier.

## Genuinely nonmonotone targets

The separate 16-case suite covers parity on two through five inputs, four multiplexers, four
exactly-k functions, and four negative controls. Every target has a descending edge in its truth
table, certifying that an AND/OR-only circuit cannot compute it. This adds one necessary NOT to
the n−1 binary-gate connectivity bound. The one-second SAT sweep certified nine minima, including
parity-2 at four gates, the two-to-one multiplexer at four, and exactly-one-of-three at seven.
Parity-3 remains at [7, 8]. The other six open intervals and the witnesses are in the raw records.
[Signed target labels](results/synthesis_signed_cases.json) · [Signed results](results/synthesis_signed.jsonl)

## What the sharing parameter controls

For mixed positive and negative labels, let M be the number of distinct available columns, R the number of labeled rows, κ the exact
frontier hitting number, and b the remaining binary budget. Set s = b + 1 − κ. A successful
suffix uses an external set U of size m between κ and κ + s. If its excess fan-out is e, and
t wires are repeated, then t ≤ e ≤ s. Cutting at those wires gives t + 1 regions and exactly
e + t ≤ 2s incoming port occurrences across them. This bounds the number of repeated terminals
and the amount of communication independently of the formula sizes inside the regions.

Here is one explicit completion bound with κ supplied. Choose U, assign its m inputs to at
most q = s + 1 ordered regions, and assign each of at most 2s port occurrences a destination
and an earlier provider. This gives at most q^(m + 4s + 2) assignments per U, including choices
of e and t. Across all regions there are at most L = m + 2s formula leaves. Enumerating labeled
binary trees and AND/OR operations takes at most 2^L (2L)! choices for the forest. Evaluating a
choice on the R rows takes time polynomial in R and L. Summing over U gives the bound

```text
sum_{m=κ}^{min(M,κ+s)} binom(M,m) · (s+1)^(m+4s+2) · 2^(m+2s) · (2(m+2s))! · poly(R,m+s).
```

This bounds the work for fixed external inputs in terms of m and s and exposes the input-set
selection cost explicitly. The formula enumeration within a single region can already encode
an NP-complete problem, as shown below.

There is a useful exact special case. Give a partial monotone target one positive row, all ones,
and one negative row per element of a Set Cover instance. Input i is zero on that negative row
exactly when set i covers the element. Assume the supplied sets cover the universe and merge
duplicate rows. A circuit must read a covering set of inputs. Any circuit reading m distinct
inputs needs at least m−1 binary gates, and the AND of a minimum cover achieves that bound.
The optimum is therefore κ−1. This gives a reduction from Set Cover to minimum synthesis on
partial monotone tables and shows why computing the exact allowance in general can itself be
hard. [Karp's Set Cover result](https://cgi.di.uoa.gr/~sgk/teaching/grad/handouts/karp.pdf)

## Hardness at zero sharing

Arbitrary partial monotone synthesis is para-NP-hard in the sharing allowance `s`, even when
the exact hitting number `κ = M` is supplied and `s = 0`. This follows by adapting Pitt and
Valiant's Lemma 4.2 to the circuit budget and hitting-set definitions used here.
[Pitt and Valiant, *Computational Limitations on Learning from Examples*](https://doi.org/10.1145/48014.63140)

Start with a hypergraph two-coloring instance whose edges have at least two vertices. Give
each vertex a private partner and add the two-element edge consisting of the vertex and its
partner. Colorability is preserved because each partner can take the opposite color. Create a
partial table on the resulting `M` variables. Label every assignment with exactly one zero
positive, and label the assignment with zero set `Z` negative for each hyperedge `Z`. For each
variable `i`, the positive row missing its partner and the negative row missing the pair have
directional distinction set `{i}`. Thus every input is mandatory and `κ = M`. With budget
`b = M − 1`, connectivity forces every satisfying circuit to be a read-once formula.

A proper two-coloring gives a read-once formula by taking the OR of the two color-class
conjunctions. Each single-zero positive leaves one conjunction true, and each negative makes
both conjunctions false. Conversely, in any satisfying read-once formula, every leaf has an
OR ancestor. Otherwise setting just that leaf to zero would make the output false. The OR
gates with no OR ancestor therefore partition the leaves into subtrees. At each such gate,
color the leaves of its two children with opposite colors. In a monochromatic zero set, one
child of each of these OR gates stays all ones. Every such OR stays true, so the AND gates
above them give output true. A negative zero set must therefore contain both colors.

The labeled table has size polynomial in the hypergraph, so an algorithm with runtime
`g(s) · poly(M, R)` for arbitrary partial tables would imply P = NP. The status of explicitly
supplied complete truth tables is outside this reduction. The construction specifies only a
polynomial number of labels, and writing a full table on `M` variables requires `2^M` rows.

## Two-coloring formula completion

The optional `--twocolorcompletion` flag applies the equivalence to output formulas in direct
read-once and bounded-sharing completion. On the selected leaf signatures it checks for every
single-zero positive, then adds two clauses per negative zero set, requiring both colors.
When all positive labels are single-zero or all-ones rows, this decides the query exactly.
With additional positive labels, coloring UNSAT still excludes the layout. A coloring witness
is used only if the reconstructed formula satisfies every positive row. Otherwise the existing
exact completion procedure handles the query. Private-region formulas still use their usual
enumeration because their signal values must serve downstream readers. With only two-element
negative zero sets, the coloring condition is ordinary graph bipartiteness.

The six-leaf check enumerated 5,504 distinct read-once truth tables, including 3,317 that
accept all single-zero rows. It compared explicit coloring, Boolean formula enumeration, and
the new completion routine on 200 seeded hypergraphs with three private partner pairs. All
three methods agreed on the 94 colorable and 106 uncolorable cases, and the exact hitting
number was six throughout.

Replaying the completed configuration E jobs preserved every verdict and verified each new
witness against its original target labels and gate budget. Eligibility was rare, so the
shortcut remains opt-in. Query counts include repeated calls. The replay excludes archived
timeouts and measures applicability without estimating runtime gains.

| Replay | Completed jobs | Jobs with an eligible query | Output-formula queries | Coloring exclusions |
| --- | ---: | ---: | ---: | ---: |
| Endpoint sweep | 71 | 0 | 12,113 | 0 |
| Original ablation | 245 | 4 | 8,326 | 121 |

## Operation-aware formula obligations

For a read-once split `S = A ⊔ B`, write `D(a,b)` for the leaf positions that have value
one on positive row `a` and zero on negative row `b`. At an AND root both children must accept
all positive rows. Child `A` can reject `b` only if every `D(a,b)` meets `A`. If only one child
can reject `b`, that child inherits the negative label. If neither can, the split fails. At an
OR root both children reject all negative rows, and the dual rule assigns positive rows.

`--typedsubtreecuts` recurses on forced labels and leaves the ambiguous ones unassigned. This
is a necessary condition. `--labelcompletion` tries every allocation of ambiguous rows and
returns a witness from a successful allocation. Necessity follows by assigning an ambiguous
row to one child that already handles it in a witness. Sufficiency follows by combining the
child witnesses with the selected operation. With a single label polarity, the all-OR or
all-AND tree gives the pointwise extremum and decides the query. These options apply to final
output formulas. Private shared signals retain bottom-up enumeration of attainable columns.

For `m` leaves and `R` labeled rows, the exact recursion has a bound of
`O(3^m · 3^R · poly(m,R))`. Summing over leaf subsets and their binary splits contributes
`3^m`. For each root operation, each label is omitted, assigned to one child, or assigned to
the other. Labels common to both children only need the omitted and included choices. The
relaxation skips ambiguous assignments and has a bound of `O(3^m · 2^R · poly(m,R))`.

On 900 seeded partial tables with four to six leaves, exact completion agreed with exhaustive
enumeration throughout. The original cut rejected 35, and typed cuts rejected another 75. The
sample had no exact-only exclusions. A separate six-leaf query does have one. Use positive rows
`{19, 38, 50, 52}` and negative rows `{11, 25, 26, 41}`. Both cuts admit it, and exhaustive
formula enumeration rejects it. The earlier five-leaf query in the regression suite passes
the original cut and fails the typed cut.

All 316 completed configuration E jobs reproduced their verdicts under each new configuration.
Every returned witness matched all declared labels and its budget. Typed cuts alone excluded
929 output-formula calls that survived the original test. They reduced the sum of distinct
enumeration counts per job from 1,916 to 1,483. Exact label completion alone reduced it to
1,385. The counts include private-formula enumeration. On one serial replay, the baseline took
4.35 s, typed cuts took 4.37 s, exact label completion took 4.46 s, and the combination took
4.47 s. The experiment excluded archived timeouts and established no end-to-end speedup. Both
flags remain opt-in.

## Cograph SAT encoding for linked regions

Give each leaf occurrence a graph vertex. Join two vertices when the lowest common ancestor
of their leaves is AND. OR subtrees give disjoint union, and AND subtrees give complete join.
The resulting graphs are the cographs, characterized by the absence of an induced four-vertex
path. A cotree gives an AND/OR formula back. Its maximal cliques are the formula's minterms,
and its maximal independent sets are its minimal zero certificates. The two facts follow
recursively from disjoint union and join. [Corneil, Lerchs, and Stewart Burlingham](https://doi.org/10.1016/0166-218X(81)90013-5) ·
[Golumbic, Mintz, and Rotics](https://www.cs.haifa.ac.il/~golumbic/papers/J53-An%20Improvement-GMR2008-DAM.pdf)

A positive row must contain a maximal clique in its one positions. It suffices to choose a
clique among those positions that blocks every zero position by a missing edge. Extend that
clique to a maximal one inside the ones. The blockers remain, so the result is globally
maximal. The negative encoding is dual on the zero positions. One graph serves all rows of
a region. Guard each sign by the symbolic regional output when necessary, and link a port to
the same provider wire on every row. This retains port-source and reader constraints while
avoiding formula-table enumeration. For width `m` and `R` rows, the local encoding takes
`O(m^4 + Rm^2)` clauses and `O(m^2 + Rm^2)` variables before wiring.

`synthesize_regions(..., formula_encoding='cograph')` agreed with exhaustive enumeration on
900 partial formula queries and with the table encoding on 60 seeded layouts in the free,
consistent, and linked modes. An eleven-input example uses an eight-leaf provider read through
two ports. The one-port layout is UNSAT, and the two-port circuit passes all 2,048 assignments.
The old table implementation supports up to six leaves per region. The new encoding remains
exponential in the worst case and keeps fixed groups and port counts as inputs.

A serial comparison put each of the 22 five-input corpus targets in the same `(1, 30)`
layout with two reads of the first region. The old and new encodings agreed on seven SAT
and 15 UNSAT jobs, with witnesses checked against all original labels. Table selection took
3.777 s, the cograph encoding took 0.014 s, and concrete forward synthesis took 0.037 s.
This fixed-layout replay measures
formula encoding and SAT for one layout per target. Layout search costs were outside the run.

### Joint primary partition and support selection

For a sequence of port counts, assign each primary leaf to a region inside SAT. The cograph
constraints apply to the induced graph on the region's active leaves. Unused candidate leaf
vertices may be isolated, so the same induced-path clauses work when the partition is unknown.
The row certificate constraints only pick active leaves and only require blockers for active
forbidden leaves. A port keeps its provider across rows. If every selected distinguishing
input for a row pair belongs to one private region, its output must distinguish that pair.
This follows by cutting that single terminal and applying monotonicity to its value and to
the remaining primary inputs.

`--formula-backend joint-cograph` tries one SAT instance per port-count pattern rather than
per partition. The five-cycle returned a verified seven-gate minimum after 12 patterns.
The explicit-partition cograph and forward backends each visited 2,407 layouts. In the
recorded runs, joint, explicit cograph, and forward took 1.071 s, 2.430 s, and 5.161 s,
respectively. The joint backend also recovered the four-gate path and the nine-gate minimum
of a ten-input read-once example. The tests compare the joint solver with explicit layout
search on 20 small target-pattern pairs.

`--jointcompletion` lets the SAT instance leave inputs unused. For `r` regions, `q` ports,
and `m` selected inputs, the formula sizes sum to `m + q − r` gates. Encode the budget as
`m ≤ b + r − q`. Each of the `r − 1` private terminals needs at least two reads, so
`2(r−1) ≤ q`. The hitting bound gives `κ ≤ m`. Therefore `r ≤ s+1` and `q ≤ 2s`, where
`s = b+1−κ`. The number of port-count patterns is `2^O(s)`. For each pattern SAT chooses the
support, partition, port sources and regional formulas together. The SAT decision inside
each pattern remains hard in general. Exactness follows from cutting every repeated wire
in a circuit witness and, in the reverse direction, wiring the decoded regional formulas.

The joint frontier option matched brute-force circuit search on 144 small partial budgets.
The three-case frontier replay also reproduced each minimum and adjacent exclusion with
verified witnesses. On satisfiable budgets it took 1.71 s versus 7.14 s for `hypergraph-07`,
0.55 s versus 4.56 s for `cycle-5`, and 0.029 s versus 0.43 s for `comparator-10`. The
six-gate exclusions for the first two were faster with the existing solver. The joint
mode remains opt-in. The separate reverse-unit-propagation checker accepted proofs for
all six patterns at the excluded budget for each of `hypergraph-07` and `cycle-5`.
The checks verified 7,195 and 6,499 proof additions, respectively.

A separate probe allowed eight wall seconds per open endpoint. All three reached the
cap. Their boundary grids have overlapping distinctions and large pair-count gaps, so
the small-gap and unique-distinction results below do not certify these budgets.

| Case | Budget | Positive × negative rows | δ | Singleton distinctions |
| --- | ---: | ---: | ---: | ---: |
| `complete-5` | 8 | 10 × 5 | 45 | 20/50 |
| `threshold-5-3` | 8 | 10 × 10 | 95 | 30/100 |
| `hypergraph-12` | 7 | 5 × 6 | 25 | 17/30 |

The symbolic leaf values also allow one globally chosen sign per leaf. De Morgan's laws
push a free NOT through a read-once formula without changing its binary gate count. The
signed cograph solver matched exhaustive sign and formula enumeration on 120 seeded partial
tables. Full parity-2 and the two-way multiplexer are impossible in this basis with one
occurrence per leaf. Both have incompatible sensitivity signs on at least one variable.

Free NOT can reduce the binary budget on a partial table whose labels admit a monotone
extension. With positive masks `{5, 9}` and negative masks `{3, 12}`, the three singleton
monotone distinctions force `x0`, `x2`, and `x3`. The monotone minimum is two gates, attained
by `x0 AND (x2 OR x3)`. The signed minimum is one binary gate, attained by `x0 AND NOT x1`.
The four labels exclude every single signed literal.

## Which parameters control the difficulty?

The zero-sharing hardness survives a maximum raw distinction-set size of three. Starting
from 3-SAT, use one reference vertex `F` and opposite-color partner vertices for the two
signs of every variable. A clause `(x,y,z)` is `NAE(x,y,z,F)` once the color of `F` is called
false. Introduce a fresh opposite pair for `t` and replace this by `NAE(x,y,t)` and
`NAE(¬t,z,F)`. If `x=y` and `z=F`, the two constraints are compatible exactly when these
two common colors differ. Otherwise at least one constraint permits either value of `t`,
and the other can be satisfied. The construction uses two- and three-element edges. In the
single-zero reduction every raw distinction set is contained in its negative zero set, so
its size is at most three. The partner edges force singleton distinctions for every input,
so the inclusion-minimal distinction graph is edgeless. Together with `s=0`, neither raw
maximum size nor width of the *minimized* hitting-set constraints removes the hardness.
The same reduction holds with free NOT. Each partner pair supplies a witness differing
in the mandatory input alone, with positive value on its high side. Mandatory support and
`M − 1` binary gates force a tree even with unary NOT gates. Pushing NOT to leaves then
forces every resulting sign to be positive by its witness.

The row count does give a parameterized bound. For `p > 0` positive rows and `n > 0` negative
rows, a circuit exists exactly when every distinction set is nonempty. For each positive row,
choose one distinguishing column against each negative row, AND the choices, then OR the
`p` terms. This uses at most `pn − 1` gates. The bound is sharp. Take one variable `x_ij` per
pair, positive row `i` with ones in row `i` of the variable grid, and negative row `j` with
zeros in column `j`. Every pair mandates its own `x_ij`, giving a connectivity lower bound
of `pn − 1`. An upper gate budget at most `O(R²)` and at most `2^R` different signal columns
after projection onto `R = p+n` rows give exact synthesis in `2^O(R³) · poly(M,R)` time by
enumerating gate programs. A homogeneous label set uses a covering OR or AND with at most
`R − 1` gates if feasible without constants.

## Distinction rectangles and the first sharing obstruction

View `P × N` as a grid of positive–negative pairs. A leaf distinguishes the rectangle
consisting of its one rows in `P` and its zero rows in `N`. A formula induces a recursive
partition of the grid. At OR, route a positive row to a child accepting it. At AND, route a
negative row to a child rejecting it. The leaves receive rectangles they distinguish. Conversely,
a recursive partition into such leaf rectangles gives a consistent formula by using OR for
row splits and AND for column splits. This is the monotone Karchmer–Wigderson correspondence
restricted to the supplied labels. [Karchmer and Wigderson](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/KW90/KW90.pdf)

When each pair has exactly one distinguishing leaf and every leaf distinguishes a pair, the
grid has a unique rectangular tiling. A read-once formula has to realize every whole tile
with its single occurrence. Join rows that occur in one tile, and dually join columns. Any
root split has to keep the connected components on its axis intact. If an axis is disconnected,
split into all of its components. This is safe because a successful protocol restricts to
each component. If both axes are connected in a subgrid with multiple tiles, it certifies
that a read-once solution is impossible. The same safe split preserves optimal formula size
with repeated leaves because each leaf belongs to just one component on the split axis.

Let `δ = pn − κ`. For any mixed, monotone-consistent partial table with `δ ≤ 3`, the minimum
is `κ − 1`. Take a minimum cover of the grid by `κ` variables and assign each pair to one
covering variable. Every variable has a private pair, so no group is empty. Group sizes in
excess of one sum to `δ`. If any variable covers four cells, `δ = 3`. Take its whole rectangle
and one variable per remaining cell. Otherwise every variable's rectangle lies in one row or
one column, and every assigned group is a rectangle. A group of at most three exceptional
cells can be isolated by cuts. Two nonsingleton strips are also separable. For opposite
orientations, the horizontal row avoids the vertical strip or the vertical column avoids
the horizontal strip. The only remaining case is three two-cell strips. If both orientations
occur, take the axis on which only one strip joins two rows or columns. If more coordinates
on that axis contain a nonsingleton strip, split those off. Otherwise both opposing strips
avoid the single strip's transverse coordinate, which gives a cut on the other axis.
Singletons impose no restriction on either cut. This gives a read-once construction on `κ`
leaves in every case.

At gap four, this tiling has five mandatory leaves. Both axes are connected, so four gates
are impossible. The five-gate formula `(B AND (A OR (D AND E))) OR (D AND C)` checks against
all six labels.

```text
A A B
D E B
D C C
```

On any indivisible subgrid with `r` rows, `c` columns and local tile savings `d`, the two
connected graphs need at least `r − 1` and `c − 1` connections. A tile of dimensions `h × w`
contributes at most `(h − 1) + (w − 1) ≤ hw − 1` toward this total. Hence `r+c ≤ d+2`.
For unique distinctions, `d ≤ δ`. After safe cuts, compute exact minimum formula size in
each remaining subgrid by memoizing row and column subsets. A single-owner subgrid costs one
leaf. Otherwise minimize the sum over all row or column cuts. This gives an explicit
`O(3^(δ+2) · poly(M,R))` formula minimization algorithm for unique distinctions. Repeated
internal signals in circuits can make the circuit optimum smaller than the formula optimum.

The check covered all 763 rectangular tilings of a 3×3 grid. The greedy test and the exact
leaf algorithm agreed with an independent cut recurrence. The 18 nonseparable tilings all
had gap four and consisted of four two-cell strips around a singleton. The padded example
recovers the same six-label certificate after adding two singleton rows and columns.

At gap four every monotone-consistent mixed table has a partition with `κ` tiles. If a variable covers
five cells, its full rectangle plus one variable per remaining cell is a minimum partition.
If all rectangles are strips, a minimum cover can assign cells to its members arbitrarily
and each group remains a rectangle. The remaining case has a `2 × 2` rectangle `A`. If any
variable covers two cells outside `A`, it covers an aligned pair there. A strip gives one
directly, and the intersection of two `2 × 2` rectangles cannot remove just two diagonal
cells. Choose `A`, such a pair, and singletons. If every variable covers at most one cell
outside `A`, a minimum cover consists of exactly one variable per outside cell. Any selected
rectangle crossing into `A` is a strip, since a `2 × 2` rectangle cannot overlap `A` in
three cells. Hence a minimum rectangular partition also exists in this case.

An indivisible tiling with gap four must be `3 × 3`. A nontrivial two-row grid with a
tile spanning its rows has a separating column cut, because other tiles cannot meet that
tile's columns. If no tile spans the rows, the row cut works. The two-column case is dual.
The bound `r+c ≤ d+2` therefore forces `r=c=3` and `d=4`. Equality in the connection count
excludes tiles with both dimensions bigger than one. To connect both axes requires two
row connections and two column connections. A length-three strip on either axis isolates
its transverse coordinate in the opposing graph. Thus the core consists of four two-cell
strips. The two horizontal strips share a column, the two vertical strips share a row,
and disjointness puts their intersection in the singleton. The two orientations are the
displayed tiling up to permutations. Consequently every mixed table with `δ=4` has a
monotone circuit with at most `κ` gates. The example above attains that upper bound.

### Parameterized formula synthesis with overlapping distinctions

Make a graph on the pair cells and join cells distinguished by a common variable. A maximal
matching of `t` edges gives a cover of size at most `pn − t`, by taking one variable per
edge and one per leftover cell. Its endpoint set `X` is a vertex cover. Each variable can
cover at most one cell outside `X`. Thus `t ≤ δ ≤ 2t`. A matching can be found by greedily
pairing available cells within each variable rectangle. This requires no hitting-number
oracle.

An optimal formula partitions the grid into rectangles. Its savings below `pn` leaves are
at most `δ`, so it uses at most `δ` nonsingleton tiles with at most `2δ` total cells. Mark all
row and column coordinates touching `X`. A tile using an unmarked row must be a vertical
strip in a marked column. It has one unmarked cell and any other cells are in `X`. Otherwise
its rectangle would contain two distinct cells outside `X`. The same property holds for an
unmarked column. A request for a particular unmarked row is the subset of `X` used across
all its nonsingleton tiles. For each marked column in the request, a single available
variable must cover that column's requested cells and the cell in the unmarked row.

For every request, retain up to `2t` unmarked rows that can meet it, and treat columns
dually. An optimal protocol uses at most `2t` occupied unmarked rows or columns per axis.
For requests with fewer than `2t` candidates, the original distinct coordinates were all
retained. The other requests can each choose an unused representative greedily. Relabel
the grid by these injections, then remove unretained coordinates, whose cells are singletons.
The number of leaves saved is unchanged. Conversely any solution on the reduced grid can
be lifted by attaching the dropped rows and columns with singleton cells. Each axis retains
at most `2t + 2t·2^(2t)` coordinates, with singleton grids handled directly. The same
argument preserves hitting-number savings by assigning cells to a minimum cover. Its
assigned groups may be nonrectangular on marked coordinates, but each group containing an
unmarked coordinate still has only one unmarked cell and stays in its row or column.

The implementation runs subset dynamic programming on the retained grid. A sharper bound
follows by enumerating the shape of the at most `2δ` nonsingleton cells among the marked
coordinates and at most `δ` abstract unmarked coordinates per axis. There are
`2^O(δ log(δ+2))` ways to pick and group these cells, even using `2t` in place of `δ`. For
each shape, use bipartite matching to realize distinct abstract coordinates with actual
rows or columns satisfying their requests. Choices on opposite axes are independent, since
no nonsingleton tile meets both an unmarked row and an unmarked column. Fill the remaining
cells with singletons and check recursive separability. This gives exact minimum formula
leaves and the tight-circuit decision in `2^O(δ log(δ+2)) · poly(M,R)` time. For the hitting
number itself, permit arbitrary groups covered by one variable and omit separability. The
shape bound is a proof. The prototype uses the representative reduction and the subset DP.

The reduced formula solver agreed with an independent minimum-leaf enumeration on 120
seeded partial queries and preserved the exact hitting-number savings in every feasible
one. In a `11 × 3` grid where ten rows can share the same marked cell, it retained a
`4 × 1` grid and reconstructed an exact 32-leaf formula.

### Circuit projection and a failed additivity assumption

For a unique distinction tiling, retain every row and column touched by a nonsingleton
tile, or one of each if there are none. Every cell outside that core is a singleton with
its own input. On the core, an input from a deleted positive row is zero on all positive
labels and can be set to zero. An input from a deleted negative column is one on all
negative labels and can be set to one. Each substitution preserves the core labels by
monotonicity. Simplifying the output cone never increases its undirected cycle rank
`e = gates − used inputs + 1`. Identity simplifications contract edges and absorbing
simplifications delete edges before pruning. Every deleted input had been mandatory, so
each deleted singleton saves at least one gate. Conversely the core circuit can be lifted
with exactly one additional gate per deleted singleton by adding row and column cuts.
This proves exact circuit minimization with arbitrary sharing in
`2^O(δ² log(δ+2)) · poly(M,R)` time for unique distinctions. The retained grid has
`O(δ²)` cells and the circuit can be found by enumerating binary gate programs up to the
row-product bound. The proof is specific to singleton padding removal.

Sharing overhead is subadditive in general even for disjoint row components of a unique
tiling. Stack `k` copies of the five-tile obstruction with separate variables and common
negative columns. OR together corresponding inputs across copies, then apply the five-gate
core circuit once. This gives `5k` gates. The rectangle obstruction rules out `5k−1`, so
this is exact. Independent components with a final OR would cost `6k−1`. The three-copy
check verifies the 15-gate pooled circuit against all labels. The gap rules out using the
sum of formula-component overheads as a circuit lower bound. For overlapping distinctions,
the formula representative swap preserves rectangular protocols and covers. The circuit
extension below uses the demands of a whole circuit instead of adding component costs.

## Certificate reduction for overlapping circuit distinctions

For mixed labels `P,N` with a monotone extension, exact minimum binary AND/OR circuit
synthesis is fixed-parameter tractable in `δ = |P||N| − κ`, allowing arbitrary internal
sharing and overlapping distinctions. The proof gives
`2^O((δ+1)^4 log(δ+2)) · poly(M,R)` time on `M` inputs and `R` listed labels. It computes
the hitting number `κ` from the matching before choosing the core representatives.

### Intersection of circuit certificates

Trim the circuit to its output cone. For each positive row, choose a DAG certificate by
keeping both operands at AND and one true operand at OR. For each negative row, keep
both operands at OR and one false operand at AND. Make each gate's decision once per row,
even when the certificate reaches it along several paths. Fixing the chosen primary inputs
to their certificate values forces the corresponding output, by induction up the circuit.

Orient edges from each gate toward its operands. The positive and negative certificate
intersection contains the output, and every gate it contains has exactly one common
outgoing edge. A source in the intersection other than the output must have distinct
incoming edges in the two certificates. Count operand occurrences as edges if an operand
is used twice. Write `ρ` for the undirected cycle rank of their union. The union is rooted
and connected, so `ρ` is the sum, over its nonroot vertices, of indegree minus one. There
are at most `ρ` nonroot intersection sources. In the intersection each source follows one
path to an input sink, and each sink is reached from a source. Consequently

```text
1 ≤ |C⁺(a) ∩ C⁻(b)| ≤ 1 + ρ ≤ 1 + e,   e = B − m + 1.
```

Here `B` is the number of gates and `m` the number of used primary inputs. The bound
with `e` follows because the union is a subgraph of the output cone. Each common input
has value one on `a` and zero on `b`. For a total function, a minimal one certificate and
a minimal zero certificate can each be realized by a syntactic certificate on the assignment
that has exactly that set of required bits. Minimality forces the syntactic certificate to
use the whole set. Thus for any minterm `S` and maxterm `T`, a circuit with `m` essential
inputs needs at least `m + |S ∩ T| − 2` gates.

### Projection and representative relocation

Let `L = |P||N|`. Use the endpoint set `X` of a maximal matching on the distinction cells,
and write `x = |X|`. Each input distinguishes at most one cell outside `X`. Pairing the
matched cells and covering the rest individually gives `x/2 ≤ δ`, and the outside cells
need different owners, giving `δ ≤ x`. Mark every coordinate touching `X`.

For each input `w`, let `A_w` and `D_w` be its positive and negative certificate rows.
The demand rectangle `Q_w = A_w × D_w` is contained in the actual distinction rectangle.
Call an input exceptional when `Q_w` touches `X`. A circuit optimum has `B ≤ L−1` by the
row-product construction and `m ≥ κ`, so `e ≤ δ`. The intersection lemma bounds the
number of exceptional inputs by `x(e+1) ≤ K`, where `K = x(δ+1)` is computable below. Each
exceptional input demands at most one outside cell. Every nonexceptional input has an
empty demand rectangle or demands a single outside cell.

For the moment, keep the marked coordinates and the unmarked coordinates of each
exceptional outside demand cell. Denote the original retained grid by `I × J` and let
`d=L−|I||J|`. Every deleted cell has a common certificate input because of the lower
intersection bound. Such an input is nonexceptional, so it cannot serve another deleted
cell. On `I × J` its retained requirements have at most one polarity. Fix all inputs
with only positive requirements to one, all with only negative requirements to zero, and
all with neither arbitrarily. The retained certificates still force the output. At least
`d` distinct used inputs have been fixed. Simplification of the connected output cone
does not increase its cycle rank, so `B_core ≤ B−d` by `B=m−1+e`. The mixed output labels
ensure a nonconstant output, and constant propagation removes all constant operands.

An exceptional requirement using an unmarked row is contained in one marked column.
It asks for the new row's cell plus a nonempty subset of the marked cells in that column.
A request contains all such requirements for one unmarked row. It may contain several
different requirements in the same column, and each may use a different available input.
An unmarked column has the dual kind of request. No exceptional input needs an unmarked
row and an unmarked column together. Retain up to `K` satisfying representatives for
each nonempty request of at most `K` requirements. For requests with fewer than `K`
satisfying coordinates, the original distinct coordinates were all retained. Those
assignments can be fixed first, after which each other requested coordinate has `K`
choices. Thus truncation preserves injective realizability. In any witness, at most `K`
line requirements occur in total across both axes. Search multisets of requests with
this total cap. Solve a bipartite matching problem on each axis for each multiset to
obtain one realization. The axes are independent and any realization satisfies the same
certificate obligations. The prototype deduplicates the resulting core masks.

Apply the constant substitutions **before** relocating any remaining input. After mapping
the labels injectively, replace each remaining input by a column satisfying its entire
mapped demand rectangle. Marked rectangles keep their original owner, the representatives
supply each exceptional fringe rectangle, and feasibility supplies an owner for every
nonexceptional singleton. Both signs of every remaining certificate are preserved. Two
different inputs may map to the same column, which cannot increase gate count. This
preserves the `B−d` gate bound on the relocated grid. Keeping a one-polarity input fixed
to its original column would be insufficient, since its value can change at the new row.

### Exact lifting and runtime

To append a positive row, AND one distinguishing input against each current negative row,
then OR this term into the output. To append a negative row, use the dual construction.
Each inserted positive row costs at most the current negative count and each inserted
negative row at most the current positive count. Adding positives first and then negatives
costs at most `d` gates. Hence the full optimum is the minimum of `B*(I,J)+d` over the
candidate cores. Adding more coordinates to a candidate cannot increase this quantity.
Each realized request collection can therefore be padded arbitrarily up to `K` unmarked
coordinates. If all eligible fringe coordinates already fit, one core containing all of
them suffices.

### Computing the gap and reducing the core inputs

Compute `κ` by tracking coverage masks on `X`. Every cover can designate one input for
each outside cell, and these designated inputs must be distinct. For each outside cell in
turn, update the reachable masks by taking the union with each possible owner's coverage
of `X`. This spends exactly one input per outside cell. Then add the fewest extra inputs
to reach the full mask by shortest paths with unit cost per additional mask union. This
phase may use further inputs that also cover outside cells. Each transition is valid, and
every minimum cover admits such a designation and addition order. There are at most
`2^x` states and polynomially many choices per state, so both the full and projected
cover numbers can be computed in `2^O(δ) · poly(M,R)` time. This is a direct instance of
the structure behind the established Set Cover parameterization below universe size.
[Basavaraju, Francis, Ramanujan, and Saurabh](https://doi.org/10.4230/LIPIcs.FSTTCS.2013.67)

Fix one available owner in advance for every pair cell in a core. In a circuit of budget
`b`, each used input with one or zero retained certificate polarities can be fixed and
simplified. A nonexceptional input with both polarities serves a single cell and may be
replaced by its fixed owner. This preserves each certificate because the replacement
meets all of that input's required true and false labels. Therefore only the exceptional
owners still need to be chosen. If `κ_core` is the projected cover number, the certificate
lemma gives at most `x(b−κ_core+2)` additional owners. Use the same `X` as for the full
grid. The gap of a core is at most `δ` because a core cover can be extended to the full
grid by one owner per deleted cell. For the budgets of interest, `b ≤ L'−1` on a core of
`L'` cells. Thus at most `K` additional owners are needed, and each must distinguish a
cell of `X`. It suffices to enumerate maximal sets within this owner cap, since extra
available inputs can be left unused.

A line requirement chooses a nonempty subset of `X` in one line. There are at most
`2^x` possibilities per axis. Encoding at most `K` requirements, their grouping into
requests, and their axes gives `2^O((δ+1)^3)` request multisets to match. A core has
`O((δ+1)^2)` coordinates per axis and `L'=O((δ+1)^4)` cells. A useful projected column
is determined by its subset of `X` and at most one outside cell, giving at most
`(L'+1)·2^x` possible columns and `2^O((δ+1)^3)` choices of additional owners. Once they
are chosen there are at most `L'+K` available inputs. The core needs at most `L'−1`
binary gates, so enumerating gate programs takes `2^O((δ+1)^4 log(δ+2))` time. This
dominates the request and owner enumeration bounds and improves the previous exponent
of `O((δ+1)^5)`.

If `X` is empty, each variable distinguishes at most one pair, so the minimum is `L−1`.
For a constant-free circuit with only positive labels, append the automatic negative label
on the all-zero input. For only negative labels, append the automatic positive label on
the all-one input. The optimum is preserved and `δ` is measured on this augmented table.
The raw empty-grid gap cannot parameterize homogeneous cases in the constant-free basis.
For example, true labels corresponding to elements of a Set Cover instance need exactly
the minimum cover size minus one gates, attained by an OR and bounded below by connectivity.
An empty label list permits a zero-gate input if one is available.

### A limit on polynomial preprocessing

The budget decision problem under this parameter has no polynomial kernel unless
`NP ⊆ coNP/poly`, even with one negative row. Reduce from the known hard-to-kernelize
Set Cover decision problem asking for at most `u−k` sets on a universe of size `u`.
Remove duplicate incidence rows, adjusting the requested saving to keep the same cover
budget. Uncovered elements, empty instances, and trivial budgets are decided directly.
Let `u'` and `k'` be the resulting universe size and requested saving, with `0 < k' ≤ k`.

Use each element's set-incidence vector as a positive row and the all-zero vector as the
sole negative row. A minimum circuit uses exactly `κ−1` gates. Its inputs must cover the
universe, and OR realizes a minimum cover. Set the gate budget to `u'−k'−1`. A maximal
matching of size `t` in the element co-coverage graph guarantees saving at least `t`, so
if `t ≥ k'` return a fixed yes-instance. Otherwise the outside-cell argument bounds the
actual output parameter by `δ ≤ 2t < 2k' ≤ 2k`. This is a polynomial-time parameter
transformation even though the synthesis parameter is the actual gap and is computed
from the output instance. A polynomial-size equivalent synthesis instance could be
reduced back to Set Cover by the usual NP reduction. Listed-label circuit decision is
in NP since any feasible instance has the row-product gate bound. The composition would
give the excluded polynomial kernel for below-universe Set Cover. The result concerns a
single polynomial-size equivalent instance. The representative search is a family of
cores and uses parameter-dependent computation to produce it.
[Gutin, Jones, and Yeo, below-bound Hitting Set](https://arxiv.org/abs/1010.5881)

### Checks and relation to prior work

The prototype agreed with independent gate-set enumeration on 150 seeded tables and 60
additional overlapping grids with deleted cells. It also recovered the exact 15-gate
minimum on a padded overlapping grid with pooled sharing. The retained core has nine gates,
and the full optimum formula needs 17 leaves, so 15 gates require internal sharing. The
large overlapping star retained 6 of 33 cells and recovered its 31-gate minimum. A case
where one late row is needed used two cores under request matching. The former subset
enumeration used seven. On 64 additional feasible grids, the canonical input and
exceptional owner choices preserved the independent gate-set minima, and the marked-cell
cover counts matched the general hitting-set routine. The certificate check examined
64,071 pairs across 300 random circuits, including 175 with
shared output cones. A separate three-input circuit attains the certificate bound.

The literature pass connected the proof to the classical read-once certificate
intersection characterization and the monotone Karchmer–Wigderson relation. The rectangle-DAG
correspondence supplies a related representation of arbitrary monotone circuits on partial
functions. Cavalar et al. study hardness of approximating monotone circuit size from
listed examples. These sources establish the surrounding context. Priority for the
distinction-gap parameter and representative reduction remains unverified.
[Gurvich characterization in Golumbic, Mintz, and Rotics](https://doi.org/10.1016/j.dam.2008.02.011) ·
[Karchmer and Wigderson](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/KW90/KW90.pdf) ·
[de Rezende et al., rectangle-DAGs](https://jakobnordstrom.se/docs/publications/TrulySupercriticalTrade-offs_STOC.pdf) ·
[Cavalar et al., listed-example approximation](https://doi.org/10.4230/LIPIcs.CCC.2026.40)

## Certificate intersection rank and regional decomposition

This section uses full minterms and minimal zero certificates of a nonconstant complete
monotone function. These can also be supplied directly, as for a graph function. A label
boundary of an arbitrary partial function lacks the same certificate interpretation.
For minterm `S` and zero certificate `T`, define `H[S,T] = |S∩T| − 1`.

Use the certificate intersection DAG from the projection proof. Its common gates each
have one common outgoing operand edge, so its number of common input sinks is its vertex
count minus its edge count. Write `a_v,b_v` for the positive and negative incidence
vectors of each vertex, and define the edge vectors in the same manner. The output's
all-ones term cancels the subtracted one. A uniquely read wire's term cancels its single
incoming edge. Hence

```text
H = Σ_v (a_v b_vᵀ − Σ_ell a_ell b_ellᵀ), with v repeated and ell reading v.
```

A degree-`d` repeated wire contributes at most rank `d+1`. With `r` repeated wires
and excess `e = Σ(d−1)`, this gives `rank(H) ≤ e+2r ≤ 3e` over any field. The earlier
source-count proof also gives `max H ≤ r`, since each additional intersection source
is a distinct repeated wire.

For a two-reader wire the nonzero entries of its local table are `+1` on `10 × 01`
and `01 × 10`, and `−1` on `11 × 11`. In a one-sharing circuit, nonnegativity excludes
the negative rectangle, so the support is at most two vertex-disjoint bicliques. For the
first repeated wire in output-to-input topological order, the only common path available
is the path from the output. Its local contribution cannot be negative. If it has two
readers, this saves one rank. If it has more readers, `r ≤ e−1`. Both cases give
`rank(H) ≤ 3e−1` for `e>0`. The module estimates rank over fields of orders 2 and 101.
A nonzero minor in either field is a nonzero integer minor, so the estimate is a safe
lower bound on rational rank. The rank computation is polynomial in the size of the
listed certificate matrix.

### Ordered decomposition and an exact example

For every candidate reader-count sequence, encode Boolean edge memberships, with vertex
membership their OR. In a cell let `z_i` indicate that both certificates reach repeated
wire `i`, and `c_i` count its common incoming reads. Enforce `Σ(z_i−c_i)=H`. At any
topological prefix the common intersection graph is a forest with no branching toward
the inputs. Its number of components is `1+Σ(z_i−c_i)` over repeated wires in the prefix.
Each component has at most one edge to the next wire. Therefore

```text
c_i ≤ 1 + Σ_{j<i}(z_j−c_j).
```

The solver encodes both conditions by cardinality clauses. The prefix condition is
strictly stronger than the unordered Boolean factorization even among rank-five matrices
at excess two. The regression suite contains such a matrix. In the relaxation, duplicate
or zero rows and columns can be omitted, since any solution extends by cloning the
duplicate choices or giving a zero row or column empty memberships.

An identity submatrix of order five gives a direct excess-three lower bound. At excess
two the single degree-three case has rank at most four. In the two-binary-wire case,
the first wire gives up to two positive rectangles, and the second gives up to two
positive rectangles and one negative rectangle. The first is nonnegative, and the
second's negative rectangle is disjoint from its own positive rectangles. A second-wire
positive rectangle therefore contains at most one identity diagonal entry. If a
first-wire positive rectangle contained two diagonal entries, both intervening off-diagonal
cells would have to lie in the second-wire negative rectangle. That would also cancel
the two diagonals. Thus at most four identity diagonal entries can be covered.

Take the OR of a guarded three-input majority and a guarded five-vertex path on disjoint
inputs, with one guard variable per component. The majority block supplies an identity
of order three, and the path block supplies two independent singleton entries. The
opposite guard supplies zero entries for each block in the combined matrix, yielding
an identity of order five. Its full matrix has rank five and maximum entry one. With
ten essential inputs, the obstruction gives 12 gates. A five-gate guarded majority,
six-gate guarded path, and final OR attain this, checked on all 1,024 rows. The simpler
guarded majority alone has five gates, already certified by the sharpened rank bound.

### Region coloring and terminal certificates

Cut at each repeated wire and regard its reads as separate terminal occurrences. Every
region is a read-once tree. A positive and a negative certificate can share at most one
terminal in any region, since a common local gate has only one outgoing common edge.
Join two essential inputs in a graph if they co-occur in some minterm and also co-occur
in some minimal zero certificate. Their assigned input regions must differ. Thus the
graph needs at most `r+1` colors and `B ≥ m+χ−2`. The inexpensive implementation uses
greedy cliques and bipartiteness, which give certified lower bounds on `χ`. All internal
thresholds have a complete coexistence graph, so this gives `2m−2` gates and at least
`m−1` repeated wires. Classical threshold-specific bounds can be stronger.
[Bloniarz's threshold-circuit thesis](https://bitsavers.computerhistory.org/pdf/mit/lcs/tr/MIT-LCS-TR-0238.pdf) ·
[Sergeev's threshold-circuit results](https://doi.org/10.4213/dm1547)

For a stronger matrix relaxation, assign each reader slot a fixed earlier owner region
in the same topological order. A selected port implies the owner root is present in that
certificate. Within that region, two selected positive ports have an AND lowest common
ancestor, while two selected negative ports have an OR ancestor. Encode these choices by
the cograph of AND ancestors, using a single cograph on all slots whose induced graphs
give the separate regions. Disjoint union shows that this introduces no restrictions
between different regions. The pair constraints in particular prevent two common ports
from leaving a single owner. This relaxation still has no input-variable assignments.

The complete-function version adds each primary input as one terminal with a static
region assignment, and its membership in each certificate is fixed by `S` or `T`. Require
every region to have a terminal. A visited positive region must select a maximal clique
of its local cograph, and a visited negative region a maximal independent set. The encoding
already constrains the selected set to be a clique or independent set. Its blocker clauses
require a maximal set of the same kind contained in the selected ones, which forces that
set to equal the selected terminals. Structural certificates of a read-once regional
formula have this maximality, even if port values are correlated in the full circuit.

These complete-terminal constraints give an exact encoding. Decode the region formulas
by cotrees and connect each slot to its repeated-wire root. On a listed certificate row,
the selected primaries have the required sign. Each selected port visits its provider
in the same certificate and the topological order permits evaluation from the inputs.
The selected terminals force each visited region to the required value, including the
output. The full minterm and zero-certificate rows determine a complete monotone function.
With `q` slots the construction uses `Σ(leaves−1)=m+q−(r+1)=m+e−1` gates or fewer if
aliases are simplified. The circuit-to-encoding direction follows by cutting an actual
circuit and taking its local certificates. Unlike the matrix relaxation, the complete
encoding retains every listed row and column, including equal matrix rows with distinct
primary memberships. When transposing two inputs preserves the minterm family, their
owner indices can be ordered by symmetry. Such transpositions generate permutations
within each exchangeable class, so the restriction keeps one representative of every
circuit orbit. The known read-once characterization and cotree theory are part of
the prior literature. Priority for the rank and ordered-decomposition arguments remains
unverified. [Read-once characterization and co-occurrence graphs](https://doi.org/10.1016/j.dam.2008.02.011)

### Corpus comparison and checked endpoints

The replay examined all 90 complete targets in the frozen corpus. Rank plus the one-sharing
support test improved the pointwise bound on 39, and the ordered matrix decomposition
raised 23 further bounds at excess two. The coloring bound exceeded the rank stage
on 26. Taking the best of these bounds exceeded 14 archived lower endpoints. These are
comparisons against recorded evidence. For example, the Petersen rank bound is 13 versus
an archived endpoint of 11. Re-running the existing graph analysis without its original
half-second job cap gave 15. A more useful non-graph example is `comparator-05`, where the
coloring bound is 14 versus 10 in the archive and 11 from the rank stage. The replay
checks each bound against its verified construction upper bound.

On the two unresolved five-input thresholds, the matrix relaxation admitted excess four,
corresponding to eight gates. The complete-terminal encoding excluded nine gates for both.
Their coexistence graphs are complete, requiring at least four repeated wires on five
inputs. At most five units of excess leave six ordered reader-count patterns. Glucose
produced traces for all six per function, and an independent reverse-unit-propagation
checker accepted all of them. At ten gates both instances decoded valid regional circuits,
verified against every target label. The new results leave the archived sweep files intact.

| Target | Archived interval | Checked budget exclusion | Trace additions | Verified minimum |
| --- | ---: | ---: | ---: | ---: |
| `complete-5` | [8, 10] | 9 | 2,383 | **10** |
| `threshold-5-3` | [8, 12] | 9 | 1,617 | **10** |

Write `p = a OR b`, `q = c OR d`, and `w = (a AND b) OR (c AND d)`. The 2-of-5
construction is `w OR Majority(p,q,e)`. The 3-of-5 construction is
`Majority(w,p AND q,e)`. Use four binary gates for each three-input majority. Both
constructions use ten gates and were independently checked on all 32 assignments.
For 2-of-5, the classical separate gate-type bounds already imply six OR gates and
three AND gates, hence at least nine gates. The checked exclusion advances that lower
bound by one. The archived `complete-5` construction also used ten gates.
[Classical threshold-two gate-type bounds](https://bitsavers.computerhistory.org/pdf/mit/lcs/tr/MIT-LCS-TR-0238.pdf)

The checks exercise the ordered inequality against 899 full-certificate pairs from
360 generated output cones, including 229 with sharing. They verify a separate
matrix-decomposition UNSAT trace for the five-cycle at six gates and decode exact
terminal witnesses at the known minima of the four-cycle, four-vertex path, and five-cycle.
The simple rank and coloring rules belong at the graph root. The optional graph CLI
also tries the topology relaxation for budgets within excess three, with a cap and
ordinary circuit search on an inconclusive result.

## Lazy regional certificate compatibility

The `lazy-certificates` backend of `complete_status` keeps terminal owners, visits, and
certificate memberships in SAT. It constructs no cograph variables, induced-path clauses,
or maximality blockers. The complete-terminal backend remains the reference. This section
uses the full minterm and minimal zero-certificate families at the circuit boundary.

### Local compatibility and reconstruction

Build an AND-requirement graph by joining each pair in a selected positive certificate.
Build the OR-requirement graph from negative certificates. An OR root must keep each
AND component intact, and an AND root must keep each OR component intact. If either graph
disconnects, split into all its components with the opposite operation. If a compatible
tree exists, restricting it to each component preserves every remaining lowest-common-
ancestor requirement. Therefore the first available split may be used without backtracking.
On a nonsingleton subset with both graphs connected, a compatible tree is impossible.
For `ℓ` leaves and `R` certificates, direct adjacency construction and recursive component
tests take `O(Rℓ² + ℓ³)` time. This is the cograph sandwich problem on the required AND
edges and forbidden OR edges. [Golumbic, Kaplan, and Shamir](https://doi.org/10.1006/jagm.1995.1047)

If every positive certificate meets every negative certificate, the compatible tree
can be pruned to satisfy the obligations. At an OR, every positive certificate is confined
to one child. Retain those children and pass every negative certificate to each retained
child by intersection with its leaves. Each restriction is nonempty and still meets all
local positives. Apply the dual rule at AND. For a single polarity, OR or AND the union
of the selected leaves, and use any leaf when there are no obligations. A join with just
one retained child becomes that child. The resulting formula has no more leaves than
the original regional tree. This extension uses the at-most interpretation of the gate
budget. It can remove designated terminals or reader occurrences. The decoder trims
unreachable regions. The experiment harness checks each decoded circuit against all
target labels.

### Spanning-tree clauses and local intersection constraints

The SAT literal for a local membership is the conjunction of certificate selection and
terminal ownership. For a fixed primary membership it is simply its ownership literal.
Selection of a terminal implies that the owning region is visited, and each visited
region selects at least one terminal. On a rejected model, take a spanning tree from each
requirement graph in the obstructed subset. Each edge has one certificate row as its
witness. The learned clause negates the corresponding local membership literals. It
has at most `4(ℓ−1)` literals on an `ℓ`-leaf subset, often fewer after deduplication.
An independent union-find check validates the witnessed spans before adding the clause
to SAT. A conflicting pair gives the two-leaf special case. For proof runs, a fresh solver
replays each final UNSAT clause set and a separate checker verifies its DRUP trace.

An initial version kept the global certificate-intersection matrix equality and prefix
inequalities. In a positive–negative pair, let `C` count commonly visited regions including
the output, `D` common port reads, and `I` common primary inputs. The matrix equality gives
`C = D + I`. Every common terminal is owned by a common region, and compatibility permits
at most one common terminal per region. Thus each commonly visited region has exactly
one common terminal. This proves cross-intersection for each visited local pair without a
separate family of clauses.

The faster tested version uses `local_intersection=True`. It directly requires exactly
one common terminal in each commonly visited region. The clause for at least one is
guarded by the two visits. The at-most-one constraint can be unconditional because a
common terminal already implies both visits. The encoding reuses the common-read literals
and uses an ownership literal directly for a primary input in both certificates. These
local constraints enforce cross-intersection and imply the matrix equality by summation,
so this variant omits both the matrix counters and prefix inequalities. The usual rank and
coloring bounds still filter the reader-count patterns. Co-occurrence compatibility is
checked lazily in both variants.

Every actual circuit supplies a model using its structural certificates. For the reverse
direction, use the reconstructed formulas in the acyclic region order. Each selected
port visits its provider, which computes the required polarity by induction. The root
then meets every full certificate, determining the target. Removing terminals only
decreases the total `Σ(ℓ_r−1)` budget. The solver skips undecided patterns only after
reporting an inconclusive overall result if it has no SAT witness.

The local comparison agreed with all enumerated cographs on 1,800 seeded queries over
four, five, and six leaves. There were 113 compatible, cross-intersecting queries and all
reconstructed correctly, dropping unused leaves in this sample. An additional 300 full
read-once certificate families reconstructed their whole truth tables without dropping a
leaf. The five-leaf pinwheel gives a failure even when every opposite pair intersects
once. The SAT regression learns its witnessed spanning-tree clause and checks the final
UNSAT trace.

### Matched comparison and frontier replay

The serial comparison used eight identical budgets for each backend, a six-second hard
wall cap per worker, and the same requested conflict allowance of 1,500 per reader-count
pattern. The conflict limit is cumulative across incremental lazy solves for a pattern.
Glucose can overrun its requested conflict allowance, so the subprocess cap is the hard
limit. These timings exclude process launch and proof replay for completed jobs.
The timed section starts after certificate extraction and includes witness validation.

| Backend | Completed | UNSAT | SAT | Initial clauses across all eight jobs | Summed encoding and solving seconds |
| --- | ---: | ---: | ---: | ---: | ---: |
| Complete-terminal reference | 8 | 4 | 4 | 1,247,039 | 1.440 |
| Lazy certificates with matrix constraints | 2 | 1 | 1 | — | — |
| Lazy certificates with local intersections | 8 | 4 | 4 | 359,432 | 0.323 |

The matrix-based lazy variant returned four inconclusive results and hit the wall cap
twice. The local-intersection variant matched the reference verdict and ran faster on
each of the eight jobs, with about 71% fewer initial clauses in aggregate. Most exclusions
in this sample were resolved by the initial local-intersection constraints. At the
eight-gate `hypergraph-21` budget, the solver examined five candidate models and added
four spanning-tree clauses before returning a verified witness. The nine-gate
`comparator-02` witness also required two learned clauses. These are small matched runs.
They measure the combined effect of the local intersection encoding and lazy compatibility.

Fresh proof replay on the local-intersection encoding reproduced the nine-gate exclusions
for `complete-5` and `threshold-5-3`, checking 846 and 390 DRUP additions respectively.
The frontier replay used the same six-second cap with proof checking. Follow-up probes at
the next budgets had an eight-second wall cap. The corpus gained five exact minima.

| Target | Archived interval | Verified minimum | Lower evidence |
| --- | ---: | ---: | --- |
| `hypergraph-03` | [8, 15] | **9** | Co-occurrence clique on inputs `0,1,2,3,5` |
| `hypergraph-12` | [7, 11] | **8** | Checked seven-gate exclusion |
| `hypergraph-21` | [7, 12] | **8** | Co-occurrence clique on all five inputs |
| `comparator-02` | [7, 17] | **9** | Checked eight-gate exclusion |
| `comparator-04` | [9, 28] | **12** | Checked eleven-gate exclusion |

| Target | Archived interval | Latest interval | Highest checked exclusion |
| --- | ---: | ---: | ---: |
| `hypergraph-04` | [9, 21] | [12, 21] | 11 |
| `hypergraph-09` | [9, 21] | [11, 21] | 10 |
| `hypergraph-10` | [10, 21] | [12, 21] | 11 |
| `threshold-6-4` | [8, 17] | [12, 17] | 11 |
| `random-monotone-05` | [10, 23] | [13, 23] | 12 |

Each of these five open next budgets reached the eight-second cap. The raw frozen sweep
records remain available for comparison. The two module-level backends share the same
budget enumeration and trusted rank and coloring filters.

## Reproduction

```powershell
python sat-search/experiments/audit_synthesis.py --baseline sat-search/results/synthesis_ablation.jsonl --manifest sat-search/results/synthesis_cases.json
python sat-search/experiments/synthesis_followup.py --baseline sat-search/results/synthesis_ablation.jsonl --manifest sat-search/results/synthesis_cases.json --output fresh-endpoints.jsonl --seconds 1 --rounds 2 --workers 6
python sat-search/experiments/certify_synthesis.py --verify-packet sat-search/results/synthesis_proofs/hypergraph-07-b6.json --manifest sat-search/results/synthesis_cases.json
python sat-search/experiments/nonmonotone_bench.py --manifest fresh-signed-cases.json --output fresh-signed.jsonl
python sat-search/experiments/synthesis_followup_check.py -v
python sat-search/experiments/twocolor_completion_check.py -v
python sat-search/experiments/twocolor_completion_check.py --profile
python sat-search/experiments/label_formulas_check.py -v
python sat-search/experiments/label_formulas_check.py --profile
python sat-search/experiments/cograph_formulas_check.py -v
python sat-search/experiments/cograph_formulas_check.py --profile
python sat-search/experiments/cograph_formulas_check.py --frontier-profile
python sat-search/experiments/cograph_formulas_check.py --certify-frontier
python sat-search/experiments/distinction_rectangles_check.py -v
python sat-search/experiments/distinction_circuits_check.py -v
python sat-search/experiments/certificate_rank_check.py -v
python sat-search/experiments/certificate_rank_check.py --profile
python sat-search/experiments/certificate_rank_check.py --endpoint complete-5 9 --proof
python sat-search/experiments/certificate_rank_check.py --endpoint threshold-5-3 9 --proof
python sat-search/experiments/lazy_certificates_check.py -v
python sat-search/experiments/lazy_certificates_check.py --compare --seconds 6 --conflicts 1500
python sat-search/experiments/lazy_certificates_check.py --frontier --seconds 6 --rounds 2 --proof
python sat-search/experiments/lazy_certificates_check.py --job hypergraph-12 7 lazy-local-intersection --proof
python sat-search/experiments/lazy_certificates_check.py --job comparator-04 12 lazy-local-intersection --proof
```

## Quick-reference summary

Moved word for word from the root RESEARCH_NOTES.md on November 27, 2026.

| Topic | Result |
| --- | --- |
| Sharing parameter | Partial monotone synthesis is NP-hard already at zero sharing with every input mandatory and the exact hitting number supplied. The opt-in two-coloring shortcut applied to 121 of 20,439 output-formula query calls in 316 completed benchmark jobs. [Proof and reproduction](NOTES_SYNTHESIS_FOLLOWUP.md#hardness-at-zero-sharing) |
| Formula obligations | Typed subtree cuts excluded 929 further output queries on the 316-job replay. Exact obligation search matched exhaustive formula enumeration on 900 partial tables. The replay established no end-to-end speedup. [Proof and measurements](NOTES_SYNTHESIS_FOLLOWUP.md#operation-aware-formula-obligations) |
| Regional SAT | A cograph encodes each read-once region with consistent symbolic ports. Joint SAT recovered the five-cycle's seven-gate minimum in 12 port patterns. A proof checker verified every pattern for the six-gate exclusions on the five-cycle and `hypergraph-07`. [Encoding and measurements](NOTES_SYNTHESIS_FOLLOWUP.md#cograph-sat-encoding-for-linked-regions) |
| Rectangular distinctions | For `δ = positives × negatives − κ`, the support bound is exact through `δ=3`. A six-label example at `δ=4` needs an extra gate. [Proofs and known answers](NOTES_SYNTHESIS_FOLLOWUP.md#distinction-rectangles-and-the-first-sharing-obstruction) |
| Circuit synthesis in `δ` | Certificate intersection, request matching, and bounded extra input choices give exact synthesis with overlapping distinctions and arbitrary monotone sharing in `2^O((δ+1)^4 log(δ+2)) · poly(M,R)` time. A reduction from below-universe Set Cover gives a conditional barrier to polynomial kernels. [Proof, scope, and checks](NOTES_SYNTHESIS_FOLLOWUP.md#certificate-reduction-for-overlapping-circuit-distinctions) |
| Certificate intersections | Rank, ordered decomposition, and coexistence coloring give sharing lower bounds on complete functions. The exact terminal encoding closed `complete-5` and `threshold-5-3` at **10 gates each** with checked nine-gate exclusions. [Proofs and reproduction](NOTES_SYNTHESIS_FOLLOWUP.md#certificate-intersection-rank-and-regional-decomposition) |
| Lazy certificates | Local intersection constraints and checked spanning-tree clauses gave an exact at-most backend without cograph variables. It matched all eight reference jobs at 0.323 s versus 1.440 s in the serial sample and established five additional non-graph minima. [Proofs and matched comparison](NOTES_SYNTHESIS_FOLLOWUP.md#lazy-regional-certificate-compatibility) |
