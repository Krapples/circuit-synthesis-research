# L-meta-1343: how we might actually solve it (notes, 2026-11-23)

**Claim.** The 11-vertex graph G (no 4-cycle, 16 edges, cover number 7) needs at least 22 gates in any
fan-in-two AND/OR (monotone) circuit for its edge function, i.e. edges + cover − 1 survives here.

**Where we stand.**
- Shard 2 (first three gates x6∨x9, x7∨x10, their AND): no circuit genuinely using the seed with ≤ 16 gates
  (sizes 4–13 old encoding, 14–16 with `cube_search --fast`); size 17 running.
- Analytical lower bound (no SAT) for this function: 14 binary gates (recursive + closure + colouring +
  connection bounds). Target: 22. Gap: 8.
- Search cost grows ~10× per size (5 s, 54 s, …), so brute force to 21 needs either far stronger bounds or a
  different strategy.

## Why our bounds stall at 14 here

Every bound we have is a **general-circuit** bound (NOT gates free). For this graph general circuits may truly
be smaller than monotone ones; the desk's whole point is that the AND count can drop below the cover number.
Our rules never use monotonicity of the *circuit*, only of the *target*. So the honest ceiling of the current
engine is the general-circuit complexity, which can sit well below 22.

## Strategy 1 — monotone-specific lower bounds (most promising)

In a monotone circuit every gate computes a monotone function, and no information can be "cancelled":
- **Monotone gate elimination is stronger.** Fixing x = 0 makes every AND reading x constant 0 *and* every
  OR reading x a copy; fixing x = 1 the reverse. Both remove all readers, but monotone restrictions also
  preserve monotonicity, so the restricted bound can recurse on **monotone** complexity, not general.
- **Sunflower / implicant counting.** Each output prime implicant (an edge uv) must be produced by some AND
  gate whose two inputs carry u and v; in a monotone circuit an AND gate's implicants are products of its
  inputs' implicants. Counting which AND gates can "first create" each edge gives a lower bound on AND gates
  per vertex neighbourhood. The cover-number term (τ − 1) is exactly the OR gates needed to join AND
  products whose supports are disjoint.
- **Known exact technique:** for monotone circuits computing graph functions, the "replacement" argument
  (Schnorr, Wegener) shows certain OR gates can be pushed to the top; combined with a vertex-cover argument
  this is the published route to E + τ − 1 on special graph classes. Our desk's missing lemma is the step at
  a degree-3 vertex.

Concretely: build a **monotone recursive bound** M(f) that recurses on monotone restrictions and adds
monotone-only charges (an OR reading x vanishes under x = 0, an AND under x = 1, and *both* kinds of reader
must exist unless x's neighbourhood is special). If M reaches 22 for this graph, the step is proved
analytically, and we could even turn the recursion into a Lean proof (finite, decidable case analysis).

## Strategy 2 — use SAT to discover the missing lemma

Instead of one giant search, ask small, local questions on many small graphs:
"in every minimal monotone circuit, does fixing a degree-3 vertex v to 0 remove at least
deg(v) + τ(G) − τ(G−v) gates?" Our `--elim` encoding already counts eliminated gates; adding
`eliminated ≤ k − 1` and checking UNSAT across the range-2 graph list would show which local "paying step"
always holds. A pattern that holds on all small graphs is a candidate lemma; that lemma is what the desk
actually needs (it is listed as the open step), and it is far more valuable than one more exhausted shard.

## Strategy 3 — make the remaining sizes cheap

If we still want 17–21 by search:
- **Monotone mode in the encoder:** drop all NOT machinery (parity, NOT bounds, signed-dominator's N_g are
  all trivial), use one-directional certificate rows (edges must be certified 1, maximal independent sets 0),
  ~55% fewer row clauses.
- **Reuse solvers across pieces:** each piece currently builds a fresh solver; with 338 pieces per size, a
  persistent solver per worker fed by assumptions keeps learned clauses (we did this in `mono_shard.py`).
- **Reject pieces analytically per piece with two fixed gates** (seed + piece gate): the cube bound only uses
  the first gate today.
- **Adaptive splitting only for stragglers** (static splitting hurt ~25×, but splitting the last few slow
  pieces with a conflict budget does not have that problem).

## Rule improvements to try next (ranked)

1. `--monotone` encoder mode (certificate rows, no NOT variables at all) — cheap, large constant factor.
2. Monotone recursive bounds M(f) as above, used for piece rejection and NOT-free budgets.
3. Persistent per-worker solvers in `cube_search.py` (assumption-based pieces).
4. Two-gate cube bounds (first gate + next gate) for shard searches.
5. Restricted colouring (`--restrictedcolor`, from the last review) and pair restrictions on the first
   gate's operands.
6. Exact fan-out multiplicities (`--exactfanout`).
7. v16 rules (active/zero/isolated colour, connection bounds): implemented, quick-checked, hard-piece test
   pending.

## Update (later the same day)

- **Multi-gate bound (implemented):** the seed's two ORs x6|x9 and x7|x10 force inputs 6, 7, 9, 10 to be read
  again, so any circuit starting with them needs >= 16 gates analytically; shard-2 pieces get 16–18.
- **Monotone ports (implemented, `--monoports`):** Sperner antichain and chain bounds on region ports. Sound,
  but no change for this graph (whole bound stays 14).
- **Typed AND/OR bounds (implemented, `typed` flag in monotone mode):** #AND >= log2(#maximal independent
  sets) = 5, #OR >= log2(#edges) = 4 here.
- **Where 22 comes from:** C4-free means every AND of two ORs is a star or makes a non-edge. The star
  construction costs |E| - k (neighbourhood ORs) + k (ANDs) + k - 1 (final ORs) = |E| + k - 1 with k >= tau,
  i.e. 9 + 7 + 6 = 22 here. Multi-level ANDs (Jukna 2006: single-level conjecture fails in general) are the
  only way to beat it.
- **Filtering lemma:** a wire that is 1 on a false row must meet, on every path to the output, an AND whose
  other operand is 0 there. The seed (x6|x9)(x7|x10) is a K2,2, so it always creates a non-edge that must be
  filtered; counting the filters is the promising handle on shard 2.
- **Critical seed edges:** cut the seed, call the edges that then fail E_s; replacing the seed by the OR of
  E_s is valid, so a globally minimum circuit cannot use the seed when |E_s| <= 2 adjacent (cheaper
  replacement), unless its ORs are shared elsewhere. Gives a case split by E_s.
- **Private-neighbourhood paying lemma (proved case):** if x_v has a unique reader g = x_v AND h and h's cone
  is private to g, then setting v = 0 removes >= d(v) - 1 ORs + g + a reader of g, i.e. >= d(v) + 1 gates.
  The open case is a shared neighbourhood aggregate; C4-freeness limits such sharing to one common neighbour.
- **Still to build:** monotone certificate encoder (needs sensitivity rules rewritten for certificates),
  typed AND/OR restriction frontiers, and a dead-code-aware elimination test of the degree-3 paying step.

## Monotone theory: filtering and shared neighbourhoods (worked out)

**Setting.** G is C4-free, f = OR of x_u x_v over edges, C a monotone fan-in-2 circuit with every wire used.
Star cost of an edge set F: s(F) = |F| + tau(F) - 1 (the single-level optimum for C4-free F).

**Fact 1 (what one AND of two ORs can do).** If g = (OR of A) AND (OR of B) with A, B disjoint vertex sets,
g's implicants are the |A||B| pairs of the biclique A x B. G has no 4-cycle, so G contains no K2,2: when
|A|, |B| >= 2, at least one pair of A x B is a non-edge. That non-edge is a false row on which g = 1.

**Fact 2 (filtering lemma, proved).** If a wire is 1 on a false row z, then every path from it to the output
contains an AND gate whose other operand is 0 on z (otherwise the 1 propagates to the output). So every
non-star biclique costs at least one filtering AND somewhere downstream.

**Worked example: the shard-2 seed.** (x6|x9) AND (x7|x10) covers the edges 6-7, 6-10, 7-9 (a P4) and the
non-edge 9-10. Cost: 2 ORs + 1 AND + >= 1 filter = 4 gates. The star cost of that P4 is
s = 3 edges + tau 2 - 1 = 4 gates. Counting one downstream filter brings the local seed calculation
to the star cost of these three edges. A global lower bound still requires accounting for which
edges the seed transmits and which filters it shares with the rest of the circuit.

**Conjectured accounting lemma.** For every AND gate g in a minimum monotone circuit for a C4-free graph,
(ORs feeding only g) + 1 + (filters g forces) >= s(edges g is the first to create). Summing over AND gates
(each edge is created first by exactly one AND gate) plus the final ORs (>= #AND - 1) would give
size >= |E| + tau - 1. The private-neighbourhood case (one star centre, no filter needed) is the proved case
above; the seed shows the bookkeeping balancing exactly in the smallest non-star case.

**What remains to make it a proof.**
1. A filter gate can serve several non-edges at once; the lemma must charge each filter to one AND gate
   (e.g. the topologically first gate whose non-edge it kills) so that nothing is double-counted.
2. OR gates shared between several AND gates' inputs must be charged once; C4-freeness bounds sharing: two
   star centres share at most one neighbour, so a shared OR aggregate of >= 2 vertices always creates a
   non-edge for one of its users (Fact 1) and therefore triggers Fact 2.
3. Induct on AND gates in topological order with these charges; the degree-3 paying step of L-meta-519 is
   the special case where the AND gate is the first to create the edges at a degree-3 vertex.
4. An edge may be created by several gates. Selecting its earliest creator assigns it uniquely, but the
   selected gate's value may be blocked before reaching the output on that edge row. An accounting proof
   needs to track transmission as well as creation and charge shared filtering and transmission only once.

**Computational check that is now cheap (proposed).** With `cube_search` monotone mode (nonot) plus the
analytical bounds, scan every C4-free graph up to ~9 vertices for a monotone circuit of size |E| + tau - 2
(one below the star cost). A witness anywhere would refute the accounting lemma (and show exactly how);
no witness supports it and gives test cases for the charging argument.

## Fixed-prefix suffix reads (2026-11-24)

For a fixed prefix, evaluate its wires on every edge row and maximal independent-set row. For each
opposite-output pair, the suffix must read a prefix wire whose values differ. A monotone suffix needs
a wire that is 1 on the edge row and 0 on the independent-set row. If it read only wires whose values
were ordered the other way, the suffix output would inherit that order.

In the all-wires-used encoding, every frontier wire with no reader inside the prefix must have a reader
in the suffix. Disjoint sets of distinguishing wires that miss these mandatory wires each require an
additional distinct read. A suffix with B binary gates has at most B + 1 operand slots for distinct
frontier wires because every non-output suffix gate must itself be read there. Together these give a
binary-gate lower bound. `--frontier` also encodes each remaining separation requirement directly in SAT.
When a solver is reused, the clause is conditional on the cube and pinned piece used to derive it.

On the 338 size-18 shard pieces, the frontier bound alone ranges from 14 to 16 binary gates. It leaves
all of those pieces open by itself. This is a limit of the distinct-read count even when the fixed
prefix values are known. Stronger partial-function bounds would need to charge for how the suffix
combines those values.

In one eight-worker comparison at size 16, both configurations proved all 338 pieces UNSAT. Each
rejected 230 pieces analytically. With persistent solvers in both runs, frontier clauses reduced
conflicts from 1.71 million to 1.63 million and wall time from 39.6 s to 35.5 s.

In a separate one-worker comparison covering all 36 first-gate cubes of the six-cycle at size nine,
the general-circuit search took 105.8 s with fresh unit-cube solvers and 7.3 s with assumption-based
reuse. Both returned 10 satisfiable cubes, and every witness passed full truth-table verification.
Repeating the comparison after the cache corrections, with the configuration order reversed, gave
127.1 s fresh and 8.2 s reused. The repeat matched every cube verdict and both conflict totals
(2,147,302 fresh and 128,206 reused).

## Partial ordered bound (2026-11-24)

For each possible suffix-input set, retain every feature with no prefix reader and every feature that
is the sole directional distinction for some opposite-output pair. Project the boundary rows and discard
any projection with a positive row below a negative row. Close the remaining projections upward from
positives and downward from negatives. This labels 6,992 of 8,192 patterns for the two-OR prefix and
13,709 of 16,384 for the full three-gate prefix.
When the two closures are disjoint, setting every remaining entry to zero or setting every remaining
entry to one gives two valid monotone completions. The closure therefore captures all labels forced
by monotonicity alone.

Cutting the suffix at repeated wires gives terminal regions. The features in a region with more than
one feature occur once in its local tree, and their influence passes through the same terminal. If
fixing outside features leaves both members of a pair essential, their restricted function is AND
or OR according to their fixed lowest common ancestor in that tree. A pair with both types of
restriction in the closed partial table cannot share a group.

An opposite-output pair with all its directional distinctions in a group also forces opposite values
at that group's terminal. Taking every positive and negative forced this way, the terminal must be
able to distinguish every cross pair using features from its own group or earlier groups. The ordered
partition search uses these constraints and minimizes the number of nonempty groups. If the suffix
uses m features and has k nonempty groups, its binary size is at least m + k − 2 because each repeated
wire contributes at least one excess read and there are at most one plus the number of repeated
wires in total regions. The bound adds the fixed prefix size and takes the minimum across projections.

| Fixed prefix | Suffix inputs | Ordered groups | Total binary lower bound |
| --- | ---: | ---: | ---: |
| Two seed ORs | 13 | 5 | 18 |
| Three-gate seed, neither OR read in the suffix | 12 | 6 | 19 |
| Three-gate seed, either one OR read in the suffix | 13 | 5 | 19 |
| Three-gate seed, both ORs read in the suffix | 14 | 5 | 20 |

All 11 primary inputs are mandatory in every projection. The bound of 19 for the 12-input projection
was cross-checked with a separate explicit closure and partition enumerator. The normal shard task
path rejects all 182 case-a size-18 pieces using the three-gate prefix and all 156 case-b pieces using
the two-OR prefix, whose actual size budget is 17. This extends the shard exclusion through size 18.
The test at `experiments/partial_ordered_check.py` reproduces the calculation without appending results.

## Partial-domain forced repeats (2026-11-24)

In a viable suffix-input projection, take an opposite-output pair whose only directional distinction is
feature x. If the first suffix gate reads x and loses that distinction, x needs another suffix reader.
Without one, all signals seen by the rest of the suffix would be ordered in the wrong direction.
This applies to derived wires as well as original inputs. A candidate gate is evaluated only on
projections containing both of its operands.

Each forced repeat is a dependency-free singleton terminal. Move those terminals to the beginning of the
region order. If their set is H, the remaining partition takes at least K(H) groups, so the suffix needs at
least m + |H| + K(H) − 2 binary gates for m used features. `--partialrepeat` caches K per projection and
queries it for each next gate. It takes the minimum across viable projections and applies the rule at
each step of the contiguous pinned prefix. `--partialordered` can also bound the suffix after the gate.

On the 12-feature projection, the 132 next gates give bounds 19, 20, and 21 in 74, 53, and 5 cases.
The forced-repeat counts for zero, one, and two operands are 5, 18, and 109. One projected partition
search handled all 132 gates, visiting 3,717 distinct states.

Across all viable projections, the forced-repeat rule alone gives the following size-19 audit.

| Shard case | Next gates | Actual size budget | Rejected | Remaining after this rule |
| --- | ---: | ---: | ---: | ---: |
| A, seed AND used | 182 | 19 | 78 | 104 |
| B, seed AND dropped | 156 | 18 | 84 | 72 |

Running the existing ordered bound on the extended prefixes excludes 89 more case-A pieces and
64 more case-B pieces. Together the two bounds exclude 315 of 338 pieces without SAT. The remaining
15 case-A pieces and 8 case-B pieces all pin an OR as the next gate. Size 19 remains open for the shard.

For example, case A with next gate x0 OR x2 remains at bound 19. With that gate pinned too,
the rule excludes 166 of the 208 next gates allowed by the operand ordering. The bounds are
19, 20, and 21 for 42, 107, and 59 choices, respectively.

Two further refinements have a mathematical formulation. For common read-once branching, an AND root
requires the prescribed-OR graph to be disconnected, and an OR root requires the prescribed-AND graph
to be disconnected. Recursing on the corresponding components is sufficient because a valid tree
restricts to each component and the component roots can be joined by the chosen operation. For a
terminal with forced positive and negative values, use one graph vertex per required separation and
join separations that cannot share a monotone signal. Each color class is realized by the upward
closure of its positive endpoints. This gives an exact port count when incoming signals and the local
combining function may be arbitrary monotone functions. That model relaxes the requirement to construct
those signals with the actual earlier regions.

## Reader multiplicity and coupled projections (2026-11-24)

Fix a viable set of m inputs for the suffix and a block of its initial gates. Count the direct
readers of every wire in the block. For an original suffix input x, a positive-negative row pair
whose only directional distinction is x forces one further reader if no pinned output preserves
the distinction. Let the resulting reader lower bounds be ℓ. Each original input with ℓ ≥ 2 is a
singleton terminal in H. Each unit of ℓ beyond two is additional excess fan-out, including on
pinned internal wires.

An internal wire with ℓ ≥ 2 is a repeated terminal. Cut its private cone at all other wires known
to repeat. If no suffix input remains in the cone, its region is empty. If t such regions are forced,
the excess fan-out identity gives the suffix bound m + |H| + K(H) − 2 + t + ∑ max(0, ℓ − 2).
The same ordered partition calculation supplies K(H).

For coupling, let V be the features used after the pinned block and A the original operands read
inside it. The original suffix-input set U must be A ∪ (V restricted to original features). This
determines U from V without a Cartesian search. Every member of V establishes another reader beyond
the pinned block, including for an internal output. For each compatible pair, take the maximum
of the reader bound on U and the pinned gate count plus the ordered bound on V. Minimize that
maximum across compatible pairs.

On the 12-feature projection with x0 OR x2 pinned, the 152 continuations whose operand pair is
strictly later in colex order reproduced the proposed result. The bound increased by one gate on
29 continuations. Counts at bounds 19, 20, and 21 went from 56 / 79 / 17 to 42 / 78 / 32.
This is a single-projection comparison.

Across all viable projections, the 23 surviving size-19 pieces retained their previous bounds
with multiplicity, empty regions, and coupling enabled. Case A stayed at 19 for all 15 pieces and
case B at 18 for all eight. The regression audit used analytical bounds and launched no SAT search.

## Terminal merging and regional synthesis (2026-11-24)

If a wire has exactly one reader in the pinned block and is absent from the after-projection, that
reader is its unique successor. Both wires have the same first repeated terminal or output. Following
these known successors gives blocks of original inputs that a partition must keep together. When a
block ends at a known repeated internal terminal, its ancestry is fixed and the inputs reaching it
through unique-reader paths give its entire group. A repeated terminal reached by no such input has
an empty group. A fixed terminal upstream of another block precedes that block's terminal. This
argument uses only the reader relation and also applies with NOT gates.

One incoming port occurrence is a read-once leaf. Set its value to the neutral value of its parent
gate. Passing the sibling through leaves a monotone read-once formula on all the primary inputs,
so at least one of the two cofactors depends on all of them. Thus two required nonconstant functions
that both omit primary inputs need at least two occurrences. For the path with edges 01, 03, and 12,
take the final group {0, 2, 3}. Its restrictions at x1 = 0 and x1 = 1 have supports {0, 3} and {0, 2}.
One bit of outside information suffices, and exact synthesis needs two occurrences of that bit.

The local one-port checker enumerates read-once formulas and uses forced rows to constrain the port
values of their cofactors. A candidate survives precisely when the requirements admit a monotone
port signal on the earlier features. This can be tested on partial rows since a set of required 1
contexts extends by upward closure whenever it stays disjoint from the required 0 contexts.

The regional prototype fixes ordered groups and the number of port leaves in each region. It selects
one read-once formula per region and enforces the terminal demands and output labels on the supplied
rows. The three modes successively use free row values, monotone port signals shared across earlier
contexts, and the actual outputs of earlier regions. Linked ports choose their providers once for
all rows, and each port occurrence counts against the provider's reader limit. Different occurrences
may use the same provider. This is exact for the bounded regional formula model with up to six leaves
per region. Relaxed-mode feasibility describes that relaxation, while a linked solution supplies
formulas and their wiring.

On the path above, the prototype verified a linked solution with two occurrences of x1. For the
three-input majority function, one free port can satisfy the last two inputs' region, but one
consistent port cannot. The linked prototype reproduced minima 1, 2, 3, 4, and 4 for an edge, a
three-vertex path, two disjoint edges, a triangle, and a four-vertex path. The tests enumerated the
regional decompositions at the claimed budget and one gate below it. They supplied boundary rows
and checked reconstructed circuits on every input. Direct cube search independently confirmed all
five minima. No hard shard was searched with this prototype.

## Boundary dominance and forward regional search (2026-11-24)

On labeled rows, a dominating column is at least as high on each positive row and at least as low
on each negative row. XOR with the negative-row mask turns this into inclusion of agreement bits.
AND and OR preserve the ordering in each operand. A dominated subformula can therefore be replaced
by a dominating subformula with the same labeled leaves. The replacement has the same port
occurrences and preserves correctness on the target's boundary rows. The forward enumerator keeps
one reconstructible formula per nondominated column. It applies the rule only to concrete provider
columns. The symbolic SAT encoder still enumerates formulas independently of provider assignments.

For a fixed layout, the forward search memoizes failed states at each region. A covering matching
allows one state to simulate another if matched columns dominate, the stronger state requires no
more future reads, and it permits at least as many future reads. Each distinct terminal gets its
own match. A failed stronger state therefore also rules out the weaker state. The canonical
minimum search requires at least two reads of every non-output terminal and at least two port
occurrences in an empty region. A width limit of nine leaves applies to concrete formula search.
If an unsupported layout could still affect the minimum, the search reports an inconclusive result.

The separate minimum-only usefulness mode requires each AND to see both opposing operand patterns
on negative rows and each OR to see them on positive rows. A gate that fails this test can be
replaced by one of its operands in a minimum-size argument. This mode checks actual columns and
uses equality memoization. Keeping the modes separate avoids treating usefulness as a requirement
for a fixed layout and avoids replacing a useful subformula by a different column during that test.

On a reproducible sample of 100 distinct leaf sets at each width from the L-meta-1343 primary and
seed signals, recursive pruning matched exhaustive enumeration followed by pruning in all 300 cases.
The random seed was 20261124.

| Leaves | Distinct boundary columns | Nondominated columns | Reduction |
| ---: | ---: | ---: | ---: |
| 4 | 3,713 | 1,569 | 57.7% |
| 5 | 20,226 | 3,658 | 81.9% |
| 6 | 99,964 | 7,047 | 93.0% |

Forward dominance and minimum-only usefulness both found minima of 5 for the five-vertex path,
7 for the five-cycle, and 7 for the six-vertex path. Direct cube search independently confirmed
each minimum, and all forward witnesses passed full truth-table verification.

With formula dominance enabled in both runs, state matching caught 23 additional failed visits
on the five-cycle and reduced the number of formula candidates considered from 153,130 to 153,093.
It caught no additional visits on either path. Matching increased wall time on the five-cycle and
six-vertex path in these single runs. The local compression is substantial, while state matching
has yet to show a runtime benefit on this set.

## Exact antichain search and tight frontiers (2026-11-24)

With unrestricted fan-out and an at-most gate budget, a dominated signal can be removed as a future
operand. Its producing gate may still be an ancestor of a live signal. The search stores sorted
antichains of concrete boundary columns and skips any new column already dominated by the frontier.
Failed antichains are memoized with the largest remaining budget proved impossible. Witnesses retain
the original gate history and refer to actual wire indices. The optional state dominance rule can
use one dominating wire as a substitute for several weaker wires because fan-out is unrestricted.

For each positive-negative pair, form the set of frontier columns that distinguish it. Every suffix
must hit all these sets. Removing redundant demands and finding the exact hitting number κ gives a
binary-gate lower bound of κ − 1. With b gates left and κ = b + 1, every successful suffix uses exactly
b + 1 external signals and can have no excess fan-out. The search tries read-once formulas on all
minimum hitting sets. For a larger but small allowance b + 1 − κ, the optional regional completion
enumerates viable suffix sets U and their canonical layouts with at most b − |U| + 1 units of sharing.
Unsupported formula or region widths fall back to ordinary gate search.

All three configurations excluded the budgets below. Counts are gate-search visits after memo
lookup. Formula and regional completion work is counted separately.
Before hitting-set pruning, antichains alone reduced visits from 115 to 43 for the four-vertex
path and from 2,958 to 1,092 for the five-vertex path at the listed budgets.

| Excluded budget | Hitting sets | Tight formulas | Regional completion at allowance ≤ 1 |
| --- | ---: | ---: | ---: |
| Four-vertex path, 3 gates | 9 | 1 | 1 |
| Five-vertex path, 4 gates | 16 | 1 | 1 |
| Five-cycle, 6 gates | 2,452 | 252 | 21 |
| Six-vertex path, 6 gates | 418 | 25 | 1 |
| Six-cycle, 7 gates | 6,025 | 443 | 27 |

On the six-cycle, median runtimes over three runs with caches cleared were about 169 ms for hitting
sets, 71 ms with tight formulas, and 373 ms with one-unit regional completion. Noninjective state
dominance reduced the tight search to 131 visits on the five-cycle and 256 on the six-cycle. It
increased wall time in the single runs measuring that option. The solver reconstructed seven- and
eight-gate witnesses for the five- and six-cycles, verified them on every input, and independently
matched direct cube search at both the excluded and feasible budgets.

For future typed bounds, a true certificate may keep one child of each OR and must keep both children
of each AND. If certifying one positive row against all negative rows needs κₐ distinct external
signals, at least κₐ − 1 AND gates are needed. The dual gives an OR bound from a negative row.
The prototype uses the untyped frontier bound. No hard shard was part of this experiment.

## Direct sharing completion and sharing expenditure (2026-11-24)

For a fixed external input set U with m signals and a suffix of B gates, the excess fan-out is
B − m + 1. With one unit of excess there is one repeated wire h with two readers. Its private
formula uses a nonempty subset S of U. The output is a formula over U outside S and two separate
occurrences of h. The implementation enumerates both assignments of the subset to these roles.
With two units of excess, one repeated wire can instead supply three occurrences. The other case
has two repeated wires, each with two readers.

Order the two repeated wires as h1 then h2. Their private original inputs and the output's private
inputs partition U into A, B, and C. The first formula uses A. The second uses B and q copies of h1,
where q is 0, 1, or 2. The output uses C, the remaining 2 − q copies of h1, and two copies of h2.
This covers independent and nested repeated terminals. An empty private group for h2 requires a
binary gate. The search keeps identical columns as separate leaf occurrences, shares its formula
cache across frontiers, and reconstructs the resulting gates. Larger sharing budgets can still
use general regional layouts. Widths beyond the formula cap fall back to gate search.

A column that distinguishes no positive-negative pair can be replaced by a constant in a proof
of pruning. For mixed labels, propagating that constant eliminates gates and cannot leave a
constant output. The solver does not add constant wires. Homogeneous partial labels keep the
original columns because a constant output could be required on the supplied rows.

A binary gate can decrease the hitting number by at most one. Replacing that gate in a new
minimum cover by its operands gives an old cover. If the number decreased, this old minimum
cover contains both operands, and the new gate covers every pair left uncovered by its other
members. This gives the exact test used by `--sharing-order`. Dominance preserves coverage,
and a column that distinguishes no pair contributes none. Thus a step spends either zero or
one unit of remaining sharing allowance. The optional gate order tries the zero-cost steps first.

The following counts are gate-search visits. Each row was rejected in all four modes.

| Excluded budget | Tight formulas before signal pruning | Tight with signal pruning | Direct one-sharing | Direct two-sharing |
| --- | ---: | ---: | ---: | ---: |
| Five-cycle, 6 gates | 252 | 176 | 16 | 1 |
| Six-vertex path, 6 gates | 25 | 19 | 1 | 1 |
| Six-cycle, 7 gates | 443 | 340 | 22 | 1 |

On the six-cycle, median runtimes over three runs with cleared caches were about 74 ms for tight
formulas with signal pruning, 300 ms with direct one-sharing, and 5.7 s with direct two-sharing.
In a separate matched comparison with signal pruning enabled in both modes, replacing regional
layouts with direct one-sharing changed medians from 55 to 41 ms on the five-cycle and from 354
to 289 ms on the six-cycle. Each pair visited the same gate states. Sharing order did not reduce
visits on these excluded budgets and added overhead.

## Subtree cuts before formula enumeration (2026-11-24)

For labeled leaf occurrences U and a candidate subtree S, each positive-negative pair with all
directional distinctions in S forces the subtree to be 1 on the positive row and 0 on the negative
row. If any cross pair of forced rows has no distinction in S, the subtree is impossible. The
structural DP accepts S only if it passes this test and can split into two accepted children, with
singletons as the base case. This tests tree shapes before considering any gate operations. The
exact Boolean enumeration also enforces the forced labels of every subtree it builds.

In direct sharing completion, the first private formula derives its required rows from the
original inputs outside that formula. Once h1 is known, the second private formula derives its
required rows from the output's private inputs and any copies of h1 that bypass that formula.
The output formula uses the full target labels. Copies of a signal retain distinct leaf
indices. Dominance for surviving tables uses all global labels, including rows on which a
private terminal has no forced value.

| Excluded budget | Distinct tight formula queries | Rejected before enumeration | One-sharing median, cuts off → on | Two-sharing median, cuts off → on |
| --- | ---: | ---: | ---: | ---: |
| Five-cycle, 6 gates | 21 | 21 | 41.7 → 4.6 ms | 500 → 10.9 ms |
| Six-vertex path, 6 gates | 5 | 5 | 93.2 → 2.6 ms | 92.9 → 2.6 ms |
| Six-cycle, 7 gates | 31 | 31 | 361 → 16.5 ms | 7,196 → 35.0 ms |

Timings are medians of three runs with the formula and hitting caches cleared. Each matched
comparison visited the same number of gate-search states. On the six-cycle with two-sharing,
the distinct queries reaching Boolean enumeration decreased from 16,801 to 45. The five- and
six-cycle witnesses still verify at seven and eight gates in all three completion modes.

The structural test is necessary. With five inputs, the partial positive masks
{3, 14, 20, 24, 27, 29, 30} and negative masks {4, 5, 9, 17, 18} force every input to be used.
An admissible tree exists, and exact enumeration rules out all read-once formulas.

For a general monotone DAG, suppose every path from a set S of primary inputs to the output hits
an interface H. For a pair with D(a,b) contained in S, at least one wire in H must distinguish it.
A wire whose external ancestors miss D(a,b) cannot do so. If only one interface wire has suitable
ancestors, that wire inherits the pair's forced labels. A cross pair of its forced rows with no
distinction among its ancestors then rules out the proposed topology, even if the private cone is
allowed to share internally. An unrestricted size bound would require an exhaustive argument
over the possible interfaces and their ancestor sets.

## Matching widths and provider-specific interface coloring (2026-11-24)

For an independent set S, cut the circuit at all wires whose structural ancestors lie entirely in
S and that are read outside this pure part. To separate the positive row {u,v} for a crossing edge
from the negative row {v} ∪ (S minus the neighbors of v), some pure export must distinguish the
two inputs. For a given export h, those edges form a biclique. A left endpoint u is eligible when
h({u}) is 1 and a right endpoint v is eligible when h(S minus N(v)) is 0. A missing edge between
such endpoints would contradict monotonicity. The exports therefore give a biclique cover.
Conversely, use an OR of each biclique's left endpoints as a signal and have the decoder combine
it with the OR of its right endpoints, together with the internal edges on the outside. This gives
the exact width in the relaxed model of arbitrary monotone signals and decoder.

If the crossing graph is C4-free, bicliques are stars, so the width is the bipartite vertex-cover
number and hence the matching number. With B_S pure binary gates and t_S outgoing operand reads,
counting reads of pure wires gives e_S = B_S + t_S − |S|. Thus e_S ≥ B_S + matching − |S|. The
global excess budget bounds e_S because the all-wires-used encoding gives every non-output wire
a nonnegative excess. The analytical check uses all eligible independent cuts and known pinned
gates with known structural support. The optional SAT encoding selects up to eight cuts of width
at least two, prioritizing the smallest matching deficit and then larger widths. It counts
distinct pure wires with an outside reader, even if a wire has several such readers.

For the outgoing information bound, vary the assignment on S and count the residual functions
on the outside. Each is the outside graph function OR the variables in a union of neighborhoods
of selected S vertices. Distinct unions differ on a singleton outside assignment. The Heawood
bipartition has 37 residuals including the empty union, giving an information lower bound of six
and an exact monotone width of seven. A pinned gate on two vertices of that side is excluded at
13 gates because it needs at least one excess read and the budget is zero. The atlas check
reproduced equality between the two bounds on 3,095 cuts in 116 C4-free graphs without isolates.

The list-coloring experiment represents each required pair by the providers whose allowed
ancestors distinguish it. Two pairs cannot share a provider if either projected positive endpoint
is below the other's negative endpoint. A satisfying assignment gives each provider the upward
closure of its assigned positive endpoints, and gives the decoder the upward closure of the
positive interface signatures and outside inputs. This is exact for the relaxed interface with
free monotone provider and decoder functions. On three disjoint crossing edges, two providers
with full access to S fail even though every requirement has both providers on its list. Three
providers give a verified decoder. Brute enumeration of monotone provider tables agreed on 80
small cases with varying ancestor sets.

The rule preserved all 36 cube verdicts in checks at the minimum and one gate below it for the
four-vertex path, five-cycle, and six-cycle. It rejected four path cubes before SAT. In single
runs on the cycle checks, enabling the structural clauses increased elapsed time. This is an
opt-in structural bound, and the result for L-meta-1343 at size 19 remains open.

The crossing adjacency matrix's Boolean rank is the established biclique-cover quantity. Jukna's
work provides related context for monotone circuits computing quadratic graph functions. These
references situate the formulation, and the novelty of the specific interface and fan-out
argument remains to be established. [Kovács, Günlük, and Hauser](https://ojs.aaai.org/index.php/AAAI/article/view/16500) · [Jukna](https://web.vu.lt/mif/s.jukna/ftp/single1.pdf)

## Two-minute size-19 probe (2026-11-24)

A 120-second wall-clock attempt on shard 2 produced no new verdict. Recomputing the
survivor list exhausted the window before the batch submitted any SAT jobs. A parallel
CaDiCaL 1.9.5 probe tested the known case-A cube with x0 OR x2 first after the three seed
gates, using the fast monotone settings with certificate rows and frontier constraints.
The probe timed out after 71.6 seconds with no witness or UNSAT result. Case B received no
SAT time in this run. Cache the survivor list before timing a repeat of this comparison.

## Size-19 ordered-only replay (2026-11-24)

The fixed-prefix ordered bound alone excludes 315 of 338 shard-2 cubes at size 19.
It rejects 167 of 182 in case A and 148 of 156 in case B. The forced-repeat check
excludes none of the 23 survivors. Thus the 315 exclusions in the earlier
repeat-first audit are all obtainable from the ordered bound alone on this frontier.
The repeat test can still serve as a prefilter before the more expensive ordered test.

The two-pass replay took 96.71 seconds with 16 workers and made zero SAT solver
calls. The exact surviving cube IDs are recorded in
[the replay log](logs/l1343_size19_partialordered.log).
