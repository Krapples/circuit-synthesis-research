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
s = 3 edges + tau 2 - 1 = 4 gates. **The seed saves nothing**: whatever it gains in shared ORs it pays back in
filtering. This is the mechanism by which multi-level ANDs fail to beat |E| + tau - 1 on C4-free graphs, and
it explains why every shard-2 size we checked (<= 17) is UNSAT.

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

**Computational check that is now cheap (proposed).** With `cube_search` monotone mode (nonot) plus the
analytical bounds, scan every C4-free graph up to ~9 vertices for a monotone circuit of size |E| + tau - 2
(one below the star cost). A witness anywhere would refute the accounting lemma (and show exactly how);
no witness supports it and gives test cases for the charging argument.

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
