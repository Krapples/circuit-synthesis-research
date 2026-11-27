# Smaller-memory tree DP: candidate methods (design note, 2026-11-27)

Status: **theory and design only.** Nothing here is implemented. The only computation is the key-orbit
count in method 1.

Target: rect46 L-meta-22162 and 22172 (4x6, all 10 inputs essential, budget 12, so k = n-1+S with
S = 3). `TREE_DP.md` has the method and notation: shapes, keys, R(key), tables, meet. A 4x6 S = 3 run
was estimated at about 4G tables in the largest shape, which is over 64 GB.

**Where the memory goes.** In the rect45b S = 3 log the heaviest shape (`p2 M211111111 r1=10 r2=12`)
stores 313M tables, but its largest single key holds only 4.0M of them. So the memory is spread over
thousands of keys: sub-multisets of M times placeholder counts. It is not one huge output key. A
method has to shrink the whole key lattice, not only the top key.

## 1. Input symmetry on keys (exact; recommended first)

The cared rows of an n x m rect unit are the whole grid {(u,v)}. S_n x S_m (permuting left inputs
and right inputs) permutes these rows, so it is a symmetry of the wires.

R(key) does not depend on T. So for any permutation π that fixes the shape's multiset M,
R(π K) = π · R(K), where π acts on each table entry as a bit permutation of the 24 cared rows.

Method:
- Store R only for one representative key per orbit of Stab(M).
- When a split A + B needs a non-representative operand, apply the permutation to the stored
  representative on the fly. A 24-bit permutation costs 3 byte lookups.
- Only representative keys are built.

Number of sub-multisets of M versus number of orbits (placeholder counts multiply both equally):

| M (4x6) | keys | orbits | size 9 | size 10 |
| --- | --- | --- | --- | --- |
| all once | 1024 | 35 | 10/2 | 1/1 |
| x1 twice | 1536 | 84 | 46/6 | 10/3 |
| y1 twice | 1536 | 90 | 46/6 | 10/3 |
| x1, y1 twice | 2304 | 216 | 138/18 | 47/10 |
| x1 thrice | 2048 | 112 | 130/10 | 46/6 |

- Because the mass is spread over many keys, the expected memory saving is about 8-20x. This is
  enough to bring 4G tables to roughly 0.2-0.5G.
- The time cost is one bit permutation per operand fetch.
- **Soundness:** this is a bijection between R(K) and R(πK). It needs no assumption about T, and
  the meet still sees every table.
- **Companion (time, not memory):** shapes in the same orbit (M211111111 vs M121111111 in the log
  above, with identical table counts) need only one DP. Run it once and check against every image
  π⁻¹T.
- **Second level (optional):** canonicalize the tables inside a key under Stab(K). For the full key
  this is all of S4 x S6, which has 17280 elements. Canonical form: try the 4! row orders, then sort
  the columns by their tuple across the table entries. Combining operands then needs double-coset
  enumeration, which is harder. Only do this if level 1 is not enough.

## 2. Context/subtree meet in the middle on the output tree (exact; the README's suggestion made precise)

Any binary tree with L leaves has a centroid edge: an edge below which the subtree W has between
L/3 and 2L/3 leaves. Cut the output tree at that edge:

- Output tree = C[hole := W]. The context C is a tree with one extra placeholder, the hole, read
  exactly once.
- With every other placeholder value fixed, C is monotone in the hole and acts row by row. So
  C(w) = lo | (hi & w) with lo ⊆ hi, which is the same algebra as the existing meet.
- C(w) = T if and only if lo ⊆ T ⊆ hi and D = hi & ~lo is a subset of A(w) = ~(w XOR T), the rows
  where w agrees with T.

**Agreement-set bitmap.**
- For a fixed T and a subtree key K_W, mark A(w) for every w in R(K_W) in a 2^24-bit table (2 MB).
- Take its downward superset closure: f[S] |= f[S ∪ {i}] for each bit i. This costs about 24 · 2^24
  bit operations, well under a second with packed words.
- Then each context answers "does some w fit?" in O(1).
- The W side is never stored. It is streamed once per (T, K_W). Only its sub-keys need to be in
  memory.

Effect: no key larger than about 2L/3 of the output tree, plus the hole, is ever materialized. The
context sets can also be streamed at their last level.

Points to settle:
- **Placeholder-free W.** The bitmap is computed once per T only when W contains no placeholder
  reads. Otherwise A(w) depends on the earlier values v_j and the bitmap would have to be rebuilt for
  each choice of values. So choose W among the placeholder-free subtrees. The output tree has at most
  3 placeholder reads, so a placeholder-free subtree with a constant fraction of the leaves exists,
  but the balance is weaker than L/3.
- **The hole is a 4th placeholder.** For p = 3 shapes this needs 16-entry tables and `maxin` indexed
  base 5^4. Whether R(K_C + hole) is really smaller than the R(K) it replaces must be **measured on
  4x5 before building**. The expectation is yes, since about L/3 leaves collapse into one entry
  pair, but this is not proven.
- **Soundness:** every output tree has exactly one such decomposition per chosen edge, and the
  enumeration covers every edge size class. So no structure is lost, and the step-1 normal forms are
  unchanged.

## 3. Row-projection relaxation with refinement (sound for the lower bound only)

AND and OR act row by row, so restricting to a subset W of the cared rows commutes with every gate.
Any circuit that computes T on all rows computes T|W on W, so min_W ≤ min.

- Run the same DP on the partial label T|W. Vectors are |W| bits, and the number of distinct tables
  per key is at most what the projection can distinguish. With |W| ≈ 12-16, R collapses heavily.
- If the DP finds no structure at S = 3 on W, then min ≥ 13 on the full label too, and the statement
  is false. This is the verdict we need.
- If it returns a witness, simulate it on all 24 rows:
  - If it passes, it is a real circuit of at most 12 gates, so the statement is TRUE and can go to a
    PR.
  - If it fails, add a failing row to W and repeat (CEGAR).

Obligations:
- The DP assumes every input is essential. W must keep all 10 inputs essential (reuse the tool's
  essentiality test on W), or the DP must also allow multisets without the inessential inputs, with
  k = n'-1+s.
- Dropping constant gates is valid for any label, so step 1 is unaffected.
- **Risk:** min_W may be only 12 for every W that is small enough to help. A cheap probe would settle
  this: run S ≤ 2 on row subsets of 22162, where the full minimum is known to be at least 12, and see
  how many rows are needed to keep min_W ≥ 12.

## 4. Target filtering at the output root (exact, cheap add-on)

Let the root of the output tree be AND. Let its maximal AND cluster have children c_1..c_r.

- Each child must satisfy c_i ⊇ T, and the zero sets Z_i = ~c_i ∩ cared must cover ~T.
- With placeholders this is checked on the all-ones entry (`hi`), which is a necessary condition.
- The OR root is dual: lo ⊆ T, and the children's one sets cover T.

Consequences:
- The children of the cluster can be kept filtered and projected to Z_i ⊆ ~T. There are at most
  2^|~T| distinct ones.
- The cover check is a superset-closure lookup, as in method 2.
- The OR nodes directly below the cluster are produced by streaming pairs and then filtered. They are
  never stored unfiltered.

This removes about one level of the largest keys. It combines with method 1.

## 5. Storage engineering (exact; constant factors)

- After a key is complete, store it as a sorted, deduplicated array instead of a hash set: about
  12 B per p = 2 table instead of about 24-32 B.
- Pack the 24-bit entries.
- Build keys level by level by size, and spill completed levels to NVMe. Keys of size j are read only
  while building larger keys and in the meet. A 4G-table shape is about 48 GB on disk.

Overall saving about 2-3x, and disk removes the hard ceiling at the cost of time.

## 6. Considered and set aside

- **Index by leaf count instead of exact multiset.** This merges keys, but the union over all
  multisets of a size is larger than the per-shape lattice. It is worse.
- **Gate elimination (set x_u = 0 to reach a 3x6 sub-instance).** It loses about 1 gate in the
  accounting, so the 3x6 instance would need S = 4. It is worse.
- **First-gate elimination bound** (`theory/partial_first_gate_bound.py`, monotone, partial labels).
  Measured 2026-11-27, under 1 s per unit:
  - 21050 and 21279 (4x5) both give 8. Their known minima are 10 and at least 12.
  - 22162 and 22172 (4x6) both give 9.
  - So it only reaches the trivial n-1, with and without the first-gate pair step.
  - The stronger C++ version, `represents_8x8_11869/repro/rep-elimination.cpp`, is hard-coded to
    8x8. It reports its exclusions only as "conditional" and reached n+1 there (budget 16 with 16
    inputs).
  - The tree DP already proves n+2 on these units, so this direction is weaker than what we have.
- **Analytic shape pruning with the project's rank certificates (port ranks, rank(H) ≤ 2e).** This
  could rule out the heavy p = 2, e = 1 shapes for a given mask without any DP. It is worth asking
  the theory side whether a mask-rank bound excludes f = (2,2) sharing at S = 3. Untested.

## Quick measurements (2026-11-27)

`tree_dp.cpp` now has an opt-in dump: set `TREE_DP_DUMP=<file>` and it writes the table count of every
stored key after each DP. Without the variable its behaviour is unchanged.

Run: L-meta-21279 (4x5), `--smax 2`, 23 s. Analysis with `tree_dp_checks/orbit_weight.py DUMP 4`:
- Group the keys into orbits under Stab(M) ⊂ S4 x S5.
- Check that every key in an orbit has the same count.
- Sum the counts over orbit representatives only.

**Method 1 (input symmetry), measured.**
- **All keys in each orbit have identical table counts.** 0 of about 2,900 orbits differ, which
  confirms the symmetry claim on real data.
- Shapes where every input appears once save 15-37x. For example, the heaviest S = 2 shape
  (`p2 M111111111 r2=12`) goes from 56.0M to 2.14M tables, a 26x saving.
- Shapes with one repeated input save 5.3-5.6x (25.8M to 4.6M).
- Over all S ≤ 2 shapes together: 3.78 GB of tables becomes 0.50 GB, a 7.6x saving.
- The heaviest S = 3 shapes in the rect45b log have one repeated input (`p2 M211111111 ...`), so
  about 5-6x is the relevant figure there.
- For 4x6 the stabilizers are larger (S6 instead of S5 on the right), so the factor should be at
  least as large. Applied to the estimated 4G tables, that is about 0.7G tables, roughly 11 GB at
  16 B per table. This fits in 64 GB.
- The shape-orbit companion runs only 2 of the 9 one-repeat S = 2 shapes (one left repeat, one
  right repeat). Their counts are identical to each other in the dump.

**Method 3 (row subsets), measured negative.**
- Random subsets of the 20 cared rows:
  - 7 of 8 subsets with 10-16 rows make some input inessential, so the DP skips them.
  - The one valid 16-row subset dropped the minimum from > 10 to exactly 10.
- So the relaxation loses the lower bound before it saves much memory (3.78 GB down to 1.20 GB at 16
  rows).
- Row subsets chosen by refinement (CEGAR) might do better, but this is weak evidence against
  method 3 as a main route.

## Suggested order

1. Method 1, plus the shape-orbit time saving, plus method 5's sorted arrays. All are exact and
   local to `tree_dp.cpp`. Gate it by checking that rect45b S = 3 reproduces the same verdicts and
   witnesses.
2. Measure context table sizes on 4x5 (method 2's open point). Build method 2 only if they shrink.
3. Method 3 as an independent cross-check route. Its probe is cheap and it can also return a
   ≤ 12-gate circuit (a PR) directly.
