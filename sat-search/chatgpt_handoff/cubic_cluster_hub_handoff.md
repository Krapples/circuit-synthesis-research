# Cubic witness clusters and a common high-degree-hub kernel

Date: 2026-11-26. Base [540e540](https://github.com/Krapples/circuit-synthesis-research/commit/540e540d239e881d2eb39695d94234ef95efb0fc). Read [cubic_neighborhood_handoff.md](cubic_neighborhood_handoff.md) first. This round provides an exact connected-cluster algorithm for low-weight marginal witnesses, strengthens the tractable marginal dimension from order k/log k to a constant fraction of k for constant graph degree, and handles high-degree hubs using one common coefficient kernel and batched Walsh queries. These are paper circuit bounds with finite algebraic checks. No unrestricted SAT upper or lower bound, no new Lean verification, and no literature-priority claim. L-clb-036 remains open.

## 1. Exact truncated weight/address counts by connected clusters

Let P: GF(2)^Q -> GF(2)^t be a degree-at-most-three polynomial map with P(0)=0, given by actual canceled monomial coefficients. Move a nonzero constant out and shift the final image. Let G be its interaction graph, of maximum degree Delta. Put D=max(1,Delta). For each lambda in GF(2)^t and vertex subset U define an integer polynomial

    Z_U(z) = sum_(S subset U) (-1)^(lambda dot P(1_S)) z^|S|.

The constant is one. Its coefficient of degree j is the signed sum over weight-j assignments supported in U. We will compute Z_[Q] through degree d, then use Walsh inversion. Define the formal logarithmic derivative

    H_U(z) = z Z'_U(z) / Z_U(z) mod z^(d+1).

No analytic convergence, zero-free disk, probability approximation or floating point is used. The division is legal in integer formal series since Z_U(0)=1. The general connected-induced-subgraph method is standard in the partition-function literature, e.g. Patel and Regts, Deterministic Polynomial-Time Approximation Algorithms for Partition Functions and Graph Polynomials, SIAM J. Comput. 46 (2017), DOI https://doi.org/10.1137/16M1101003, preprint https://arxiv.org/abs/1607.01167, and their Computing the Number of Induced Copies of a Fixed Graph in a Bounded Degree Graph, https://arxiv.org/abs/1707.05186. The following specialization is proved directly for exact signed weight/address series; it does not import an approximation theorem or claim novelty of the underlying cluster technique.

For U define its inclusion-exclusion contribution

    C_U(z) = sum_(T subset U) (-1)^(|U|-|T|) H_T(z).

Two cancellation facts are decisive.

(1) If G[U] is disconnected then C_U=0. Indeed for disjoint graph components U_i of U, P(1_S)=XOR_i P(1_(S intersect U_i)), because no nonempty monomial meets distinct components and P(0)=0. Hence Z_T=product_i Z_(T intersect U_i), and H_T=sum_i H_(T intersect U_i). In the alternating sum, each summand cancels on a nonempty component outside its own.

(2) The coefficient of z^j in C_U is zero for j<|U|. To see this without any approximation, introduce distinct formal variables z_i and the multivariate Z_U= sum_(S subset U) sign(S) product_(i in S) z_i. Apply the Euler derivative sum_i z_i partial_i, divide by Z_U, and expand through total degree d. Restricting z_i to zero outside T commutes with these operations. Thus alternating inclusion-exclusion retains exactly monomials whose variable support is U. Each has total degree at least |U|. Set all remaining z_i equal to z to get the asserted univariate cancellation.

By ordinary subset Mobius inversion, H_[Q]=sum_U C_U. Combining the two cancellation facts gives the exact truncated identity

    H_[Q](z) = sum_(U connected, 1<=|U|<=d) C_U(z) mod z^(d+1).

The empty set contributes zero. This works for connected graphs with cycles, not only paths.

## 2. Arithmetic and circuit cost

For coefficients Z_0=1, write H_j=[z^j]H. Multiplying H Z = z Z' gives integer recurrences

    H_j = j Z_j - sum_(i=1..j-1) H_i Z_(j-i),
    Z_j = (H_j + sum_(i=1..j-1) H_i Z_(j-i)) / j.

The second recurrence is exact integer division for the recovered global Z. It suffices to compute all local Z_T through degree d and their H_T, sum C_U, then recover Z_[Q]. For a fixed U of size u, evaluate P on every subset of U once (the polynomial restricted to U); for each lambda initialize an array indexed by S subset U with a single signed entry in degree |S|. Subset zeta transform, separately for each coefficient degree, gives all Z_T at cost 2^u poly(u,d,Q,t) binary gates, including local polynomial evaluation and integer arithmetic. Computing H_T and alternating sums also costs 2^u poly(u,d,Q,t), avoiding the naive 3^u enumeration of pairs S subset T subset U.

A connected set of size u has a spanning tree with a depth-first tour of length 2(u-1). Therefore at most Q D^(2(u-1)) connected sets of size u occur. On a dense poly(k)-size kernel, store sorted, padded neighbor lists with D slots (invalid entries masked); enumerate all roots and all sequences of 2(u-1) neighbor-slot indices. Follow each walk with bounded-fanin multiplexers over the fixed Q positions, sort visited IDs, and retain valid records having exactly u distinct vertices. A connected set is covered by a tree tour and every retained walk visits a connected set. Sort keys and mark one record per distinct set; invalid and duplicate slots contribute zero. For u=1 include all roots, even isolates. This costs at most Q D^(2(u-1)) poly(k,Q,d) gates and avoids an adaptive/exponential RAM oracle. If Q=0 use just the constant image. This tour enumeration is a paper circuit implementation, not the exact algorithm in the checker, which uses connected-set growth.

Arithmetic width is polynomial in d and log(Q+2). In detail, |Z_j| <= (Q+1)^j, and expansion of 1/Z as the geometric series in 1-Z bounds |H_j| by j 2^j (Q+1)^j. The same applies locally. Summing inclusion-exclusion over at most (Q+1)^(d+1) sets and at most 2^d local subsets increases bit width by O(d log(Q+2)+d). Recurrences have polynomially bounded intermediates by the same geometric coefficient bound (allow another constant factor in the exponent); exact signed arithmetic and division by j can be performed with standard bounded-fanin integer circuits. In the intended application Q=poly(k), d=O(k), so all widths are poly(k). The Walsh transform over lambda gives each weight/address count via exact division by 2^t. These counts are nonnegative; OR their positivity over j<=d.

After the previous coordinate kernel has reduced Q to poly(k), the total gate cost for all 2^t scalar character series, all connected sets of size <=d and the inverse Walsh transforms is bounded by

    2^t (2 D^2)^d poly(k),

where Delta and Q are at most poly(k); the polynomial may depend on fixed bounds for these quantities. This is a conservative walk-enumeration bound, not an optimized connected-set count. The direct method on an unreduced large Q does not by itself give a near-linear circuit in the original word length.

## 3. Stronger deterministic marginal evaluation

Every attained address of a degree-three t-output map has a witness of weight <=3t: its fiber indicator is nonzero of degree <=3t, and an inclusion-minimal monomial of nonzero coefficient supplies an accepting input of that weight. Consequently take d=min(Q,3t). For t=0 the sole marginal address is attained.

For the bounded-degree packed cubic promise, first construct the previous neighborhood kernel and residual projection pi of dimension t. The compressed marginal graph has degree at most the original Delta (projection and restriction can only delete graph edges). Use the cluster algorithm on the compressed marginal. Compute its image exactly, then lift to full addresses as in the neighborhood theorem. The total size bound at M=2^k=Theta(n) is

    O(M poly(k) + 2^t (2 D^2)^(3t) poly(k)).

For fixed upper bound on Delta, this is deterministic O(n log^C n) whenever

    (1 + 3 log_2(2 D^2)) t <= k.

For example Delta<=4 gives the explicit sufficient bound 16t<=k. This replaces the earlier support enumeration requirement t=O(k/log k) with a constant fraction of k for constant Delta. For variable t use fixed t_max in the resource bounds; pad the projection rows with zeros and use d=min(Q,3t_max), which preserves correctness. Q is padded to its fixed polynomial upper bound; dummy variables absent from the polynomial do not create new image addresses. The result does not cover arbitrary high-dimensional cubic marginals.

This algorithm returns image support, not the unrestricted full witness histogram. Counting hardness for cubic character sums is not contradicted: we only recover low-weight counts on a bounded-degree, polynomial-size kernel, and the cost is exponential in t.

## 4. High-degree hubs: one common kernel for every assignment

Let H be a set of s hub variables such that removing H from the interaction graph leaves maximum degree <=Delta. No bound is placed on the degrees of vertices in H. H may be supplied or selected deterministically from the actual input, e.g. choose all vertices above a fixed degree threshold, count them and verify the residual degree bound. For the latter, canonicalize edges, sort by endpoint, deduplicate and count degrees with segmented scans; route flags back to vertices. A failed promise is not an UNSAT certificate. For circuits use a fixed bound s<=s_max=O(k) and pad the hub list with dummy slots.

Write the cubic map as

    F(u,y) = C(u) XOR sum_(B subset H, |B|<=2) u_B G_B(y),

where u_B is the monomial on hub set B, C collects terms involving only hubs (including constants), each G_B has zero constant, and all its terms have degree <=3-|B|. The coefficient maps are collected into the joint map

    G(y) = (G_B(y))_(|B|<=2).

Its output dimension is

    k' = k (1+s+binom(s,2)) = O(k(s+1)^2).

Its interaction graph is a subgraph of the original graph with H deleted: if a residual monomial contains two variables then the original containing monomial did too. Cancellations between identical residual monomials are handled by XOR in the joint coefficient label. Hence the graph degree is <=Delta. Apply the previous neighborhood theorem once to G, obtaining a coordinate set K with

    |K| <= 8 (k')^2 (1+Delta+Delta^2+Delta^3),
    image(G|K)=image(G).

For every fixed u, F(u,y) is an affine linear function of G(y). Equality of joint images therefore proves the simultaneous identity

    for every u: image(F(u,all y)) = image(F(u,y restricted to K)).

In particular retaining H union K preserves the full original image, and preserves every conditioned image, with a single input-dependent coordinate kernel. This works for s and Delta polynomial in k at the structural level, including hubs of unbounded degree and connected cores with such hubs. For s=O(k), Delta=O(1), |K|=O(k^6), independent of q. No enumeration of 2^s hub assignments is needed to construct the kernel.

Bounded-fanin preprocessing: split each actual monomial's at-most-three labels into hub and nonhub IDs by routing hub flags and local indices. For each nonempty residual support, put the k-bit coefficient into the block of the k'-bit joint label indexed by B; use fixed scans/comparisons over O(s^2) possible blocks. XOR equal residual supports by sorting and segmented scans. Store C in a fixed O(s^3) coefficient array. The earlier neighborhood kernel construction is linear in sparse record count up to polynomials in output dimension and log(input size). Since k'=poly(k), the common kernel and dense retained coefficient arrays cost O(n poly(k)) gates for the packed promise, independent of the number of branches. Dense arrays have O(|K|^3) entries, polynomial in k under the hypotheses. This argument uses the prior neighborhood theorem and its explicit routing cost, not the previous sparse quadratic rank theorem.

For each u, evaluate the affine combination of joint coefficient arrays on the kernel, using poly(k) gates per branch. Reapply the neighborhood selection algorithm on this now-small map, obtaining a possibly different residual projection pi_u and dimension t_u. Each branch still has graph degree <=Delta. Under a promise that all t_u<=t_max, compute the marginal image g_u by Section 3 on the branch kernel. The promise refers to this explicit deterministic selection algorithm, including a fixed tie order, after common compression. It need not hold for all high-degree instances. The per-branch cost is 2^t_max (2 D^2)^(3t_max) poly(k), using padded projection rows; s_max bounds the number of enumerated hub bits.

## 5. Single Walsh transform for all acceptance-table queries

Naively lifting each branch to its full k-bit address image costs 2^s M, destroying quasi-linearity even when the branch marginal is tiny. Instead exploit the fact that we need only decide whether the table intersects at least one branch image.

Let h: GF(2)^k -> {0,1} be the input accepting table. Write unnormalized integer Walsh transforms

    hhat(v)=sum_a h(a)(-1)^(v dot a),
    ghat_u(w)=sum_b g_u(b)(-1)^(w dot b).

For a linear projection pi_u: GF(2)^k -> GF(2)^t (t=t_max after zero-row padding), Fourier inversion of g_u gives the exact identity

    2^t sum_a h(a) g_u(pi_u(a))
       = sum_(w in GF(2)^t) ghat_u(w) hhat(pi_u^T(w)).

The left side is nonnegative and positive exactly when the table intersects the lifted branch image. The formula does not require pi_u to have full row rank, so zero-row padding is harmless; g_u contains only its attained padded keys. It works also when t=0 and when the table is all zero. Constant offsets are included when constructing g_u.

Precompute hhat once in O(M poly(k)) gates by a fast Walsh transform. Compute each ghat_u and the frequency keys pi_u^T(w) using poly(k) work per query. Route the entire collection of 2^(s_max+t_max) queries to the M table records (frequency, hhat value) by sorting on frequency with table-first ordering, segmented copy, and sorting back by (branch, marginal frequency). Records are poly(k) bits, and log(number of records) is O(k). Per branch, multiply and sum the returned integers with ghat_u, compare the signed sum with zero, and OR across branches. All widths are O(k) because |hhat|<=2^k, |ghat|<=2^t and there are 2^t terms. No approximate cancellations or random memory access are assumed.

Thus the complete deterministic packed cubic promise circuit has size

    O( (M + 2^s_max 2^t_max (2 D^2)^(3t_max)) poly(k) ).

It is quasi-linear, hence o(n^1.01), whenever

    s_max + (1 + 3 log_2(2 D^2)) t_max <= k.

Example for Delta<=4: s_max+16 t_max<=k. This permits a linear-in-k number of arbitrarily high-degree hubs, provided the branch exceptional marginals are sufficiently small. It avoids both 2^s repeated scans of the original n-bit input and 2^s repeated scans of the length-M acceptance table. If every branch marginal is zero-dimensional, s_max up to k fits the cost bound; the decision itself may of course simplify further. This is a new sufficient regime, not a claim that arbitrary cubic images can be decided quasi-linearly.

A variant for a quadratic exceptional marginal: apply dense quadratic character elimination after the branch compression rather than the cluster method. Its cost is 2^t_max poly(k), so the sufficient condition is simply s_max+t_max<=k, provided every branch marginal is quadratic. This uses the same one-table-transform identity and the elementary dense quadratic algorithm.

## 6. Finite replay and limitations

Run from this directory:

    node cubic_cluster_check.js
    node cubic_hub_check.js

Seed 870013 [cluster replay](cubic_cluster_replay.txt): 80 small maps (including 8 high-degree hub maps), 8 longer connected path maps, 12,753 connected sets, 1,436,556 local formal series, 153,336 verified low-degree cancellations, 2,434 exact weight/address count comparisons, 424 full-image comparisons. Largest q=160, largest truncation 8, largest degree 7. The independent reference is exhaustive enumeration for small maps and exact BigInt last-two-bit/weight/address transfer matrices for long paths. All assertions passed. The checker enumerates connected sets by growth rather than the fixed-array walk circuit.

Seed 870014 [hub replay](cubic_hub_replay.txt): 112 maps, 264 hub branches, 108 exact joint-image checks on small maps, 264 original-vs-common-kernel branch-image comparisons, 1,212 marginal-lift checks, 792 exact Walsh table query comparisons (including all-zero/all-one tables and variable-rank padding). Four large planted connected systems with detected high-degree hubs and bounded-degree residual paths, 32 strict joint reductions; largest observed reduction 3,002 -> 450 total variables (two hubs, one address bit). Largest retained count 1,794 in a different case. Long branch images are computed independently by exact finite-state path support DP, not by the kernel theorem. All assertions passed. The hub checker uses the earlier neighborhood algorithm and directly checks the identities; it does not implement the combined cluster/circuit routing end to end.

No synthesized AIG sizes, no actual cubic paired-grammar replay yet, and no Lean executable used. The previous deterministic quadratic sparse-rank circuit argument remains independently unaudited. The known connected cluster technique is credited above; novelty of its specialization/composition is not asserted. No production solver or verified Lean library changes.

## 7. Native-agent priorities

- Review the formal-series support cancellation, exact integer recurrence and bit-width bounds; replay both scripts. Verify the fixed-array walk deduplication and batched Walsh routing if implementing AIG regressions.
- Independently audit the previous neighborhood theorem and earlier quadratic sparse rank bound. The new hub kernel only invokes the neighborhood theorem; its quadratic-marginal variant only uses dense elimination.
- Continue actual cubic paired-grammar replay (including repeated labels, zero labels, coordinate layout, balance and padding), which remains distinct from the polynomial tests.
- Remaining targets include interaction graphs with no small hub modulator to bounded degree, or branch marginals too large and genuinely cubic for the cluster bound. Neither cubic counting hardness nor a large residual kernel proves a gate lower bound. To advance L-clb-036, a distinct-gate argument or a substantially more expressive SAT family is still required. L-clb-036 remains open.
