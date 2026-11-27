# Graph-selector intermediate reserve: exact polar-support profile and packed two-table lookup

Date: 2026-11-26. Starting master observed 4d7d636dbcb6d754966b6f9d2b750b6459db7124, including native-agent L-meta-16102 commit e18d675191d357de4f1e7c8971a96db5b8289fad. Extends [quadratic fiber compatibility](quadratic_fiber_compatibility_handoff.md), [parallel fiber elimination](parallel_fiber_elimination_handoff.md), and [packed directional lookup](packed_directional_handoff.md). New paper proofs, finite exact regression, and stronger data-dependent gate allocation for the already packed two-table lookup. No independent audit or Lean verification of these results, no production modification, new physical grammar, or unrestricted superlinear gate bound. No originality claim. L-clb-036 remains open.

## 1. Intermediate parallel fibers and remaining ingress

Use the contracted XOR-AND model with free affine operations and t_D syntactically data-dependent ANDs (pure data and mixed included). All data assignments x in GF(2)^d are allowed at every query q in common domain Y. The target residuals of interest are scalar quadratic polynomials. Query-only gates have no data-dependent predecessors and may be moved before the data-dependent gates in a topological order, or evaluated as arbitrary functions of q for the following argument. Each counted AND corresponds to a distinct original nonlinear binary gate after contraction.

Choose 0<=r<=t_D. Execute the previous parallel-fiber elimination on the first p=t_D-r data-dependent ANDs. This gives a common linear K and query-specific offsets c_q, with dim K>=d-p=d-t_D+r. All processed gate outputs are independent of k in x=c_q+k, k in K. Query-only gates are also independent of k. The raw data ingress linear forms of the remaining r gates restricted to K span L subset K*, dim L<=2r. On the chosen fibers, each remaining operand is its fixed raw data form on k plus a query-specific constant plus affine combinations of earlier remaining ANDs. Hence every remaining AND output, and the final output except for its direct raw affine data term, factors through the linear evaluation map of L on k for each q. No assumption of independence or low degree of internal outputs is required.

For a quadratic residual F_q, translating by c_q leaves its polar bilinear form B_q unchanged. Every a in ann(L) subset K has directional derivative of F_q(c_q+k) equal to a constant (the direct affine output contribution). Therefore B_q|K x K annihilates ann(L) in either argument. Equivalently all rows of its linear map K -> K* are in L. In exterior form terminology its support is contained in L. This holds simultaneously across q. For multiple quadratic outputs the same L works; this round's graph consequences use a scalar output with a separate query per edge.

Let kappa_b be the largest dimension of K for which there exists such a common support L of dimension <=b. The necessary bound is
    t_D >= d+r-kappa_(2r).
This is an intermediate budget: p reserved AND IDs and r remaining AND IDs are disjoint. It is a necessary condition, not sufficient for implementing the residuals with r remaining ANDs. In particular it drops all translated-slope compatibility equations and any restrictions on constants c_q from the prefix. Taking a maximum over valid r is sound; summing different reserves is not.

## 2. Exact graph polar-support profile

For a nonempty finite simple graph G on d labeled data coordinates, assume the query domain has at least one residual per edge ij, equal to x_i*x_j or x_i OR x_j. The latter has the same polar form as the former. For the exact profile take only those edge residuals; extra queries impose additional constraints but cannot invalidate the lower bound.

Write l_i=x_i|K in K*. The l_i span K*. For edge ij its polar form is l_i wedge l_j, i.e. the alternating bilinear form l_i(u)l_j(v)+l_j(u)l_i(v). If l_i,l_j are independent, its support (image in K*) is exactly their two-dimensional span. If dependent it vanishes. Over GF(2), two nonzero dependent forms are equal.

**Exact theorem**, for each integer 0<=b<=d:
    kappa_b(G) = max_{I independent in G} ( |I| + min(b, |V(G) minus N[I]|) ),
where N[I] is the union of I with all its neighboring vertices. For b>=d use kappa_d=d.

Upper bound: fix a feasible K,L. Call a vertex active when l_i is nonzero. Among active vertices with l_i outside L, adjacent vertices must have equal forms, since an independent pair would force both into L by the support condition. Thus each connected component of this induced active-outside graph contributes at most one distinct form. Choose one representative vertex from each component, giving an independent set I. No active-outside vertex is adjacent to an active-inside vertex: their nonzero forms are independent since exactly one lies outside L, contrary to the support condition. Consequently every active-inside vertex lies outside N[I]. Their forms span dimension <=min(b, |V minus N[I]|). The outside forms span dimension <=|I|. Inactive forms are zero. All l_i span K*, giving the desired upper bound even when outside forms are not independent modulo L.

Lower bound: choose any independent I and a set J subset V minus N[I] of size min(b, |V minus N[I]|). Use the coordinate subspace K supported on I union J, with L the span of coordinate forms indexed by J. Since no edge joins two I vertices or I to J, every nonzero restricted polar form is supported on L. This attains the expression. Note K here is feasible for the polar-support relaxation only; no circuit construction or translated-slope feasibility for a suffix is inferred. At b=0 the exact profile is alpha(G), recovering the earlier common-isotropy theorem.

Useful simpler upper bound: set beta(G)=max_{ij edge} alpha(G[V minus (N[i] union N[j])]). If all restricted polar forms vanish, dim K<=alpha. Otherwise choose an edge whose restricted polar form is nonzero. Both endpoints are active inside L. The representative outside set I above is nonadjacent to both endpoints, hence |I|<=beta. Thus
    kappa_b(G)<=max(alpha(G), b+beta(G)).
The exact independent-set formula can be sharper. Finding alpha or optimizing over I is in general combinatorial; no polynomial-time algorithm for arbitrary G is claimed. Given a specified K, common support dimension is just the rank of all coordinate forms at endpoints of nonzero restricted edges.

## 3. Target-only optimized lower bound and complete multipartite graphs

Let z be the number of isolated vertices. The common polar radical of all full-data edge residuals is exactly the coordinate span of the isolated vertices: on each edge the polar form forces the two endpoint direction components to vanish. A direction annihilating all raw data ingress forms of the entire circuit must be in this common radical, since all ANDs are invariant in it and output changes at most by a constant. Hence raw ingress rank >=d-z and
    t_D>=ceil((d-z)/2).
So every r in 0..ceil((d-z)/2) is admissible independently of the unknown t_D. We obtain
    t_D >= max_{0<=r<=ceil((d-z)/2)} (d+r-kappa_min(d,2r)(G)).
Combine with old vertex-cover and ingress bounds by maximum (in fact r=0 recovers vertex cover). All values are integers.

For a complete multipartite graph with at least two nonempty parts and largest part alpha, any nonempty independent I lies in one part. Its undominated vertices are exactly the remainder of that same part. Hence its expression is <=alpha; taking a whole largest part gives alpha. Empty I gives b. Therefore
    kappa_b=max(alpha,b).
Choose r=floor(alpha/2), admissible by raw ingress bound (z=0). Then 2r<=alpha and
    t_D>=d-alpha+floor(alpha/2)=d-ceil(alpha/2).
For balanced complete bipartite G=K_(M,M), this is M+floor(M/2), versus old common-isotropy/vertex-cover M and raw ingress M. For M even this is 3M/2, a 50% improvement over those particular lower bounds. It is not a 50% improvement over every known lower-bound method.

## 4. Actual packed SAT application: independent batched lookup with two tables

Use exactly the earlier packed batched lookup grammar in packed_directional_handoff.md, Section 4, with number of groups r_group=2 (distinct from the remaining gate count r above), M=2^k independent bits in each table, and k free address polarity bits per group. All data coordinates occur once in their physical words. The previous packing fixes all remaining grammar bits to constants and has word length Theta(M) for sufficiently large k, with independent addresses. Its truth function is
    F(H_1,H_2;q_1,q_2)=H_1[q_1] AND H_2[q_2].
For each query pair the data residual is exactly a cross-table product, covering every edge of K_(M,M). None is affine. This is not a new SAT encoding. It reuses the previous exact grammar and single-copy premise; no new grammar or padding replay this round.

The new theorem proves
    # syntactically data-dependent ANDs >= 3M/2   (M power of two >=2).
Via simulation of every two-input Boolean gate by at most one AND with free affine operations, every SAT circuit restricted to that valid packed word length has at least 3M/2 distinct original binary gates with ancestry in the designated table data positions. A restriction cannot create new original ancestry, so the same necessary count holds in the original circuit. Do not add it to a separate count of query-dependent or mixed gates without accounting for overlap. This is a linear lower bound in the packed word length, and not necessarily an improvement over the repository's existing global SAT size bounds. An explicit XOR-AND upper bound for this target is 2M-1, two M-1 AND mux trees and one final product. No exact complexity claim for M>2. For M=2 the lower and upper both equal 3. In particular the target cannot itself witness superlinear circuit complexity.

## 5. Sharper one- and two-remaining-gate polar variation

The common support bound ignores that each remaining AND has fixed dependency coefficients and fixed raw slopes. We can also bound the variation of the quadratic forms across q.

One remaining data-dependent AND: on the parallel fibers output is affine in k plus a fixed multiple of (a(k)+A(q))(b(k)+B(q)), with a,b fixed linear forms. Thus its polar form is the same for all q, either zero or a wedge b. This gives an exact graph profile for the relaxed requirement of equal restricted polar forms:
    kappa_equal(G)=max(alpha(G), z+2 if the nonisolated graph is 3-colorable).
If the common form is zero use the alpha theorem. Otherwise every edge has the same nonzero support plane; every nonisolated vertex has a nonzero form in that plane and adjacent vertices have different forms. The three nonzero vectors in a GF(2) plane yield a proper 3-coloring of the nonisolated graph. Isolated vertices can add at most z dimensions. Conversely given such a coloring assign its three color classes the three nonzero forms on a two-dimensional parameter space (at least two appear since G has an edge); assign isolated vertices independent extra coordinates. The resulting coordinate evaluation embeds the parameter space into the data cube, and every edge has the unique nonzero wedge of the plane. This attains z+2. It is an exact equal-polar subspace profile, not an exact one-gate realization profile; slope compatibility and fixed output affine contribution could impose further constraints.

Every graph with at least one edge has t_D>=1, so reserve t_D-1 gates. It follows
    t_D>=d+1-kappa_equal(G).
For K4, alpha=1,z=0, not 3-colorable, so t_D>=4 versus vertex-cover 3 and ingress 2. For the nonlinear-only shared-witness rook graph of dimensions m,ell>=2, alpha=min(m,ell)>=2,z=0, hence t_D>=m*ell-min(m,ell)+1, improving previous nonlinear-only bound by one. Full shared-witness still has the stronger m*ell bound from zero and singleton affine contexts; no improvement of that full-family bound.

Two remaining data-dependent ANDs: if the scalar output is quadratic at all allowed queries, the span of differences between its polar forms on K has dimension <=1, and any nonzero difference is a rank-two alternating form. Proof: write
    g1=(a+A)(b+B),
    g2=(c+C+u*g1)(d+D+v*g1)
where a,b,c,d are fixed linear forms on K, A,B,C,D are arbitrary q-dependent constants, u,v in GF(2). An affine output uses fixed coefficients of g1,g2. If g2 is unused, the polar is fixed. Otherwise expand using g1^2=g1:
    g2=(c+C)(d+D)+g1*(delta+h),
    delta=u*d+v*c,
    h=u*D+v*C+uv.
Include the output g1 coefficient in h. If a,b independent, the homogeneous cubic part is the exterior triple a wedge b wedge delta, independent of q (the coefficient of each square-free triple is its determinant, because characteristic two). Quadratic output forces delta in span(a,b). For two query contexts, the first product difference is affine. The g1 difference is affine with slope in span(a,b), and the varying h times g1 contributes a polar multiple of a wedge b. Multiplying g1 difference by delta likewise contributes only a multiple of a wedge b. Hence all polar differences are multiples of that wedge. If a,b dependent, g1 is affine with slope a query-dependent scalar multiple of a single fixed form w (or zero). Its product with delta contributes only a scalar multiple of w wedge delta to polar variation. The remaining terms have fixed polar or are affine. This proves the dimension and rank-two statements, even for arbitrary query-dependent offsets and an arbitrary nonempty allowed query subset. No universal analogous sharp formula for >=3 remaining gates is claimed. For a specified intermediate K this supplies another topology rejection test, stronger than support-only in some cases.

## 6. Executed regression

Run node graph_suffix_reserve_check.js (no dependencies). Checker body executed in JavaScript tool runtime before upload, not separately in Node or Lean. Seed 870043. Exact finite regression:
- All nonempty labeled graphs on n=2,3,4; 30 sampled nonempty graphs on five vertices; complete bipartite K2,2, K2,3, K3,3 controls. Total 104 graph instances (duplicates across categories possible).
- 18824 RREF subspace cases. For each, compute coordinate forms, edge wedges and exact common support rank, compare all support budget profile maxima to the independent-set formula and equal-polar maximum to the coloring formula. 648 profile comparisons, all passed. Also verifies edge-neighborhood beta cap for each subspace. 12 graph instances show strict optimized support-reserve improvement over max(old vertex cover,old ingress); 55 show strict equal-polar reserve improvement over same old max (not necessarily over optimized support reserve).
- Additional independent-set enumeration controls K4,4 through K8,8 (m=4,5,6,8) verify exact analytic formula, not exhaustive subspace enumeration. Optimized lower bounds 6,7,9,12 respectively.
- 1200 pseudorandom abstract suffix circuits with one or two gates (600 each), fixed data ingress slopes and fixed formal dependency and output masks. Exhaust all 4 or 16 formal offset strings, total 12000 contexts. Of these circuits 1044 always quadratic or lower, 156 have cubic degree at every context. Exact ANF coefficient elimination verifies maximum difference-polar rank 0 for one gate and 1 for two; 115 nonzero differences, all of alternating rank two. All assertions passed.
Checker commit 16a3cface4fa6f7edea3bf65b72c3ff5b118fa06.

## 7. Scope and next directions

The new exact graph-support profile and intermediate reserve are sound distinct-gate accounting mechanisms, and the two-table SAT restriction is an actual transfer to the existing packed grammar, not just an abstract benchmark. The stronger one/two gate polar variation constraints are independent of the more complicated sharp joint-rank theorem. They may support incremental pruning in the engineering track once audited. No production changes to avoid interfering with that track. The native agent's recent L-meta-16102 result is separate; no edits or review of that proof this round. No new SAT grammar/padding replay or upstream submission.

Main limitation: each target-only bound obtained here remains linear, and the existing packed two-table target has a linear upper construction. L-clb-036 remains open. Next: seek constraints that combine polar support across several simultaneously restricted input blocks or higher-degree residuals while controlling repeated use of original gates; investigate exact three-gate polar variation and whether a stronger profile can approach the 2M-1 upper construction for two-table lookup. Do not treat sampled checks as proof, or assume multiple reserve bounds can be added. Independent audit and Lean formalization remain outstanding.
