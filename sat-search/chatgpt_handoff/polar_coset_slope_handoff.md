# Polar coset budgets and complementary slope demands for packed two-table lookup

Date: 2026-11-26. Starting master verified 451e37135fd88a5296c9d3a0bc4b4d35d92195a6. Extends [graph suffix reserve](graph_suffix_reserve_handoff.md), [parallel affine-fiber elimination](parallel_fiber_elimination_handoff.md), and [packed directional lookup](packed_directional_handoff.md). New paper proofs, exact finite regression, improved data-dependent gate lower bound for the existing two-table SAT restriction, and exact multiplicative complexity of the abstract four-entry case. No independent audit, Lean verification, originality claim, production modification, new physical grammar, or unrestricted superlinear lower bound. L-clb-036 remains open.

## 1. Quotient of suffix ingress: a polar coset budget

Retain the contracted XOR-AND model with free affine operations, scalar output, independent data x and allowed queries q in a common domain. Reserve p syntactically data-dependent gates by the previous parallel affine-fiber elimination. Let K be the surviving common linear subspace, and x=c(q)+k the associated parallel fibers. All reserved gates and all syntactically query-only gates are constant as functions of k for fixed q. Count r remaining data-dependent ANDs, with their original dependency coefficients fixed, and their two restricted raw data ingress forms per gate.

Let A:K -> GF(2)^(2r) be the linear map collecting these forms; write l=rank A. As in the generic translation lift, the output on the parallel fibers has the form
    F(c(q)+k,q)=H(Ak+w_q)+lambda(k)+e(q).
Here H is one fixed generic r-AND function with a fixed affine output mask of the remaining gate outputs; w_q is a vector of 2r bits containing all contributions from query variables, reserved outputs, offset c(q), and constants. Lambda is the raw affine output slope restricted to K and is fixed across queries; e(q) is arbitrary. This is an algebraic identity after the restriction, not an assertion that w_q or c(q) can be computed at no cost in the original circuit. Query-only gates have no data-dependent ancestors, so may be evaluated first; reserved gates are exactly a prefix of the remaining data-dependent topological order. The r counted gates are disjoint from the p reserved gates.

If w_q+w_q' belongs to im A, pick v in K with Av=w_q+w_q'. Then
    H(Ak+w_q')=H(A(k+v)+w_q).
Thus the two full residuals differ only by a translation in K and a scalar constant (lambda(v) plus the two e values). In particular, if all selected target residuals are quadratic or lower, their polar forms are identical whenever the offsets lie in the same coset of im A. This is true even if H itself is high-degree on the full formal cube, and even if only a proper subset of the cosets is used. Consequently, if P(K) counts the distinct restricted polar forms, including zero if present,
    P(K) <= 2^(2r-l).
Equivalently l+ceil(log2 P(K))<=2r. This is a necessary condition on the actual fixed ingress map, beyond l<=2r and the common support dimension bound. It does not assume that every offset coset is attainable. Rank of the linear span of the polar forms is <=P(K), so any lower bound on that span also gives a valid lower bound on the number of cosets. If one uses affine span dimension instead, P>=affine_dimension+1 (not 2^affine_dimension); do not conflate these.

More generally, for any fixed D>=2, among selected residuals of degree <=D, the degree-D homogeneous ANF component (including zero) is constant within each offset coset, since translation preserves the top-degree component under that degree promise. The same budget applies to the number of distinct degree-D components. For a multioutput family with common ingress and common fixed output slopes, it applies to the number of distinct joint tuples of such components (not a product of separate counts without justification). No unrestricted high-degree coefficient invariance claimed: a lower-degree component can change under translation of a higher-degree polynomial.

## 2. Geometry of two-table lookup on an arbitrary surviving subspace

Target
    F(x,y;i,j)=x_i*y_j,
where x has M independent table bits and y has N independent table bits; all index pairs allowed. On parallel fibers K, let d=dim K. The restrictions of the x-coordinate forms span U subset K*, those of the y-coordinate forms span V subset K*. Write u=dim U,v=dim V,h=dim(U intersect V). U+V=K*, so h=u+v-d. For q=(i,j), the quadratic polar form on K is the wedge l_i wedge m_j, independent of the query-specific translation offset. If d>max(M,N), both U,V are nonzero and d>=2.

The span of these polars is U wedge V, with exact dimension
    w=uv-h(h+1)/2.
Proof: choose bases of complementary spaces U0,V0,C where C=U intersect V, U=U0 directsum C,V=V0 directsum C. Exterior basis pairs span U0 wedge V0, U0 wedge C, V0 wedge C, and wedge^2 C; these have disjoint basis supports. Their total dimensions are (u-h)(v-h)+(u-h)h+(v-h)h+h(h-1)/2, giving the formula. Bilinearity means the given coordinate-form wedges span the entire space, so no need for queries selecting arbitrary linear forms. All ranks and forms here over GF(2); the exterior pairing is the alternating bilinear form a(s)b(t)+b(s)a(t), with no division by 2.

Moreover the common support of these forms is the entire K*: every nonzero coordinate form occurs as an endpoint of a nonzero wedge, or is equal to such an endpoint. One proof: let a in K annihilate all polar maps. If a nonzero then some x or y coordinate form takes value 1 on a. Suppose l_i(a)=1 (swap tables otherwise). The equalities for each pair imply m_j=m_j(a) l_i for all j. Since V nonzero, choose m_j=l_i, with m_j(a)=1. Then all l_i' likewise lie in span(l_i). This implies d<=1, contradiction. Thus common radical is zero, and common support is K*. In particular the suffix ingress map A must have rank l=d by Section 1 / prior support theorem (otherwise its kernel lies in the common polar radical). Hence d<=2r. Note this fails for arbitrary K where one table vanishes or all active forms lie in a single line; the stated dimension premise excludes these cases.

## 3. Complementary affine slope obligations

The same suffix also has to carry ordinary affine-slope diversity on two different surviving data subspaces. Fix W=ann(U) subset K; dim W=d-u. Choose any linear complement to W in K. Treat coordinates w in W as the new data and the complementary coordinate together with the original query (i,j) as the new query. This is a valid mathematical pullback of the suffix, with at most r ANDs, with arbitrary query-only preprocessing allowed. The previous affine-fiber theorem applies because all its raw data slopes on W are fixed independent of the new query. No need to realize the earlier query offsets as an efficient circuit, since they contribute only to query-only terms.

For every query pair the left factor is independent of w, so each residual in w is affine. For any j choose an i with nonzero l_i on K, possible since U nonzero. The form l_i vanishes on W and is nonzero on its complement, so varying the complementary coordinate can set the left factor to either zero or one, regardless of offset c(i,j). The resulting affine slope on W is respectively zero or m_j|W. As the right coordinate forms restricted to W span W* (because U+V=K* and U annihilates W), the within-output affine slope differences span all W*. The prior one-constraint-per-gate slope bound gives
    r>=dim W=d-u.
Interchange tables to get r>=d-v. This is NOT an addition of two gate lower bounds; both constrain the same remaining r gates, and their consequences are u,v>=d-r.

Suppose d/2<=r<d. Then there are complementary subspaces U' subset U,V' subset V with dimensions u',v' both at least d-r. Indeed choose integer u' in [d-v,u] intersect [d-r,r], which is nonempty from u+v>=d and u,v>=d-r. Assign the h shared basis vectors between U0 and V0 to achieve the chosen dimensions. Thus U' wedge V' has dimension u'(d-u')>=r(d-r), by the concavity of the product on [d-r,r]. It is contained in U wedge V. Combining with the polar coset budget, when d>max(M,N) and d/2<=r<d,
    r(d-r) <= dim(U wedge V) <= P(K) <= 2^(2r-d).
This is the coupled necessary inequality. It uses the complementary slope constraints on the same suffix to prohibit extremely unbalanced U,V, then uses the single joint polar coset budget. There is no summation of overlapping counts, and no dependence on the previous sharp augmentation-rank theorem.

## 4. Improved packed two-table bound for powers of two

Take N=M=2^k, k>=1. Let t_D be the total data-dependent AND count of any realization. Existing raw-ingress lower bound gives t_D>=M (common full polar radical zero). Reserve exactly p=M-1 data-dependent gates, so
    r=t_D-M+1,
    d=dim K>=2M-p=M+1.
If t_D>=2M-1 the new claimed lower bound is already satisfied, since k<=M/2 for powers of two M>=2. Otherwise r<M; in either case of interest r<=M<d, and Section 2 gives d<=2r. Section 3 yields
    r(M+1-r) <= r(d-r) <= 2^(2r-d) <= 2^(2r-M-1).
Therefore for t_D<2M-1 the above inequality is necessary, with r>=ceil((M+1)/2). The same numerical inequality holds at r=M, since M<=2^(M-1), so it can be used throughout the interval up to the upper construction count.

**Closed bound:**
    t_D >= 3M/2 + k - 1.
For k=1 this is the previous bound 3 (and exact). For k>=2, suppose t_D<=3M/2+k-2, i.e. r<=r0=M/2+k-1. If r<ceil((M+1)/2), the full support bound already rejects it. On the remaining integer interval, r(M+1-r) is nonincreasing and 2^(2r-M-1) increasing. At r0 their values are
    r0(M+1-r0) = M^2/4 + M/2 - (k-1)(k-2),
    2^(2r0-M-1) = 2^(2k-3) = M^2/8.
For k>=2, k-1<=M/4 (base k=2 and elementary induction), so (k-1)(k-2)<=M^2/16. The left value is strictly above M^2/8. Contradiction. If r0 falls below the admissible interval, support alone suffices (no such problematic k>=2). At t_D=3M/2+k-1 the simplified necessary inequality no longer excludes the count: r=M/2+k, left product <=M^2/4+M/2 <=M^2/2, right equals M^2/2. This does not show existence of a circuit at that count. The exact upper construction remains 2M-1 ANDs using two mux trees and a final product.

Examples:
    M | previous bound | new bound | upper construction
    2 | 3              | 3         | 3
    4 | 6              | 7         | 7
    8 | 12             | 14        | 15
    16| 24             | 27        | 31
    32| 48             | 52        | 63
    64| 96             | 101       | 127
    256|384            | 391       | 511
Exact total multiplicative complexity for M=4 is now 7, since every AND of the upper construction has data ancestry and the lower bound counts data-dependent ANDs alone. M=2 was already exact. M=8 remains 14..15. No exact ordinary binary Boolean gate count claimed (affine operations free in this model).

For the actual SAT application, reuse exactly the earlier batched packed lookup grammar with two independent groups, each M=2^k bits, independent address polarity bits, and single-copy data positions at fixed physical coordinates. All query pairs used here are valid under that restriction. Therefore the same lower bound on distinct original nonlinear binary gate IDs with ancestry in the designated table bits applies to SAT circuits at those existing packed lengths (arbitrary binary gates simulate by at most one AND plus affine operations). The M=4 exact case is an abstract lookup benchmark, not an assertion of an exact SAT circuit size. The logarithmic additive improvement is on data-dependent gate allocation for that restriction, not necessarily an improvement over the best repository-wide total SAT gate lower bound. No new grammar or padding replay. Existing packed lengths are Theta(M) as k grows, and this target has a linear upper circuit, so this is not superlinear.

## 5. Executed regression

Run node polar_coset_slope_check.js (no dependencies). Checker body executed in JavaScript tool runtime before upload, not separately in Node or Lean. Seed 870044:
- Enumerate all RREF subspaces with dimension >max(M,N) in small two-table spaces (M,N)=(2,2),(2,3),(3,3), total 763. Compute exact coordinate-form wedge span, common support, dimension formula and distinct polar count; 1495 admissible complementary dimension inequalities. For both annihilator subspaces per K, explicitly vary complementary query coordinates with deterministic random offsets and check full slope span (1526 checks). No general conclusion derived from enumeration alone.
- 480 pseudorandom generic suffix circuits with 1..4 gates and up to 6 data coordinates, arbitrary fixed ingress slopes, dependency masks and output masks. Exhaust all formal query offset strings (46032 total), compute ANF directly and canonical coset representative modulo ingress image. Compare degree/top components for each repeated coset (38297 comparisons), and polar forms for quadratic or lower residuals (27712 such offsets). Distinct polar count never exceeds number of used quadratic cosets; 416 circuits have strict inequality relative to the entire offset coset budget. Nonconstant polar forms occurred at 11360 offsets (count of offsets, not distinct forms).
- Integer arithmetic checks of the simplified necessary inequality and closed lower formula for k=1..16; strict improvement over previous 3M/2 bound at 15 sizes.
All assertions passed. Checker commit 1cb68055e5c9aac5ac18ad6ba397eb4db74d38f3.

## 6. Scope and next direction

New result is a coupled gate-allocation proof using fixed ingress rank, quotient cosets and complementary affine slopes. It closes an exact small lookup complexity case and increases the data-dependent gate lower bound in an existing valid SAT restriction by log2 M-1. It does not establish a superlinear bound or close the general 2M-1 target; for M=8 a one-gate gap remains. Investigate stronger joint constraints on the polar forms realized within the quotient offsets, rather than just their count, and consider extending the top-degree coset budget to independently addressed three-or-more table products. For general targets, do not infer independence of gate obligations merely because their data subspaces are disjoint. Independent auditing and Lean formalization remain outstanding; no production changes or upstream submission. L-clb-036 remains open.
