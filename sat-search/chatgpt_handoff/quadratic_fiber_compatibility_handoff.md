# Quadratic parallel-fiber compatibility and graph-selector gate allocation

Date: 2026-11-26. Continues [parallel affine-fiber elimination](parallel_fiber_elimination_handoff.md), [symplectic profiles](symplectic_rank_profile_handoff.md), and the previously packed [shared witness](response_period_handoff.md). New general paper results, an exact abstract multiplicative complexity benchmark, and a robust restricted-query SAT allocation bound. Exact finite regression; no independent audit, Lean verification, originality claim, or unrestricted superlinear lower bound. L-clb-036 remains open.

## 1. Exact compatible affine-fiber profile

Retain the contracted XOR-AND model, data x in GF(2)^d, common independent allowed query domain Y, and t_D syntactically data-dependent ANDs (both pure-data and mixed). The preceding parallel-fiber elimination theorem guarantees a single linear subspace K, dim K>=d-t_D, offsets c_q, and a common output slope lambda_j for each output j, with
    F_j(c_q+v,q)=F_j(c_q,q)+lambda_j(v) for every v in K, q in Y.
Offsets may depend on query but must be the SAME across all outputs for each query. The slope is the raw affine output primary slope restricted to K, independent of query. This holds for every allowed ordered greedy elimination of original ANDs. No assumption about full residuals being affine.

Suppose all output residuals F_(j,q) are quadratic or lower degree, for the selected query domain. Define
    B_(j,q)(u,v)=F_(j,q)(u+v)+F_(j,q)(u)+F_(j,q)(v)+F_(j,q)(0).
Each B is alternating bilinear (direct monomial expansion). Write s_(j,q)(v)=F_(j,q)(v)+F_(j,q)(0). Then on a coset c+K,
    F_(j,q)(c+v)+F_(j,q)(c)=s_(j,q)(v)+B_(j,q)(c,v).
Consequently K is feasible for the parallel-fiber output property if and only if:
    (i) B_(j,q)|K x K=0 for all j,q;
    (ii) there exist common linear slopes lambda_j in K* and offsets c_q in GF(2)^d satisfying
         lambda_j(v)+B_(j,q)(c_q,v)=s_(j,q)(v) for all j,q,v in K.
Proof: (i) is necessary since the polarization of an affine function on K is zero, and under (i) the function s restricted to K is linear. Under (i) it suffices to impose (ii) on a basis of K. Substitution gives sufficiency for the affine-fiber property. This is not sufficiency for realizing the target with d-dim K ANDs. It is an exact characterization of a necessary property of every circuit. The shared c_q variables must not be replaced by separate independent c_(j,q) for multioutput families.

Let kappa be the maximum dimension of a subspace satisfying (i),(ii). Then
    t_D>=d-kappa.
For a fixed K, checking (i) and (ii) is polynomial in d, dim K, number of listed residuals, and output count, given exact quadratic coefficients: evaluate each polar form on pairs of basis vectors, then solve one GF(2) linear system for the lambda_j and c_q coordinates. Finding max K is a separate finite subspace optimization, not claimed polynomial. If a target contains nonlinear residuals of higher degree, this test can use any subset of queries/outputs for which the required quadratic promises are certified, ignoring other residuals. Choosing a smaller independent allowed query set cannot invalidate the necessary bound on the original circuit.

For scalar outputs only, the image of c -> B_q(c,.)|K is exactly the annihilator in K* of K intersect rad B_q. Indeed its annihilator on K is exactly that radical intersection by symmetry; finite-dimensional rank duality gives equality. Thus compatibility is equivalently existence of lambda on K whose restriction to each K intersect rad B_q equals s_q there. Equivalently the various linear forms agree with all linear relations among those subspaces: whenever v_q in K intersect rad B_q sum to zero, the sum of s_q(v_q) is zero. This is stronger than comparing common radical vectors only.

## 2. Common directional linearity and fixed-polar exact family

For general (not necessarily quadratic) residuals let A be the data directions a for which D_a F_j(x,q) is constant in x for each fixed q,j (constant may vary with q,j). This is linear by the derivative cocycle. Let E subset A consist of directions for which those constants are also independent of q, for each j. This is exactly the previous common constant-derivative space. Every feasible K obeys K intersect A subset E: evaluate the global directional derivative on each surviving coset; its value is the common lambda_j(a), independent of q.

For quadratic residuals A is the intersection of all polar radicals. The polar forms descend to the quotient V/A, and the image of K there must be simultaneously isotropic. If beta is the maximum common isotropic dimension in V/A, then
    dim K <= dim E+beta
    t_D >= d-dim E-beta = eta-beta,
where eta=d-dim E. Combine with earlier coupled rho/eta bound by maximum, not addition, since both use same gates. This quotient bound can be weaker than the exact compatibility profile of Section 1.

If every residual has the same polar form of rank 2r, then dim A=d-2r and beta=r, by nondegenerate alternating rank on the quotient (an isotropic subspace U is contained in U^perp, so dim U<=r; a symplectic basis attains r). Write sigma=dim A-dim E, the rank of differences of query slopes on the common radical, not the old rank of full-data affine residual differences. Then
    t_D>=r+sigma.
In fact kappa=dim E+r in this fixed-polar case, for arbitrary output count one if the scalar residuals have the same form. For scalar: choose an isotropic lift of a Lagrangian complement quotient together with E. Such K has K intersect A=E and is isotropic. All q agree on E, so the scalar radical compatibility test gives a common slope. For vector outputs we only claim the upper bound on kappa via the common-radical argument where applicable; joint offsets can impose additional constraints.

**Exact benchmark.** Let M=2^k with k>=1, r>=1. Data consists of M table bits x and 2r bits z. Query consists of address a and enable e. Define
    F(x,z;a,e) = sum_(i=1)^r z_(2i-1)*z_(2i) + e*x_a.
Every residual is nonaffine, since r>=1. The previous full-residual slope rank rho is zero. All polar forms equal the rank-2r form on z, with common radical A equal to the full x space. Disabled query has zero x slope, and enabled addresses expose each x coordinate, so E=0 and sigma=M. Thus t_D>=M+r. Compute the r products and XOR them, compute the lookup with M-1 ANDs by a binary mux tree, and enable with one AND. Hence exact total multiplicative complexity M+r, all these ANDs data-dependent. The earlier coupled rho/eta target-only bound is ceil((M+2r)/2)=M/2+r, so the new lower bound strictly improves by M/2. For M=16,r=8 old 16, new exact 24. This is an abstract XOR-AND benchmark, not a new SAT encoding or exact ordinary binary gate count. No circuit experiments for this hybrid in the new checker; both lower and matching upper are elementary analytic arguments.

## 3. Explicit affine compatibility obstruction

Four coordinates x1,x2,x3,x4 and three scalar residuals
    f1=x2*x4,
    f2=x2*x3,
    f3=x1*x2+x3.
All are quadratic, A=E=0 (common polar radical zero). If a common isotropic K has nonzero coordinate form x2|K, then each of x1,x3,x4|K must be zero or equal to x2|K (the corresponding edge alternating form vanishes exactly when its endpoint forms are dependent). Hence dim K<=1. Every common isotropic subspace of dimension>=2 lies in x2=0. The unique dimension-three candidate K is the full hyperplane x2=0, indeed isotropic for all three. Its allowable translated slopes for f1 are span(x4|K), for f2 span(x3|K), whose intersection is zero. For f3 the possible slopes are x3|K and (x3+x1)|K, neither zero. Hence dimension three infeasible. Dimension two is feasible (K=span(e1,e4), c_q=0, common slope zero). Therefore max common isotropic dimension 3, max compatible dimension 2. The exact-profile gate lower bound 2 strictly beats isotropy alone 1, though equals the older eta/2 bound 2 for this example. No claim it beats all prior methods. In particular checking only the intersection of polar radicals does not suffice to decide compatibility.

## 4. Graph-selector theorem and shared-witness application

Let G be any nonempty finite simple graph on d labeled data coordinates. For each edge ij an allowed query selects either residual x_i*x_j (AND) or x_i OR x_j = x_i+x_j+x_i*x_j. It is enough that one of those two residuals occurs for each edge; repeated contexts of either type are harmless. No other residuals assumed for this restricted query domain; additional queries only strengthen the necessary bound. Every such residual has degree two.

For each K let l_i be the coordinate linear form x_i restricted to K. Common isotropy holds iff for every edge ij the two forms l_i,l_j are linearly dependent: over GF(2) that means one is zero or they are equal. Proof: polar form on K is l_i(u)l_j(v)+l_j(u)l_i(v), zero iff the two forms are dependent (two independent forms give surjective map to GF(2)^2). Take the induced subgraph on active vertices whose l_i is nonzero. Along each edge in that subgraph the forms coincide, hence one form per connected component. All coordinate restrictions together span K* (they separate points and restriction of full coordinate dual is surjective), so dim K<=number of active components. Choosing one vertex from each active component gives an independent set in G, so dim K<=alpha(G).

Conversely take an independent set I of maximum cardinality alpha, and K the coordinate subspace supported on I. Each edge has at least one endpoint outside I. On every AND edge, choose its outside endpoint to be zero via c_q; on every OR edge choose its outside endpoint to be one. Thus the residual is constant on the corresponding coset, and common slope zero works. Offsets for different edge queries may differ, so no conflict between AND and OR constraints. Therefore for this exact edge-query family,
    max common isotropic dim = max compatible fiber dim = alpha(G)
and the parallel-fiber theorem proves
    t_D>=d-alpha(G)=tau(G),
where tau is minimum vertex-cover size (complement of maximum independent set). This is an exact subspace profile, not generally exact multiplicative complexity of the selector. For graphs without isolated vertices the old eta=d, rho=0 for these queries, giving ceil(d/2); the new bound may exceed this for small independence number. Isolated vertices are permitted by the graph theorem itself.

For the earlier actual packed shared-witness F(H,S,Q)=OR_(j in Q) AND_(i in S) H_ij, m,ell>=2, restrict the allowed query contexts to:
    |S|=2, |Q|=1 (two cells in one column, AND);
    |S|=1, |Q|=2 (two cells in one row, OR).
The data cube remains all m*ell bits. Every residual now quadratic, none affine. The graph on table cells is the rook graph: edges join distinct cells sharing row or column. Independent sets are nonattacking rook placements, size<=min(m,ell), achieved by a diagonal placement. Thus the exact compatible dimension of this restricted query family is min(m,ell), and
    a+t >= m*ell-min(m,ell)
for a pure-data ANDs and t mixed ANDs, counting original IDs once. Common polar radical zero because every cell occurs in an edge; eta=m*ell and rho=0. The bound improves the previous ceil(m*ell/2) target-only bound whenever m*ell-min(m,ell)>ceil(m*ell/2). For m=128,ell=4, d=512 gives 508 versus 256; this ell is a power of two but does NOT meet ell<=0.5 log2(m) at m=128. Use m=256,ell=4 instead as an example satisfying the inequality, with d=1024 giving 1020 versus 512 (the earlier asymptotic packing also has ell=Theta(log m) as a family, not a guarantee of useful numerical constants at a single size). No claim of new grammar verification: the same earlier packing has independent row and column selection coordinates, and all selected masks are legal within that packing. The original binary-gate ancestry bound follows via simulation of any two-input Boolean gate with at most one AND and free affine ops.

Important: the FULL shared-witness family already has the stronger bound a+t>=m*ell using its zero and singleton affine residuals, from the previous handoff. This round does NOT improve the full-family numerical bound. Its contribution is robustness under removal of ALL affine residual contexts and a different geometric certificate that may apply to restrictions where affine witnesses are unavailable. No new SAT-wide total size bound; ordinary full degree already imposes a larger total AND requirement. The data-ancestry counts cannot be added across overlapping partitions.

## 5. Executed regression

Run node quadratic_fiber_compatibility_check.js (no dependencies). Checker body executed in JavaScript tool runtime before upload, not separately in Node or Lean. Seed 870042. Enumerates all RREF subspaces in dimension four for 320 random scalar and 160 random two-output families of three or four quadratic queries (each residual forced to have a quadratic monomial). For every common isotropic subspace compares exact linear consistency with independent exhaustive offset slope-signature intersection; shared offsets enforced across outputs. Computes common radical and common constant derivative spaces, and checks feasible K meets common radical only in E. 87 families strict gap between max common isotropic and exact compatible dimensions, including 50 scalar and 37 vector. In these samples max common-radical-filtered dimension equals max isotropic dimension; this need not hold in general. Greedily minimizes one scalar separation by deleting contexts and terms while preserving strict gap and zero common radical, yielding the explicit example in Section 3. Total 10073 compatible-vs-offset comparisons, including intermediate minimization cases.

Graph regression: all 63 nonempty labeled graphs on four vertices, 12 sampled graphs on five vertices, and two rook graphs 2x2 and 2x3; random AND/OR edge choices except rook uses specified column AND/row OR. Enumerates 11601 subspace cases across 77 graphs; compares coordinate-form isotropy rule, actual polar test, exact compatibility equations and exhaustive offsets where isotropic; computes alpha by brute-force subsets and verifies both maxima equal alpha. Rook controls: 2x2 alpha=2, data-dependent lower 2; 2x3 alpha=2, lower 4. These tiny parameters are abstract controls, not asserted to satisfy physical packing assumptions. All assertions passed. Checker commit 85171062f87beefbb74a589a83e937ccc9ecff96.

## 6. Algorithmic and research scope

New target-only subspace compatibility profile and per-candidate certificate: from the raw ingress forms of any candidate, execute one allowed greedy elimination, obtain K, check polar vanish and common slope equations. Failure refutes the candidate (if residual coefficients and query restrictions certified). For quadratic targets, given K this is linear algebra, without exhaustive data truth tables. This has not been integrated into production algorithms, nor independently audited. It gives a potential pruning rule for the engineering agent. Next seek compatible-fiber constraints on intermediate/ancestor-closed subsets, where each remaining gate has limited capacity to repair an inconsistent system; investigate restrictions with higher degree and no affine queries. Distinct-gate overlap accounting across partitions remains unresolved. All new numerical bounds here are linear in the input data length; no superlinear gate-size bound, new grammar/padding replay, or upstream submission. Independent review/Lean formalization remain outstanding. L-clb-036 remains open.
