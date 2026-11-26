# Exact mixed-rank ceilings through four gates by translation lift

Date: 2026-11-26. Continues [mixed dependency rank transfers](mixed_dependency_rank_handoff.md) and [two-sided degree-rank frontiers](two_sided_degree_rank_handoff.md). Starting head verified d3b795f54d72429fc7eb2f53c5cac3b4b9ab5d0a. Paper reduction plus complete finite enumeration, not independently audited or Lean checked. No novelty or priority claim. L-clb-036 remains open.

## 1. Universal translation-lift reduction

Keep the syntactic XOR-AND partition, arbitrary pure-side preprocessing, free affine wiring. After contracting affine wiring and collecting pure-side terms, any circuit with t mixed ANDs can be written

    g_i = (P_(2i-1)(x)+Q_(2i-1)(q)+alpha_i.g_<i)
          (P_(2i)(x)+Q_(2i)(q)+beta_i.g_<i),
    F = P_0(x)+Q_0(q)+lambda.g,

where all arithmetic is GF(2), all alpha_i,beta_i are (i-1)-bit vectors, lambda is a t-bit vector. Assign constants to either pure side. This is a syntactic partition: a pure gate has no mixed ancestors. Allowing arbitrary pure functions only relaxes the original size model. All gates can be treated as formal distinct IDs even if semantically redundant or dead. No assumption of independent actual ingress values.

Introduce 2t independent variables z and define recursively

    G_i(z)=(z_(2i-1)+alpha_i.G_<i)(z_(2i)+beta_i.G_<i),
    H(z)=lambda.G(z).

Then F(x,q)=P_0(x)+Q_0(q)+H(P(x)+Q(q)), where P,Q each have 2t coordinates. Let T_H(u,v)=H(u+v) on two full 2t-bit cubes. For anchors u0,v0 define mixed tensor by subtracting both axis slices and adding the corner. Its rank is independent of anchors: quotient each full function space by the span of the constant function; the choice of anchor is a linear section of that quotient, so does not change rank. A direct argument for zero anchors suffices: each separable term a(u)b(v) in T_H becomes a(P(x))b(Q(q)), and anchoring on actual x=q=0 kills every pure term and maps each mixed separable term to a product of anchored factors. Thus

    R_mix(F) <= R_mix(T_H).

Equivalently, pullback by P and Q induces linear maps on function spaces modulo constants. Conversely every generic template is realized with P(x)=x,Q(q)=q on 2t raw bits per side and no pure AND gates. All generic ANDs have both blocks in syntactic ancestry. Hence the maximum over all syntactically t-mixed-gate circuits is EXACTLY the maximum over these finite templates. Allowing fewer than t gates makes no difference for the maximum (pad with unused mixed gates). This is not an efficient enumeration for large t.

## 2. Exact coefficient matrix computation

For H(z)=sum_S h_S z_S in Boolean ANF, expanding H(u+v) gives mixed coefficient matrix

    C_(I,J)=h_(I union J) if I intersect J is empty, otherwise 0,

with I,J nonempty subsets of [2t]. Indeed each original monomial is square-free and each coordinate chooses u or v exactly once. Pure terms (empty I or J) are excluded. Boolean Mobius transforms on the two cubes are invertible, so rank C equals anchored mixed truth-table rank. The matrix is symmetric with zero diagonal, hence alternating over GF(2) and has even rank (standard alternating bilinear form rank theorem). This evenness applies to the GENERIC lifted matrix, not necessarily to actual F after different data/query pullbacks. In particular it rounds down a universal odd rank cap for the generic maximum.

Further exact identity: if H is nonconstant, ordinary unanchored translation rank is rank C+2. Include the empty row and column. The full coefficient matrix has blocks [[h_empty,c^T],[c,C]], where c lists nonempty ANF coefficients. Take a maximum-degree monomial S with h_S=1: row S in C is zero, since disjoint nonempty J would make degree exceed deg H, and intersecting J gives zero. Thus c is not in the column space of C. Bordering C by c and c^T increases rank by two: the nonempty columns gain one independent first-coordinate direction, and the empty column is independent of them since its restriction c is outside col C. This proof works even if h_empty=1. For constant H, mixed rank zero and full rank zero or one. Here all generic H(0)=0, so the only constant case is H=0.

Consequently the conjecture in Section 5 is equivalent to a bound on the rank of the translation matrix (or dimension of the span of translates of H), not a general bound on the degree or number of ANF monomials. A full mixed-rank maximum need not be attained by an arbitrary circuit computing a restriction.

## 3. Complete enumeration and sharp results

There are 2^(t(t-1)) ordered choices of dependency vectors, and 2^t output masks, totaling 2^(t*t) templates. For t<=3 we enumerate all ordered pairs. At t=4 we reduce by operand swap: restrict the two masks at each gate to a<=b. Swapping the two operands and simultaneously swapping that gate's fresh formal variables z_(2i-1),z_(2i) preserves the gate output and every later gate output after coordinate renaming. These permutations commute across gate indices. Simultaneously permuting u and v coordinates preserves rank. Thus the reduced enumeration still covers every possible rank. No assumed symmetry under arbitrary semantic resynthesis.

For each template compute H by exact bitset Boolean evaluations on all 2^(2t) assignments; recover ANF by Boolean Mobius transform; construct C via proper nonempty subsets of each monomial support; perform GF(2) elimination with fixed highest-bit pivots. Cache only identical H truth tables. Check all distinct t<=3 functions plus deterministic sample and record maxima at t=4 using independent direct anchored truth-table matrices and full unanchored matrices. Replay asserts exact agreement and the full-rank identity on those cases.

    t | templates (ordered or reduced) | distinct H | exact maximum | independent direct checks
    1 | 2                             | 2          | 2             | 2
    2 | 16                            | 10         | 6             | 10
    3 | 512                           | 242        | 14            | 242
    4 | 17280 (operand-swap reduced)   | 7460       | 30            | 151

Total 17810 evaluated template/output selections, 7714 distinct H across the four sizes, 405 direct matrix cross-checks. Note distinct-function counts are within each enumeration, not a union across sizes. At t=3 the dependency rank profiles 000,001,002,010,011,012 have respective exact maxima 6,10,14,8,14,14. In particular rank-two gates do not improve the universal maximum for t=3. At t=4 every profile has maximum <=30, including profiles with two rank-two gates. Full profile maxima and rank histograms emitted by replay. Histograms for t=4 count reduced representatives, not equally weighted original ordered circuits.

Tightness for all four t follows already from the rank-one chain paper proof in the previous handoff:
    G_i=(G_(i-1)+a_i+b_i)(c_i+d_i),
with independent data a_i,c_i and query b_i,d_i. Its mixed rank is exactly 2^(t+1)-2. Alternatively record-max templates are printed. The t=3,4 upper bounds are computational finite theorems conditional on the sound reduction and correct checker, not handwritten closed-form upper proofs or Lean-certified statements.

Run node exact_mixed_rank_ceiling_check.js. Both exploratory enumeration and final replay executed in JavaScript tool runtime; no separate Node or Lean execution. Final assertions passed. Checker commit 97a24921a99c484fcd6afe78937ab4effe24743f. No production changes or upstream submission.

## 4. Consequences for shared-witness SAT restriction

Earlier exact formula R_mix(F)=(2^m-1)(2^ell-1) for F(H,S,Q)=OR_(j in Q) AND_(i in S) H_ij.

For (m,ell)=(2,3), R_mix=21>14, so at least FOUR syntactically mixed AND gates, irrespective of rank-two dependencies and arbitrary pure preprocessing. Previously only three-gate rank-one profiles were excluded. Old aggregate full-span cap 3^3=27 could pass the full rank 22. Information demand six data bits could pass 2t=6. Exact direct replay covers 2048 data/query assignments.

For (m,ell)=(2,4), R_mix=45>30, so at least FIVE syntactically mixed ANDs. Old full-span cap 3^4=81 could pass full rank 46, and data information demand eight could pass 2t=8. Exact direct replay covers 16384 data/query assignments.

These are unconditional mixed gate bounds in the stated syntactic model for the abstract shared-witness functions, not total minimum sizes or asymptotic SAT lower bounds. The small examples need not satisfy earlier asymptotic packing assumptions (ell a power of two with ell=Theta(log m)<=0.5 log2 m); in particular ell=3 is not a power of two. No new physical grammar, padding or SAT-wide replay. Use earlier encoding only where its premises hold. Shared-witness functions have linear-size circuits. Do not claim an unrestricted superlinear lower bound.

## 5. General conjecture and next attack

Conjecture: R_max(t)=2^(t+1)-2 for all t>=1 in the syntactic mixed XOR-AND model allowing arbitrary pure-side preprocessing. Proven lower bound for every t by rank-one chain; matching upper bound for t<=4 by reduction and exhaustive computation, and for all t with rho_i<=1 by paper proof. No arbitrary-topology upper proof for t>=5. Equivalently for every nonzero generic H, span of its GF(2) translates has dimension <=2^(t+1). Previous universally proven upper bound remains 3^t (even rounding for generic mixed matrix), and the two-sided degree/rank and dependency recurrence can also apply.

Potential further reduction: at each gate, the unordered coefficient pair may be canonicalized by the subspace it spans, using Boolean AND identity uv=u(u+v+1), swap, and an invertible affine transform on that gate's fresh z pair. This should reduce t=5 enumeration substantially, but prove coverage and test transformation before relying on it. Next try either this exact enumeration or a direct translation-space dimension induction on the triangular generic circuit. Beware that simply treating two rank-r functions as independent product factors gives overly loose r^2 bounds and loses common dependencies; and full translation rank differs from real Fourier sparsity. No general theorem claimed from the numerical pattern. L-clb-036 remains open.
