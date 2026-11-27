# Joint translation rank and exact prefix residual accounting

Continues [five-gate Schur decomposition](five_mixed_rank_schur_handoff.md) and [exact rank ceilings](exact_mixed_rank_ceiling_handoff.md). New paper identity, complete canonical enumeration of joint spaces through five gates, deterministic samples at six and seven gates, and a weighted accounting formulation of the general conjecture. No independent audit, Lean certification, originality claim, or unrestricted superlinear lower bound. L-clb-036 remains open.

## 1. Stronger joint invariant

Use the same syntactic mixed XOR-AND model, translation lift and fresh-pair generic template
    G_i=(z_(2i-1)+alpha_i.G_<i)(z_(2i)+beta_i.G_<i).
All G_i vanish at zero. Write C(f) for the mixed translation ANF coefficient matrix indexed by nonempty subsets; c(f) for its nonconstant ANF coefficients. Define
    U_j=sum_(i<=j) im C(G_i), J_j=dim U_j.
All matrices are embedded into the full current coefficient space by zero extension for new variables. C(f) is symmetric, so row and column spaces agree under this identification. For an affine output mask H=sum_i lambda_i G_i, im C(H) subset U_j. Thus R_mix(H)<=J_j. The same bound applies to an arbitrary actual circuit through the earlier pure-side pullback theorem, including a common mixed factor-space bound for multiple outputs under common ingress maps. Pure output terms contribute nothing after anchoring.

Stronger conjecture: J_j<=2^(j+1)-2 for every generic template. Sharp lower bound follows from the already proved rank-one chain output rank. This is stronger than the scalar conjecture; equality of scalar and joint maxima is not asserted for arbitrary j. The fresh-pair affine coordinate changes from the previous handoff preserve every G_i simultaneously, hence induce one common invertible map of the function space modulo constants. They preserve the dimension of the sum of mixed factor spaces. Thus the same dependency-subspace enumeration covers joint rank, without enumerating output masks.

## 2. Exact joint last-gate update

Let E denote the coefficient space indexed by nonempty old subsets. Write U=U_(j-1) subset E and J=dim U. The new gate is G=(a+P)(b+Q)=PQ+aQ+bP+ab, with P,Q linear combinations of earlier G_i. Set
    B=[C(Q) C(P)] : E directsum E -> E,
    r=rank B, K=ker B^T=ker C(P) intersect ker C(Q),
    A=C(PQ)+c(P)c(Q)^T+c(Q)c(P)^T,
    delta=dim((U+A K)/U).
In particular im B subset U and r<=J.

**Exact identity:** J_j=2+J+r+delta.

Proof: consider the mixed coefficient matrix C(G), with old-empty/fresh-empty joint index excluded (as required for mixed coefficients). The two indices consisting of a alone and b alone have principal block [[0,1],[1,0]]. Eliminate this invertible 2x2 pivot by a congruence. Old-only prefix vectors have zeros in the two pivot positions; the right column transformation in pivot/rest order is [[I,Pivot^-1*Cross],[0,I]], so these row vectors are unchanged. The remaining nonzero block in fresh-subset order empty,a,b, with nonempty old indices, is
    D=[[A,B],[B^T,0]].
The other rows/columns (fresh-ab indices) are zero; this is the mixed-only counterpart of the previous full Schur complement. The correction A is exactly the two indicated outer products from the pivot inverse. The joint dimension therefore equals two plus the dimension of row(D)+embedded U.

Project this latter space onto the two fresh-nonempty blocks. Its image is the row space of B, dimension r. The kernel of projection consists of old-only vectors: a linear combination of the first block of rows with coefficient x has fresh projection x^T B, which vanishes iff x in K; its old part is Ax since A is symmetric. The lower rows contribute im B and the prefix contributes U. Hence the kernel is A K+im B+U=A K+U, dimension J+delta. Rank-nullity proves the formula. No assumption of independence of P,Q as semantic functions, no shared gate double charge.

Relation to previous scalar residual s=rank(A restricted to K): dim(row(D) intersect E)=r+s, and delta<=s, because im B=K^perp and im B subset U. In particular J_j>=2+2r+s (as required by the scalar bound) follows directly from inclusion, not from the inequality delta<=s alone. More precisely
    J_j - R_mix(G) = J-r + delta-s = dim U - dim(U intersect (im B+A K)) >=0.
The quotient delta removes already available old factor-space directions that scalar residual s can count. It is unaffected by an additional earlier-output mask W in the final output, since C(W) maps into U; the common space of old outputs and G+W is the same as old outputs and G.

## 3. Rank-one suffix theorem and weighted gate debt

If the two formal coefficient dependencies have rank <=1, use the proved subspace symmetry to choose Q=0. This may require an affine transformation of the fresh pair; it leaves old-only prefix space fixed. Then A=0, delta=0, and r<=J. Therefore
    J_j<=2J_(j-1)+2.
For any prefix of p gates whose joint rank obeys J_p<=2^(p+1)-2, any suffix of rank-zero/one gates preserves this bound for every later count. In particular our exhaustive theorem for p<=5 below implies the exponential scalar and joint bound for arbitrary-length circuits in which all rank-two dependencies occur within the first five mixed gates of some topological ordering. This is a genuine extension of the earlier all-rank-one theorem, but its prefix case relies on complete finite verification; no general proof for arbitrary placement of rank-two dependencies.

Define e_j=r_j+delta_j-J_(j-1). The exact update rewrites as
    J_j+2=2(J_(j-1)+2)+e_j.
Starting J_0=0,
    J_t+2=2^(t+1)+sum_(j=1)^t 2^(t-j)e_j.
Thus the stronger conjecture is equivalent to the nonpositivity of the weighted sum for every template. Rank-one steps have e_j<=0. Rank-two steps can have positive e_j and cannot be bounded by local doubling alone. Explicit control: two independent seeds G1=z1*z2,G2=z3*z4, then G3=(a+G1)(b+G2). Prefix ranks J1=2,J2=4; at gate 3 r=4,delta=4,J3=14. The three e values are 0,-2,+4; their weighted sum at t=3 is exactly zero. The gate-3 local bound 2J2+2=10 fails. The conjecture must therefore control positive debt using earlier accumulated slack, rather than assuming every gate locally doubles rank.

Another exact implication: a suffix of k rank-one steps has J_(p+k)<=2^k(J_p+2)-2, preserving any normalized slack from the prefix. A possible next target is a rank-two debt bound in terms of earlier dependency-cone overlaps, or a certificate proving that every positive contribution can be paid from unused prefix capacity. The present identity alone does not establish such a bound.

## 4. Joint space enumeration and larger samples

Run node joint_translation_rank_check.js. Checker body executed in JavaScript tool runtime, not separately in Node or Lean. Sparse exact ANFs, BigInt mixed coefficient rows, GF(2) elimination with fixed lowest-bit pivots. Enumerates canonical dependency subspaces of ranks 0..2 for t<=5, without any output-mask enumeration. Joint rank is obtained by stacking all original G_i mixed coefficient rows and computing rank. All counts and expected maxima asserted. For sampled sizes use deterministic LCG seed 870034 and arbitrary ordered formal dependency masks; also check a sampled last-used scalar output rank <=joint rank. No probabilistic claim on counterexample absence.

    t | configurations | max joint rank | attaining max | coverage
    1 | 1              | 2              | 1             | complete
    2 | 2              | 6              | 1             | complete
    3 | 10             | 14             | 4             | complete
    4 | 150            | 30             | 60            | complete
    5 | 7650           | 62             | 3312          | complete
    6 | 5000           | 126            | 2948          | sample only
    7 | 1000           | 254            | 592           | sample only

7813 complete canonical configurations across sizes 1..5, plus 6000 pseudorandom larger configurations. These are counts of canonical dependency templates (or sampled ordered templates), not of original circuits or all output masks. No violations observed. Six/seven maxima are lower bounds on their universal maxima, not proven upper bounds. Their sampled scalar maxima also attain 126,254. The universal scalar upper bound for t>=6 remains the prior established bounds; conjecture not promoted to theorem.

## 5. Exact update regression and obstruction

Additional 300 deterministic pseudorandom preceding circuits with one to five gates, and one explicit two-seed fork, check the exact joint update identity. The sparse implementation obtains images of a kernel basis under A by tagged elimination on active columns of the vertical stack; omitted coordinates have zero A and stack columns and cannot contribute. It measures delta by adding those images to the old common row span and subtracting its rank. Direct stacking of all old and new mixed matrices gives independent new J. All 301 comparisons passed. 44 positive deltas; 38 failures of local doubling J_new<=2J+2; largest observed delta=52 (five preceding gates, J=36,r=36,delta=52,J_new=126). This is a strong negative control: local doubling can fail even though the global exponential capacity is met exactly. Do not extrapolate largest delta or observed frequency. Rank-one normalization checked whenever a=0,b=0 or a=b.

An exploratory exhaustive scan of spaces generated by products of multiple gate outputs timed out. No results or conclusions from that incomplete scan are claimed. Prior complete joint-space enumeration and final regression succeeded. Checker commit 52f17db5939aac845b8f6def2d23257455ed2d93.

## 6. Next direction and scope

Investigate weighted rank debt, particularly whether the residual image of AK modulo the common prefix space admits a bound based on structural slack of ancestor cones. Need account for reconvergence and shared gates; simple component tensorization or local doubling cannot prove the general bound. Consider a stronger invariant on subspaces of previous output masks and their products, but first design smaller exact checks rather than re-running the timed-out broad scan. Independently audit the Schur step and common-coordinate invariance. No new SAT grammar replay or minimum SAT gate bound in this round. Existing five-gate scalar and packed-witness lower bounds unchanged. No production modification or upstream submission. L-clb-036 remains open.
