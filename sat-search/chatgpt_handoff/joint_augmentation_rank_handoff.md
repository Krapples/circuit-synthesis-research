# General joint translation rank ceiling via augmentation operators

Date: 2026-11-26. Continues [joint directional recursion](joint_directional_recursion_handoff.md), [first-gate scalar proof](first_gate_translation_proof_handoff.md), and [joint rank update](joint_translation_rank_handoff.md). Starting head verified ad32b0749b95ef54d4a8a5ae1e7b489ca553278a. Main result is a general paper proof of the stronger joint conjecture, using a strengthened induction over all characteristic-two fields. Includes exact regression, but no independent audit or Lean certification. No originality claim, new physical SAT grammar, or unrestricted superlinear lower bound. L-clb-036 remains open.

## 1. Translation algebra and strengthened invariant

Use the previous generic mixed XOR-AND template
    G_i=(z_(2i-1)+alpha_i.G_<i)(z_(2i)+beta_i.G_<i).
All coefficients defining the Boolean template are GF(2); use any characteristic-two field k for linear spans. Let W_t(k) be the k-span of all translates of all t gate outputs as functions on the Boolean cube. It is invariant under translations. Write D_j=T_(e_j)+I. The translation group algebra is
    R_n(k)=k[D_1,...,D_n]/(D_1^2,...,D_n^2).
Indeed the products of the D_j are a basis by invertible change of basis from the translation group elements. Its augmentation ideal m consists of polynomials with zero constant coefficient in this basis. Every element A of m satisfies A^2=0 by commutativity and characteristic two. An element of R with nonzero constant coefficient is a unit: if P=c+N, N in m and c nonzero, P^-1=c^-1+c^-2 N.

**Strengthened theorem:** for every t>=1, every generic template with t gates, every characteristic-two field k, and every A in m, rank_k(A|W_t(k))<=2^t. (For t=0, W=0.) This is stronger than the previous directional conjecture; the universal quantifier over fields is essential to the induction. It is not merely a bound for single directions. Scalar proof previously established separately.

For any nonzero translation-invariant subspace of functions on the Boolean cube over k, the constant 1 belongs to the space: apply the iterated difference on a maximal-degree ANF support to any nonzero function and divide by its resulting nonzero scalar. This also handles a nonzero constant function directly.

## 2. First-gate representation

Delete the first gate ab. Remaining generic gate outputs F_i(z) are those at first-gate value zero. Fixing the first-gate value to one shifts the remaining fresh variables by one fixed Boolean vector s (the direct dependency coefficients), so after restoring the first gate their outputs are Phi(F_i), where
    L=D_s=T_s+I,
    Phi(w)=w+ab Lw.
Let p=t-1, W=W_p(k), B=span_k(1,LW). For p>=1, 1 in W. B is translation invariant, contained in W, and LB=0. Since L^2=0, the exact full translation-space decomposition from the preceding handoff is
    Wnew = Phi(W) directsum k*ab directsum aB directsum bB.
For clarity: old translations generate Phi(W); fresh differences give aLW,bLW and LW, and translating ab gives a,b,1. LW is in Phi(W) since Phi(Lw)=Lw, and 1=Phi(1). The four spaces span a translation-invariant space containing the gate outputs; independence follows from expansion in the fresh Boolean monomials 1,a,b,ab. The old translation algebra acts on these coordinates in the natural way; on k*ab its action is the scalar constant coefficient. This proof is valid over k, not only GF(2).

## 3. Exact normalized augmentation rank

Every augmentation element on the new variables can be written uniquely as
    T=A+D_a P+D_b Q+D_aD_b R,
where A is in the old augmentation ideal and P,Q,R are old translation algebra elements. First suppose P is a unit. Multiplication by its inverse is an invertible operator on Wnew, commutes with T and every old translation, preserves rank, and replaces A,Q,R by old operators of the same types. Normalize P=1. Let q0,r0 be the constant coefficients of Q,R.

Use coordinates Phi(w)+a u+b v+c ab, w in W, u,v in B, c in k. By direct expansion, T sends this vector into Phi(W)+aB+bB with coordinates
    x=(A+RL)w+u+Qv+c r0*1,
    y=A u+QLw+c q0*1,
    z=A v+Lw+c*1.
There is no remaining ab coordinate, since A kills constants. All old operators commute with L, preserve W and B; A^2=L^2=0 and LB=0. Therefore
    y=(A+RL)x+Qz.
Verification: (A+RL)^2=0 in characteristic two, RL kills B and constants, and Q commutes with A. Thus projection onto (x,z) is injective on the image. The x projection has image AW+B. For x=0, solving for u is possible exactly when Aw belongs to B (since RLw,Qv,c r0 all lie in B), with v,c arbitrary. The remaining z-coordinate image is
    span(1,LZ,AB), Z=A^-1(B) in W.
AB=A(LW)=L(AW) subset LZ since A^2=0 and AW subset Z. Hence the exact rank formula is
    rank(T|Wnew)=dim(AW+B)+dim(span(1,LZ)).
This generalizes the prior two-direction identity to arbitrary augmentation operators A and arbitrary Q,R; the exact value after normalization does not depend on Q,R. The roles of unit normalization and fresh-coordinate pivot are important; do not use this formula for unnormalized T with nonunit P.

If L acts as zero on W, then B=k*1 and LZ=0, so rank(T)<=rank(A|W)+2. (If AW nonzero it already contains 1, giving a slightly sharper +1.)

Now assume L acts nontrivially on W. Its image is translation invariant and nonzero, so B=LW. Set l=dim B, E=AW, e=dim E, C=E intersect B, c0=dim C, and K=ker(L|W). Since L^2=0, B subset K. A preserves K and B by commutation, so it induces an operator Abar on K/B. Let q=rank(Abar)=dim AK-dim(AK intersect B). Compute
    dim LZ = l-codim_W(Z+K)
           = l-e+dim(C+AK).
Indeed Z=A^-1(B)=A^-1(C), and Z+K=A^-1(C+AK): the reverse inclusion follows by subtracting a suitable element of K. Hence
    dim(E+B)+dim LZ
      = e+l-c0+l-e+dim(C+AK)
      = 2l+dim AK-dim(C intersect AK)
      = 2l+q,
since AK subset E. Also 1 in LZ: LZ is translation invariant; alternatively if nonzero it contains 1. Need show it is nonzero: choose w with Lw=1 (exists since B=LW contains 1). This alone need not imply Aw in B, so use translation-invariant LZ and the following argument. Let M=L(W), and select w with Lw nonzero. Choose a maximal-degree nonzero ANF monomial of Lw and apply corresponding product D_S; then L(D_S w) is a nonzero constant. To ensure D_S w in Z may require more. Instead note: if A acts nontrivially on K/B, this does not ensure LZ nonzero; but A preserves B and squares to zero. The map induced by A from W/K to W/(Z+K) can have full rank in principle. We must prove LZ contains 1 for all nonzero L in this setting. A direct argument uses a w with Lw=1 chosen to have Aw in B: use the generic fresh-pair structure of the OLD circuit. Since s is a nonzero shift vector, select the first gate j with a nonzero coordinate in s. Its predecessor outputs are invariant under the shift. Then G_j is product of two operands u,v whose shifts are constants alpha,beta not both zero. Its difference L G_j=alpha v+beta u+alpha beta. One fresh coordinate in the shifted linear combination of u,v has coefficient 1; apply that coordinate difference to G_j to obtain w equal to one operand (u or v). This w has Lw=1 and belongs to W. It equals a fresh primary coordinate plus a linear combination of predecessor gate outputs. Because the latter are invariant under s, their contribution under A may not automatically belong to B. However each predecessor output g_i is in B if it occurs in an operand of G_j? Not necessarily both operands. More directly, if beta=1, choose w=v by differentiating G_j in the u fresh coordinate. Then w has Lw=1. To get Aw in B, it suffices that every translate difference of v lies in LW. Since L G_j=alpha v+beta u+alpha beta, if alpha=0, L G_j=u, not v, so this is not immediate.
The issue is resolved by the general module argument in the following paragraph, which does not require this stronger claim.

**Constant correction (required for generality):** if LZ is zero, the exact formula is 2l+q+1 rather than 2l+q. In that case dim LZ=0 implies l=e-dim(C+AK). In particular e>=l. More importantly, LZ=0 implies Z subset K, and ker A subset Z subset K. Since A^2=0, AW subset ker A subset K. The rank-nullity chain gives dim K>=dim ker A, and rank(A|W)=e. We only need bound 2l+q+1 using the pencil, except possibly if q=0 and l=2^p. If q>=1, 2l+q+1<=2(l+q). If q=0 and l<2^p, 2l+1<=2^(p+1). In the remaining case q=0 and l=2^p, the conjectured smaller-operator cap implies e<=2^p=l, so e=l and dim LZ=0 forces C=0 and AK=0. But C=AW intersect LW cannot be zero if both images are nonzero translation-invariant spaces, because both contain 1. Since e=l>0, contradiction. In fact even without the saturation condition, if LZ=0 then e>=l+1 since C contains 1. Therefore l<=2^p-1 directly from the induction bound for e. This proves the correction is harmless. Use the exact formula with +epsilon, epsilon=1 if LZ=0 and 0 otherwise. The prior regression observed no epsilon=1 cases, but no general nonvanishing proof claimed. This explicit correction avoids relying on a hidden nonvanishing assumption in the rank calculation.

## 4. Matrix-pencil lemma and induction

For commuting square-zero linear maps L,A on a finite-dimensional space W over a characteristic-two field k, let l=rank L and q=rank of Abar on ker L/im L. Over k(xi) one has
    rank(L+xi A)>=l+q.
Proof: choose basis in three blocks B=im L, H a complement of B in ker L, and C a complement of ker L in W, with L mapping C isomorphically to B. The matrix of L has identity at rows B, columns C, zero elsewhere. The matrix of A in the H/H block represents Abar, because A maps ker L into itself and B into itself. Take a nonsingular q-by-q minor of that block. In the pencil take the (l+q)-square minor with all B rows and C columns, together with the H rows/columns of that q minor. Its determinant has leading term xi^q times the nonzero determinant of the selected Abar minor: the upper-left I+xi*(...) block is a unit in formal power series, lower-right xi*Abar_minor, both off-diagonal blocks O(xi). Schur elimination yields lower-right xi*Abar_minor+O(xi^2). Thus the determinant is a nonzero polynomial. The argument works also for l=0 or q=0 with empty minors.

Induct simultaneously for all characteristic-two fields. For t=1 the full translation space of ab has basis 1,a,b,ab, and every augmentation operator squares to zero, so rank<=2. For p>=1 assume the theorem at p gates. Normalize any T with unit P as above. If L=0 on W, rank(T)<=2^p+2<=2^(p+1). If L nonzero, the matrix pencil L+xi A is itself an old augmentation element over k(xi); induction bounds its rank by 2^p. W over the extension is precisely the scalar extension of W over k, since the same finite collection of translated Boolean outputs spans it. Thus l+q<=2^p. With epsilon correction from Section 3,
    rank(T)=2l+q+epsilon<=2^(p+1).
For epsilon=0 this is immediate from 2l+q<=2(l+q). For epsilon=1 and q>=1 the same doubled bound holds. For epsilon=1 and q=0, l<=2^p-1 as shown above, giving the result. This completes the unit-P case.

For arbitrary P, extend scalars to k(eta) with independent indeterminate eta and consider T+eta D_a. Its coefficient P+eta has nonzero constant coefficient and is a unit in the old algebra over that field. Apply the unit-P result (including induction on still further field extensions if necessary). Rank of T is no greater than rank of T+eta D_a over k(eta): every nonzero minor at eta=0 is a nonzero polynomial minor. Thus specialization preserves the bound and completes the induction for arbitrary T. This is a proof for every t, not an extrapolation from the finite replay.

## 5. General joint rank theorem and exact full module dimension

For a nonempty suffix of p gates, define D(W) as the span of all directional difference images on W. It contains 1 and its dimension is J_p+1 (quotient by constants gives the common anchored mixed response factors, equivalent to common mixed ANF coefficient column space under Mobius transform). The previous exact first-gate joint update
    J_(p+1)=J_p+2 dim(span(1,LW))
holds over k by the same graph argument: the new joint difference space equals Phi(D(W)) directsum aB directsum bB, because L W subset D(W), LB=0, and fresh differences of ab generate a,b,1. For p=0 the first gate has J1=2 directly. For p>=1, if LW nonzero it contains 1, and otherwise B has dimension 1. The augmented theorem therefore gives dim B<=2^p, so induction from J1=2 proves
    J_t<=2^(t+1)-2
for every t>=1. Sharpness follows from the previous scalar rank-one chain (its final scalar rank equals this ceiling; the joint space contains that scalar factor space). Hence the exact universal maximum of the joint mixed rank is 2^(t+1)-2. In fact, the graph decomposition also gives
    dim Wnew=dim W+1+2 dim B.
Subtract the exact J update, and use dim W1=4,J1=2: dim W_t=J_t+t+1 exactly. Equivalently dim(W_t/D(W_t))=t, explaining the previous sampled equality. Full joint translation span can exceed the scalar bound by t-1, while every augmentation operator still obeys the stronger rank bound.

For actual circuits with arbitrary pure-side preprocessing, common ingress pullback sends the generic mixed factor spaces linearly to actual factor spaces modulo constants; hence their dimensions cannot increase. A family of affine output masks of t syntactically mixed gates, plus arbitrary pure-side outputs, satisfies the same joint rank ceiling on each side. This is a simultaneous result, not a sum of separate output lower bounds. Does not apply to semantic mixed counting with pure gates having mixed ancestors unless an additional valid reduction is proved. For any required common mixed dimension J, t>=ceil(log2(J+2))-1. No superlinear size lower bound from this alone: joint factor spaces are still bounded by the dimension of the input-side function spaces (logarithm at most the number of bits on that side). Need structural allocation over different partitions or cuts with no repeated charge. No new physical SAT encoding or stronger unrestricted bound this round.

## 6. Regression and status

Run node joint_augmentation_rank_check.js. Checker body executed in JavaScript tool runtime, not separately in Node or Lean. Seed 870038: 480 pseudorandom generic suffix circuits, 80 at each p=1..6. Exact ANF bitsets and lowest-bit GF(2) elimination. Tests arbitrary augmentation operators (not just directional differences), square-zero, normalized exact rank formula dim(AW+B)+dim(span(1,LZ)), unit multiplication, joint first-gate update, and cap at p and p+1. 350 cases L nonzero, 130 zero. In nonzero cases the checker also asserts rank=2l+q (i.e. epsilon=0); all sampled cases passed, but the general proof above allows epsilon=1 rather than relying on sampled nonvanishing. Positive homology rank in 23 cases, largest observed q=12. 350 exact GF(4) pencil specializations L+omega A checked against the induction cap and observed rank>=l+q in all samples. This is a regression, not a replacement for the rational-function minor proof; a fixed specialization need not preserve generic rank in general. Max sampled augmentation ranks p=1..6: 2,4,8,16,32,64. All assertions passed. Checker commit e540c56eff3cae681da7db5dab688ddbaa7e5c47.

Main results: paper proof of general joint ceiling, stronger augmentation operator bound, exact module quotient generator dimension. Independent review and formal verification outstanding. Next prioritize formalizing matrix-pencil lemma, normalized augmentation action (including constant correction), field extension/specialization and first-gate lift; then use joint rank obligations in multi-partition ledgers and seek a genuinely stronger structural bound, rather than further enumerating the now-proved rank ceiling. No production modifications or upstream submission. L-clb-036 remains open.
