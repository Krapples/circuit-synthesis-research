# First-gate square-zero induction: general scalar mixed-rank ceiling

Date: 2026-11-26. Continues [joint translation rank](joint_translation_rank_handoff.md), [last-gate decomposition](five_mixed_rank_schur_handoff.md), and [translation lift](exact_mixed_rank_ceiling_handoff.md). Starting head verified d9e3f564fa63b11dddebdf0d458f1a377db07a90. Main result is a general paper proof of the scalar conjecture, with exact finite regression. Not independently audited or Lean checked. The stronger joint conjecture remains open. No novelty/priority claim, physical SAT encoding update, or unrestricted superlinear lower bound. L-clb-036 remains open.

## 1. First-gate deletion identity

Keep the previous syntactic mixed XOR-AND model (pure-side gates have no mixed ancestors; arbitrary pure-side preprocessing allowed) and generic translation lift:
    G_i=(z_(2i-1)+alpha_i.G_<i)(z_(2i)+beta_i.G_<i),
    H=lambda.G.
All generic G_i vanish at zero. Let a,b be the first two coordinates, G_1=ab, and z all remaining fresh coordinates. Let F_i(z) be the remaining gate outputs when G_1=0. They form exactly the same generic template with t-1 gates, deleting the first coordinate of each dependency mask and relabeling IDs. Define f(z)=sum_(i>=2) lambda_i F_i(z). Let s consist of the two coefficients of G_1 in each later pair of operands. Fixing G_1=1 shifts precisely those fresh coordinates by s. Inducting through the later gates shows that their outputs are F_i(z+s), even with reconvergence, shared gates, or arbitrary downstream output masks. Thus exactly
    H(a,b,z)=f(z)+ab*(f(z+s)+f(z)+lambda_1).
This deletes the FIRST gate, not the last. The smaller circuit is a suffix with its first-gate input fixed, not the old prefix whose rank can be too small for local doubling. The positive local rank debt counterexamples in the previous handoff therefore do not contradict this approach.

## 2. Square-zero translation lemma

For any Boolean function f on GF(2)^n let W_f be the GF(2) span of its translates T_u f, where (T_u f)(z)=f(z+u). Let R(f)=dim W_f, equivalently the rank of the full translation matrix (entries f(x+y)). Define D_u=T_u+I. Over GF(2), D_u^2=0 since T_u^2=I. These operators all commute, preserve W_f and commute with every translation.

Suppose f is nonconstant. Pick a maximum-degree ANF monomial with nonempty support S. Define D_S=product_(i in S) D_(e_i). The finite difference D_(e_i) deletes variable i from each ANF monomial containing i and annihilates monomials not containing i. Since no strictly larger support can contain S, D_S f=1. Also D_S^2=0 since S is nonempty and the factors commute and square to zero. This proves in particular that 1 belongs to W_f.

For any direction s and lambda in GF(2), set L=D_s+lambda D_S. Both summands are commuting square-zero operators, hence L^2=0. L preserves W_f. Put d=dim L(W_f). Its image is in its kernel, so 2d<=R(f). Furthermore, by commutation with translations, L(W_f) is exactly W_(Lf); therefore d=R(D_s f+lambda).

Introduce fresh Boolean variables a,b. For h=f+ab Lf, define a graph map Phi(w)=w+ab Lw. Then
    W_h = Phi(W_f) directsum a L(W_f) directsum b L(W_f).
Proof of equality: translating in z gives every Phi(T_u f), hence their span Phi(W_f). Subtracting the translate by a or b from each such function gives b L(T_u f) or a L(T_u f); these generate the second and third spaces. Every translate in all variables has form Phi(T_u f)+(epsilon*b+eta*a+epsilon*eta)L(T_u f), for fresh shifts epsilon,eta. The extra term L(T_u f) lies in Phi(W_f), because Phi(Lw)=Lw by L^2=0. Thus there are no other needed generators. Independence follows from the unique expansion in the four fresh monomials 1,a,b,ab: Phi(w)+a p+b q=0 implies w=0,p=0,q=0. This is a direct sum in the function vector space, not an assumption of independent circuit branches.

It follows that
    R(h)=R(f)+2R(D_s f+lambda)<=2R(f).
This lemma holds for any nonconstant Boolean f, not only a circuit template; no bound on degree or on number of translated terms is assumed. The extra lambda constant is crucial and is handled by D_S; merely asserting D_s f+lambda is an ordinary first difference would be wrong.

If f is constant c, h=c+lambda ab. Its rank is 4 when lambda=1 (nondegenerate quadratic in fresh bits), 1 when lambda=0,c=1, and 0 when both zero. In the generic first-gate application f(0)=0, so only c=0 is possible.

## 3. General scalar theorem

Induct on t for generic templates. For t=0 H=0. For t>=1, apply Section 1. If f=0, H is either zero or ab and its full translation rank is at most 4<=2^(t+1). Otherwise f is nonconstant and a generic (t-1)-gate output, so the induction hypothesis and Section 2 give R(H)<=2R(f)<=2^(t+1). This also covers dead first gates and arbitrary output masks. No hypothesis on dependency rank or topology.

By the earlier coefficient-matrix border identity, R_mix(H)=R(H)-2 for nonconstant H; for zero H mixed rank is zero. For completeness: in the full translation ANF coefficient matrix, the nonempty/nonempty block is C(H), the added row/column is the nonconstant coefficient vector c(H), and a highest-degree nonempty support with coefficient 1 has zero row in C(H). Hence c(H) is outside its column space; the symmetric border adds exactly two ranks. Mixed ANF rank equals doubly anchored truth-table rank by invertible Boolean Mobius transforms.

The generic lift of an actual syntactically t-mixed-AND circuit is H(P(x)+Q(q)) plus pure output terms. Pullback of the mixed tensor in each side cannot increase rank (work modulo constant functions or anchor both sides). Hence for t>=1,
    R_mix(F)<=2^(t+1)-2.
For t=0 mixed rank is zero. Equality of the universal maximum is attained by the previously proved rank-one chain with independent side bits, G_i=(G_(i-1)+a_i+b_i)(c_i+d_i), G_0=0. Each step adds two pure cross terms and two independent copies of the earlier mixed factor space, giving exact rank recurrence R_i=2R_(i-1)+2. Therefore
    R_max(t)=2^(t+1)-2 for every t>=1.
This proves the previous scalar conjecture by a paper argument, without relying on the finite enumeration. It does NOT prove the stronger joint conjecture, a bound for semantic mixed gates with mixed ancestors classified as pure, or any new unrestricted superlinear lower bound. The model relaxes XOR and pure preprocessing costs, so the mixed lower bound also lower bounds total binary gate count where the relevant circuit reduction applies.

## 4. First-gate joint update and remaining joint conjecture

For the old suffix family F_i define W=sum_i W_(F_i), and let D(W)=span{D_u w:u in GF(2)^n,w in W}, the joint difference space. If the family contains a nonconstant function then 1 in D(W) by the iterated-difference argument (all its translates belong to W). Joint mixed factor space is the image of D(W) modulo constants, so J_old=dim D(W)-1. Indeed anchoring D_u F_i at z=0 gives exactly the mixed response factors; D_u T_v F_i=D_(u+v)F_i+D_v F_i, so no extra factors from taking translates first. Via the Mobius identification this is the common image of the mixed coefficient matrices. For the empty/constant family J_old=0.

Let L=D_s (no lambda needed for individual later gate outputs); let B=span(1,LW). The new gate family consists of ab and Phi(F_i)=F_i+ab LF_i. Its full joint translation span is
    Phi(W)+span(ab)+aB+bB+span(1).
When W contains a nonconstant function the last constant term is already in Phi(W); this full space decomposition is not needed to assume independence of generators. The joint difference space of the new family is exactly
    Phi(D(W))+aB+bB
when W contains a nonconstant function. To see this, z differences of Phi(W) give the first space; fresh differences of Phi(W) give aLW,bLW and their double differences LW. Fresh differences of ab generate a,b,1. Since LW subset D(W) and L^2=0, LW=Phi(LW) is already in the graph. Old differences of aB,bB stay in these spaces because B translation invariant; fresh differences give B subset D(W), and B=Phi(B) by L^2=0 and L1=0. Thus no other directions arise. The graph and aB,bB spaces are independent by fresh monomial expansion. Consequently
    J_new=J_old+2 dim B.
If no nonconstant suffix function exists, the generic suffix must have no gates (every generic gate has its fresh-pair monomial); then J_new=2 and B=span1, so the same identity holds separately. This is the FIRST-gate joint formula, different from the previous last-gate update.

Sufficient remaining target: show for every p-gate generic suffix family W and every direction s,
    dim(span(1,D_s W)) <= 2^p.
For p>=1 this is equivalent to dim D_s W<=2^p since a nonzero translation-invariant function space contains 1 (apply a maximum-degree derivative to a nonconstant member, or take the constant member), and the zero case has B dimension 1. Then induction using J_new=J_old+2 dim B yields J_new<=2^(p+2)-2. Square-zero alone only yields dim D_s W<=dim W/2; W now sums all gate translation spaces and may have dimension larger than the scalar bound 2^(p+1). The scalar proof cannot be applied to this family by pretending it is one function. Do not claim the stronger conjecture is proved. This directional joint-space bound may be easier than the old weighted residual inequality; finite tests below passed but do not establish it.

## 5. SAT consequences and limitations

For the abstract packed shared-witness F(H,S,Q)=OR_(j in Q) AND_(i in S) H_ij, exact mixed rank is (2^m-1)(2^ell-1), from earlier rank-spectrum proof. Thus universally in the syntactic mixed model
    t >= ceil(log2((2^m-1)(2^ell-1)+2))-1.
For m,ell>=2, the quantity inside log lies strictly between 2^(m+ell-1) and 2^(m+ell): lower bound follows from (1-2^-m)(1-2^-ell)>=9/16>1/2, upper from 2^m+2^ell>3. Hence t>=m+ell-1. For ell=2 this is m+1, exceeding the old data information bound m by one; for larger ell the information bound ceil(m*ell/2) often dominates. This rank-only theorem cannot produce a superlinear lower bound in total input length, since mixed rank <=2^min(d,k) and its logarithm is at most min(d,k). Shared-witness function has a linear-size circuit. No new claim about physical encoding lengths, SAT grammar or unrestricted SAT gate constants; combine only at parameters where earlier encoding premises hold. For L-clb-036 the remaining challenge is a structural accounting theorem combining many such obligations without charging overlapping gates repeatedly.

## 6. Executed regression and follow-up

Run node first_gate_translation_proof_check.js. Checker body executed in JavaScript tool runtime, not separately in Node or Lean. Seed 870035, 1100 pseudorandom generic circuits with 1..7 gates and random output masks; 557 masks include first gate, 371 cases have f=0. Exact sparse GF(2) ANF operations; verifies first-gate deletion by polynomial equality, maximum-degree difference gives 1, full rank equality R(H)=R(f)+2R(D_s f+lambda) and doubling in each nonconstant case, zero cases, mixed/full border, and scalar upper bound. Max sampled full rank 256. Also verifies exact joint first-gate formula for all 1100, with no joint conjecture violation; one random direction per circuit tested for directional joint bound, no violations. Sampled only, not exhaustive. 200 additional arbitrary nonconstant Boolean polynomials in 1..5 old variables (random coefficients, shifts and lambda) verify exact scalar rank lemma and direct truth translation matrix rank versus ANF coefficient ranks independently. All assertions passed. Checker commit 18fe599eb608506f996f94c246c0e4137ef8bb16.

Brief public literature search found NIST's work on multiplicative complexity and linearity dimension (https://csrc.nist.gov/pubs/journal/2020/07/boolean-functions-with-multiplicative-complexity-3/final) as related context, not a source for this proof and not sufficient for any originality claim. Main proof is self-contained. Next: independently audit the first-gate deletion and square-zero graph lemma, formalize in Lean; attempt joint directional bound and use scalar theorem to replace old 3^t scalar caps where the syntactic hypotheses apply. No production code modified or upstream proof submitted. L-clb-036 remains open.
