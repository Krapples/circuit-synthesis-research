# Symplectic higher-order rank profiles and stronger affine-reserve lower bounds

Date 2026-11-26. Starting head verified d46f94855bbb97c9bb4d692bf0ff3dcd44476854. Extends [affine-prefix rank reserve](affine_prefix_rank_reserve_handoff.md) and [sharp joint rank theorem](joint_augmentation_rank_handoff.md). New paper proofs of structural subspace constraints and explicit linear multiplicative-complexity lower bounds. Finite regression passed; independent audit and Lean formalization outstanding. No originality claim. L-clb-036 remains open.

## 1. Higher derivative reserve, independent of sharp rank theorem

Use the contracted XOR-AND model with t total AND gates, free affine operations, n original variables. Let K_p be the common kernel of the raw primary affine ingress linear forms of the first p gates (or use any ancestor-closed p-gate set). dim K_p>=n-2p. Every reserved gate is invariant under all translations by K_p, by induction on its dependencies.

For any independent directions a_1,...,a_d in K_p, if d>=t-p+1, then the iterated Boolean translation difference D_(a_1)...D_(a_d)F is constant (possibly zero). Proof: after reserving p gates, express each remaining gate operand as a raw affine form plus a linear combination of reserved outputs plus earlier remaining gates. Collect the first two contributions into an ingress coordinate z_j(x). The remaining circuit is the generic lifted template H(z), with t-p gates, plus an output affine combination of raw inputs and reserved outputs. For a in K_p, z(x+a)=z(x)+s_a for a fixed vector s_a given by the raw affine forms, since reserved outputs are invariant. Thus iterated differences of H(z(x)) are pullbacks of iterated fixed translation differences of H. The Boolean degree of H is <=t-p+1 (reverse substitution of each AND variable into its two affine operands, reducing squares each time, increases degree by at most one). Each directional difference lowers degree by at least one, so d such differences yield a constant when d>=t-p+1. The direct affine and reserved output contribution yields only a constant after one difference, zero after two. For t-p=0 the same conclusion holds directly. This proof uses no communication-rank or augmentation theorem and works even for arbitrary, not necessarily independent directions. Therefore a nonconstant d-fold derivative supported in K_p forces t>=p+d.

There is a corresponding exact rank fact: if a basis a_1,...,a_d of K has nonconstant full product derivative D_[d]F, then the canonical full-query mixed rank R_F(K)=2^d-1, saturating the row-count upper bound. Indeed D_(sum_{i in S}a_i)=product_{i in S}(1+D_i)+1=sum_{empty!=T subset S} D_T, so the span of all nonzero-direction differences is the span of all nonempty subset derivatives, by triangular inversion. Suppose a nontrivial combination of D_T F is constant. Pick an inclusion-minimal T among its nonzero coefficients. Apply product of differences over the complement of T. Every other term contains an index outside T (by minimality) and is killed by square-zero; the selected term becomes D_[d]F. If the complement is nonempty this contradicts even nonzeroness (constant right side killed); if the complement is empty the sole possible term is already D_[d]F, contradicting nonconstancy. Hence the 2^d-1 anchored derivative classes are independent. The rank reserve also gives t>=p+d from saturation, but the preceding elementary degree argument establishes this consequence independently of the general rank theorem.

## 2. Explicit family and symplectic type

Let n=2m, with m>=2 and 2<=r<=m. Write variables (x_i,y_i), q_i=x_i*y_i, and define
    F_(m,r) = XOR_{I subset [m], |I|=r} product_{i in I} q_i.
This is the r-th elementary symmetric Boolean polynomial in the m pair products. Its degree is exactly 2r. The r=2 case is the previous quartic family.

Let omega be the nondegenerate alternating form
    omega(a,b)=sum_i (a_xi b_yi+a_yi b_xi).
The top degree-2r polarization of F is the sum over all perfect matchings of its 2r arguments of products of the corresponding omega values. Proof: this expression is multilinear and alternating (if two arguments equal, terms pairing them vanish, and other matchings pair off under their transposition); on distinct coordinate basis vectors it is 1 exactly when they form r complete coordinate pairs. This equals the top iterated-difference polarization of the given ANF. No division by r! or characteristic-zero exterior-power formula is used. In particular it is invariant under symplectic changes of basis. Under such a linear change, the degree-2r homogeneous ANF is again the same elementary symmetric polynomial in pair products (its polarization determines the coefficients on distinct basis arguments), although lower-degree terms can change due to Boolean idempotence.

For a subspace K of dimension d write h=rank(omega|K)/2. Alternating elimination gives h hyperbolic pairs in K and a radical of dimension d-2h. A symplectic basis of the whole space can be chosen so K consists of those h complete pairs and d-2h single vectors from distinct further pairs. Brief construction: split off the nondegenerate h-pair subspace and work in its orthogonal complement; the radical is isotropic there. Extend its independent vectors to hyperbolic pairs by choosing duals via nondegeneracy, adjusting the duals by adding radical vectors to make mutual pairings zero, then completing a symplectic basis of the remaining nondegenerate complement. Consequently d-h<=m, or h>=d-m.

Take independent a_1,...,a_d spanning K. The top degree-(2r-d) part of D_(a_1)...D_(a_d)F is nonzero exactly when
    d<=2r and d-h<=r
(for d<=2r). Indeed its polarization is the contraction of the top 2r-form with the d directions. After changing to the adapted symplectic basis and any basis of K (contraction changes by nonzero determinant, which is 1 over GF(2)), a nonzero matching completion exists exactly when the d vectors, occupying d-h distinct pairs, fit into r full pairs. Complete all missing partners and add enough unused full pairs; conversely no basis completion can remove any already occupied pair. If d=2r and the condition holds, the derivative is the nonzero constant 1. If d<2r and condition holds, the derivative has degree exactly 2r-d>=1, hence nonconstant. If condition fails the indicated top degree vanishes; lower-degree derivatives may still survive. No claim of total vanishing in that case.

In particular every d-plane with d<=r has a nonconstant full derivative, since d-h<=d<=r and d<2r. Every such plane has exact full-query mixed rank 2^d-1 by Section 1.

## 3. Structural subspace constraint beyond dimension

For K of dimension d and symplectic half-rank h, define
    s(K)=min(d,r+h,2r-1).
K contains an s(K)-dimensional subspace K' with a nonconstant full derivative. In an adapted basis, choose min(h,floor(s/2)) complete pairs and fill the remaining dimensions with individual vectors from unused pairs or radical. This is possible because s<=d. Its symplectic half-rank is min(h,floor(s/2)) and its occupied-pair count is max(s-h,ceil(s/2))<=r by the definition of s. Section 2 applies. (For s=0 interpret the rank lower bound as zero.)
Thus
    R_F(K)>=2^s(K)-1.
For EVERY actual reserved prefix K_p of a circuit computing this F,
    t-p >= min(dim K_p, r+rank(omega|K_p)/2, 2r-1).
This follows directly from the derivative reserve, and also from sharp mixed rank. It is a simultaneous necessary condition on the actual nested ingress-kernel flag, not a sum over different subspaces. In particular if t-p<min(dim K_p,2r-1), then
    rank(omega|K_p)/2 <= t-p-r.
If the right side is negative the profile is impossible. This forbids certain high-symplectic-rank kernels even at an admissible dimension.

Additional rank profile: any K contains an isotropic subspace I of dimension d-h (choose one vector from each hyperbolic pair and the entire radical). More generally for an isotropic I of dimension l, the anchored derivatives indexed by nonempty subsets of an adapted basis of size <=r are linearly independent. To see this, change to a symplectic basis where I consists of coordinate singles x_1,...,x_l. For a subset S of these singles of size k<=r, the highest-degree part of its subset derivative has degree 2r-k and every monomial has exactly the unpaired partners y_i for i in S and r-k full pairs outside S. At least one such monomial exists since m>=r. Distinct S of the same size give disjoint monomial support (different sets of unpaired coordinates); different sizes give different leading degrees, so a relation modulo constants is impossible by taking the smallest order present. Lower-degree terms from the basis change cannot affect the leading-degree argument. Therefore also
    R_F(K)>=sum_{i=1}^{min(r,d-h)} binom(d-h,i).
This is a lower bound, not an exact formula for arbitrary K; it can be combined with the preceding bound by taking their maximum, not their sum.

## 4. Two explicit improved gate bounds

First, t>=m by the full ingress kernel argument: if t<m then K_t contains a nonzero vector, whose first derivative is constant because all gates reserved, contrary to Section 2. Also t>=2r-1 by ordinary degree.

**Bound A.** Set p=floor((2m-r)/2)=m-ceil(r/2). Then t>=m>=p and dim K_p>=r. It contains an r-plane with nonconstant full derivative, so t-p>=r. Thus
    t >= m+floor(r/2).
This extends the quartic m+1 theorem to higher degree.

**Bound B.** Use the stronger symplectic type constraint. Suppose t<ceil((m+3r-2)/2). Since t>=2r-1, choose p=t-2r+2>=1, leaving 2r-2 gates. The assumed inequality implies 2t<=m+3r-3. Hence
    d=dim K_p >=2m-2p=2m-2t+4r-4 >=m+r-1.
Then d>=2r-1 since m>=r, and h>=d-m>=r-1. Thus s(K_p)=2r-1, contradicting t-p=2r-2. Consequently
    t >= ceil((m+3r-2)/2).
Together,
    MC(F_(m,r)) >= max(m+floor(r/2), ceil((m+3r-2)/2)).
The second term is always >=2r-1 for m>=r, so includes the ordinary degree bound. The result is a lower bound only, not an exact complexity. For example m=12,r=8 gives 24 inputs, degree16, ingress bound12, ordinary degree bound15, bound A16, bound B17. Taking m=3k,r=2k gives lower bound ceil((9k-2)/2) vs 6k inputs, asymptotically 3/4 of the number of inputs, improving the ingress and degree bounds. This is a linear, not superlinear, gate lower bound. Every ordinary two-input Boolean gate can be simulated by at most one AND with free affine operations, so it also lower bounds binary gate count in that model. The specific proof of bounds A and B uses only elementary derivative reserve, not the unreviewed sharp rank proof.

For small r proportional to m this also improves the aggregate sharp rank bound. The aggregate mixed translation coefficient matrix has total row+column degree <=2r, so cover by all nonempty rows of degree<=r and all columns of degree<=r-1; rank <=2 sum_{i=0}^r binom(2m,i). For r<=m/8, using x=1/15, sum_{i=0}^r binom(2m,i)<=15^r*(16/15)^(2m). Since (16/15)^8<2 and 15<16, aggregate rank <2^(1+3m/4)<=2^m for m>=4. The sharp aggregate cap at t=m is 2^(m+1)-2 >=2^m, so aggregate rank cannot exclude t=m. For m>=16 choose r=2 floor(m/16), giving degree bound <=m and ingress bound m, whereas Bound A gives m+floor(m/16). This establishes a linear additive improvement over those three particular lower-bound methods. It does not claim improvement over all known methods or best-known bounds.

## 5. Executed regression

Run node symplectic_rank_profile_check.js (no dependencies). Checker body executed in JavaScript tool runtime before upload, not separately in Node or Lean. Seed 870040. For m=2..6 and each r=2..m, computes explicit ANF, symplectic half-rank of sampled or exhaustive subspace bases, and exact iterated Boolean differences. Checks predicted degree of top contraction in nonvanishing cases and strict degree drop (or zero) otherwise. Exhaustive RREF subspace enumeration for ambient dimension <=6 and d<=4; for other sizes 60 pseudorandom independent bases per (m,r,d), not necessarily distinct subspaces. Total 10866 subspace-basis cases, 9218 nonconstant-top cases, 808 nonzero-constant-top cases, remaining 840 top-vanishing cases. For n<=8, 5743 direct full-query mixed rank checks on predicted saturated subspaces. 20 additional coordinate isotropic binomial rank checks (not general random isotropic verification). All assertions passed. The bound formulas are derived analytically, not inferred from the finite tests. Checker commit b6c479b56bb94964b8b61f96c7cc0ec933cccd4c.

## 6. Limitations and next direction

This round adds robust higher-order nonlinear obligations and a symplectic invariant of the actual reserved kernel flag. The lower bounds are explicit and can improve several aggregate methods by a growing linear amount, but they are not SAT restrictions and do not establish superlinear size. The general rank ledger may help exclude candidate ingress subspaces with incompatible geometric types; an engineering agent could implement the derivative and alternating-form checks on small ANFs. No production changes made to avoid interfering with the separate engineering track. No new SAT grammar, packing proof, upstream submission, or priority claim. Next target: obtain structurally robust derivatives or projected rank profiles from a valid SAT restriction, and examine whether more than one ancestor-closed reserve can be forced to spend independent gates using the geometry of their kernels. Do not add overlapping charges or assume SAT promise preserved by arbitrary affine changes. Independent review and Lean formalization remain outstanding. L-clb-036 remains open.
