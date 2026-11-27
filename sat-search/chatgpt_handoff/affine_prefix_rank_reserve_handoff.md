# Affine-prefix rank reserve and explicit quartic lower bound

Date: 2026-11-26. Starting head verified 641f35b28ed2864cd2f0e85b9120291a52718bb8. Extends [joint augmentation rank](joint_augmentation_rank_handoff.md), [first-gate scalar theorem](first_gate_translation_proof_handoff.md), and earlier stable gate ledgers. New paper gate-allocation theorem and explicit quartic family, with finite regression. Not independently audited or Lean checked. No novelty/priority claim or unrestricted superlinear SAT bound. L-clb-036 remains open.

## 1. Model and prefix reserve

Let an actual XOR-AND circuit on n raw bits have t AND gates, all counted (not merely the mixed subset for a previously chosen partition). Affine gates, constants and fan-out are free. Contract affine wiring into
    g_i=(ell_i(x)+alpha_i.g_<i)(m_i(x)+beta_i.g_<i)
where ell_i,m_i are affine primary-input functions and alpha_i,beta_i are formal GF(2) dependency masks. Output is an affine combination of primaries and ANDs. For a prefix of p gates let S_p be the linear span of the linear parts of ell_i,m_i for i<=p, and K_p=S_p^perp. Thus K_0=GF(2)^n, K_p are nested, and dim K_p>=n-2p with codimension increment at most two per gate.

Introduce two independent blocks: data k ranges over K_p (represented by dim K_p independent coordinates using any linear basis), query q ranges over the ENTIRE GF(2)^n, not merely a complement. The input supplied to the original circuit is x=k+q. Every prefix gate is query-only in the contracted syntactic model: its primary affine terms have no k component, and induction over its formal dependencies gives the claim. Hence at most t-p original ANDs are syntactically mixed. Pure-side preprocessing is allowed for free when applying the sharp joint-rank theorem, but the p reserved gates are already counted once in the original total AND budget. The remaining gate count includes any later pure gates as well, which only weakens the bound. No new gates need be charged for the linear input map in the XOR-AND model.

For a scalar target F define
    R_F(K)=rank_GF(2) of M_K(k,q)
    M_K(k,q)=F(k+q)+F(k)+F(q)+F(0).
The rows are all translation differences D_k F(q) anchored at q=0. This is a canonical invariant of K, independent of basis or complement. For multiple outputs define J_query(K) as the dimension of the span of all these row functions of q across all outputs and k, and J_data(K) analogously using column functions of k. One may take J=max of the two common factor dimensions. The joint theorem bounds each separately. For a scalar the two equal R_F(K). Applying sharp mixed-rank ceiling gives
    R_F(K_p)<=2^(t-p+1)-2
and likewise J(K_p)<=2^(t-p+1)-2, including p=t where the cap is zero. Consequently
    t>=p+ceil(log2(R_F(K_p)+2))-1.
Use integer arithmetic if implementing large rank-to-gate bounds. This is a distinct-gate charge: p reserved gates and t-p remaining gates are disjoint. The general ceiling uses the earlier paper proof; independently the special case with t-p<=1 follows directly because the product of two pure-side sums has mixed part consisting of at most two separable products, and affine output sums do not increase it.

An arbitrary ancestor-closed set A of original AND IDs can replace the prefix. Take S_A to span its raw affine ingress forms, K_A=S_A^perp. All dependencies of a gate in A are also in A (syntactically), so those |A| gates are query-only and the same bound holds with p=|A|. For a general subset first take its ancestor closure and count that union once. For every subspace K, let A(K) consist of gates whose entire ancestor ingress span lies in K^perp; this is ancestor-closed and yields
    |A(K)|+ceil(log2(R_F(K)+2))-1<=t.
The analogous common joint bound holds. This is a family of simultaneous constraints on the SAME original gate ledger, not permission to sum lower bounds for different K or ancestor closures.

Full query domain is important: a usual partition into K and a complementary subspace C restricts q to C and can lose rank. Here q can vary through K as well, exposing translations inside each coset. Duplication of input coordinates in this derived function is only a linear pullback; it does not invent mixed gates in the prefix. R_F(K) is monotone under inclusion K. Its value is the dimension of the span of anchored D_k F for k in K, NOT just the maximum rank of a derivative along a basis direction.

## 2. Topology-independent rank-profile criterion

For each integer p>=0 with 2p<=n define
    r_p(F)=min_{dim K=n-2p} R_F(K).
If a realization has at least p gates, its actual K_p has dimension>=n-2p and contains a subspace of that exact dimension. Monotonicity gives R_F(K_p)>=r_p(F). Thus every such realization obeys
    t>=p+ceil(log2(r_p(F)+2))-1.
The qualification t>=p matters; if proving a lower bound larger than p, first establish t>=p independently, or split off t<p as a separate case. For joint query-side rank the same argument works; joint data-side rank under K restriction cannot increase either, so max also monotone. Multiple different p can be optimized by a maximum, not by summing the reserves. Computing min over all subspaces can be expensive; no efficient algorithm claimed.

A useful scalar two-plane criterion: suppose for every independent a,b in GF(2)^n, D_a D_b F is nonconstant. Then for K=span(a,b), R_F(K)=3. Proof: its three nonzero anchored rows are D_a F, D_b F, D_(a+b) F modulo constants. Their span is also that of D_a F,D_b F,D_aD_b F, because D_(a+b)=D_a+D_b+D_aD_b. Suppose a nontrivial linear combination of these three functions is constant. Applying D_b annihilates the latter two and implies the coefficient of D_a must be zero, since D_aD_b F is nonzero. Applying D_a likewise kills the coefficient of D_b. The remaining term cannot be a nonzero constant by assumption. Thus the three classes are independent. Every larger K has rank at least 3. Also every nonzero a has nonconstant D_a F, by choosing independent b.

## 3. Explicit family beating aggregate rank and ingress bounds

On n=2m bits with m>=2, write coordinates (x_i,y_i), and define
    q_i=x_i y_i,
    F_m=sum_(i<j) q_i q_j.
All arithmetic GF(2). This is an explicit quartic; an O(m)-AND upper construction computes the m q_i then m-1 products q_j*(sum_(i<j)q_i), for total 2m-1. Not a SAT restriction or superlinear witness.

Let omega be the nondegenerate alternating bilinear form on GF(2)^(2m):
    omega(a,b)=sum_i (a_(x_i)b_(y_i)+a_(y_i)b_(x_i)).
The degree-four polarization of F_m is the alternating 4-linear form
    P(a,b,c,d)=omega(a,b)omega(c,d)+omega(a,c)omega(b,d)+omega(a,d)omega(b,c).
Proof: both sides alternating and multilinear; evaluate on four distinct coordinate basis vectors. The left is 1 exactly for supports consisting of two complete coordinate pairs, and zero otherwise; the right has the same values by the definition of omega. Repeated basis vectors vanish by alternation. This characterization uses characteristic two and square-free monomials, not division by 4!.

For independent a,b, the quadratic homogeneous part of D_aD_b F_m has polarization (c,d)->P(a,b,c,d). Set u=omega(a,.),v=omega(b,.); they are independent linear forms by nondegeneracy. If omega(a,b)=0 then P(a,b,.,.)=u wedge v is a nonzero alternating form of rank two. If omega(a,b)=1 it is omega+u wedge v, also nonzero: omega has rank n>=4 whereas u wedge v has rank two. Thus D_aD_b F_m has degree exactly two for EVERY independent pair. In particular the two-plane criterion applies without an enumeration assumption.

The affine ingress dimension lower bound is t>=m: if t<m then the common kernel of all 2t raw ingress forms contains a nonzero vector a. Every gate is invariant under translation by a, and the affine output primary contribution changes by at most a constant. Thus D_a F_m is constant, contradiction.

Now assume t=m. Reserve the first p=m-1 gates. Their common kernel K_p has dimension at least two, hence R_F(K_p)>=3. At most one remaining mixed gate has rank cap 2. Contradiction. Therefore
    multiplicative_complexity_GF(2)(F_m)>=m+1.
This particular proof only needs the elementary one-mixed-gate ceiling, so is independent of any unaudited general augmentation proof. It also gives a lower bound on ordinary binary Boolean gates, because every binary Boolean function is an affine combination of its two input bits and their product and costs at most one AND in the relaxed model.

Compare ordinary aggregate mixed translation rank R_F(GF(2)^n). Since the polynomial degree is four, the mixed ANF matrix has nonzero entries only for row degree i>=1,column degree j>=1,i+j<=4. Cover these by all degree-one rows, all degree-one columns, and all degree-two rows. Thus R<=2n+binom(n,2)=n(n+3)/2. For n=2m with m>=6, this upper bound is <=2^(m+1)-2 (at m=6,90<=126; induction or exponential growth gives all larger m). Consequently even the sharp aggregate rank ceiling cannot rule out t=m for this family, whereas the prefix rank reserve does. The ingress count alone only gives m. No claim that other existing lower-bound methods cannot also establish m+1 or more, nor that m+1 is the exact complexity. No priority claim.

At n=12, exhaustive ANF coefficient calculation gives full mixed translation rank 90, aggregate rank lower bound 6, ingress lower bound 6, new reserved-prefix lower bound 7. Finite regression also gives n=4,6,8,10 full mixed ranks 14,26,44,64 respectively. The new bound at these sizes equals the aggregate rank lower bound; strict improvement is asserted for m>=6 using the analytic comparison.

## 4. Executed regression

Run node affine_prefix_rank_reserve_check.js (no dependencies). Checker body executed in JavaScript tool runtime before upload, not separately in Node or Lean. Seed 870039:
- 240 pseudorandom actual XOR-AND circuits with 2..7 raw input bits and 1..6 ANDs; 1058 prefixes (including empty/full), checks of codimension, scalar and common joint query-side rank cap, and exact purity of 2139 reserved gate instances. Output masks and all gate outputs included in the common span. Complete truth tables, exact BigInt GF(2) elimination.
- For every prefix choose a complement greedily and compare standard complement-only response rank to full-query canonical rank. Full-query rank never smaller, strictly greater in 263 cases. No claim about typicality of this fraction.
- Explicit quartic: all 35 two-planes in dimension 4, all 651 in dimension 6, all 10795 in dimension 8, each checked for exact full-query rank 3 by truth tables and for the quadratic derivative identity. Additionally 1200 distinct deterministically sampled two-planes in each of dimensions 10 and 12 checked for quadratic derivative identity (not full truth-table mixed rank). Total 13881 planes, 445435 exact polar coefficient comparisons. Complete enumeration counts match Gaussian binomial coefficient (2^n-1)(2^n-2)/6. Exact full mixed ANF ranks for all five n. All assertions passed.
Checker commit 6abf2c830ba40aaf3a35f9290fdaf32c58b01576.

## 5. Limitations and next attack

The profile method is a sound mechanism for reserving distinct gates while exposing a robust nonlinear obligation on a leftover subspace. It is not an additive lower bound over arbitrary unrelated partitions. For scalar F, R_F(K)<=2^dim K-1. Therefore the dimension-only robust minimum r_p yields p+ceil(log2(r_p+2))-1<=n-p, so optimizing that scalar minimum alone cannot give an unrestricted superlinear lower bound. To go further need structural constraints on the entire nested flag or multiple incomparable ancestor-closed sets, or combine with independently justified charges for actual affine wiring and nonlinear gates. The quartic example is a useful non-SAT benchmark showing strict improvement over the two specific aggregate methods, not progress to a new SAT-wide asymptotic bound. Investigate whether restrictions of SAT grammar exhibit similarly robust rank on low-dimensional affine subspaces that must survive after many gate eliminations; avoid assuming arbitrary affine changes preserve the SAT promise. Consider extending from reserve counts to disjoint nonlinear obligations across ancestor-closed components; include shared-routing counterexamples. Independent review/Lean formalization of the preceding joint theorem still outstanding. No production changes or upstream submission. L-clb-036 remains open.
