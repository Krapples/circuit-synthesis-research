# Mixed dependency rank transfers and exact rank-one capacity

Date: 2026-11-26. Extends [two-sided degree-rank frontiers](two_sided_degree_rank_handoff.md) and [multi-baseline transversals](multi_baseline_transversal_handoff.md). Starting head verified e5b08cd5e4ca998d6b9d4a4b5db89d80b2dc53a6. Paper proof and finite exact replay; not independently audited or Lean checked. No priority claim. L-clb-036 remains open.

## 1. Model and mixed component

Use the previous syntactic XOR-AND partition with free affine wiring; pure data and pure query gates have no mixed ancestors. Contract affine wiring. Each mixed AND has operands u=P(x)+Q(q)+alpha.g_<i and v=A(x)+B(q)+beta.g_<i (constants can be assigned to either pure side). Let rho_i be the GF(2) rank of the two formal coefficient vectors alpha,beta. This rank is of FORMAL previous mixed output coordinates, not their semantic functions, and is invariant under an invertible change of those coordinates. Such coordinate changes need not be allowed topology changes. No claim about semantic mixed counts.

For any Boolean function f define its anchored mixed part H_f(x,q)=f(x,q)+f(x,0)+f(0,q)+f(0,0). Let D(f)=span_q H_f(.,q) and E(f)=span_x H_f(x,.). Their dimensions equal the rank of the doubly mixed ANF coefficient matrix R_(1,1): the Boolean Mobius transforms in both coordinate blocks are invertible, and anchoring removes exactly pure monomials. Equivalently these are the two function spaces of a separable rank decomposition H_f=sum_j d_j(x)e_j(q), where both factor families are independent and vanish at zero. Denote the pointwise product span of two function spaces U,V by UV. The output is an affine combination of gate outputs and primary inputs, so its mixed part lies in the sum of the gate mixed tensors; its rank is bounded by the dimension of the common data space and by the dimension of the common query space.

## 2. Local transfer lemma

Write actual operands in anchored form u=P(x)+Q(q)+c+H, v=A(x)+B(q)+d+K, where P,A,Q,B vanish at their zero inputs, c,d constants and H,K vanish on both axes. Let D_H,D_K and E_H,E_K be their mixed factor spaces. Expanding uv and deleting pure terms gives mixed contributions PB+AQ, PK+QK+different constant multiples of K, AH+BH+constant multiples of H, and HK. Consequently

    D(uv) subset span(P,A,D_H,D_K,P D_K,A D_H,D_H D_K)
    E(uv) subset span(Q,B,E_H,E_K,Q E_K,B E_H,E_H E_K).

The two constants only add terms already in D_H/D_K and E_H/E_K; the displayed bound includes them. All functions in these spans vanish at the appropriate zero. These are exact algebraic inclusions and can be evaluated on actual predecessor factor spaces, not just their dimensions. In the syntactic partition, D_H,D_K lie in the sum U of factor spaces of earlier mixed outputs named in the corresponding formal operand combination; similarly for E. One may restrict to actual ancestor sets. Using all earlier gates is a valid weaker bound. The pure contributions P,A of actual operands may include nonlinear functions of prior mixed outputs evaluated on a pure baseline; no separate cost or independence of those functions is assumed.

If rho=0 then H=K=0, so at most two new dimensions on either side.

If rho=1, either one formal dependency vector is zero, or both are the same nonzero vector (over GF(2)). Swap operands in the first case if needed. In the latter case use the Boolean identity (h+u0)(h+v0)=(h+u0)(u0+v0+1), where h is the common formal affine combination of earlier mixed outputs and u0,v0 are pure-side sums. This is an algebraic normalization, no new AND or duplicated gate charge. The second operand has no mixed part, K=0. Thus the new data-side space lies in span(P,A,D_H,A D_H), and similarly query-side. The common prefix space grows from U to U+D(g), dimension <=2 dim U+2. More precisely its increment is at most 2+dim((U+A D_H)/U). This exposes actual local factor overlap; the analogous query version also holds.

If rho=2, let R=dim U where U is the common earlier data-side factor space. The local transfer gives U+D(g) subset span(U,P,A,PU,AU,UU). For any basis f_1,...,f_R of U, products f_i f_j span UU; the diagonal products f_i^2=f_i already belong to U, so only binom(R,2) extra generators are needed. Therefore the dimension grows to at most 3R+2+binom(R,2). Symmetric for query. This bound is often loose, and should be intersected with previous two-sided degree-rank and transversal bounds.

Starting at R=0, the resulting prefix recurrence is
    rho=0: R+2
    rho=1: 2R+2
    rho=2: 3R+2+binom(R,2).
Both directional common factor spaces satisfy it. The bounds are monotone in R, so iterating on capacities is sound. No assumption of disjoint factor spaces or additivity of independent scenario charges.

## 3. Exact rank-one capacity and sharp two-gate ceiling

If every mixed gate has rho<=1, the recurrence gives R_(1,1)<=2^(t+1)-2. If z rank-zero gates and o rank-one gates are specified, the weaker ordering-free bound (2z+2)*2^o-2 follows by moving all rank-zero increments before the rank-one doublings, which can only increase the capacity. The ordered recurrence may be tighter.

Sharpness: use independent data bits a_i,c_i and independent query bits b_i,d_i, two of each per gate. Set g_0=0 and
    g_i=(g_(i-1)+a_i+b_i)(c_i+d_i),
    F=g_t.
Every gate after the first has rank-one dependency and the first has rank zero. Let H be the anchored mixed part of g_(i-1), with exact rank r and decomposition H=sum_(j=1)^r f_j(x_old) h_j(q_old), both families independent and vanish at zero. Write P,Q for its anchored pure parts. g_(i-1)(0,0)=0. Direct expansion gives
    H_(g_i)=(P+a_i)d_i+c_i(Q+b_i)
             +sum_j (c_i f_j) h_j + sum_j f_j (d_i h_j).
The 2r+2 data factors P+a_i,c_i,c_i f_j,f_j are independent: vary a_i first to eliminate the first coefficient, evaluate old data zero to eliminate the c_i coefficient, then use c_i=0 and c_i=1 and independence of f_j. The query factors d_i,Q+b_i,h_j,d_i h_j are independent by the symmetric argument. Hence exact rank is 2r+2, base r=0. This gives 2^(t+1)-2 exactly for every t>=1 with O(t) total binary gates and 4t raw bits. No superlinear size lower bound; this is a tight rank-vs-gates theorem for this dependency class. Arbitrary pure preprocessing cannot increase the stated cap because it was already permitted as arbitrary side functions in the transfer.

For t=1 or 2, rho<=1 automatically. Thus the universal syntactic mixed rank ceiling for two mixed ANDs is exactly 6, improving the previous universal caps 9 (transversal) and 8 (two-sided frontier). The sharp chain is a witness. An explicit target on four data and four query bits is F=sum_(J in A) x_J q_J, with A the four singleton supports and three pair supports {1,2},{1,3},{1,4}. Its coefficient matrix has rank 7 (diagonal), both zero baselines, and joint degree 4. It passes the previous scalar rank caps 8 and 9, and the information demand four bits per side for t=2, but needs at least three syntactically mixed ANDs by the new theorem. Does not show that every older per-candidate certificate passes or determine total minimal size.

## 4. Component-local ledger

Take the undirected connected components of the graph of mixed gate IDs with edges given by nonzero formal mixed dependencies. Pure input functions may be shared among components; they do not create mixed edges. No mixed gate has a mixed dependency outside its component. The affine output is a sum of contributions from the components plus pure terms. Apply the ordered recurrence independently to each component and add the resulting rank capacities, using rank subadditivity for output sum. No independence assumption, no double counting mixed gates. This can be much stronger than the global recurrence: t isolated seeds give rank at most 2t. The recurrence within each component can also be improved using actual predecessor factor spaces and common-span overlap. The component bound does not claim that disconnected mixed components have disjoint data or query supports or that sums of observed ranks lower-bound gate count.

## 5. Packed witness application

Recall F(H,S,Q)=OR_(j in Q) AND_(i in S) H_ij and R_(1,1)=(2^m-1)(2^ell-1). With every rho<=1, t>=ceil(log2(R_(1,1)+2))-1. For m=2,ell=3, rank 21 (full differential span 22), data length 6 and query length 5. A three-mixed-gate profile with all dependencies rank<=1 has cap 14 and cannot realize this witness, while the earlier full transversal cap 27 does not reject it, nor does the information count 2t>=6. The degree-rank frontier can pass with sufficiently generous pure preprocessing budgets: choose a>=6,b>=5 and hypothetical lifted ingress ranks u=v=6, then all thresholds have L=M=1 and the two-sided cap is 27. These are abstract feasible scalar budgets, not an existence claim for an actual circuit. Thus any realization with exactly three syntactically mixed ANDs must include a rank-two gate combining two formally independent preceding mixed combinations. No claim that three mixed gates suffice, that rank-two gates are always expensive, or that the new conditional bound improves all previous SAT bounds. The shared-witness promise still admits linear-size circuits and no new grammar replay was performed.

## 6. Executed replay

Run node mixed_dependency_rank_check.js (no dependencies). Checker body executed in the JavaScript tool runtime, not in a separate Node or Lean process. First attempt failed with mixed Number/BigInt initialization; corrected to 0n before successful replay. Seed 870032: 320 pseudorandom XOR-AND circuits plus five explicit controls (325 total), 1173 mixed gate checks with dependency ranks 0/1/2 counts 358/559/256, 2700 data-side and 2700 query-side local factor-space inclusion checks, 335 component checks, three cases where component bound improved the global recurrence. Exact anchored truth-table bitsets and GF(2) elimination used; tests check predecessor-span inclusion, normalization, local transfer, prefix bounds, output bounds and component bounds. Tight chains t=1..4 have ranks 2,6,14,30 exactly. The t=4 chain checks 65536 data/query assignments (8 data and 8 query bits). Same-nonzero-dependency normalization control also has rank 6. Seven-monomial diagonal matrix rank checked directly. Shared-witness 2x3 has mixed rank 21 and full rank 22 by exhaustive truth tables. All final assertions passed; these are finite regressions, not a formal proof.

Checker commit a9e4774f0a4a757ec56cf0024e9c3772ad59a0d9.

## 7. Next attack

Rank-two gates remain the weak point: the pairwise factor-product span may be far larger than realizable because it forgets the joint pairing of factors between data and query and the original dependence of earlier mixed outputs. Next investigate exact rank bounds for three mixed gates, exploiting the Boolean algebra of two preceding gate outputs (e.g. if g2=(g1+u)v then g1*g2=g1*(1+u)*v). Track actual product dependencies without charging pure preprocessing repeatedly; retain the sharp rank-one chains as negative controls. More generally seek a tradeoff between rank-two gate count and rank capacity, and combine with two-sided degree projections. Independently audit and formalize the anchored mixed rank transfer before making stronger claims. No production code changed or upstream submission. L-clb-036 remains open.
